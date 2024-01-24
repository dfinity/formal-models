A high-level model of how connections are established in the people parties
project within a single group of participants. The model is based on the
algorithm implemented as of February 2022, but includes changes that fix the
issues found in the analysis.

That is, we model the part of the process where the registration has already
happened, the participants have been assigned to groups, and the participants
attempt to establish audio/video connections with each other. In this process,
participants take roughly 1-minute turns at being provers. Provers initiate
video connections to other participants, who then vote for the prover based on
the video that they see. A canister is used to provide some rough
synchronization of the participants, by indicating which participant is to be
deemed the prover. Audio connections are maintained permanently between all
pairs of participants, with a fixed rule on which participant initiates the
(duplex) audio connection.

We don't model the details of connection establishment (the "session description
protocol").  Rather, we focus on how/when participants initiate, accept, and
close connections. Additionally, we model spontaneous connection failures
(which are quite realistic, as the participants are likely using the mobile
network). We also model browser refreshes, which result in a total loss of
local state at the individual participants.

Finally, we aim to cover something close to the standard partially synchronous
network model. That is, we largely assume the network to be asynchronous and
lossy, and we expect the safety properties to hold with arbitrary network
behavior. However, for certain properties to hold, such as connections being
stably established, we require the network to eventually stabilize and stop
dropping connections. In reality, we would require a long enough period of
stability. However, quantifying "long enough" makes the model complex, so
instead we resort to the usual eventually always trickery in asynchronous models
(employed by, e.g., "global stabilization time" models of partial synchrony, or
eventually accurate failure detectors). Namely, we will pick one participant in
the analysis, and stretch its "proving period"  to infinity. That is, we will
allow the canister to progress to the state where the target participant is the
prover, but not allow it to progress further. We will then examine whether the
participant can establish permanent connections to every the other participants,
provided that the link isn't spontaneously lost infinitely often, and that the
participants don't refresh their browser infinitely often.

However, we don't really have a standard explicit model of the network in the
model; we do have a vestigial one that was there from attempts to model the
voting process, which we later decided was likely irrelevant to the main
questions our model aims to address.

The likely biggest gap in the modeling, compared to the implementation, is the
lack of detail in the connection establishment process. We assume that there's
at most one video (and also audio) connection between every participant pair.
The model includes some "spooky actions at a distance" on the connections (in
particular, starting connection negotiation), which examine/touch the state of
multiple participants simultaneously.

On the analysis side: participants are grouped in groups of 4, but we have run
the analysis only for 3-group parties, as there's nothing indicating that the
behavior would change between 3 and 4 participants (whereas the behavior might
change between 2 and 3 participants per group). The last models already take
several minutes to complete the analysis with 3 participants, so we haven't
tried running the analysis with 4.

---- MODULE Connections ----
EXTENDS TLC, Integers, Sequences, FiniteSets

\* A few generic auxiliary definitions on functions and sequences
Remove_Argument(f, x) == [ y \in DOMAIN(f) \ {x} |-> f[y] ]

Last(s) == s[Len(s)]

Range(f) ==
  { f[x] : x \in DOMAIN f }

\* The model assumes PARTICIPANTS to be a sequence that models the 
\* fixed sequence of participants in the current group, as recorded in the canister)
PARTICIPANTS == << "p1", "p2", "p3" >>

\* The set of all participants (the "unordered" version of the list)
Participant_Set == Range(PARTICIPANTS)

\* TLC will squeak if an ASSUME statement isn't fulfilled
\* Sanity check that the participant list doesn't contain duplicates
ASSUME
    Len(PARTICIPANTS) = Cardinality(Participant_Set)

\* We make non-active canister states records, so that TLC doesn't complain when 
\* comparing for equality against active states
UNINITIALIZED == [ state |-> "UNINITIALIZED" ]
INITIALIZED == [ state |-> "INITIALIZED" ]
FINISHED == [ state |-> "FINISHED" ]

NEGOTIATING == "NEGOTIATING"
ESTABLISHED == "ESTABLISHED"

\* Sanity check that the different sentinel states are distinct
ASSUME
    Cardinality({UNINITIALIZED, INITIALIZED, FINISHED}) = 3

VARIABLES 
    \* Keep the entire history of the evolution of the canister (i.e., all versions), 
    \* as the participants could get an arbitrarily stale state when performing a query
    \* or after a refresh
    canister_history,
    \* Keeps the state of each participant
    participant,
    \* To model asynchronous communication between the different participant
    \* and canister, we introduce an abstract "network" that acts as a buffer.
    \* The messages sent by the entities go to the buffer, where the other entities can
    \* (asynchronously) pull them from.
    \* Currently only used for vote messages going from participants to the canister.
    network

vars == << canister_history, participant, network >>

Empty_Map == [x \in {} |-> {}]

Init_Participant == [
    audio |-> Empty_Map,
    video |-> Empty_Map,
    canister_read |-> 1
]

Init_Active == [
    round |-> 0,
    votes |-> [rv \in {} |-> {}]
]

\* We start by assuming that the canister is already in an active state,
\* to simplify the model. We don't simplify further to have a static
\* progression of the canister, even though this would not change the
\* participants behavior, as they could always poll an old version of the canister.
\* However, like this we can easily limit the progress of the canister
\* in order to "stretch out" a proving round to infinity, such that we can
\* analyze the stability properties.
Init_Canister == << UNINITIALIZED, INITIALIZED, Init_Active >>

\* The current state of the canister is the last one in the history
\* We call it just "Canister"
Canister == Last(canister_history)

Init ==
    /\ participant = [ p \in Participant_Set |-> Init_Participant ]
    /\ canister_history = Init_Canister
    /\ network = {}

\* A participant may restart (e.g., by refreshing their browser) at any point in time
\* In that case it reads an arbitrary version of the canister and drops all connections.
Refresh_Connection(p) ==
    /\ \E i \in 1..Len(canister_history):
        /\ participant' = 
            p :> [  
                canister_read |-> i,
                audio |-> Empty_Map,
                video |-> Empty_Map
            ] @@ participant
    /\ UNCHANGED << canister_history, network >>

\* Whether p1 comes before p2 in the participant list. This governs how audio
\* connections are established.
Before(p1, p2) == \E i, j \in 1..Len(PARTICIPANTS): 
    /\ j > i
    /\ p1 = PARTICIPANTS[i]
    /\ p2 = PARTICIPANTS[j]

Start_Negotiating_Audio(p1, p2) == 
  LET
    p1_state == participant[p1]
    p2_state == participant[p2]
  IN
    /\ Before(p1, p2)
    /\ p2 \notin DOMAIN p1_state.audio
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, FINISHED}
    \* We require p2 to also have at least an initialized version of the canister,
    \* otherwise we don't allow the connection to happen in the model.
    \* In reality, p2 might not even be connected to the signalling server yet.
    \* We also require that p2 doesn't think it has any connection to p1, so this
    \* guard isn't implementable in practice.
    /\ p1 \notin DOMAIN p2_state.audio
    /\ canister_history[p2_state.canister_read] \notin {UNINITIALIZED, FINISHED}
    \* This changes the state of both participants, so isn't implementable in practice.
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.audio = p2 :> [ state |-> NEGOTIATING, initiator |-> TRUE ] @@ @],
            ![p2] = [ @ EXCEPT !.audio = p1 :> [ state |-> NEGOTIATING, initiator |-> FALSE ] @@ @]
        ]
    /\ UNCHANGED << canister_history, network >>

\* A participant can move from negotiating to established audio at any point in time.
Establish_Audio(p1, p2) ==
  LET
    p1_state == participant[p1]
  IN
    /\ p2 \in DOMAIN p1_state.audio
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, FINISHED}
    /\ p1_state.audio[p2].state = NEGOTIATING
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.audio = [ @ EXCEPT ![p2] = [ @ EXCEPT !.state = ESTABLISHED ] ] ]
        ]
    /\ UNCHANGED << canister_history, network >>

\* An audio connection can spontaneously break at any point in time at either end
Lose_Audio(p1, p2) ==
    /\ p2 \in DOMAIN participant[p1].audio
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.audio = Remove_Argument(@, p2) ]
        ]
    /\ UNCHANGED << canister_history, network >>

\* If a participant thinks it has a connection, but the other end doesn't have any
\* connection, then we assume that this connection was lost; we allow the participant
\* to detect it. This is similar to losing audio, but slightly stronger. We 
\* rely on this difference when specifying properties; eventually detection audio loss
\* is OK, but spontaneously losing connection infinitely often isn't OK.
Detect_Audio_Loss(p1, p2) ==
    LET
     p1_state == participant[p1]
     p2_state == participant[p2]
    IN
      /\ p2 \in DOMAIN p1_state.audio
      /\ p1 \notin DOMAIN p2_state.audio
      /\ participant' = [ participant EXCEPT
            ![p1] = [ @ EXCEPT !.audio = Remove_Argument(@, p2) ]
         ]
      /\ UNCHANGED << canister_history, network >>

\* A participant drops all connections when it sees a "finished" state.
Finish(p) ==
    /\ canister_history[participant[p].canister_read] = FINISHED
    /\ participant' = [ participant EXCEPT
            ![p] = [ participant[p] EXCEPT !.audio = Empty_Map, !.video = Empty_Map ] 
       ]
    /\ UNCHANGED << canister_history, network >>

Last_Round == Len(PARTICIPANTS) - 1

\* The main canister action is to update the round.
Update_Round ==
    /\ Canister # FINISHED
    /\ Canister.round # Last_Round
    /\ canister_history' = Append(canister_history, [ Canister EXCEPT
            !.round = @ + 1
        ])
    /\ UNCHANGED << participant, network >>

\* A canister also registers votes in reality; this transition captures
\* that, however, we currently don't enable it.
Update_Votes ==
    /\ Canister # FINISHED
    /\ \E vote_msg \in network:
        /\ vote_msg.round <= Canister.round
        /\ canister_history' = Append(canister_history, 
            [ Canister EXCEPT !.votes = << vote_msg.round, vote_msg.from >> :> vote_msg.vote @@ @ ]
           )
        /\ network' = network \ {vote_msg}
        /\ UNCHANGED << participant >>

\* A canister can also finish the party once it progresses past the last round.
Finish_Party ==
    /\ Canister # FINISHED
    /\ Canister.round = Last_Round
    /\ canister_history' = Append(canister_history, FINISHED)
    /\ UNCHANGED << participant, network >>

\* We define the prover based on the order in the participant list.
\* We adjust the offset by 1 as TLA sequences are 1-based, and the rounds start from 0,
Prover(round) == PARTICIPANTS[round + 1]

\* Similar to audio, we negotiate video.
Start_Negotiating_Video(p1, p2) == 
  LET 
    p1_state == participant[p1]
    p2_state == participant[p2]
  IN
    /\ p2 \notin DOMAIN p1_state.video
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    \* p1 thinks it is the prover
    /\ Prover(canister_history[p1_state.canister_read].round) = p1
    /\ p2 # p1
    \* TODO: We have another global guard here, as we inspect p2's state, so this is not
    \* directly implementable.
    \* We allow p2 to start negotiating even if it doesn't think that p1 is the prover. But
    \* we still require it to be initialized. This may or may not be a sound abstraction.
    /\ canister_history[p2_state.canister_read] \notin {UNINITIALIZED, FINISHED}
    /\ p1 \notin DOMAIN p2_state.video
    /\ participant' = [ participant EXCEPT 
            \* TODO: this is not a local event, as it reads/write the state of multiple participants.
            ![p1] = [ @ EXCEPT !.video = p2 :> [ state |-> NEGOTIATING, initiator |-> TRUE ] @@ @ ],
            ![p2] = [ @ EXCEPT !.video = p1 :> [ state |-> NEGOTIATING, initiator |-> FALSE ] @@ @ ]
        ]
    /\ UNCHANGED << canister_history, network >>

\* We allow a participant to reject a video negotiation if it doesn't think that the other side is
\* the prover.
Reject_Video(p1, p2) ==
    LET
      p1_state == participant[p1]
    IN
      /\ p2 \in DOMAIN p1_state.video
      /\ p1_state.video[p2].state = NEGOTIATING
      /\ ~p1_state.video[p2].initiator 
      /\ 
        \/ canister_history[p1_state.canister_read] \in {UNINITIALIZED, INITIALIZED, FINISHED}
        \/
           /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
           /\ Prover(canister_history[p1_state.canister_read].round) # p2
      /\ participant' = [ participant EXCEPT 
              ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
          ]
      /\ UNCHANGED << canister_history, network >>

Establish_Video(p1, p2) ==
  LET 
    p1_state == participant[p1]
  IN
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    /\ p2 \in DOMAIN p1_state.video
    /\ p1_state.video[p2].state = NEGOTIATING
    /\ 
        \/ p1_state.video[p2].initiator /\ Prover(canister_history[p1_state.canister_read].round) = p1
        \/ ~p1_state.video[p2].initiator /\ Prover(canister_history[p1_state.canister_read].round) = p2
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.video = [ @ EXCEPT ![p2] = [ @ EXCEPT !.state = ESTABLISHED ] @@ @ ] ]
        ]
    /\ UNCHANGED << canister_history, network >>

Detect_Video_Loss(p1, p2) ==
    LET
     p1_state == participant[p1]
     p2_state == participant[p2]
    IN
      /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
      /\ p2 \in DOMAIN p1_state.video
      /\ p1 \notin DOMAIN p2_state.video
      /\ participant' = [ participant EXCEPT
            ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
         ]
      /\ UNCHANGED << canister_history, network >>

Lose_Video(p1, p2) ==
  LET
    p1_state == participant[p1]
  IN
    /\ p2 \in DOMAIN p1_state.video
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
        ]
    /\ UNCHANGED << canister_history, network >>

Is_Prover_In(p, state) ==
    /\ canister_history[state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    /\ Prover(canister_history[state.canister_read].round) = p

\* We assume that, when a participant polls a canister, it doesn't go back in history.
\* I.e., even if the query returns an old state, the code should detect this and ignore
\* this change of state.
Poll_Canister(p) ==
    /\ \E i \in (participant[p].canister_read + 1) .. Len(canister_history):
        /\ participant' = [ participant EXCEPT 
                ![p] = 
                  [ @ EXCEPT 
                    !.canister_read = i ,
                    !.video = Empty_Map ]
            ]
    /\ UNCHANGED << canister_history, network >>

\* NOT USED ANYMORE - left just in case we want to model voting again at some point
Vote(p) ==
  LET
    p_state == participant[p]
  IN
    /\ canister_history[p_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    /\ LET r == canister_history[p_state.canister_read].round IN
        \* Votes are TRUE or FALSE; any is allowed (i.e., pick one arbitrarily)
        \* TODO: if we do add voting, do we really care about the value of the vote in the model?
        /\ \E v \in {TRUE, FALSE}:
            network' = network \union { [round |-> r, from |-> p, vote |-> v] }
    /\ UNCHANGED << canister_history, participant >>

Next == \E p1, p2 \in Participant_Set:
    \/ Refresh_Connection(p1)
    \/ Start_Negotiating_Audio(p1, p2)
    \/ Establish_Audio(p1, p2)
    \/ Lose_Audio(p1, p2)
    \/ Detect_Audio_Loss(p1, p2)
    \/ Finish(p1)
    \/ Update_Round
    \/ Finish_Party
    \/ Start_Negotiating_Video(p1, p2)
    \/ Establish_Video(p1, p2)
    \/ Reject_Video(p1, p2)
    \/ Lose_Video(p1, p2)
    \/ Detect_Video_Loss(p1, p2)
    \/ Poll_Canister(p1)
    \* For the moment, we disable the transitions related to voting
    \* \/ Update_Votes
    \* \/ Vote(p1)
    
\*****************************************************************
\* Properties

Participant_Doesnt_Connect_To_Itself == \A p \in Participant_Set: 
    LET 
        p_state == participant[p]
    IN
        /\ p \notin DOMAIN p_state.audio
        /\ p \notin DOMAIN p_state.video

No_Overly_Early_Messages == Canister # FINISHED => 
    \A vote_msg \in network:
        vote_msg.round <= Canister.round

Initiate_All_Or_None == \A p \in Participant_Set:
    \A p2, p3 \in DOMAIN participant[p].video:
        participant[p].video[p2].state = ESTABLISHED /\ participant[p].video[p3].state = ESTABLISHED =>
            participant[p].video[p2].initiator = participant[p].video[p3].initiator

One_Inbound_Connection == \A p \in Participant_Set:
    \A p2, p3 \in DOMAIN participant[p].video:
        /\ participant[p].video[p2].initiator = FALSE 
        /\ participant[p].video[p2].state = ESTABLISHED 
        /\ participant[p].video[p3].state = ESTABLISHED 
      => p3 = p2

\* This should be pretty trivial given our model, but we still add it
Audio_Connections_Properly_Initiated == \A p \in Participant_Set:
    \A p2 \in DOMAIN participant[p].audio:
        Before(p, p2) <=> participant[p].audio[p2].initiator

Dont_Progress_Past(p) == 
  /\ Canister # FINISHED
  /\ \A i \in 1..Len(PARTICIPANTS): PARTICIPANTS[i] = p 
        => Canister.round <= i - 1

Video_Fairness_Condition(p) == \A p2 \in Participant_Set \ {p}:
    /\ WF_vars(Prover(Canister.round) # p /\ Update_Round)
    /\ WF_vars(Start_Negotiating_Video(p, p2))
    /\ WF_vars(Establish_Video(p, p2))
    /\ WF_vars(Establish_Video(p2, p))
    /\ WF_vars(Detect_Video_Loss(p, p2))
    /\ WF_vars(Detect_Video_Loss(p2, p))
    /\ WF_vars(Poll_Canister(p))
    /\ WF_vars(Poll_Canister(p2))

Stable_Video_Connections_From(p) == \A p2 \in Participant_Set \ {p}:
    \/ 
        /\ <>[](
            /\ p2 \in DOMAIN (participant[p].video)
            /\ participant[p].video[p2] = [state |-> ESTABLISHED, initiator |-> TRUE]
          )
        /\ <>[] (
            /\ p \in DOMAIN (participant[p2].video)
            /\ participant[p2].video[p] = [state |-> ESTABLISHED, initiator |-> FALSE]
          )
    \* If we infinitely often spontaneously lose video, and if this transition couldn't be interpreted
    \* as just detecting video loss, or polling the canister (as this also closes connections),
    \* then we don't ask for other guarantees.
    \/ []<><<Lose_Video(p, p2) /\ ~Detect_Video_Loss(p, p2) /\ ~Poll_Canister(p)>>_vars
    \/ []<><<Lose_Video(p2, p) /\ ~Detect_Video_Loss(p2, p) /\ ~Poll_Canister(p2)>>_vars
    \/ []<><<Refresh_Connection(p)>>_vars
    \/ []<><<Refresh_Connection(p2)>>_vars

\* Check that p's connections remain stable forever
P_Property(p) == Stable_Video_Connections_From(p)

\* We can check the stability property for all three participants.
\* So any of these can be used as the spec/property in the TLC configuration
\* file.
\* We can eliminate the duplication as TLC gets confused about what's Init
\* or Next if we try to parametrize these definition
P1_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[1])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[1])
P1_Video_Property == P_Property(PARTICIPANTS[1])

P2_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[2])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[2])
P2_Video_Property == P_Property(PARTICIPANTS[2])

P3_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[3])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[3])
P3_Video_Property == P_Property(PARTICIPANTS[3])

Audio_Fairness_Condition == \A p1, p2 \in Participant_Set: p1 # p2 =>
    /\ WF_vars(Start_Negotiating_Audio(p1, p2))
    /\ WF_vars(Start_Negotiating_Audio(p2, p1))
    /\ WF_vars(Establish_Audio(p1, p2))
    /\ WF_vars(Establish_Audio(p2, p1))
    /\ WF_vars(Detect_Audio_Loss(p1, p2))
    /\ WF_vars(Detect_Audio_Loss(p2, p1))
    /\ WF_vars(Poll_Canister(p1))
    /\ WF_vars(Poll_Canister(p2))

Audio_Stability_Spec ==
    /\ Init
    /\ [][Next /\ Canister' # FINISHED]_vars
    /\ Audio_Fairness_Condition

Stable_Audio_Connections == \A p1, p2 \in Participant_Set: p1 # p2 =>
    \/ 
        /\ <>[](
            /\ p2 \in DOMAIN (participant[p1].audio)
            /\ participant[p1].audio[p2].state = ESTABLISHED
          )
        /\ <>[] (
            /\ p1 \in DOMAIN (participant[p2].audio)
            /\ participant[p2].audio[p1].state = ESTABLISHED
          )
    \/ []<><<Lose_Audio(p1, p2) /\ ~Detect_Audio_Loss(p1, p2)>>_vars
    \/ []<><<Lose_Audio(p2, p1) /\ ~Detect_Audio_Loss(p2, p1)>>_vars
    \/ []<><<Refresh_Connection(p1)>>_vars
    \/ []<><<Refresh_Connection(p2)>>_vars

\*****************************************************************
\* Sanity-check properties: MEANT TO BE VIOLATED
\* The purpose is to discover bugs in the model.
\* We'll say things like "we can't finish the party", and see whether
\* we can violate them

Canister_Cant_Finish_Inv == Canister # FINISHED

Parties_Cant_Finish_Inv == \A p \in Participant_Set: canister_history[participant[p].canister_read] # FINISHED

Parties_Cant_Connect_Inv == \A p1, p2 \in Participant_Set: 
    /\ 
        \/ p2 \notin DOMAIN participant[p1].audio
        \/ participant[p1].audio[p2].state # ESTABLISHED
    /\ 
        \/ p2 \notin DOMAIN participant[p1].video
        \/ participant[p1].video[p2].state # ESTABLISHED

====


TODO properties:

- Only initiate audio connections to higher-indexed participants (according to the order in PARTICIPANTS)
- For every connection (audio or video), exactly one side is the initiator
- Any established connection is established at both ends simultaneously

Progress/liveness-flavored properties:

- The prover establishes a video connection to everyone and doesn't drop (under some conditions)
- All pairs of participants have audio connections (under some conditions)
    