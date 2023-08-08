An abstract model of the Dfinity consensus algorithm IC0 as of 2021-10-01, analyzing the safety
against Byzantine behavior of the nodes. We don't look at liveness here.

The model is fairly abstract: it more closely resembles a shared-memory system than a networked one.
The state is logically partitioned per node, with actions also being per-node, in that they only change the 
state components that "belong" to a single node.
However, when performing the actions, the nodes will happily read other nodes' state components.
That is, there are no messages, and consequently, there are no message queues, distinctions between 
delivered/undelivered messages etc.

We now informally argue why this is OK for safety. 
While safety properties can be more general, the ones that care about for this are algorithm violated when we 
reach a bad state.
Thus, if the reachable states of our model are an overapproximation of the reachable states of the "real"
algorithm, and safety holds for our model, it also holds for the real algo. 
So we now argue why our model indeed yields an overapproximation.

The real algo is threshold based: the nodes only change their state if they receive a sufficient number of messages 
from other nodes that are saying the same thing (e.g., notarizing a value).
The messages received are a subset of the messages that are actually sent.
The following three characteristics of the model overapproximate this:
1. we allow nodes to change their state by arbitrarily selecting a subset of remote nodes to read from, which 
   simulates the receipt of the messages sent by those other nodes. That is, whenever the "real node" would take 
   a step, because it received a bunch of messages from remote nodes, the "model node" can also do that by simply
   reading the memory of these same remote nodes
2. the Byzantine nodes immediately have the "full state" in the beginning, that corresponds to having sent all
   possible messages (which is what the Byzantine nodes can do in the real algorithm). Thus, if an honest "real 
   node" would take a step based on a "wrong" (i.e., non protocol-conformant) message sent by a Byzantine node,
   then the "model node" can also take that step by reading the message from the Byzantine node's state.
3. there's nothing forcing nodes to take steps. That is, if the real algo would reach a bad state because some 
   "real node"  didn't change their state based on some messages it has received, the abstract model can also
   reach that state by simply not performing the action that changes that node's state.

Other significant abstractions in the model:

1. we model collision-resistance of hash functions by making them injective. As a consequence, a block B_i
   whose payload is v_i together with the hash of the parent h(B_{i-1}) is modeled just as a "value chain"
   v_i, v_{i-1}, ... v_1 (i.e., a sequence of values).
2. there's no proposal mechanism. Rather, the nodes can issue notarization shares non-deterministically, for
   arbitrary blocks. This should also clearly be an overapproximation of the behavior of the real algo.
3. there's no cryptography, in particular, no signatures; message authenticity is based on reading the memory of 
   the other node.
4. we don't model time, and we allow nodes to notarize values at any time. Clearly, this is also an overapproximation.

Other notable things about the model:

1. to make the model more readable, we do the usual splitting off of a guard for each action, that states the 
   conditions for when the action can take place
2. in our model, the nodes decide on valuechains, rather than just single values. That is, if a node decides
   on a chain <<v_3, v_2, v_1>> in round 3, that implies that it has decided on the values v_3 for round 3,
   v_2 for round 2, and v_1 for round 1. This is done just to avoid modeling of how each individual round's
   decision is computed.
3. to make the model amenable to model checking, we have to make everything finite. That means that we
   need to constrain the total number of different values that the nodes can propose/notarize/finalize in
   each block, and also the maximum length of our "value chains". This means that we might miss attacks
   that rely on the adversary using very long value chains.

--------------------- MODULE Consensus_Safety ---------------------------

EXTENDS TLC, Naturals, FiniteSets, Sequences

\* Some auxiliary definitions
PowerSet(S) == SUBSET(S)

Take(s, n) == SubSeq(s, 1, n)

ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]

Max(x, y) == IF x > y THEN x ELSE y
Min(x, y) == IF x < y THEN x ELSE y


\* As noted before, we model blockchains as just sequences of values contained in the blocks.
\* To support model checking, we have to put a hard limit on the length of the sequences.
SeqsOfLength(n, S) == [ 1 .. n -> S ]
SeqsUpToLength(n, S) == UNION { [ 1..k -> S] : k \in 0..n }
NonEmptySeqsUpToLength(n, S) == SeqsUpToLength(n, S) \ {<<>>}

\* We'll use model values for the set of nodes; hopefully makes it easier to take advantage of symmetry
\* Number of rounds and values make the state space finite
\* None is used for uninitialized state values (think null/bottom)
CONSTANTS Nodes, NrHonest, NrRounds, Values, None
Rounds == 1..NrRounds
NrValues == Cardinality(Values)

ASSUME NrHonest <= Cardinality(Nodes)

\* TLC doesn't like this assumption, but it should hold if you set the model values correctly for TLC.
\* ASSUME None \notin FiniteValuechain


VARIABLES Round, NotarizationShares, FinalizationShares, Decision, Honest

Valuechain == Seq(Values)
FiniteValuechain == NonEmptySeqsUpToLength(NrRounds, Values)
Block(vc) == Head(vc)
Parent(vc) == Tail(vc)
Extend(vc, value) == << value >> \o vc 

IsDishonest(n) == n \notin Honest
IsHonest(n) == n \in Honest
IsQuorum(S) == Cardinality(S) >= Cardinality(Honest)
Dishonest == Nodes \ Honest


RoundsPlusEnd == Rounds \cup {NrRounds + 1}
AllValuechains == PowerSet(FiniteValuechain)

TypeInvariant ==
    \* The current round of each node
    /\ Round \in [Nodes -> RoundsPlusEnd]
    \* For each round and node, record notarization shares it has published,
    \* and the recipients of each share. All shares refer to chains of value
    /\ NotarizationShares \in [ Rounds \X Nodes -> AllValuechains]
    \* Same, but for finalization shares
    /\ FinalizationShares \in [ Rounds \X Nodes -> AllValuechains]
    \* Record the decided value (if any) for each round and node
    /\ Decision \in [Rounds \X Nodes -> FiniteValuechain \cup {None}]

NodeSubsets == SUBSET(Nodes)

InitHonest == CHOOSE s \in SUBSET(Nodes) : Cardinality(s) = NrHonest

InitRound == [ n \in Nodes |-> 1 ]
\* Modeling trick: we let the dishonest nodes immediately issue notarization/finalization shares for all value 
\* chains and all rounds. We could also let them issue the shares one by one, but this would just lead to a bunch
\* of additional state transitions that aren't very interesting
InitNotarizationShares == [x \in Rounds \X Dishonest |-> FiniteValuechain] @@ [ x \in Rounds \X Nodes |-> {} ]
InitFinalizationShares == [x \in Rounds \X Dishonest |-> FiniteValuechain] @@ [ x \in Rounds \X Nodes |-> {} ]
InitDecision == [ x \in Rounds \X Nodes |-> None ]

IsNotarized(n, r, vc) == IsQuorum({ n2 \in Nodes: vc \in NotarizationShares[r, n2] })

IsFinalized(n, r, vc) == IsQuorum({ n2 \in Nodes: vc \in FinalizationShares[r, n2]})

IsValidBlock(n, r, vc) ==
    IF r = 1 THEN TRUE ELSE IsNotarized(n, r-1, Parent(vc))

EmittedNotarizationShare(n, r, vc) == 
    /\ vc \in NotarizationShares[r, n]

EmittedFinalizationShare(n, r, vc) == 
    /\ vc \in FinalizationShares[r, n]
    
EmitNotarizationShare(n, r, vc) == [NotarizationShares EXCEPT ![r, n] = @ \cup {vc}] 
EmitFinalizationShare(n, r, vc) == [FinalizationShares EXCEPT ![r, n] = @ \cup {vc}] 

NotarizeGuard(n, r, vc) ==
    /\ r <= NrRounds
    /\ Round[n] = r
    \* Comment this check out to check sanity
    /\ IsValidBlock(n, r, vc) 
    /\ ~ EmittedNotarizationShare(n, r, vc)

\* Corresponds to the notarization block in the real algorithm
Notarize(n, r, vc) ==
    /\ NotarizeGuard(n, r, vc)
    /\ NotarizationShares' = EmitNotarizationShare(n, r, vc)
    /\ UNCHANGED << Round, FinalizationShares, Decision, Honest >>
    
FinalizeGuard(n, r, vc) ==
    /\ r <= NrRounds
    /\ Round[n] = r
    /\ IsNotarized(n, r, vc)
    \* Comment the next check out to check sanity; the verification should fail
    /\ NotarizationShares[r, n] \subseteq {vc}
    /\ ~ EmittedFinalizationShare(n, r, vc)
     
\* Corresponds to the finalization block in the real algorithm
Finalize(n, r, vc) ==
    /\ FinalizeGuard(n, r, vc)
    /\ FinalizationShares' = EmitFinalizationShare(n, r, vc)
    /\ Round' = [Round EXCEPT ![n] = r + 1]
    /\ UNCHANGED << NotarizationShares, Decision, Honest >>

DecidedRounds(n) == {r \in Rounds : Decision[r, n] # None}

DecideGuard(n, r, vc) == 
    /\ IsFinalized(n, r, vc)
    \* /\ r > ReduceSet(Max, DecidedRounds(n), 0)

\* Corresponds to the decision process that's described as running in parallel in the real algo
Decide(n, r, vc) ==
    /\ DecideGuard(n, r, vc)
    /\ Decision' = [ Decision EXCEPT ![r, n] = vc ]
    /\ UNCHANGED << Round, NotarizationShares, FinalizationShares, Honest >>

\* The initial state
Init == 
    /\ Honest = InitHonest
    /\ Round = InitRound
    /\ NotarizationShares = InitNotarizationShares
    /\ FinalizationShares = InitFinalizationShares
    /\ Decision = InitDecision

\* The transition relation.
Next == \E n \in Nodes:  \E vc \in FiniteValuechain :
    \/ Notarize(n, Round[n], vc)
    \/ Finalize(n, Round[n], vc)
    \/ \E r \in Rounds : Decide(n, r, vc)

\* A sanity check for the model: this property is expected to fail, as it states that no node 
\* should ever be able to make a decision.
DecisionSanity == \A n \in Nodes : \A r \in Rounds : Decision[r, n] = None 

Reverse(s) ==
  (**************************************************************************)
  (* Reverse the given sequence s:  Let l be Len(s) (length of s).          *)
  (* Equals a sequence s.t. << S[l], S[l-1], ..., S[1]>>                    *)
  (**************************************************************************)
  [ i \in 1..Len(s) |-> s[(Len(s) - i) + 1] ]
  
IsSuffix(s1, s2) == Take(Reverse(s2), Len(s1)) = Reverse(s1)

\* The main safety property
DecisionInv == \A n1, n2 \in Nodes : \A r1 \in Rounds : \A r2 \in r1..NrRounds :
    LET 
        vc1 == Decision[r1, n1]
        vc2 == Decision[r2, n2]
    IN
        \/ vc1 = None
        \/ vc2 = None
        \/ (/\ IsSuffix(vc1, vc2)
            /\ Len(vc2) - Len(vc1) = r2 - r1)


==============================================
