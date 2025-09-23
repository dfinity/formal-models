***************
Message routing
***************

These are the rules for receiving messages (formalized in the Induct_Message action in the model) and signals
(formalized in the Induct_Signal action). 

---- MODULE Message_Induction ----

EXTENDS TLC, Naturals, FiniteSets, Apalache, Variants, Common, Sequences, SequencesExt

CONSTANT MAX_RESCHEDULINGS

VARIABLE 
    \* A directional inter-subnet stream of headers; headers are processed
    \* in the order they are emitted, so a stream works fine here.
    \* @typeAlias: hdrStreams = << $subnetId, $subnetId >> -> Seq($signal);
    \* @type: $hdrStreams;
    headers,
    \* Count how many times a response has been rescheduled due to a reject signal.
    \* Constant rescheduling (without updating the routing table in the meantime) could 
    \* yield an unbounded state space; we use this count to bound the space.
    \* @type: $subnetId -> Int;
    rescheduling_count

induction_vars == << stream, registry, headers, subnet, rescheduling_count >>

\* @type: ($subnetId, $subnetId, $message) => Bool;
Sender_Ok(subnet_id, sending_subnet_id, msg) ==
  LET 
    reg == registry[subnet[subnet_id].registry_version]
    table == reg.routing_table
    mig_list_from == Migration_List(table, msg.from)
    mig_list_to == Migration_List(table, msg.to)
  IN
    \/ Hosted(table, msg.from, sending_subnet_id)
    \/ 
        \/ \E i, j \in 1..Len(mig_list_from): 
            /\ mig_list_from[i] = sending_subnet_id  
            /\ Hosted(table, msg.from, mig_list_from[j])
        \/ 
            /\ Is_Response(msg)
            /\ Hosted(table, msg.to, subnet_id)
            /\ \E i \in 1..Len(mig_list_to): mig_list_to[i] = sending_subnet_id
 
 \* @type: ($subnetId, $message) => Bool;
Recipient_Hosted(subnet_id, msg) ==
  LET 
    reg == registry[subnet[subnet_id].registry_version]
    table == reg.routing_table
  IN 
    /\ Hosted(table, msg.to, subnet_id)

 \* @type: ($subnetId, $message) => Bool;
Should_Reroute(subnet_id, msg) ==
  LET 
    reg == registry[subnet[subnet_id].registry_version]
    table == reg.routing_table
    mig_list == Migration_List(table, msg.to)
  IN 
    \E i, j \in 1..Len(mig_list): 
        /\ mig_list[i] = subnet_id
        /\ Hosted(table, msg.to, mig_list[j])

Ack(i) == [type |-> "ACK", index |-> i]
Rej(i) == [type |-> "REJ", index |-> i]
\* @type: $signal => Bool;
Is_Ack(sig) == sig.type = "ACK"
\* @type: $signal => Bool;
Is_Rej(sig) == sig.type = "REJ"

Next_Stream_Index(sending_subnet_id, receiving_subnet_id) ==
  LET
    i == subnet[receiving_subnet_id].incoming_index[sending_subnet_id]
  IN i + 1

Next_Stream_Message(sending_subnet_id, receiving_subnet_id) ==
  LET
    str == stream[<< sending_subnet_id, receiving_subnet_id >>]
  IN str[Next_Stream_Index(sending_subnet_id, receiving_subnet_id)]

Unconsumed_Messages_Exist(sending_subnet_id, receiving_subnet_id) ==
  Next_Stream_Index(sending_subnet_id, receiving_subnet_id) 
    <= Len(stream[<< sending_subnet_id, receiving_subnet_id >>])

Is_Stopping(subnet_id, c) ==
    subnet[subnet_id].canister[c].state = STOPPING

Add_Header(sending_subnet_id, receiving_subnet_id, header) ==
    headers' = 
        [ headers 
            EXCEPT ![<< sending_subnet_id, receiving_subnet_id >>] = 
            Append(@, header) ]

\* @type: ($subnetId -> $subnetState, $subnetId, $subnetId) => $subnetId -> $subnetState;
Increment_Incoming(s, receiving_id, sender_id) ==
    [ s EXCEPT ![receiving_id] = [ @ EXCEPT 
            !.incoming_index = [ @ EXCEPT ![sender_id] = @ + 1 ]
        ]
    ]

\* @type: ($subnetId -> $subnetState, $subnetId, $message) => $subnetId -> $subnetState;
Queue_Message(s, subnet_id, msg) ==
    [ s EXCEPT ![subnet_id] =
            [ @ EXCEPT !.canister = [ @ EXCEPT ![msg.to] = [ @ EXCEPT !.queue = Append(@, [ message |-> msg, processed |-> FALSE ]) ]] ]
        ]

Subnet_Knows_Other_Subnet(subnet_id, other_subnet_id) ==
    other_subnet_id \in DOMAIN registry[subnet[subnet_id].registry_version].subnet_info

Thinks_Sender_Canister_Has_Moved(subnet_id, sending_subnet_id, canister) ==
  LET
    reg == registry[subnet[subnet_id].registry_version]
    table == reg.routing_table
  IN
    table[canister].on # sending_subnet_id

\* "Spontaneous" event: try to induct a message from a remote outgoing stream
\* In reality, we may induct several messages simultaneously. In the model, we
\* always induct them one-by-one; this shouldn't have an effect on our properties.
Induct_Message(subnet_id, sending_subnet_id) ==
    /\ subnet_id \in DOMAIN subnet
    /\ Subnet_Knows_Other_Subnet(subnet_id, sending_subnet_id)
    /\ Unconsumed_Messages_Exist(sending_subnet_id, subnet_id) 
    /\ LET 
         new_i == Next_Stream_Index(sending_subnet_id, subnet_id)
         msg == Next_Stream_Message(sending_subnet_id, subnet_id)
         s == subnet[subnet_id]
       IN
        /\ ~Subnet_Thinks_Its_Stopped(subnet_id)
        /\ Assert(Sender_Ok(subnet_id, sending_subnet_id, msg), 
            \* TODO: get reasonable error messages with TLC while keeping Apalache happy
            "Sender wasn't OK")
            \* "For subnet " \o subnet_id \o ", subnet " \o sending_subnet_id \o " wasn't OK for sending canister " \o msg.from)
        /\ Assert(~Recipient_Hosted(subnet_id, msg) => Is_Request(msg) \/ Should_Reroute(subnet_id, msg),
            \* TODO: get reasonable error messages with TLC while keeping Apalache happy
            "Recipient not hosted, but not re-routing the message")
            \* "Recipient " \o msg.to \o " not hosted on " \o subnet_id \o " and message shouldn't be re-routed")
        /\ CASE Recipient_Hosted(subnet_id, msg) /\ 
              ~(Is_Request(msg) 
                /\
                    \/ ~Is_Running(subnet_id, msg.to) 
                    \/ Thinks_Sender_Canister_Has_Moved(subnet_id, sending_subnet_id, msg.from))
                ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Ack(new_i))
                    /\ subnet' = Increment_Incoming(Queue_Message(subnet, subnet_id, msg), subnet_id, sending_subnet_id)
                    /\ UNCHANGED << stream, registry, rescheduling_count >>
             [] \/ Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) /\ ~Is_Running(subnet_id, msg.to)
                \/ ~Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) 
                \/ Thinks_Sender_Canister_Has_Moved(subnet_id, sending_subnet_id, msg.from) /\ Is_Request(msg) ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Rej(new_i))
                    /\ subnet' = Increment_Incoming(subnet, subnet_id, sending_subnet_id)
                    /\ UNCHANGED << registry, rescheduling_count, stream >>
            [] ~Recipient_Hosted(subnet_id, msg) /\ Is_Response(msg)  ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Rej(new_i))
                    /\ subnet' = Increment_Incoming(subnet, subnet_id, sending_subnet_id)
                    /\ UNCHANGED << stream, registry, rescheduling_count >>
            \* This is just a sanity check to ensure that the assertions keep the preceding cases exhaustive
            \* This ensures that the model will complain if the event is disabled even though unconsumed messages exist
            [] OTHER ->
               Assert(FALSE, 
                \* TODO: get reasonable error messages with TLC while keeping Apalache happy
                "The preceding cases should be exhaustive for messages")
                \* "The preceding cases should be exhaustive for message to " \o msg.to \o " and subnet" \o subnet_id)

Unconsumed_Signals_Exist(sending_subnet_id, receiving_subnet_id) ==
  headers[<<sending_subnet_id, receiving_subnet_id>>] # <<>>

Next_Signal(sending_subnet_id, receiving_subnet_id) ==
  Head(headers[<<sending_subnet_id, receiving_subnet_id>>])

\* @type: ($hdrStreams, $subnetId, $subnetId) => $hdrStreams;
Consume_One(h, subnet_id, remote_subnet_id) == [ h EXCEPT ![<<remote_subnet_id, subnet_id>>] = Tail(@) ]

\* @type: ($subnetId -> $subnetState, $subnetId, $subnetId) => $subnetId -> $subnetState;
Increment_Outgoing(s, subnet_id, remote_subnet_id) ==
    [ s EXCEPT ![subnet_id] = [ @ EXCEPT 
            !.outgoing_index = [ @ EXCEPT ![remote_subnet_id] = @ + 1 ]
        ]
    ]


Generate_Response_If_Needed(msg) ==
    IF Is_Response(msg) THEN msg
    ELSE Response(msg.to, msg.from, msg.id)

\* "Spontaneous" event: try to induct a signal from a remote header stream
\* In reality, we may induct several signals simultaneously. In the model, we
\* always induct them one-by-one; this shouldn't have an effect on our properties.
Induct_Signal(subnet_id, sending_subnet_id) ==
    /\ subnet_id \in DOMAIN subnet
    /\ Unconsumed_Signals_Exist(sending_subnet_id, subnet_id) 
    /\ LET
        sig == Next_Signal(sending_subnet_id, subnet_id)
        msg == stream[<< subnet_id, sending_subnet_id >>][sig.index]
        \* If the message was a request and it turns out it was rejected, turn it into a (reject) response
        \* instead
        response == Generate_Response_If_Needed(msg)
        response_recipient_current_subnet == Hosting_Subnet(registry[subnet[subnet_id].registry_version].routing_table, response.to)
       IN
        CASE 
          Is_Ack(sig) ->
            /\ headers' = Consume_One(headers, subnet_id, sending_subnet_id)
            /\ subnet' = Increment_Outgoing(subnet, subnet_id, sending_subnet_id)
            /\ UNCHANGED << stream, registry, rescheduling_count >>
          [] Is_Rej(sig) /\ response_recipient_current_subnet # subnet_id ->
            /\ 
                \* To bound the state space, we introduce two cases when we reschedule a message
                \/ 
                    \* Case one: reschedule at most MAX_RESCHEDULING times, even if the subnet is behind
                    \* the latest version of the registry
                    /\ subnet[subnet_id].registry_version < Len(registry)
                    /\ rescheduling_count[subnet_id] < MAX_RESCHEDULINGS
                    /\ rescheduling_count' = [ rescheduling_count EXCEPT ![subnet_id] = @ + 1 ]
                \/
                    \* Case two: can always reschedule if the subnet is on the latest registry version
                    /\ subnet[subnet_id].registry_version = Len(registry)
                    /\ UNCHANGED rescheduling_count
            /\ headers' = Consume_One(headers, subnet_id, sending_subnet_id)
            /\ subnet' = Increment_Outgoing(subnet, subnet_id, sending_subnet_id)
            /\ stream' = Extend_Stream(stream, subnet_id, response_recipient_current_subnet, response)
            /\ UNCHANGED << registry >>
          [] Is_Rej(sig) /\ Is_Request(msg) ->
            /\ subnet' = Increment_Outgoing(Queue_Message(subnet, subnet_id, response), subnet_id, sending_subnet_id)
            /\ headers' = Consume_One(headers, subnet_id, sending_subnet_id)
            /\ UNCHANGED << stream, registry, rescheduling_count >>
          [] Is_Rej(sig) /\ Is_Response(msg) -> Assert(FALSE, "Rejected a response from the current subnet")
          [] OTHER -> Assert(FALSE, "The previous cases should be exhaustive")

====