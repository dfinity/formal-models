---- MODULE Canister_Execution ----
EXTENDS TLC, Common, Sequences, SequencesExt, Integers

CONSTANT MAX_REQUESTS
VARIABLE next_req_id

\* As we never remove messages from the queues in our model, use the following operator to
\* access the "live" (i.e., unprocessed) queue messages.
\* @type: Seq({message: $message, processed: Bool}) => Set($message);
Live_Queue_Messages(q) == { live.message : live \in { m \in To_Set(q): m.processed = FALSE } }
\* @type: ($subnetId -> $subnetState, $subnetId, $canisterId, Int => Int) => $subnetId -> $subnetState;
Update_Pending(s, subnet_id, canister_id, upd_f(_)) ==
    [ s EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.pending = upd_f(@) ]]]
    ]

\* Logically remove a message from a queue. If the same message got delivered twice, this would 
\* mark both instances of the message as processed simultaneously. However, our properties should
\* ensure that this doesn't happen.
\* @type: ($subnets, $subnetId, $canisterId, $message) => $subnets;
Remove_Message(s, subnet_id, canister_id, msg) == [ s EXCEPT ![subnet_id] = 
    [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] =
            [ @ EXCEPT !.queue = 
                Map_Seq(@, LAMBDA m: IF m.message = msg /\ ~m.processed 
                                        THEN [ message |-> msg, processed |-> TRUE ] 
                                        ELSE m) ]
        ]
    ]
  ]

\* "Spontaneous" event: a canister processes a response from its queue.
\* TODO: we allow responses to be processed in any order, i.e., we disregard the order imposed by the queue.
Process_Response(subnet_id, c) ==
  /\ subnet_id \in DOMAIN subnet
  /\ LET
      s == subnet[subnet_id]
    IN
      /\ c \in DOMAIN s.canister
      /\ \E msg \in Live_Queue_Messages(s.canister[c].queue):
          /\ Is_Response(msg)
          /\ subnet' = Update_Pending(Remove_Message(subnet, subnet_id, c, msg), subnet_id, c, LAMBDA p: p - 1)
          /\ UNCHANGED << registry, stream, next_req_id >>

\* "Spontaneous" event: a canister sends a request to a different canister.
Send_Request(sending_subnet_id, receiving_subnet_id, from, to) ==
    /\ sending_subnet_id \in DOMAIN subnet
    /\ receiving_subnet_id \in DOMAIN subnet
    /\ LET
        sending == subnet[sending_subnet_id]
        reg == registry[sending.registry_version]
        rt == reg.routing_table
      IN
        \* Build this directly into the model, as TLC CONSTRAINT clause has weird
        \* semantics: the states violating the clause are still considered, but their successors
        \* are not. So with CONSTRAINT we would issue one request than MAX_REQUESTS, but never get a response 
        \* (as we wouldn't consider the successor state)
        /\ next_req_id <= MAX_REQUESTS
        /\ Hosted(rt, from, sending_subnet_id)
        /\ Hosted(rt, to, receiving_subnet_id)
        /\ ~Subnet_Thinks_Its_Stopped(sending_subnet_id)
        /\ Is_Running(sending_subnet_id, from)
        \* Even if the receiving and sending subnets are the same, we route the message through
        \* message routing. In practice, the execution environment might shortcircuit this and
        \* deliver the message directly to the queue, but in some cases the message will actually
        \* go through the message routing. As we assume that the execution environment works correctly
        \* here, we only look at the case where the message goes through message routing.
        /\ stream' = Extend_Stream(stream, sending_subnet_id, receiving_subnet_id, Request(from, to, next_req_id))
        /\ subnet' = Update_Pending(subnet, sending_subnet_id, from, LAMBDA p: p + 1)
        /\ next_req_id' = next_req_id + 1
        /\ UNCHANGED << registry  >>

\* "Spontaneous" event: a canister responds to a request in its input queue.
\* TODO: here, we can send a response any time for any message in the queue, ignoring the order.
\* This somewhat mimics the fact that responses don't have to be issued in the same order that
\* the requests came in.
\* However, in reality, a request 1 might trigger an outgoing request 2, and only upon
\* the completion of request 2 does the canister send the response to request 1.
\* So any fairness assumptions on this may be too strong. Not sure if this is problematic.
Send_Response(sending_subnet_id, receiving_subnet_id, from, to) ==
  /\ sending_subnet_id \in DOMAIN subnet
  /\ receiving_subnet_id \in DOMAIN subnet
  /\ LET
      sending == subnet[sending_subnet_id]
      rt == registry[sending.registry_version].routing_table
    IN
      /\ from \in DOMAIN sending.canister
      /\ Hosted(rt, to, receiving_subnet_id)
      /\ \E msg \in Live_Queue_Messages(sending.canister[from].queue):
          /\ to = msg.from
          /\ Is_Request(msg)
          \* Even if the receiving and sending subnets are the same, we route the message through
          \* message routing. In practice, the execution environment might shortcircuit this and
          \* deliver the message directly to the queue, but in some cases the message will actually
          \* go through the message routing. As we assume that the execution environment works correctly
          \* here, we only look at the case where the message goes through message routing.
          /\ stream' = Extend_Stream(stream, sending_subnet_id, receiving_subnet_id, Response(from, to, msg.id))
          /\ subnet' = Remove_Message(subnet, sending_subnet_id, from, msg)
          /\ UNCHANGED << registry, next_req_id  >>

\* @type: ($subnetId -> $subnetState, $subnetId, $canisterId, $canisterRunState) => ($subnetId -> $subnetState);
Update_Canister_State(s, subnet_id, canister_id, state) == [ s EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.state = state ] ] ]
    ]

\* Transition from stopped to started state. Note that on the IC, canisters
\* can also transition from the stopped into the started state, but we don't
\* modeled the stopped state in this model; it's equivalent to STOPPING without
\* having any pending responses.
Start_Canister(canister_id, subnet_id) ==
    /\ subnet_id \in DOMAIN subnet
    /\ canister_id \in DOMAIN subnet[subnet_id].canister
    /\ LET
            c == subnet[subnet_id].canister[canister_id]
       IN
            /\ c.state = STOPPING
            /\ c.pending = 0
            /\ subnet' = Update_Canister_State(subnet,  subnet_id, canister_id, RUNNING)
            /\ UNCHANGED << stream, registry, next_req_id >>

Empty_Canister_State == [
    state |-> RUNNING,
    queue |-> <<>>,
    pending |-> 0
]

Create_Canister(canister_id, subnet_id) ==
    /\ subnet_id \in DOMAIN subnet
    /\ canister_id \in DOMAIN registry[subnet[subnet_id].registry_version].routing_table
    /\ canister_id \notin DOMAIN subnet[subnet_id].canister
    /\ ~Subnet_Thinks_Its_Stopped(subnet_id)
    /\ registry[subnet[subnet_id].registry_version].routing_table[canister_id].on = subnet_id
    /\ subnet' = [ subnet EXCEPT ![subnet_id] = [ @ EXCEPT !.canister = canister_id :> Empty_Canister_State @@ @ ] ]
    /\ UNCHANGED << stream, registry, next_req_id >>


====