Model of II canister migration (i.e., migration specialized to the II canister).

The model encodes the following rules for message routing and the migration procedure.
We attempt to keep the textual description of the rules in sync with the TLA definitions;
in case of doubt, refer to the TLA definitions as the source of truth. 

***************
Message routing
***************

These are the rules for receiving messages (formalized in the Induct_Message action in the model).

Let:
    - C_s and C_r denote the canisters sending and receiving canisters of the message
    - S_r denote the receiving subnet of the stream from which the message is being inducted
    - S_s denote the sending subnet of the stream from which the message is being inducted
    - H_s denote the current hosting subnet of C_s (according to the routing table of S_r)
    - H_r denote the current hosting subnet of C_r (according to the routing table of S_r)
    - M_s denote the migration list for C_s (according to the routing table of S_r)
    - M_r denote the migration list for C_r (according to the routing table of S_r)
Then, if the message is a:

- Request:
    - If H_s = S_s, or both H_s and S_s are in M_s then:
        - If H_r is not S_r, then:
            - If both S_r and H_r are on M_r, then send ACK signal and send reject response.
            - Else, drop message (should not happen)
        - Else send ACK signal, queue request, eventually send response (or send immediate reject response if queuing the request fails)
    - Else drop request (should never occur from honest sending subnet)
- Response:
    - If H_s = S_s, or both H_s and S_s are in M_s then:
        - If H_r is not S_r: this should never happen for II migration (the reason being that the II canister
          does not send requests and thus can't receive responses, and H_r stays static for all other canisters)
        - Else send ACK signal, queue response (queuing should never fail)
    - Else drop response (should never occur from honest sending subnet)

Note: the above two rules are formalized in the Induct_Message predicate in the model.

These are the rules for receiving signals (formalized in the Induct_Signal action in the model). When receiving a:

- ACK signal:
    - Garbage collect acked message
- REJ signal
    - Should not happen in the II migration case

***************
Execution rules
***************

These are the rules for automatically deleting canister state:
    - Delete state of canister C if C is not on local subnet according to routing table, and the migration list for C is empty.

*******************
Migration Procedure
*******************

Formalized in the Migration_Procedure action.

To move canister C from subnet A to subnet B:

1. Add A and B to “migrating list” for canister C in registry in that order (A before B).
2. After all subnets observed this registry change, start migration process.
    2.1 C goes into stopping state on A (meaning, new incoming requests get reject responses, new outgoing requests get local reject responses, wait for all in-flight requests to be replied to)
    2.2 Once in-flight requests have been replied to, C goes into stopped state. Wait until it is stopped.
    2.3 Wait until C's input queues become empty. 
    2.4 Wait until C's output queues become empty. 
    2.5 Copy over state of C to subnet B (which B will accept because B is last destination in migration list for C)
    2.6 Update routing table
    2.7 Once B observes the routing table change from 2.6, manually put C into running state on subnet B
3. When
    - A doesn’t have any more responses from C in any of its outgoing streams,
    - all subnets have observed the routing table change from 2.7, and
    - no subnet (including A) has a message to C in its outgoing stream for A,
   then remove A from migrating list for C.
4. When subnet A observes routing table change, it will delete the state of C.

*****************
TLA+ cheat sheets
*****************

https://lamport.azurewebsites.net/tla/summary-standalone.pdf
https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html

Additionally, the model uses a couple of operators from the TLC module:

f @@ g is defined to be a function h with domain (DOMAIN f \union DOMAIN g),
where h[x] = f[x] if x \in DOMAIN f and h[x] = g[x] otherwise

x :> y is a function f whose domain is {x}, and f[x] = y

---- MODULE II_Migration ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

\******************************************************
\* General utility definitions
Range(f) == { f[x] : x \in DOMAIN f }
To_Set(seq) == Range(seq)
Remove_Arguments(f, S) == [ y \in DOMAIN f \ S |-> f[y] ]
Remove_Argument(f, x) == Remove_Arguments(f, {x})
Last(seq) == seq[Len(seq)]

\******************************************************
\* Constants that define the bounds on the model.
\* If you want to perform model checking with more subnets,
\* canisters, more requests or migrations, this is the place.

SUBNET_ID_LIST == << "s1", "s2", "s3" >>
SUBNET_ID == To_Set(SUBNET_ID_LIST)
CANISTER_ID_LIST == << "c1", "c2", "c3", "c4" >>
CANISTER_ID == To_Set(CANISTER_ID_LIST)
INIT_ROUTING_TABLE == 
  LET 
    s == SUBNET_ID_LIST
    c == CANISTER_ID_LIST
  IN
    c[1] :> [ on |-> s[1], migration_list |-> << >> ] 
    @@
    c[2] :> [ on |-> s[2], migration_list |-> << >> ]
    @@
    c[3] :> [ on |-> s[3], migration_list |-> << >> ]
    @@
    c[4] :> [ on |-> s[1], migration_list |-> << >> ]

CANISTERS_TO_MIGRATE == 
  LET 
    s == SUBNET_ID_LIST
    c == CANISTER_ID_LIST
  IN
    c[1] :> [ from |-> s[1], to |-> s[2]]

\* Requests can be issued at any time. Since we assign an increasing
\* ordinal number to every request (in order to distinguish multiple
\* requests between the same pairs of canisters), this could yield an
\* unbounded search space. We limit the total number of requests with
\* this constant.
MAX_REQUESTS == 3
\* Migrations can also start at any time (provided that the target
\* canister isn't being currently migrated). While this doesn't yield
\* an unbounded state space, we may still end up investigating a lot
\* of "uninteresting" states. For invariants, we could probably get rid 
\* of this with a symmetry-style equivalence relation on states, but
\* for liveness this is tricky.
MAX_MIGRATIONS == 1

\******************************************************
\* Named constants to help with readability/consistency
\* of the model
RUNNING == "RUNNING"
STOPPING == "STOPPING"
MIG_STARTED == "MIG_STARTED"
MIG_CANISTER_STOPPING == "MIG_CANISTER_STOPPING"
MIG_COPIED == "MIG_COPIED"
MIG_SWITCHED == "MIG_SWITCHED"
MIG_CANISTER_RUNNING == "MIG_CANISTER_RUNNING"

\* Global state:
VARIABLE 
    \* Directional inter-subnet streams
    stream, \* (SubnetId, SubnetId) -> [Messages]
    \* A list of routing tables, one for each successive registry version
    routing_table, \* [ CanisterId -> record with fields:
       \* on: SubnetId
       \* migration_list: [SubnetId]
    \* A directional inter-subnet stream of headers; headers are processed
    \* in the order they are emitted, so a stream works fine here.
    headers, \* (SubnetId, SubnetId) -> [ Signal ] 
    \* The state of each subnet
    subnet, \* SubnetId -> Record with fields:
       \* incoming_index: Nat - index into the remote subnet's outgoing stream, of what we've consumed
       \* outgoing_index: Nat - index into local outgoing stream to a subnet, saying what the remote 
       \*                                    subnet has acknowledged so far (used for garbage collection - which is not modelled)
       \* registry_version: Nat - local registry version
       \* canister: CanisterId -> CanisterState - state kept for canisters; not a total function, it's defined only for the canisters
       \*           kept on the local subnet, and the state is a record with fields as follows:
       \*    state: RUNNING | STOPPING - only these two states are modeled
       \*    queue: [{message: Message, processed: Bool}] - the canister input queue. Deviates from the implementation in that it's append-only: for each 
       \*                               we also keep a flag saying whether it has been processed, unlike the real queue that removes
       \*                               the message. This simplifies the specification of our in-order, at-most-once delivery.
       \*    pending: Nat - how many responses are pending for the canister (i.e., the count of call contexts)
    \* A counter used to order and distinguish requests
    next_req_id,
    \* Control information for the (manual) migration process, a map from CanisterId to the record with fields:
    \* state: MIG_STARTED | ... - the last executed step of the procedure
    \* registry_version: Nat - the registry version when the migration was started
    \* switch_registry_version: Nat - the registry version when the switch happened
    migration_procedure,
    \* Count how many migrations we've done so far, such that we can limit
    \* the total number of migrations in the state space
    migration_count

vars == << stream, routing_table, headers, subnet, next_req_id, migration_procedure, migration_count >>

Hosted(routing, canister_id, subnet_id) ==
    routing[canister_id].on = subnet_id

All_Hosted(routing, subnet_id) == { c \in CANISTER_ID: Hosted(routing, c, subnet_id)}

Current_Table == Last(routing_table)

\* "Spontaneous" event: update a subnet's local view on the registry (i.e., fetch new registry versions)
Update_Local_Registry(subnet_id) ==
  LET
    s == subnet[subnet_id]
  IN
    /\ \E new_version \in s.registry_version + 1..Len(routing_table):
       LET
        rt == routing_table[new_version]
        canisters_to_remove == { c \in DOMAIN s.canister: 
                /\ rt[c].on # subnet_id 
                /\ 
                    \/ rt[c].migration_list = << >> 
                    \* For II migration, we're being extra cautious to not lose the canister state.
                    \* Thus, we only remove state once the canister migration list is empty. So
                    \* The following disjunct does not apply to II migration.
                    \* \/ Last(rt[c].migration_list) # subnet_id
            }
       IN
        subnet' = [ subnet EXCEPT ![subnet_id] = [ @ EXCEPT 
            !.registry_version = new_version, 
            !.canister = Remove_Arguments(@, canisters_to_remove) 
          ]
        ]
    /\ UNCHANGED << stream, routing_table, headers, next_req_id, migration_procedure, migration_count >>

Sender_Ok(subnet_id, sending_subnet_id, msg) ==
  LET 
    table == routing_table[subnet[subnet_id].registry_version]
    from_entry == table[msg.from]
    mig_list == from_entry.migration_list
  IN
    \/ sending_subnet_id = from_entry.on
    \/ 
        /\ \E i \in 1..Len(mig_list): mig_list[i] = sending_subnet_id  
        /\ \E i \in 1..Len(mig_list): mig_list[i] = from_entry.on

Recipient_Hosted(subnet_id, msg) ==
  LET 
    table == routing_table[subnet[subnet_id].registry_version]
    to_entry  == table[msg.to]
  IN 
    /\ subnet_id = to_entry.on
    /\ msg.to \in DOMAIN subnet[subnet_id].canister

Should_Reroute(subnet_id, msg) ==
  LET 
    table == routing_table[subnet[subnet_id].registry_version]
    to_entry == table[msg.to]
    mig_list == to_entry.migration_list
  IN 
    /\ \E i \in 1..Len(mig_list): mig_list[i] = subnet_id
    /\ \E i \in 1..Len(mig_list): mig_list[i] = to_entry.on

Ack(i) == [type |-> "ACK", index |-> i]
Rej(i) == [type |-> "REJ", index |-> i]
Is_Ack(sig) == sig.type = "ACK"
Is_Rej(sig) == sig.type = "REJ"

Response(from, to, id) == [type |-> "RESP", from |-> from, to |-> to, id |-> id]
Request(from, to, id) == [type |-> "REQ", from |-> from, to |-> to, id |-> id]
Is_Request(msg) == msg.type = "REQ"
Is_Response(msg) == msg.type = "RESP"

Add_Header(sending_subnet_id, receiving_subnet_id, header) ==
    headers' = [ headers EXCEPT ![<< sending_subnet_id, receiving_subnet_id >>] = Append(@, header) ]

Increment_Incoming(s, receiving_id, sender_id) ==
    [ s EXCEPT ![receiving_id] = [ @ EXCEPT 
            !.incoming_index = [ @ EXCEPT ![sender_id] = @ + 1 ]
        ]
    ]

Queue_Message(s, subnet_id, msg) ==
    [ s EXCEPT ![subnet_id] =
            [ @ EXCEPT !.canister = [ @ EXCEPT ![msg.to] = [ @ EXCEPT !.queue = Append(@, [ message |-> msg, processed |-> FALSE ]) ]] ]
        ]

Set_Canister_State(s, subnet_id, canister_id, state) ==
    [ s EXCEPT ![subnet_id] = [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.state = state ]]] ]

Extend_Stream(s, sending_subnet_id, receiving_subnet_id, msg) ==
    [ s EXCEPT 
        ![<< sending_subnet_id, receiving_subnet_id >>] = 
            Append(@, msg)
    ]

Next_Stream_Index(sending_subnet_id, receiving_subnet_id) ==
  LET
    i == subnet[receiving_subnet_id].incoming_index[sending_subnet_id]
  IN i + 1

Unconsumed_Messages_Exist(sending_subnet_id, receiving_subnet_id) ==
  Next_Stream_Index(sending_subnet_id, receiving_subnet_id) 
    <= Len(stream[<< sending_subnet_id, receiving_subnet_id >>])

Next_Stream_Message(sending_subnet_id, receiving_subnet_id) ==
  LET
    str == stream[<< sending_subnet_id, receiving_subnet_id >>]
  IN str[Next_Stream_Index(sending_subnet_id, receiving_subnet_id)]

Is_Stopping(subnet_id, c) ==
    subnet[subnet_id].canister[c].state = STOPPING

\* "Spontaneous" event: try to induct a message from a remote outgoing stream
\* In reality, we may induct several messages simultaneously. In the model, we
\* always induct them one-by-one; this shouldn't have an effect on our properties.
Induct_Message(subnet_id, sending_subnet_id) ==
    /\ Unconsumed_Messages_Exist(sending_subnet_id, subnet_id) 
    /\ LET 
         new_i == Next_Stream_Index(sending_subnet_id, subnet_id)
         msg == Next_Stream_Message(sending_subnet_id, subnet_id)
         s == subnet[subnet_id]
       IN
        /\ Assert(Sender_Ok(subnet_id, sending_subnet_id, msg), 
            "For subnet " \o subnet_id \o ", subnet " \o sending_subnet_id \o " wasn't OK for sending canister " \o msg.from)
        /\ Assert(~Recipient_Hosted(subnet_id, msg) => Should_Reroute(subnet_id, msg),
            "Recipient " \o msg.to \o " not hosted on " \o subnet_id \o " and message shouldn't be re-routed; sender " \o msg.from)
        /\ Assert(Is_Response(msg) => Recipient_Hosted(subnet_id, msg),
            "Recipient " \o msg.to \o " of response not hosted on " \o subnet_id)
        /\ CASE Recipient_Hosted(subnet_id, msg) /\ ~(Is_Request(msg) /\ Is_Stopping(subnet_id, msg.to)) ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Ack(new_i))
                    /\ subnet' = Increment_Incoming(Queue_Message(subnet, subnet_id, msg), subnet_id, sending_subnet_id)
                    /\ UNCHANGED << stream, routing_table, next_req_id, migration_procedure, migration_count >>
             [] \/ Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) /\ Is_Stopping(subnet_id, msg.to)
                \/ ~Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Ack(new_i))
                    \* Send a reject response; we don't differentiate between "regular" and reject responses in the model
                    /\ stream' = Extend_Stream(
                              stream, 
                              subnet_id, 
                              sending_subnet_id, 
                              Response(msg.to, msg.from, msg.id))
                    /\ subnet' = Increment_Incoming(subnet, subnet_id, sending_subnet_id)
                    /\ UNCHANGED << routing_table, next_req_id, migration_procedure, migration_count >>
             \* This is just a sanity check to ensure that the assertions keep the preceding cases exhaustive
             \* This ensures that the model will complain if the event is disabled even though unconsumed messages exist
             [] OTHER ->
                Assert(FALSE, "The preceding cases should be exhaustive for message to " \o msg.to \o " and subnet" \o subnet_id)

Unconsumed_Signals_Exist(sending_subnet_id, receiving_subnet_id) ==
  headers[<<sending_subnet_id, receiving_subnet_id>>] # <<>>

Next_Signal(sending_subnet_id, receiving_subnet_id) ==
  Head(headers[<<sending_subnet_id, receiving_subnet_id>>])

Consume_One(h, subnet_id, remote_subnet_id) == [ h EXCEPT ![<<remote_subnet_id, subnet_id>>] = Tail(@) ]

Increment_Outgoing(s, subnet_id, remote_subnet_id) ==
    [ s EXCEPT ![subnet_id] = [ @ EXCEPT 
            !.outgoing_index = [ @ EXCEPT ![remote_subnet_id] = @ + 1 ]
        ]
    ]

\* "Spontaneous" event: try to induct a signal from a remote header stream
\* In reality, we may induct several signals simultaneously. In the model, we
\* always induct them one-by-one; this shouldn't have an effect on our properties.
Induct_Signal(subnet_id, sending_subnet_id) ==
    /\ Unconsumed_Signals_Exist(sending_subnet_id, subnet_id) 
    /\ LET
        sig == Next_Signal(sending_subnet_id, subnet_id)
       IN
        CASE Is_Ack(sig) -> 
            /\ headers' = Consume_One(headers, subnet_id, sending_subnet_id)
            /\ subnet' = Increment_Outgoing(subnet, subnet_id, sending_subnet_id)
            /\ UNCHANGED << stream, routing_table, next_req_id, migration_procedure, migration_count >>
          [] Is_Rej(sig) -> Assert(FALSE, "Got a reject signal")

Update_Pending(s, subnet_id, canister_id, upd_f(_)) ==
    [ s EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.pending = upd_f(@) ]]]
    ]

\* "Spontaneous" event: a canister sends a request to a different canister.
Send_Request(sending_subnet_id, receiving_subnet_id, from, to) ==
  LET
    sending == subnet[sending_subnet_id]
    rt == routing_table[sending.registry_version]
  IN
    \* Build this directly into the model, as TLC CONSTRAINT clause has weird
    \* semantics: the states violating the clause are still considered, but their successors
    \* are not. So with CONSTRAINT we would issue one request than MAX_REQUESTS, but never get a response 
    \* (as we wouldn't consider the successor state)
    /\ next_req_id <= MAX_REQUESTS
    \* The II canister never sends requests to other canisters, so we prohibit this in the II migration model.
    /\ from \notin DOMAIN(CANISTERS_TO_MIGRATE)
    /\ rt[from].on = sending_subnet_id
    /\ rt[to].on = receiving_subnet_id
    /\ from \in DOMAIN sending.canister
    /\ sending.canister[from].state = RUNNING
    \* Even if the receiving and sending subnets are the same, we route the message through
    \* message routing. In practice, the execution environment might shortcircuit this and
    \* deliver the message directly to the queue, but in some cases the message will actually
    \* go through the message routing. As we assume that the execution environment works correctly
    \* here, we only look at the case where the message goes through message routing.
    /\ stream' = Extend_Stream(stream, sending_subnet_id, receiving_subnet_id, Request(from, to, next_req_id))
    /\ subnet' = Update_Pending(subnet, sending_subnet_id, from, LAMBDA p: p + 1)
    /\ next_req_id' = next_req_id + 1
    /\ UNCHANGED << routing_table, headers, migration_procedure, migration_count >>

\* Map a function over a sequence
Map_Seq(s, f(_)) == [i \in 1 .. Len(s) |-> f(s[i])]

\* Logically remove a message from a queue. If the same message got delivered twice, this would 
\* mark both instances of the message as processed simultaneously. However, our properties should
\* ensure that this doesn't happen.
Remove_Message(s, subnet_id, canister_id, msg) == [ s EXCEPT ![subnet_id] = 
    [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] =
            [ @ EXCEPT !.queue = 
                Map_Seq(@, LAMBDA m: IF m.message = msg /\ ~m.processed 
                                        THEN [ message |-> msg, processed |-> TRUE ] 
                                        ELSE m) ]
        ]
    ]
  ]

\* As we never remove messages from the queues in our model, use the following operator to
\* access the "live" (i.e., unprocessed) queue messages.
Live_Queue_Messages(q) == { live.message : 
    live \in { m \in To_Set(q): m.processed = FALSE } }

\* All the messages ever received in a queue (in the order they were received in)
Queue_History(q) == Map_Seq(q, LAMBDA m: m.message)

\* "Spontaneous" event: a canister responds to a request in its input queue.
\* Here, we can send a response any time for any message in the queue, ignoring the order.
\* This somewhat mimics the fact that responses don't have to be issued in the same order that
\* the requests came in.
\* However, in reality, a request 1 might trigger an outgoing request 2, and only upon
\* the completion of request 2 does the canister send the response to request 1.
\* So any fairness assumptions on this may be too strong. Not sure if this is problematic.
Send_Response(sending_subnet_id, receiving_subnet_id, from, to) ==
  LET
    sending == subnet[sending_subnet_id]
    rt == routing_table[sending.registry_version]
  IN
    /\ from \in DOMAIN sending.canister
    /\ \E msg \in Live_Queue_Messages(sending.canister[from].queue):
        /\ to = msg.from
        /\ Is_Request(msg)
        /\ receiving_subnet_id = rt[to].on
        \* Even if the receiving and sending subnets are the same, we route the message through
        \* message routing. In practice, the execution environment might shortcircuit this and
        \* deliver the message directly to the queue, but in some cases the message will actually
        \* go through the message routing. As we assume that the execution environment works correctly
        \* here, we only look at the case where the message goes through message routing.
        /\ stream' = Extend_Stream(stream, sending_subnet_id, receiving_subnet_id, Response(from, to, msg.id))
        /\ subnet' = Remove_Message(subnet, sending_subnet_id, from, msg)
        /\ UNCHANGED << routing_table, headers, next_req_id, migration_procedure, migration_count >>

\* "Spontaneous" event: a canister processes a response from its queue.
\* We allow responses to be processed in any order, i.e., we disregard the order imposed by the queue.
Process_Response(subnet_id, c) ==
  LET
    s == subnet[subnet_id]
  IN
    /\ c \in DOMAIN s.canister
    /\ \E msg \in Live_Queue_Messages(s.canister[c].queue):
        /\ Is_Response(msg)
        /\ subnet' = Update_Pending(Remove_Message(subnet, subnet_id, c, msg), subnet_id, c, LAMBDA p: p - 1)
        /\ UNCHANGED << routing_table, stream, headers, next_req_id, migration_procedure, migration_count >>

\* "Operator" event: start migrating a canister
Start_Migrating_Canister(c, from_subnet_id, to_subnet_id) == 
    /\ migration_count < MAX_MIGRATIONS
    /\ c \notin DOMAIN migration_procedure
    /\ from_subnet_id = Current_Table[c].on
    /\ to_subnet_id # Current_Table[c].on
    /\ routing_table' = Append(routing_table, 
        c :> [on |-> Current_Table[c].on, migration_list |-> Current_Table[c].migration_list \o << from_subnet_id, to_subnet_id >> ]
            @@ Current_Table
       )
    /\ migration_procedure' = c :> [state |-> MIG_STARTED, registry_version |-> (Len(routing_table) + 1) ] @@ migration_procedure
    /\ UNCHANGED << headers, stream, subnet, next_req_id, migration_count >>

Set_Migration_State(mig_proc, c, state) ==
    [ mig_proc EXCEPT ![c] = [ @ EXCEPT !.state = state ] ]


Migration_Universally_Observed(c) ==
    /\ \A s \in SUBNET_ID: subnet[s].registry_version >= migration_procedure[c].registry_version

\* "Operator" event: put canister into a stopping state
Stop_Canister(subnet_id, c) ==
  LET
    s == subnet[subnet_id]
    rt == routing_table[s.registry_version]
  IN
    /\ c \in DOMAIN migration_procedure
    /\ migration_procedure[c].state = MIG_STARTED
    /\ c \in DOMAIN s.canister
    /\ s.canister[c].state = RUNNING
    /\ Migration_Universally_Observed(c)
    /\ subnet_id = routing_table[migration_procedure[c].registry_version][c].on
    /\ subnet' = [subnet EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![c] = [ @ EXCEPT !.state = STOPPING ]]]
       ]
    /\ migration_procedure' = Set_Migration_State(migration_procedure, c, MIG_CANISTER_STOPPING)
    /\ UNCHANGED << routing_table, headers, stream, next_req_id, migration_count >>

\* "Operator" event: copy canister state
Copy_Canister_State(canister_id, old_subnet_id, new_subnet_id) ==
  LET 
    old_subnet == subnet[old_subnet_id]
    new_subnet == subnet[new_subnet_id]
    old_entry == routing_table[old_subnet.registry_version][canister_id]
    new_entry == routing_table[new_subnet.registry_version][canister_id]
  IN
    /\ canister_id \in DOMAIN migration_procedure
    /\ migration_procedure[canister_id].state = MIG_CANISTER_STOPPING
    \* To move the canister, the operator should ensure that it's stopped.
    \* We conflate the stopped state with the following two conditions:
    \* 1. the canister is stopping 
    \* 2. it has no more messages pending responses, i.e., has no open call contexts
    \* Moreover, the operator should manually check the following two conditions:
    \* 1. the canister has an empty input queue.
    \* 2. the canister has an empty output queue
    \* Note that these should be checked in the order specified, as a canister with
    \* a non-empty input queue may add messages to the output queue later on. Moreover,
    \* the check on the output queues is not modelled here, as the model does not include
    \* output queues.
    /\ canister_id \in DOMAIN old_subnet.canister
    /\ old_subnet.canister[canister_id].state = STOPPING
    /\ old_subnet.canister[canister_id].pending = 0
    /\ Live_Queue_Messages(old_subnet.canister[canister_id].queue) = {}
    /\ old_entry.on = old_subnet_id
    /\ new_entry.on = old_subnet_id
    /\ old_entry.migration_list # << >>
    /\ new_subnet_id = Last(old_entry.migration_list)
    /\ new_entry.migration_list # << >>
    /\ new_subnet_id = Last(new_entry.migration_list)
    /\ subnet' = [ subnet EXCEPT ![new_subnet_id] = 
        [ @ EXCEPT !.canister = 
            canister_id :> old_subnet.canister[canister_id] @@ @
        ] 
       ]
    /\ migration_procedure' = Set_Migration_State(migration_procedure, canister_id, MIG_COPIED)
    /\ UNCHANGED << headers, stream, routing_table, next_req_id, migration_count >>

Add_Switch_Registry_Version_Field(mig_proc, c, version) == [ mig_proc EXCEPT ![c] =
    [ switch_registry_version |-> version ] @@ @ ]

\* "Operator" event: switch canister to the target subnet in the routing table
Switch_Canister(c) ==
    /\ c \in DOMAIN migration_procedure
    /\ migration_procedure[c].state = MIG_COPIED
    /\ LET
        start_version == migration_procedure[c].registry_version
        start_rt == routing_table[start_version]
        to_subnet_id == Last(start_rt[c].migration_list)
       IN
        /\ c \in DOMAIN subnet[to_subnet_id].canister
        /\ routing_table' = Append(routing_table, c :> [ 
                on |-> to_subnet_id, 
                migration_list |-> Current_Table[c].migration_list 
            ] @@ Current_Table)
        /\ migration_procedure' = Add_Switch_Registry_Version_Field(
            Set_Migration_State(migration_procedure, c, MIG_SWITCHED),
            c,
            Len(routing_table) + 1
          )
        /\ UNCHANGED << stream, subnet, next_req_id, headers, migration_count >>

Start_Canister(c, subnet_id) ==
    /\ c \in DOMAIN migration_procedure
    /\ migration_procedure[c].state = MIG_SWITCHED
    /\ LET
        switch_version == migration_procedure[c].switch_registry_version
       IN
        /\ subnet[subnet_id].registry_version >= switch_version
        /\ routing_table[subnet[subnet_id].registry_version][c].on = subnet_id
        /\ subnet' = Set_Canister_State(subnet, subnet_id, c, RUNNING)
        /\ migration_procedure' = Set_Migration_State(migration_procedure, c, MIG_CANISTER_RUNNING)
        /\ UNCHANGED << stream, next_req_id, routing_table, headers, migration_count >>

\* "Live" (not garbage collected) part of the stream between two subnets
Live_Stream(from, to) ==
    LET
        s == stream[<<from, to>>]
        i == subnet[from].outgoing_index[to]
    IN
        SubSeq(s, i + 1, Len(s))

\* "Operator" event: start migrating a canister
Finish_Migration(subnet_id, c) ==
    /\ c \in DOMAIN migration_procedure
    /\ migration_procedure[c].state = MIG_CANISTER_RUNNING
    /\ subnet_id = routing_table[migration_procedure[c].registry_version][c].on
    /\ \A sn2 \in SUBNET_ID: 
          \A msg \in To_Set(Live_Stream(subnet_id, sn2)): msg.from # c
    /\ \A sn2 \in SUBNET_ID:
        /\ subnet[sn2].registry_version >= migration_procedure[c].switch_registry_version
        /\ \A msg \in To_Set(Live_Stream(sn2, subnet_id)): msg.to # c
    /\ migration_procedure' = Remove_Argument(migration_procedure, c)
    /\ routing_table' = Append(routing_table, 
           c :> [
            on |-> Current_Table[c].on,
            migration_list |-> << >>
          ] @@ Current_Table
       )
    /\ migration_count' = migration_count + 1
    /\ UNCHANGED << stream, subnet, next_req_id, headers >>

\* All "operator" events
Migration_Procedure(from_subnet_id, to_subnet_id, c) ==
    \/ Start_Migrating_Canister(c, from_subnet_id, to_subnet_id)
    \/ Stop_Canister(from_subnet_id, c)
    \/ Copy_Canister_State(c, from_subnet_id, to_subnet_id)
    \/ Switch_Canister(c)
    \/ Start_Canister(c, to_subnet_id)
    \/ Finish_Migration(from_subnet_id, c)

Init ==
    /\ stream = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ routing_table = << INIT_ROUTING_TABLE >>
    /\ headers = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ subnet = [s \in SUBNET_ID |-> [
                incoming_index |-> [ s2 \in SUBNET_ID |-> 0 ],
                outgoing_index |-> [ s2 \in SUBNET_ID |-> 0 ],
                registry_version |-> 1,
                canister |-> [c \in All_Hosted(INIT_ROUTING_TABLE, s) |-> 
                    [ state |-> RUNNING, queue |-> << >>, pending |-> 0] 
                ]
            ]
        ]
    /\ migration_procedure = [ x \in {} |-> {}]
    /\ next_req_id = 1
    /\ migration_count = 0
    \* A dummy request that is allowed to preceed any other request

\* An additional event to explicitly idle when we are done with migration,
\* so that we can turn on deadlock warnings.
Idle == 
    /\ migration_count = MAX_MIGRATIONS
    /\ UNCHANGED vars

Next == \E s1, s2 \in SUBNET_ID: \E c1, c2 \in CANISTER_ID:
    \/ Send_Request(s1, s2, c1, c2)
    \/ Send_Response(s1, s2, c1, c2)
    \/ Process_Response(s1, c1)
    \/ Induct_Message(s1, s2)    
    \/ Induct_Signal(s1, s2)    
    \/ Update_Local_Registry(s1)
    \/ \E c \in DOMAIN(CANISTERS_TO_MIGRATE): 
        Migration_Procedure(CANISTERS_TO_MIGRATE[c].from, CANISTERS_TO_MIGRATE[c].to, c)
    \/ Idle
    \* \/ Update_Routing_Table

\*************************************************
\* Properties
Inv_Requests_Capped ==
    next_req_id <= MAX_REQUESTS + 1

Inv_Registry_Length_Capped ==
    Len(routing_table) <= 4 * MAX_MIGRATIONS

Inv_Queues_Correct == \A c \in CANISTER_ID, s \in SUBNET_ID:
    c \in DOMAIN subnet[s].canister =>
        \A m \in To_Set(subnet[s].canister[c].queue): m.message.to = c

\* The natural specification of the in-order delivery requirement isn't an invariant,
\* but a temporal property: after we induct a C1->C2 message with id i into a queue, we never induct
\* another  C1 -> C2 message with an id j <= i (the <= instead of < also ensures at-most-once delivery).
\* We convert this into an invariant by keeping the entire history of the queue in the model
\* state, and never removing messages from the queue, but just marking them as processed (see
\* Remove_Message).
Inv_In_Order == \A s \in SUBNET_ID: \A c \in DOMAIN subnet[s].canister:
  LET qh == Queue_History(subnet[s].canister[c].queue)
  IN
    \A i, j \in 1..Len(qh):
        /\ i < j
        /\ Is_Request(qh[i])
        /\ Is_Request(qh[j])
        /\ qh[i].from = qh[j].from 
        => qh[i].id < qh[j].id 
    
\* Invariant: a canister only receives a single response for a message.
\* Again, as our queues keep the entire history fo received messages, this
\* suffices to prove at-most-once delivery of responses.
Inv_At_Most_One_Response == \A s \in SUBNET_ID: \A c \in DOMAIN subnet[s].canister:
  LET qh == Queue_History(subnet[s].canister[c].queue)
  IN
    \A i, j \in 1..Len(qh):
        /\ i < j
        /\ Is_Response(qh[i])
        /\ Is_Response(qh[j])
        /\ qh[i].from = qh[j].from 
        => qh[i].id # qh[j].id 

\* To guarantee delivery of responses, we need certain fairness conditions.
\* Namely, we require that the events below are not postponed forever
Response_Fairness_Condition == \A s1, s2 \in SUBNET_ID: \A c1, c2 \in CANISTER_ID:
    /\ WF_vars(Send_Response(s1, s2, c1, c2))
    /\ WF_vars(Induct_Message(s1, s2))

Spec == Init /\ []([Next]_vars) /\ Response_Fairness_Condition

\* The guaranteed response property uses the "leads to" operator: A ~> B means
\* that whenever A happens, B must also happen at that time or later
Guaranteed_Response == \A from, to \in CANISTER_ID: \A i \in 1..MAX_REQUESTS:
      (\E s1, s2 \in SUBNET_ID: 
        Request(from, to, i) \in To_Set(Live_Stream(s1, s2))) 
    ~>
      (\E s \in SUBNET_ID: 
                /\ from \in DOMAIN subnet[s].canister
                /\ Response(to, from, i) \in To_Set(Queue_History(subnet[s].canister[from].queue)))

====