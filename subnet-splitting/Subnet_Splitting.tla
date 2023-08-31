A model of message routing for subnet splitting.

The model encodes the following rules for message routing and the migration procedure.

***************
Message routing
***************

These are the rules for receiving messages (formalized in the Induct_Message action in the model). 
All references to "routing table" refer to the current routing table of the subnet receiving the message.

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
        - If H_r is not S_r, send a REJ signal
        - Else send ACK signal, queue response (queuing should never fail)
    - Else drop response (should never occur from honest sending subnet)

Note: the above two rules are formalized in the Induct_Message predicate in the model.

These are the rules for receiving signals (formalized in the Induct_Signal action in the model). When receiving a:

- ACK signal:
    - Garbage collect acked message
- REJ signal; if the rejected message is a:
    - Request: this should never happen
    - Response: garbage collect the response and re-schedule the response according to the current routing table 

*******************
Migration Procedure
*******************

Formalized in the Migration_Procedure action.

If canister C is moved from subnet A to (the newly created) subnet B during a subnet split:

0. The subnet B is created. This part is not modeled, we assume that the target already exists.
1. Add A and B to “migrating list” for canister C in registry in that order (A before B).
2. After all subnets observed this registry change, start migration process.
    2.1 Subnet A halts and produces final CUP
    2.2 Someone fetches final CUP from subnet A, creates recovery CUPs for subnets A and B with appropriate state hash.
    2.3 Update the routing table in the registry.
    2.4 Recover the subnets A and B with the appropriate state.
    Steps 2.1-2.4 are modeled as an atomic step for simplicity.
3. Execute the following in any order.
   3.1. When:
        - step 2 completes
        - subnet A delivers all messages to other subnets that were in its outgoing streams at the time it was halted
    then unhalt subnet B
   3.2. When step 2 completes, record the indices of the ends of all outgoing streams from other subnets to A. Then
    3.2.1 When all the subnets have garbage collected the above indices, record the outgoing indices from A to all other subnets.
    3.2.3 When A delivers all messages from the previous step, clear the migrating list for C

*****************
TLA+ cheat sheets
*****************

https://lamport.azurewebsites.net/tla/summary-standalone.pdf
https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html

Additionally, the model uses a couple of operators from the TLC module:

f @@ g is defined to be a function h with domain (DOMAIN f \union DOMAIN g),
where h[x] = f[x] if x \in DOMAIN f and h[x] = g[x] otherwise

x :> y is a function f whose domain is {x}, and f[x] = y

---- MODULE Subnet_Splitting ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Apalache, Variants, SequencesExt

\******************************************************
\* General utility definitions
\* @type: (a -> b) => Set(b);
Range(f) == { f[x] : x \in DOMAIN f }
\* @type: Seq(a) => Set(a);
\* To_Set(seq) == ApaFoldSeqLeft(LAMBDA x, y: {y} \union x, {}, seq)
To_Set(X) == ToSet(X)
\* @type: ((a -> b), Set(a)) => a -> b;
Remove_Arguments(f, S) == [ y \in DOMAIN f \ S |-> f[y] ]
Remove_Argument(f, x) == Remove_Arguments(f, {x})
\* Last(seq) == seq[Len(seq)]

\******************************************************
\* Constants that define the bounds on the model.
\* If you want to perform model checking with more subnets,
\* canisters, more requests or migrations, this is the place.

\* The following differ for each scenario, so they are instantiated later
CONSTANT 
    \* @type: Seq($subnetId);
    SUBNET_ID_LIST,
    \* @type: Seq($canisterId);
    CANISTER_ID_LIST,
    \* Specifies where canisters are located. Differs for each s
    \* @type: $canisterId -> { on: $subnetId, migration_list: Seq($subnetId)};
    INIT_ROUTING_TABLE,
    \* @type: Set($canisterId);
    \* Which canisters exist initially. Canisters from CANISTER_ID_LIST may still exist in
    \* the routing table, without actually having state on their "hosting" subnet. This models
    \* the canister ranges in the routing table, which may (and normally do) contain canisters
    \* which do not exist.
    INITIAL_EXISTING,
    \* @type: Set($canisterId) -> { from: $subnetId, to: $subnetId };
    CANISTERS_TO_MIGRATE

SUBNET_ID == To_Set(SUBNET_ID_LIST)

CANISTER_ID == To_Set(CANISTER_ID_LIST)


INIT_SUBNET_INFO ==
  LET
    s == SUBNET_ID_LIST
  IN
    s[1] :> [ is_halted |-> FALSE ]
    @@
    s[2] :> [ is_halted |-> FALSE ]
    @@
    s[3] :> [ is_halted |-> TRUE ]

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

MAX_RESCHEDULINGS == 1

\* @typeAlias: canisterId = Str;
\* @typeAlias: subnetId = Str;
\* @typeAlias: message = { type: Str, from: $canisterId, to: $canisterId, id: Int };
\* @typeAlias: signal = { type: Str, index: Int };
\* @typeAlias: canisterRunState = C_Running(UNIT) | C_Stopping(UNIT);
_dummy_alias_constant == TRUE

\******************************************************
\* Named constants to help with readability/consistency
\* of the model
RUNNING == Variant("C_Running", UNIT)
STOPPING == Variant("C_Stopping", UNIT)

\* @typeAlias: migrationListRemovalPhase = To_Parent($subnetId -> Int) | From_Parent($subnetId -> Int) | Removed_From_List(UNIT);
\* @type: $migrationListRemovalPhase;
Removed_From_List == Variant("Removed_From_List", UNIT)
\* @type: ($subnetId -> Int) => $migrationListRemovalPhase;
To_Parent(indices) == Variant("To_Parent", indices)
\* @type: ($subnetId -> Int) => $migrationListRemovalPhase;
From_Parent(indices) == Variant("From_Parent", indices)
\* @typeAlias: unhaltingPhase = Has_Outgoing($subnetId -> Int) | Unhalting_Done(UNIT);
\* @type: $unhaltingPhase;
Unhalting_Done == Variant("Unhalting_Done", UNIT)
\* @type: ($subnetId -> Int) => $unhaltingPhase;
Has_Outgoing(indices) == Variant("Has_Outgoing", indices)
\* @typeAlias: migrationState = 
\*  Mig_Started(Int)
\*  | Mig_Switched({switch_version: Int, stream_index_for_unhalting: $unhaltingPhase, stream_index_for_migration_list: $migrationListRemovalPhase}) 
\*  | Mig_Done(UNIT);
\* @type: Int => $migrationState;
MIG_STARTED(registry_version) == Variant("Mig_Started", registry_version)
\* @type: $migrationState => Bool;
Is_Mig_Started(mig_state) == VariantTag(mig_state) = "Mig_Started"
\* @type: $migrationState => Int;
Get_Start_Version(state) == VariantGetUnsafe("Mig_Started", state)
\* @type: $migrationState => Bool;
Is_Mig_Switched(mig_state) == VariantTag(mig_state) = "Mig_Switched"
\* @type: ({ switch_version: Int, stream_index_for_unhalting: $unhaltingPhase, stream_index_for_migration_list: $migrationListRemovalPhase}) => $migrationState;
MIG_SWITCHED(data) == Variant("Mig_Switched", data)
\* @type: $migrationState => Int;
Get_Switched_Version(migration_state) == VariantGetUnsafe("Mig_Switched", migration_state).switch_version
\* @type: $migrationState => Bool;
Watching_Indices_To_Parent(migration_state) ==
    /\ Is_Mig_Switched(migration_state) 
    /\ 
      LET s == VariantGetUnsafe("Mig_Switched", migration_state)
      IN
        /\ VariantTag(s.stream_index_for_migration_list)  = "To_Parent"
\* @type: $migrationState => $subnetId -> Int;
Get_Switched_Indices_To_Parent(migration_state) == VariantGetUnsafe("To_Parent", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list)
\* @type: $migrationState => Bool;
Watching_Indices_From_Parent(migration_state) ==
    /\ Is_Mig_Switched(migration_state) 
    /\ 
      LET s == VariantGetUnsafe("Mig_Switched", migration_state)
      IN
        /\ VariantTag(s.stream_index_for_migration_list) = "From_Parent"
\* @type: ($migrationState, $migrationListRemovalPhase) => $migrationState;
Set_Migration_List_Index(migration_state, index) == 
  LET
    current == VariantGetUnsafe("Mig_Switched", migration_state)
  IN
    MIG_SWITCHED([ current EXCEPT !.stream_index_for_migration_list = index ])
\* @type: ($migrationState, $subnetId, Int) => $migrationState;
Set_Switched_Index_To_Parent(migration_state, subnet_id, index) ==
    Set_Migration_List_Index(migration_state, To_Parent(subnet_id :> index @@ Get_Switched_Indices_To_Parent(migration_state)))

\* @type: $migrationState => Bool;
Done_Observing_Streams(migration_state) ==
    /\ Is_Mig_Switched(migration_state)
    /\ VariantTag(VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list) # "Removed_From_List"
\* @type: ($migrationState, $unhaltingPhase) => $migrationState;
Set_Unhalting_Index(migration_state, index) == 
  LET
    current == VariantGetUnsafe("Mig_Switched", migration_state)
  IN
    MIG_SWITCHED([ current EXCEPT !.stream_index_for_unhalting = index ])
\* @type: $migrationState => Bool;
Done_Unhalting(migration_state) ==
    /\ Is_Mig_Switched(migration_state)
    /\ VariantTag(VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_unhalting) = "Unhalting_Done"
\* @type: $migrationState => ($subnetId -> Int);
Get_Unhalting_Indices(migration_state) ==
    VariantGetUnsafe("Has_Outgoing", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_unhalting)

\* @type: $migrationState => $subnetId -> Int;
Get_Switched_Indices_From_Parent(migration_state) == VariantGetUnsafe("From_Parent", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list)

\* Global state:
VARIABLE 
    \* Directional inter-subnet streams
    \* @typeAlias: msgStreams = << $subnetId, $subnetId >> -> Seq($message);
    \* @type: $msgStreams;
    stream,
    \* A list of registries, one for each successive registry version
    \* @typeAlias: routingTable = $canisterId -> {on: $subnetId, migration_list: Seq($subnetId) };
    \* @typeAlias: registries = Seq({
    \*      routing_table: $routingTable,
    \*      subnet_info: $subnetId -> { is_halted: Bool }
    \* });
    \* @type: $registries;
    registry,
    \* A directional inter-subnet stream of headers; headers are processed
    \* in the order they are emitted, so a stream works fine here.
    \* @typeAlias: hdrStreams = << $subnetId, $subnetId >> -> Seq($signal);
    \* @type: $hdrStreams;
    headers,
    \* The state of each subnet
    \* @typeAlias: canisterState = {
    \*      state: $canisterRunState,
    \*      queue: Seq({message: $message, processed: Bool}), // the canister input queue. Deviates from the implementation in that it's append-only. 
    \*                                                        // For each we also keep a flag saying whether it has been processed, unlike the real queue that removes the message. 
    \*                                                        // This simplifies the specification of our in-order, at-most-once delivery. 
    \*      pending: Int
    \* }; 
    \* @typeAlias: subnetState = {
    \*      incoming_index: $subnetId -> Int, // index into the remote subnet's outgoing stream, of what we've consumed
    \*      outgoing_index: $subnetId -> Int,  // index into local outgoing stream to a subnet, saying what the remote subnet has acknowledged so far (used for garbage collection - which is not modelled)
    \*      registry_version: Int, // local registry version
    \*      canister: $canisterId -> $canisterState // State kept for canisters. Not a total function, it's defined only for the canisters kept on the local subnet
    \* };
    \* @typeAlias: subnets = $subnetId -> $subnetState;
    \* @type: $subnets;
    subnet, 
    \* A counter used to order and distinguish requests
    \* @type: Int;
    next_req_id,
    \* Control information for the (manual) migration process, a map from CanisterId to the record with fields:
    \* @typeAlias: migrationProcedure = Set($canisterId) -> $migrationState;
    \* @type: $migrationProcedure;
    migration_procedure,
    \* Count how many migrations we've done so far, such that we can limit
    \* the total number of migrations in the state space
    \* @type: Int;
    migration_count,
    \* Count how many times a response has been rescheduled due to a reject signal.
    \* Constant rescheduling (without updating the routing table in the meantime) could 
    \* yield an unbounded state space; we use this count to bound the space.
    \* @type: $subnetId -> Int;
    rescheduling_count

vars == << stream, registry, headers, subnet, next_req_id, migration_procedure, migration_count, rescheduling_count >>

\* @type: ($routingTable, $canisterId) => $subnetId;
Hosting_Subnet(routing, canister_id) ==
    routing[canister_id].on

Hosted(routing, canister_id, subnet_id) ==
    Hosting_Subnet(routing, canister_id) = subnet_id

\* @type: ($routingTable, $canisterId) => Seq($subnetId);
Migration_List(routing, canister_id) ==
    routing[canister_id].migration_list

All_Hosted(routing, subnet_id) == { c \in CANISTER_ID: Hosted(routing, c, subnet_id) }

Current_Table == Last(registry).routing_table
Current_Subnet_Info == Last(registry).subnet_info

Empty_Subnet_State(canisters) == [
    incoming_index |-> [ s2 \in SUBNET_ID |-> 0 ],
    outgoing_index |-> [ s2 \in SUBNET_ID |-> 0 ],
    registry_version |-> 1,
    canister |-> [c \in canisters |-> 
        [ state |-> RUNNING, queue |-> << >>, pending |-> 0]  
    ]
  ]

Empty_Canister_State == [
    state |-> RUNNING,
    queue |-> <<>>,
    pending |-> 0
]

Subnet_Thinks_Its_Stopped(subnet_id) ==
    \/ subnet_id \notin DOMAIN subnet
    \/ subnet_id \notin DOMAIN registry[subnet[subnet_id].registry_version].subnet_info
    \/ registry[subnet[subnet_id].registry_version].subnet_info[subnet_id].is_halted


\* Apalache doesn't like string concatenation
\* String_Of_Elements(S) == ApaFoldSet(LAMBDA x, y: y \o ", " \o x, "", S)
\* Set_To_String(S) == "{" \o String_Of_Elements(S) \o "}"

\* @type: ($registries, Int, $subnets, $subnetId) => $subnets;
Apply_Registry_Update(registries, registry_version, s, subnet_id) ==
  LET
    reg == registries[registry_version]
    rt == reg.routing_table
    \* TODO: we should probably only allow this if the subnet is unhalted,
    \* but we'd need to make Split_State more fine-grained for this to work
    \* (as we rely on applying the registry update on the parent in order to trim
    \* the state of the existing canisters)
    state == s[subnet_id]
    canisters_to_remove == { c \in DOMAIN state.canister: /\ ~Hosted(rt, c, subnet_id)  }
    canisters_to_start == { c \in DOMAIN state.canister:
            /\ Migration_List(rt, c) # << >> 
            /\ Last(Migration_List(rt, c)) = subnet_id
        }
    intersection == canisters_to_remove \intersect canisters_to_start
    check == Assert(intersection = {},
        "Subnet doesn't know whether to start or remove canisters " \* \o Set_To_String(intersection)
        \* "Subnet " \o subnet_id \o " doesn't know whether to start or remove canisters " \* \o Set_To_String(intersection)
    )
  IN
    [ s EXCEPT ![subnet_id] = [ @ EXCEPT 
            !.registry_version = registry_version, 
            !.canister = Remove_Arguments(@, canisters_to_remove)
        ]
      ]

\* "Spontaneous" event: update a subnet's local view on the registry (i.e., fetch new registry versions)
Update_Local_Registry(subnet_id) ==
  LET
    s == subnet[subnet_id]
  IN
    /\ \E new_version \in s.registry_version + 1..Len(registry):
        /\ subnet' = Apply_Registry_Update(registry, new_version, subnet, subnet_id)
    /\ UNCHANGED << stream, registry, headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

\* @type: ($subnetId -> $subnetState, $subnetId, $canisterId, $canisterRunState) => ($subnetId -> $subnetState);
Update_Canister_State(s, subnet_id, canister_id, state) == [ s EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.state = state ] ] ]
    ]

\* Transition from stopped to started state. Note that on the IC, canisters
\* can also transition from the stopped into the started state, but we don't
\* modeled the stopped state in this model; it's equivalent to STOPPING without
\* having any pending responses.
Start_Canister(canister_id, subnet_id) ==
    /\ canister_id \in DOMAIN subnet[subnet_id].canister
    /\ LET
            c == subnet[subnet_id].canister[canister_id]
       IN
            /\ c.state = STOPPING
            /\ c.pending = 0
            /\ subnet' = Update_Canister_State(subnet,  subnet_id, canister_id, RUNNING)
            /\ UNCHANGED << stream, registry, headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

Create_Canister(canister_id, subnet_id) ==
    /\ canister_id \in DOMAIN registry[subnet[subnet_id].registry_version].routing_table
    /\ canister_id \notin DOMAIN subnet[subnet_id].canister
    /\ ~Subnet_Thinks_Its_Stopped(subnet_id)
    /\ registry[subnet[subnet_id].registry_version].routing_table[canister_id].on = subnet_id
    /\ subnet' = [ subnet EXCEPT ![subnet_id] = [ @ EXCEPT !.canister = canister_id :> Empty_Canister_State @@ @ ] ]
    /\ UNCHANGED << stream, registry, headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

\* @type: ($subnetId, $subnetId, $message) => Bool;
Sender_Ok(subnet_id, sending_subnet_id, msg) ==
  LET 
    reg == registry[subnet[subnet_id].registry_version]
    table == reg.routing_table
    mig_list == Migration_List(table, msg.from)
  IN
    \/ Hosted(table, msg.from, sending_subnet_id)
    \/ \E i, j \in 1..Len(mig_list): 
        /\ mig_list[i] = sending_subnet_id  
        /\ Hosted(table, msg.from, mig_list[j])
 
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

Response(from, to, id) == [type |-> "RESP", from |-> from, to |-> to, id |-> id]
Request(from, to, id) == [type |-> "REQ", from |-> from, to |-> to, id |-> id]
\* @type: $message => Bool;
Is_Request(msg) == msg.type = "REQ"
\* @type: $message => Bool;
Is_Response(msg) == msg.type = "RESP"

Add_Header(sending_subnet_id, receiving_subnet_id, header) ==
    headers' = [ headers EXCEPT ![<< sending_subnet_id, receiving_subnet_id >>] = Append(@, header) ]

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

\* @type: ($msgStreams, $subnetId, $subnetId, $message) => $msgStreams;
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

Is_Running(subnet_id, c) ==
    /\ c \in DOMAIN subnet[subnet_id].canister
    /\ subnet[subnet_id].canister[c].state = RUNNING

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
        \* TODO: should we have a guard that prevents the sending subnet from
        \* sending if it's halted? Can this have undesired consequences, as subnets
        \* are distributed in practice? I.e., could a "halted" subnet might
        /\ ~Subnet_Thinks_Its_Stopped(subnet_id)
        /\ Assert(Sender_Ok(subnet_id, sending_subnet_id, msg), 
            \* TODO: get reasonable error messages with TLC while keeping Apalache happy
            "Sender wasn't OK")
            \* "For subnet " \o subnet_id \o ", subnet " \o sending_subnet_id \o " wasn't OK for sending canister " \o msg.from)
        /\ Assert(~Recipient_Hosted(subnet_id, msg) => Should_Reroute(subnet_id, msg),
            \* TODO: get reasonable error messages with TLC while keeping Apalache happy
            "Recipient not hosted, but not re-routing the message")
            \* "Recipient " \o msg.to \o " not hosted on " \o subnet_id \o " and message shouldn't be re-routed")
        /\ CASE Recipient_Hosted(subnet_id, msg) /\ ~(Is_Request(msg) /\ ~Is_Running(subnet_id, msg.to)) ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Ack(new_i))
                    /\ subnet' = Increment_Incoming(Queue_Message(subnet, subnet_id, msg), subnet_id, sending_subnet_id)
                    /\ UNCHANGED << stream, registry, next_req_id, migration_procedure, migration_count, rescheduling_count >>
             [] \/ Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) /\ ~Is_Running(subnet_id, msg.to)
                \/ ~Recipient_Hosted(subnet_id, msg) /\ Is_Request(msg) ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Ack(new_i))
                    \* Send a reject response; we don't differentiate between "regular" and reject responses in the model
                    /\ stream' = Extend_Stream(
                              stream, 
                              subnet_id, 
                              sending_subnet_id, 
                              Response(msg.to, msg.from, msg.id))
                    /\ subnet' = Increment_Incoming(subnet, subnet_id, sending_subnet_id)
                    /\ UNCHANGED << registry, next_req_id, migration_procedure, migration_count, rescheduling_count >>
            [] ~Recipient_Hosted(subnet_id, msg) /\ Is_Response(msg)  ->
                    /\ Add_Header(subnet_id, sending_subnet_id, Rej(new_i))
                    /\ subnet' = Increment_Incoming(subnet, subnet_id, sending_subnet_id)
                    /\ UNCHANGED << stream, registry, next_req_id, migration_procedure, migration_count, rescheduling_count >>
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

\* "Spontaneous" event: try to induct a signal from a remote header stream
\* In reality, we may induct several signals simultaneously. In the model, we
\* always induct them one-by-one; this shouldn't have an effect on our properties.
Induct_Signal(subnet_id, sending_subnet_id) ==
    /\ Unconsumed_Signals_Exist(sending_subnet_id, subnet_id) 
    /\ LET
        sig == Next_Signal(sending_subnet_id, subnet_id)
        msg == stream[<< subnet_id, sending_subnet_id >>][sig.index]
        recipient_current_subnet == Hosting_Subnet(registry[subnet[subnet_id].registry_version].routing_table, msg.to)
       IN
        CASE Is_Ack(sig) -> 
            /\ headers' = Consume_One(headers, subnet_id, sending_subnet_id)
            /\ subnet' = Increment_Outgoing(subnet, subnet_id, sending_subnet_id)
            /\ UNCHANGED << stream, registry, next_req_id, migration_procedure, migration_count, rescheduling_count >>
          [] Is_Rej(sig) /\ Is_Response(msg) ->
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
            /\ stream' = Extend_Stream(stream, subnet_id, recipient_current_subnet, msg)
            /\ UNCHANGED << registry, next_req_id, migration_procedure, migration_count >>
          [] Is_Rej(sig) /\ Is_Request(msg) ->
            /\ Assert(FALSE, "Got a reject signal for a request")
          [] OTHER -> Assert(FALSE, "The previous cases should be exhaustive")

\* @type: ($subnetId -> $subnetState, $subnetId, $canisterId, Int => Int) => $subnetId -> $subnetState;
Update_Pending(s, subnet_id, canister_id, upd_f(_)) ==
    [ s EXCEPT ![subnet_id] = 
        [ @ EXCEPT !.canister = [ @ EXCEPT ![canister_id] = [ @ EXCEPT !.pending = upd_f(@) ]]]
    ]

\* "Spontaneous" event: a canister sends a request to a different canister.
Send_Request(sending_subnet_id, receiving_subnet_id, from, to) ==
  LET
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
    /\ UNCHANGED << registry, headers, migration_procedure, migration_count, rescheduling_count >>

\* Map a function over a sequence
\* @type: (Seq(a), a => b) => Seq(b);
Map_Seq(s, f(_)) == MkSeq(Len(s), LAMBDA i: f(s[i]))

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

\* As we never remove messages from the queues in our model, use the following operator to
\* access the "live" (i.e., unprocessed) queue messages.
\* @type: Seq({message: $message, processed: Bool}) => Set($message);
Live_Queue_Messages(q) == { live.message : live \in { m \in To_Set(q): m.processed = FALSE } }

\* @type: {message: $message, processed: Bool} => $message;
Get_Message(queue_msg) == queue_msg.message

\* All the messages ever received in a queue (in the order they were received in)
\* @type: Seq({message: $message, processed: Bool}) => Seq($message);
Queue_History(q) == Map_Seq(q, Get_Message)

\* "Spontaneous" event: a canister responds to a request in its input queue.
\* TODO: here, we can send a response any time for any message in the queue, ignoring the order.
\* This somewhat mimics the fact that responses don't have to be issued in the same order that
\* the requests came in.
\* However, in reality, a request 1 might trigger an outgoing request 2, and only upon
\* the completion of request 2 does the canister send the response to request 1.
\* So any fairness assumptions on this may be too strong. Not sure if this is problematic.
Send_Response(sending_subnet_id, receiving_subnet_id, from, to) ==
  LET
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
        /\ UNCHANGED << registry, headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

\* "Spontaneous" event: a canister processes a response from its queue.
\* TODO: we allow responses to be processed in any order, i.e., we disregard the order imposed by the queue.
Process_Response(subnet_id, c) ==
  LET
    s == subnet[subnet_id]
  IN
    /\ c \in DOMAIN s.canister
    /\ \E msg \in Live_Queue_Messages(s.canister[c].queue):
        /\ Is_Response(msg)
        /\ subnet' = Update_Pending(Remove_Message(subnet, subnet_id, c, msg), subnet_id, c, LAMBDA p: p - 1)
        /\ UNCHANGED << registry, stream, headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

\* "Operator" event: start migrating multiple canisters between subnets
Start_Migrating_Canisters(cs, from_subnet_id, to_subnet_id) == 
    /\ migration_count < MAX_MIGRATIONS
    /\ \A migration_set \in DOMAIN migration_procedure: migration_set \intersect cs = {}
    \* Sanity checks on the migration procedure
    /\ Assert(
        subnet[to_subnet_id] = Empty_Subnet_State({}),
        "The new migration subnet doesn't have empty state"
      )
    /\ Assert(Current_Subnet_Info[to_subnet_id].is_halted, "The new migration subnet isn't halted")
    \* Disabled to cover the case of non-empty canister range on the subnet startup
    \* /\ Assert(
    \*     \A s \in SUBNET_ID: 
    \*         stream[<<s, to_subnet_id>>] = <<>> /\ stream[<<to_subnet_id, s>>] = <<>>,
    \*     "There are messages in some stream from/to the new migration subnet"
    \*   )
    /\ Assert(
        \A s \in SUBNET_ID: 
            headers[<<s, to_subnet_id>>] = <<>> /\ headers[<<to_subnet_id, s>>] = <<>>,
        "There are signals in some header stream from/to the new migration subnet"
      )
    /\ Assert(
        \A c \in cs: Hosted(Current_Table, c, from_subnet_id),
        "Some canisters marked for migration are not hosted on the parent subnet"
      )
    /\ Assert(from_subnet_id # to_subnet_id, "Tried to migrate from/to the same subnet")
    /\ Assert(cs # {}, "Tried to migrate an empty set of canisters")
    /\ registry' = Append(registry, 
        [ routing_table |-> [ c \in cs |-> [on |-> Current_Table[c].on, migration_list |-> Current_Table[c].migration_list \o << from_subnet_id, to_subnet_id >> ] ]
            @@ Current_Table,
        subnet_info |-> Current_Subnet_Info
        ])
    /\ migration_procedure' = cs :> MIG_STARTED(Len(registry')) @@ migration_procedure
    /\ UNCHANGED << subnet, headers, stream, next_req_id, migration_count, rescheduling_count >>

\* @type: ($migrationProcedure, Set($canisterId), $migrationState) => $migrationProcedure;
Set_Migration_State(mig_proc, cs, state) ==
    [ mig_proc EXCEPT ![cs] = state ]

\* @type: ($subnets, Set($canisterId), $subnetId, $subnetId) => $subnets;
Move_State(s, canister_ids, from_subnet_id, to_subnet_id) ==
  IF from_subnet_id = to_subnet_id THEN s
  ELSE
    LET
      from_canisters == s[from_subnet_id].canister
    IN
      [ s EXCEPT ![to_subnet_id] = [ @ EXCEPT !.canister =
          [ canister_id \in canister_ids \intersect DOMAIN from_canisters
              |-> from_canisters[canister_id] ] @@ @
      ], ![from_subnet_id] = [ @ EXCEPT !.canister = Remove_Arguments(from_canisters, canister_ids)] ]

Streams_Are_Empty(subnet_id) == \A s2 \in SUBNET_ID: 
    /\ stream[<<subnet_id, s2>>] = <<>>
    /\ stream[<<s2, subnet_id>>] = <<>>


\* "Operator event": this event models several steps of the migration procedure at once: stopping the parent subnet,
\* fetching CUPs, changing the registry (adding the CUP and the routing table), and starting the
\* parent/child subnets
\* We look at a simplified version of subnet splitting, where only one canister is moved from
\* its old subnet to a new subnet.
Split_Subnet(canister_ids) ==
  /\ canister_ids \in DOMAIN migration_procedure
  /\ Is_Mig_Started(migration_procedure[canister_ids])
  /\
    LET
        start_version == Get_Start_Version(migration_procedure[canister_ids])
        cr == registry[start_version]
        rt == cr.routing_table
        parent_subnet_id == Migration_List(rt, CHOOSE c \in canister_ids: TRUE)[1]
        child_subnet_id == Migration_List(rt, CHOOSE c \in canister_ids: TRUE)[2]
    IN
        \* All subnets have observed the registry version where the migration started
        /\ \A s \in SUBNET_ID: subnet[s].registry_version >= start_version
        \* To ensure that our model resembles subnet splitting, the child subnet 
        /\ registry' = Append(registry, [
            subnet_info |-> Current_Subnet_Info,
            routing_table |-> 
                [canister_id \in canister_ids |-> [ 
                    on |-> child_subnet_id, 
                    migration_list |-> Current_Table[canister_id].migration_list 
                    ]
                ] @@ Current_Table
            ])
        \* We atomically copy the canister to the child subnet and apply the registry update
        \* to both parent and child subnets
        /\ subnet' = Apply_Registry_Update(
                registry', 
                Len(registry'), 
                Apply_Registry_Update(
                    registry', 
                    Len(registry'), 
                    Move_State(subnet, canister_ids, parent_subnet_id, child_subnet_id),
                    parent_subnet_id),
                child_subnet_id
           )
        /\ migration_procedure' =
                Set_Migration_State(migration_procedure, canister_ids, 
                    MIG_SWITCHED([ 
                        switch_version |-> Len(registry'), 
                        stream_index_for_unhalting |-> Has_Outgoing([ s2 \in SUBNET_ID |-> Len(stream[<<parent_subnet_id, s2>>])]),
                        stream_index_for_migration_list |-> To_Parent([ s2 \in {} |-> 0 ])
                    ])) 
        /\ UNCHANGED << headers, stream, next_req_id, migration_count, rescheduling_count >>


Record_Incoming_Indices_With_New_Registry(canister_ids, parent_subnet_id, subnet_id) ==
    /\ canister_ids \in DOMAIN migration_procedure
    /\ Watching_Indices_To_Parent(migration_procedure[canister_ids])
    /\
      LET
        switch_version == Get_Switched_Version(migration_procedure[canister_ids])
        stream_index_to_parent == Get_Switched_Indices_To_Parent(migration_procedure[canister_ids])
      IN
        /\ subnet_id \notin DOMAIN stream_index_to_parent
        /\ subnet[subnet_id].registry_version >= switch_version
        /\ migration_procedure' = Set_Migration_State(migration_procedure, canister_ids, 
            Set_Switched_Index_To_Parent(migration_procedure[canister_ids], subnet_id, Len(stream[<<subnet_id, parent_subnet_id>>]))
           )
    /\ UNCHANGED << registry, headers, stream, subnet, next_req_id, migration_count, rescheduling_count >>

Record_Outgoing_Indices(canister_ids, parent_subnet_id) ==
    /\ canister_ids \in DOMAIN migration_procedure
    /\ Watching_Indices_To_Parent(migration_procedure[canister_ids])
    /\
      LET
        switch_version == Get_Switched_Version(migration_procedure[canister_ids])
        stream_index_to_parent == Get_Switched_Indices_To_Parent(migration_procedure[canister_ids])
        outgoing_indices == [ sn2 \in SUBNET_ID |-> Len(stream[<< parent_subnet_id, sn2 >>])]
      IN
        /\ DOMAIN stream_index_to_parent = SUBNET_ID
        /\ Assert(subnet[parent_subnet_id].registry_version >= switch_version, "Parent's registry not reflecting the split")
        /\ migration_procedure' = Set_Migration_State(migration_procedure, canister_ids, 
            Set_Migration_List_Index(migration_procedure[canister_ids], From_Parent(outgoing_indices))
           )
    /\ UNCHANGED << registry, headers, stream, subnet, next_req_id, migration_count, rescheduling_count >>

\* "Live" (not garbage collected) part of the stream between two subnets
Live_Stream(from, to) ==
    LET
        s == stream[<<from, to>>]
        i == subnet[from].outgoing_index[to]
    IN
        SubSeq(s, i + 1, Len(s))

\* @type: ($registries, $subnetId) => $registries;
Unhalt_Subnet_In_Registry(reg, subnet_id) == Append(reg, 
    [ Last(reg) EXCEPT !.subnet_info = subnet_id :> [ is_halted |-> FALSE] @@ @])

Unhalt_Subnet(old_subnet_id, new_subnet_id, cs) ==
    /\ cs \in DOMAIN migration_procedure
    /\ Is_Mig_Switched(migration_procedure[cs])
    /\ ~Done_Unhalting(migration_procedure[cs])
    \* Sanity check
    \* /\ Assert(\A c \in cs: 
    \*     Hosted(registry[migration_procedure[cs].registry_version].routing_table, c, old_subnet_id),
    \*     "Something went wrong with the migration procedure; the moved canisters are not on the parent subnet according to the migration procedure records"
    \*   )
    \* Sanity check
    /\ Assert(\A c \in cs: c \notin DOMAIN subnet[old_subnet_id].canister, "Trying to unhalt migration, but old state still hanging on to the canister state")
    /\
      LET 
        index_from_parent == Get_Unhalting_Indices(migration_procedure[cs])
      IN
        /\ \A to \in SUBNET_ID \ {new_subnet_id}:
            /\ to \in DOMAIN index_from_parent
            /\ subnet[old_subnet_id].outgoing_index[to] >= index_from_parent[to]
    /\ migration_procedure' = Set_Migration_State(migration_procedure, cs, 
            Set_Unhalting_Index(migration_procedure[cs], Unhalting_Done))
    /\ registry' = Unhalt_Subnet_In_Registry(registry, new_subnet_id)
    /\ UNCHANGED << headers, stream, next_req_id, migration_count, rescheduling_count, subnet >>

Remove_From_Migration_List(old_subnet_id, new_subnet_id, cs) ==
    /\ cs \in DOMAIN migration_procedure
    /\ ~Done_Observing_Streams(migration_procedure[cs])
    /\ Watching_Indices_From_Parent(migration_procedure[cs])
    /\ 
      LET
        indices == Get_Switched_Indices_From_Parent(migration_procedure[cs])
      IN
        /\ DOMAIN indices = SUBNET_ID
        /\ \A sn2 \in SUBNET_ID: subnet[old_subnet_id].outgoing_index[sn2] >= indices[sn2]
    /\ migration_procedure' = Set_Migration_State(migration_procedure, cs, Set_Migration_List_Index(migration_procedure[cs], Removed_From_List))
    /\ registry' = Append(registry, 
        [
            routing_table |-> [ c \in cs |-> [ on |-> Current_Table[c].on, migration_list |-> << >> ] ]
                            @@ Current_Table,
            subnet_info |->  Current_Subnet_Info

        ]
       )
    /\ UNCHANGED << stream, subnet, next_req_id, headers, rescheduling_count >>


\* "Operator" event: start migrating a canister
Finish_Migration(old_subnet_id, new_subnet_id, cs) ==
    /\ cs \in DOMAIN migration_procedure
    /\ Is_Mig_Switched(migration_procedure[cs])
    /\ Done_Unhalting(migration_procedure[cs])
    /\ Done_Observing_Streams(migration_procedure[cs])
    /\ migration_procedure' = Remove_Argument(migration_procedure, cs)
    /\ migration_count' = migration_count + 1
    /\ UNCHANGED << stream, subnet, next_req_id, headers, rescheduling_count, registry >>

\* All "operator" events
Migration_Procedure(from_subnet_id, to_subnet_id, cs) ==
    \/ Start_Migrating_Canisters(cs, from_subnet_id, to_subnet_id)
    \/ Split_Subnet(cs)
    \/ \E subnet_id \in SUBNET_ID: Record_Incoming_Indices_With_New_Registry(cs, from_subnet_id, subnet_id)
    \/ Record_Outgoing_Indices(cs, from_subnet_id)
    \/ Remove_From_Migration_List(from_subnet_id, to_subnet_id, cs)
    \/ Unhalt_Subnet(from_subnet_id, to_subnet_id, cs)
    \/ Finish_Migration(from_subnet_id, to_subnet_id, cs)

Init ==
    /\ stream = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ registry = << [ routing_table |-> INIT_ROUTING_TABLE, subnet_info |-> INIT_SUBNET_INFO ] >>
    /\ headers = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ subnet = [s \in SUBNET_ID |-> Empty_Subnet_State(All_Hosted(INIT_ROUTING_TABLE, s) \intersect INITIAL_EXISTING) ]
    /\ migration_procedure = SetAsFun({})
    /\ next_req_id = 1
    /\ migration_count = 0
    /\ rescheduling_count = [ s \in SUBNET_ID |-> 0 ]

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
    \/ Start_Canister(c1, s1)
    \/ Create_Canister(c1, s1)
    \/ \E cs \in DOMAIN(CANISTERS_TO_MIGRATE): 
        Migration_Procedure(CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to, cs)
    \/ Idle
    \* \/ Update_Routing_Table

\*************************************************
\* Properties
Inv_Requests_Capped ==
    next_req_id <= MAX_REQUESTS + 1

Inv_Registry_Length_Capped ==
    Len(registry) <= 5 * MAX_MIGRATIONS

Inv_Queues_Correct == \A c \in CANISTER_ID, s \in SUBNET_ID:
    c \in DOMAIN subnet[s].canister =>
        \A msg \in To_Set(subnet[s].canister[c].queue): msg.message.to = c


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
\* Again, as our queues keep the entire history for received messages, this
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
Response_Fairness_Condition == 
    /\ \A s \in SUBNET_ID: WF_vars(Update_Local_Registry(s))
    /\ \A s1, s2 \in SUBNET_ID:
        /\ WF_vars(Induct_Message(s1, s2))
    /\ \A s1, s2 \in SUBNET_ID: \A c1, c2 \in CANISTER_ID:
        /\ WF_vars(Send_Response(s1, s2, c1, c2))
    /\ \A cs \in DOMAIN CANISTERS_TO_MIGRATE:
        \* /\ \E subnet_id \in SUBNET_ID: Record_Incoming_Indices_With_New_Registry(cs, from_subnet_id, subnet_id)
        \* /\ Record_Outgoing_Indices(cs, from_subnet_id)
        /\ WF_vars(Start_Migrating_Canisters(cs, CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to))
        /\ WF_vars(Split_Subnet(cs))
        /\ WF_vars(Unhalt_Subnet(CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to, cs))
        /\ \A s2 \in SUBNET_ID: 
            \* Need to induct signals to the parent, such that we can unhalt
            \* the child subnet
            /\ WF_vars(Induct_Signal(CANISTERS_TO_MIGRATE[cs].from, s2))
            \* Need to induct signals from the parent, such that we can reschedule
            \* the responses on REJ signals
            /\ WF_vars(Induct_Signal(s2, CANISTERS_TO_MIGRATE[cs].from))
        (* /\ WF_vars(Migration_Procedure(
                CANISTERS_TO_MIGRATE[cs].from,
                CANISTERS_TO_MIGRATE[cs].to,
                cs 
            ))
        *)
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