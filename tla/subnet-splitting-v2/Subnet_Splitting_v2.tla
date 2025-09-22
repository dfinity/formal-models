A model of message routing for subnet splitting v2.


TODO: adapt the description for v2.
The model encodes the following rules for message routing and the migration procedure.

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

---- MODULE Subnet_Splitting_v2 ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Apalache, Variants, SequencesExt, Common


\******************************************************
\* Constants that define the bounds on the model.
\* If you want to perform model checking with more subnets,
\* canisters, more requests or migrations, this is the place.

\* The following differ for each scenario, so they are instantiated later
CONSTANT
    \* Specifies where canisters are located. Differs for each s
    \* @type: $canisterId -> { on: $subnetId, migration_list: Seq($subnetId)};
    INIT_ROUTING_TABLE,
    \* @type: Set($canisterId);
    \* Which canisters exist initially. Canisters from CANISTER_ID_LIST may still exist in
    \* the routing table, without actually having state on their "hosting" subnet. This models
    \* the canister ranges in the routing table, which may (and normally do) contain canisters
    \* which do not exist.
    INITIAL_EXISTING,
    \* @type: Set($subnetId);
    INITIALLY_EXISTING_SUBNETS,
    \* @type: Set($canisterId) -> { from: $subnetId, to: $subnetId };
    CANISTERS_TO_MIGRATE

\* @type: $subnetId -> $subnetInfo;
INIT_SUBNET_INFO ==
  LET
    s == SUBNET_ID_LIST
  IN
    s[1] :> [ is_halted |-> FALSE ]
    @@
    s[2] :> [ is_halted |-> FALSE ]


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

\* \* @typeAlias: migrationListRemovalPhase = To_Parent($subnetId -> Int) | From_Parent($subnetId -> Int) | Removed_From_List(UNIT);
\* \* @type: $migrationListRemovalPhase;
\* Removed_From_List == Variant("Removed_From_List", UNIT)
\* \* @type: ($subnetId -> Int) => $migrationListRemovalPhase;
\* To_Parent(indices) == Variant("To_Parent", indices)
\* \* @type: ($subnetId -> Int) => $migrationListRemovalPhase;
\* From_Parent(indices) == Variant("From_Parent", indices)
\* \* @typeAlias: unhaltingPhase = Has_Outgoing($subnetId -> Int) | Unhalting_Done(UNIT);
\* \* @type: $unhaltingPhase;
\* Unhalting_Done == Variant("Unhalting_Done", UNIT)
\* \* @type: ($subnetId -> Int) => $unhaltingPhase;
\* Has_Outgoing(indices) == Variant("Has_Outgoing", indices)
\* @typeAlias: migrationState = 
\* SubnetSplitEnacted(Int)
\* | SubnetSplitDone;
\* @type: Int => $migrationState;
MIG_SUBNET_SPLIT_ENACTED(registry_version) == Variant("SubnetSplitEnacted", registry_version)
\* \* @type: $migrationState => Bool;
Is_Mig_Enacted(mig_state) == VariantTag(mig_state) = "SubnetSplitEnacted"

\* \* @type: Int => $migrationState;
\* MIG_STARTED(registry_version) == Variant("Mig_Started", registry_version)
\* \* @type: $migrationState => Bool;
\* Is_Mig_Started(mig_state) == VariantTag(mig_state) = "Mig_Started"
\* \* @type: $migrationState => Int;
\* Get_Start_Version(state) == VariantGetUnsafe("Mig_Started", state)
\* \* @type: $migrationState => Bool;
\* Is_Mig_Switched(mig_state) == VariantTag(mig_state) = "Mig_Switched"
\* \* @type: ({ switch_version: Int, stream_index_for_unhalting: $unhaltingPhase, stream_index_for_migration_list: $migrationListRemovalPhase}) => $migrationState;
\* MIG_SWITCHED(data) == Variant("Mig_Switched", data)
\* \* @type: $migrationState => Int;
\* Get_Switched_Version(migration_state) == VariantGetUnsafe("Mig_Switched", migration_state).switch_version
\* \* @type: $migrationState => Bool;
\* Watching_Indices_To_Parent(migration_state) ==
\*     /\ Is_Mig_Switched(migration_state) 
\*     /\ 
\*       LET s == VariantGetUnsafe("Mig_Switched", migration_state)
\*       IN
\*         /\ VariantTag(s.stream_index_for_migration_list)  = "To_Parent"
\* \* @type: $migrationState => $subnetId -> Int;
\* Get_Switched_Indices_To_Parent(migration_state) == VariantGetUnsafe("To_Parent", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list)
\* \* @type: $migrationState => Bool;
\* Watching_Indices_From_Parent(migration_state) ==
\*     /\ Is_Mig_Switched(migration_state) 
\*     /\ 
\*       LET s == VariantGetUnsafe("Mig_Switched", migration_state)
\*       IN
\*         /\ VariantTag(s.stream_index_for_migration_list) = "From_Parent"
\* \* @type: ($migrationState, $migrationListRemovalPhase) => $migrationState;
\* Set_Migration_List_Index(migration_state, index) == 
\*   LET
\*     current == VariantGetUnsafe("Mig_Switched", migration_state)
\*   IN
\*     MIG_SWITCHED([ current EXCEPT !.stream_index_for_migration_list = index ])
\* \* @type: ($migrationState, $subnetId, Int) => $migrationState;
\* Set_Switched_Index_To_Parent(migration_state, subnet_id, index) ==
\*     Set_Migration_List_Index(migration_state, To_Parent(subnet_id :> index @@ Get_Switched_Indices_To_Parent(migration_state)))
\* 
\* \* @type: $migrationState => Bool;
\* Done_Observing_Streams(migration_state) ==
\*     /\ Is_Mig_Switched(migration_state)
\*     /\ VariantTag(VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list) # "Removed_From_List"
\* \* @type: ($migrationState, $unhaltingPhase) => $migrationState;
\* Set_Unhalting_Index(migration_state, index) == 
\*   LET
\*     current == VariantGetUnsafe("Mig_Switched", migration_state)
\*   IN
\*     MIG_SWITCHED([ current EXCEPT !.stream_index_for_unhalting = index ])
\* \* @type: $migrationState => Bool;
\* Done_Unhalting(migration_state) ==
\*     /\ Is_Mig_Switched(migration_state)
\*     /\ VariantTag(VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_unhalting) = "Unhalting_Done"
\* \* @type: $migrationState => ($subnetId -> Int);
\* Get_Unhalting_Indices(migration_state) ==
\*     VariantGetUnsafe("Has_Outgoing", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_unhalting)
\* 
\* \* @type: $migrationState => $subnetId -> Int;
\* Get_Switched_Indices_From_Parent(migration_state) == VariantGetUnsafe("From_Parent", VariantGetUnsafe("Mig_Switched", migration_state).stream_index_for_migration_list)

\* Global state:
VARIABLE 
    \* A directional inter-subnet stream of headers; headers are processed
    \* in the order they are emitted, so a stream works fine here.
    \* @typeAlias: hdrStreams = << $subnetId, $subnetId >> -> Seq($signal);
    \* @type: $hdrStreams;
    headers,
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

Induction == INSTANCE Message_Induction
Execution == INSTANCE Canister_Execution
RegistryOps == INSTANCE Registry_Operations

Empty_Subnet_State(canisters) == [
    incoming_index |-> [ s2 \in SUBNET_ID |-> 0 ],
    outgoing_index |-> [ s2 \in SUBNET_ID |-> 0 ],
    registry_version |-> 1,
    canister |-> [c \in canisters |-> 
        [ state |-> RUNNING, queue |-> << >>, pending |-> 0]  
    ]
  ]

\* Apalache doesn't like string concatenation
\* String_Of_Elements(S) == ApaFoldSet(LAMBDA x, y: y \o ", " \o x, "", S)
\* Set_To_String(S) == "{" \o String_Of_Elements(S) \o "}"

\* @type: ($migrationProcedure, Set($canisterId), $migrationState) => $migrationProcedure;
Set_Migration_State(mig_proc, cs, state) ==
    cs :> state @@ mig_proc

\* "Operator event": this event models the "enact split" NNS proposal.
\* We model a simplified version of subnet splitting, where only one canister is moved from
\* its old subnet to a new subnet.
Enact_Split_Subnet(cs, from_subnet_id, to_subnet_id) == 
    /\ migration_count < MAX_MIGRATIONS
    /\ \A migration_set \in DOMAIN migration_procedure: migration_set \intersect cs = {}
    \* Sanity checks on the migration procedure
    /\ Assert(
        to_subnet_id \notin DOMAIN subnet,
        "The new migration subnet doesn't have empty state"
      )
    /\ Assert(
        \A s \in SUBNET_ID: 
            headers[<<s, to_subnet_id>>] = <<>> /\ headers[<< to_subnet_id, s >>] = <<>>,
        "There are signals in some header stream from/to the new migration subnet"
      )
    /\ Assert(
        \A s \in SUBNET_ID: 
            stream[<<s, to_subnet_id>>] = <<>> /\ stream[<< to_subnet_id, s >>] = <<>>,
        "There are messages in some stream from/to the new migration subnet"
      )
    /\ \A c \in cs:
        Assert(
            Hosted(Current_Table, c, from_subnet_id),
            "Some canisters marked for migration are not hosted on the parent subnet " \o from_subnet_id \o " and canister " \o c \o "; hosting subnet is " \o Hosting_Subnet(Current_Table, c)
        )
    /\ Assert(from_subnet_id # to_subnet_id, "Tried to migrate from/to the same subnet")
    /\ Assert(cs # {}, "Tried to migrate an empty set of canisters")
    /\ Assert(
        \A c \in DOMAIN Current_Table: Current_Table[c].on # to_subnet_id,
        "Some canisters are already on the child subnet"
        )
    /\ migration_procedure' = Set_Migration_State(migration_procedure, cs, MIG_SUBNET_SPLIT_ENACTED(Len(registry) + 1))
    /\ registry' = Append(registry, 
        [ routing_table |-> [ c \in cs |-> [on |-> to_subnet_id, migration_list |-> Current_Table[c].migration_list \o << from_subnet_id, to_subnet_id >> ] ]
            @@ Current_Table,
        subnet_info |-> 
            to_subnet_id :> [ is_halted |-> FALSE ]
            @@ Current_Subnet_Info
        ])
    /\ UNCHANGED << subnet, headers, stream, next_req_id, migration_count, rescheduling_count >>

(*
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

\* @type: ($subnets, Set($canisterId), $subnetId, $subnetId) => $subnets;
Move_State(s, canister_ids, from_subnet_id, to_subnet_id, new_registry_version) ==
  IF from_subnet_id = to_subnet_id THEN s
  ELSE
    LET
      from_canisters == s[from_subnet_id].canister
    IN
      [ s EXCEPT ![from_subnet_id] = [ @ EXCEPT !.canister = Remove_Arguments(from_canisters, canister_ids)] ]
      @@ to_subnet_id :> [ Empty_Subnet_State EXCEPT 
        !.canister =
          [ canister_id \in canister_ids \intersect DOMAIN from_canisters
              |-> from_canisters[canister_id] ],
        !.registry_version = new_registry_version
      ] 
*)

(*
\* "Operator event": this event models the "enact split" NNS proposal.
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
        /\ subnet' = RegistryOps!Apply_Registry_Update(
                registry', 
                Len(registry'), 
                RegistryOps!Apply_Registry_Update(
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
*)

\* "Live" (not garbage collected) part of the stream between two subnets
Live_Stream(from, to) ==
    LET
        s == stream[<<from, to>>]
        i == subnet[from].outgoing_index[to]
    IN
        SubSeq(s, i + 1, Len(s))

(*
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
    /\ migration_procedure' = Set_Migration_State(migration_procedure, cs, Set_Migration_List_Index(migration_procedure[cs], Removed_From_List))
    /\ registry' = Append(registry, 
        [
            routing_table |-> [ c \in cs |-> [ on |-> Current_Table[c].on, migration_list |-> << >> ] ]
                            @@ Current_Table,
            subnet_info |->  Current_Subnet_Info

        ]
       )
    /\ UNCHANGED << stream, subnet, next_req_id, headers, rescheduling_count >>
*)



\* "Operator" event: start migrating a canister
Finish_Migration(old_subnet_id, new_subnet_id, cs) ==
    /\ cs \in DOMAIN migration_procedure
    /\ Is_Mig_Enacted(migration_procedure[cs])
    /\ LET
        split_reg_version == VariantGetUnsafe("SubnetSplitEnacted", migration_procedure[cs])
       IN \A s \in DOMAIN subnet: subnet[s].registry_version >= split_reg_version
    /\ migration_procedure' = Remove_Argument(migration_procedure, cs)
    /\ migration_count' = migration_count + 1
    /\ UNCHANGED << stream, subnet, next_req_id, headers, rescheduling_count, registry >>

\* All "operator" events
Migration_Procedure(from_subnet_id, to_subnet_id, cs) ==
    \/ Enact_Split_Subnet(cs, from_subnet_id, to_subnet_id)
    (*
    \/ Start_Migrating_Canisters(cs, from_subnet_id, to_subnet_id)
    \/ Split_Subnet(cs)
    \/ \E subnet_id \in SUBNET_ID: Record_Incoming_Indices_With_New_Registry(cs, from_subnet_id, subnet_id)
    \/ Record_Outgoing_Indices(cs, from_subnet_id)
    \/ Remove_From_Migration_List(from_subnet_id, to_subnet_id, cs)
    \/ Unhalt_Subnet(from_subnet_id, to_subnet_id, cs)
    \/ Remove_From_Migration_List(from_subnet_id, to_subnet_id, cs)
    *)
    \/ Finish_Migration(from_subnet_id, to_subnet_id, cs)

Init ==
    /\ stream = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ registry = << [ routing_table |-> INIT_ROUTING_TABLE, subnet_info |-> INIT_SUBNET_INFO ] >>
    /\ headers = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ subnet = [s \in INITIALLY_EXISTING_SUBNETS |-> Empty_Subnet_State(All_Hosted(INIT_ROUTING_TABLE, s) \intersect INITIAL_EXISTING) ]
    /\ migration_procedure = SetAsFun({})
    /\ next_req_id = 1
    /\ migration_count = 0
    /\ rescheduling_count = [ s \in SUBNET_ID |-> 0 ]

\* An additional event to explicitly idle when we are done with migration,
\* so that we can turn on deadlock warnings.
Idle == 
    /\ migration_count = MAX_MIGRATIONS
    /\ UNCHANGED vars

non_execution_vars == << headers, migration_procedure, migration_count, rescheduling_count >>
non_induction_vars == << next_req_id, migration_count, migration_procedure >>
non_registry_vars == << headers, next_req_id, migration_procedure, migration_count, rescheduling_count >>

Next == \E s1, s2 \in SUBNET_ID: \E c1, c2 \in CANISTER_ID:
    \/ Execution!Send_Request(s1, s2, c1, c2) /\ UNCHANGED non_execution_vars
    \/ Execution!Send_Response(s1, s2, c1, c2) /\ UNCHANGED non_execution_vars
    \/ Execution!Process_Response(s1, c1) /\ UNCHANGED non_execution_vars
    \/ Execution!Start_Canister(c1, s1) /\ UNCHANGED non_execution_vars
    \/ Execution!Create_Canister(c1, s1) /\ UNCHANGED non_execution_vars
    \/ Induction!Induct_Message(s1, s2) /\ UNCHANGED non_induction_vars    
    \/ Induction!Induct_Signal(s1, s2) /\ UNCHANGED non_induction_vars    
    \/ RegistryOps!Update_Local_Registry(s1) /\ UNCHANGED non_registry_vars
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

Inv_Queues_Correct == \A c \in CANISTER_ID, s \in DOMAIN subnet:
    c \in DOMAIN subnet[s].canister =>
        \A msg \in To_Set(subnet[s].canister[c].queue): msg.message.to = c


\* @type: {message: $message, processed: Bool} => $message;
Get_Message(queue_msg) == queue_msg.message

\* All the messages ever received in a queue (in the order they were received in)
\* @type: Seq({message: $message, processed: Bool}) => Seq($message);
Queue_History(q) == Map_Seq(q, Get_Message)

\* The natural specification of the in-order delivery requirement isn't an invariant,
\* but a temporal property: after we induct a C1->C2 message with id i into a queue, we never induct
\* another  C1 -> C2 message with an id j <= i (the <= instead of < also ensures at-most-once delivery).
\* We convert this into an invariant by keeping the entire history of the queue in the model
\* state, and never removing messages from the queue, but just marking them as processed (see
\* Remove_Message).
Inv_In_Order == \A s \in DOMAIN subnet: \A c \in DOMAIN subnet[s].canister:
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
Inv_At_Most_One_Response == \A s \in DOMAIN subnet: \A c \in DOMAIN subnet[s].canister:
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
    /\ \A s \in SUBNET_ID: WF_vars(RegistryOps!Update_Local_Registry(s))
    /\ \A s1, s2 \in SUBNET_ID:
        /\ WF_vars(Induction!Induct_Message(s1, s2))
    /\ \A s1, s2 \in SUBNET_ID: \A c1, c2 \in CANISTER_ID:
        /\ WF_vars(Execution!Send_Response(s1, s2, c1, c2))
    /\ \A cs \in DOMAIN CANISTERS_TO_MIGRATE:
        \* /\ \E subnet_id \in SUBNET_ID: Record_Incoming_Indices_With_New_Registry(cs, from_subnet_id, subnet_id)
        \* /\ Record_Outgoing_Indices(cs, from_subnet_id)
        \* /\ WF_vars(Start_Migrating_Canisters(cs, CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to))
        /\ WF_vars(Enact_Split_Subnet(cs, CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to))
        \* /\ WF_vars(Unhalt_Subnet(CANISTERS_TO_MIGRATE[cs].from, CANISTERS_TO_MIGRATE[cs].to, cs))
        /\ \A s2 \in SUBNET_ID: 
            \* Need to induct signals to the parent, such that we can unhalt
            \* the child subnet
            /\ WF_vars(Induction!Induct_Signal(CANISTERS_TO_MIGRATE[cs].from, s2))
            \* Need to induct signals from the parent, such that we can reschedule
            \* the responses on REJ signals
            /\ WF_vars(Induction!Induct_Signal(s2, CANISTERS_TO_MIGRATE[cs].from))
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
