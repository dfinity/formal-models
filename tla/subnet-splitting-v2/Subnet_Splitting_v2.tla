A model of message routing for subnet splitting v2.


****************
Subnet splitting
****************

Formalized in the Splitting_Procedure action. Assuming we're splitting subnet A to create a new child subnet B, the procedure is as follows:

1. In a single proposal, the registry is changed to create B, move the desired canisters from A to B in the routing table, and add a migration list entry for each moved canister, containing A and B (in that order).
2. Wait for all subnets to observe this registry change. In particular, when A observes the change, it halts and produces two final CUPs, one for each A and B; both A and B delete the canisters that no longer belong to them and restart.
3. Flushing the streams from/to the parent A; record the end of each stream from and to A, and wait for all these messages to be inducted (both from and to A), in any order. The model does this by observing the outgoing indices, though we could observe the incoming indices too.
4. Flush the stream from A to B again (record the end of the stream from A to B, and wait for all these messages to be inducted).
5. Clear the migration list entries in the registry (through another proposal).

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
\* canisters, more requests or splits, this is the place.

\* The following differ for each scenario, so they are instantiated later
CONSTANT
    \* Specifies where canisters are located. Differs for each scenario
    \* @type: $canisterId -> { on: $subnetId, migration_list: Seq($subnetId)};
    INIT_ROUTING_TABLE,
    \* @type: Set($canisterId);
    \* Which canisters exist initially. Canisters from CANISTER_ID_LIST may still exist in
    \* the routing table, without actually having state on their "hosting" subnet. This models
    \* the canister ranges in the routing table, which may (and normally do) contain canisters
    \* which do not exist.
    INITIAL_EXISTING,
    \* As we create the child subnet with a proposal, we also model the adding of subnets. Here,
    \* you can control which subnets exist from the beginning.
    \* @type: Set($subnetId);
    INITIALLY_EXISTING_SUBNETS,
    \* The description of a subnet split.
    \* @type: Set($canisterId) -> { from: $subnetId, to: $subnetId };
    CANISTERS_TO_SPLIT_OFF

\* Unlike subnet splitting v1, we don't halt subnets in this model any more. 
\* So we just assume that all initally existing subnets are unhalted.
\* @type: $subnetId -> $subnetInfo;
INIT_SUBNET_INFO ==
  [ s \in INITIALLY_EXISTING_SUBNETS |-> [ is_halted |-> FALSE ] ]


\* Requests can be issued at any time. Since we assign an increasing
\* ordinal number to every request (in order to distinguish multiple
\* requests between the same pairs of canisters), this could yield an
\* unbounded search space. We limit the total number of requests with
\* this constant.
MAX_REQUESTS == 3
\* The model assumes a single subnet split; i.e., we don't model concurrent
\* splits. We don't intend to support concurrent splits in production, and 
\* modeling them would also blow up the model checking search space massively. 
\* This constant is a remnant of a more ambitious original attempt with multiple
\* concurrent splits. Concurrent splits could start at any time (provided that the target
\* canisters aren't already undergoing a split). While this doesn't yield
\* an unbounded state space, we may still end up investigating a lot
\* of "uninteresting" states. For invariants, we could probably get rid 
\* of this with a symmetry-style equivalence relation on states, but
\* for liveness this is tricky. So the idea was to limit the total number
\* of splits.
\* We kept this constant since we'll use it to allow the system to idle when
\* we reach MAX_SPLITS, without considering this to be a deadlock.
MAX_SPLITS == 1

MAX_RESCHEDULINGS == 1

\* @typeAlias: splitState = 
\* SubnetSplitEnacted(Int)
\* | SubnetSplitFlushingParentToAndFromAll($subnetId -> Int, $subnetId -> Int)
\* | SubnetSplitFlushingToChild(Int);
\* @type: Int => $splitState;
SPLIT_SUBNET_ENACTED(registry_version) == Variant("SubnetSplitEnacted", registry_version)
\* \* @type: $splitState => Bool;
Is_Split_Enacted(split_state) == VariantTag(split_state) = "SubnetSplitEnacted"
\* \* @type: (Int, Int) => $splitState;
SPLIT_SUBNET_FLUSHING_PARENT_TO_AND_FROM_ALL(outgoing_indices, incoming_indices) == Variant("SubnetSplitFlushingParentToAndFromAll", << outgoing_indices, incoming_indices >>)
\* \* @type: $splitState => Bool;
Is_Split_Flushing_Parent_To_And_From_All(split_state) == VariantTag(split_state) = "SubnetSplitFlushingParentToAndFromAll"

\* \* @type: Int => $splitState;
SPLIT_SUBNET_FLUSHING_TO_CHILD(index) == Variant("SubnetSplitFlushingToChild", index)
\* \* @type: $splitState => Bool;
Is_Split_Flushing_To_Child(split_state) == VariantTag(split_state) = "SubnetSplitFlushingToChild"

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
    \* The state of the splitting procedure (i.e., of the human operator). Maps the set of Canister IDs being split to the appropriate step of their splitting.
    \* @typeAlias: splitProcedure = Set($canisterId) -> $splitState;
    \* @type: $splitProcedure;
    splitting_procedure,
    \* Count how many subnet splits we've done so far. Originally meant to limit
    \* the total number of splits in the state space, now used for the idling action,
    \* to allow deadlock checking by simply idling once we have completed the split.
    \* @type: Int;
    split_count,
    \* Count how many times a response has been rescheduled due to a reject signal.
    \* Constant rescheduling (without updating the routing table in the meantime) could 
    \* yield an unbounded state space; we use this count to bound the space.
    \* @type: $subnetId -> Int;
    rescheduling_count

vars == << stream, registry, headers, subnet, next_req_id, splitting_procedure, split_count, rescheduling_count >>

Induction == INSTANCE Message_Induction
Execution == INSTANCE Canister_Execution
RegistryOps == INSTANCE Registry_Operations
registry_ops_vars == << stream, registry, subnet >>
induction_vars == << stream, registry, subnet, headers, rescheduling_count >>
execution_vars == << stream, registry, subnet, next_req_id >>

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

\* @type: ($splitProcedure, Set($canisterId), $splitState) => $splitProcedure;
Set_Split_State(split_proc, cs, state) ==
    cs :> state @@ split_proc

\* "Operator event": this event models the "enact split" NNS proposal.
\* We model a simplified version of subnet splitting, where only one canister is moved from
\* its old subnet to a new subnet.
Enact_Split_Subnet(cs, from_subnet_id, to_subnet_id) == 
    /\ split_count < MAX_SPLITS
    /\ \A canisters_being_split \in DOMAIN splitting_procedure: canisters_being_split \intersect cs = {}
    \* Sanity checks on the split procedure
    /\ Assert(
        to_subnet_id \notin DOMAIN subnet,
        "The child subnet already has some state"
      )
    /\ Assert(
        \A s \in SUBNET_ID: 
            headers[<<s, to_subnet_id>>] = <<>> /\ headers[<< to_subnet_id, s >>] = <<>>,
        "There are already signals in some header stream from/to the newly created child subnet"
      )
    /\ Assert(
        \A s \in SUBNET_ID: 
            stream[<<s, to_subnet_id>>] = <<>> /\ stream[<< to_subnet_id, s >>] = <<>>,
        "There are messages in some stream from/to the new child subnet"
      )
    /\ \A c \in cs:
        Assert(
            Hosted(Current_Table, c, from_subnet_id),
            "Some canisters marked for splitting are not hosted on the parent subnet " \o from_subnet_id \o " and canister " \o c \o "; hosting subnet is " \o Hosting_Subnet(Current_Table, c)
        )
    /\ Assert(from_subnet_id # to_subnet_id, "Tried to split from/to the same subnet")
    /\ Assert(cs # {}, "Tried to split an empty set of canisters")
    /\ Assert(
        \A c \in DOMAIN Current_Table: Current_Table[c].on # to_subnet_id,
        "Some canisters are already on the child subnet"
        )
    /\ splitting_procedure' = Set_Split_State(splitting_procedure, cs, SPLIT_SUBNET_ENACTED(Len(registry) + 1))
    /\ registry' = Append(registry, 
        [ routing_table |-> [ c \in cs |-> [on |-> to_subnet_id, migration_list |-> Current_Table[c].migration_list \o << from_subnet_id, to_subnet_id >> ] ]
            @@ Current_Table,
        subnet_info |-> 
            to_subnet_id :> [ is_halted |-> FALSE ]
            @@ Current_Subnet_Info
        ])
    /\ UNCHANGED << subnet, headers, stream, next_req_id, split_count, rescheduling_count >>

\* "Operator" event: start flushing the streams from/to the parent
Start_Flush_Parent_To_And_From_All(cs, parent_subnet_id) ==
    /\ cs \in DOMAIN splitting_procedure
    /\ Is_Split_Enacted(splitting_procedure[cs])
    /\ LET
        split_reg_version == VariantGetUnsafe("SubnetSplitEnacted", splitting_procedure[cs])
        outgoing_indices == [ sn2 \in SUBNET_ID |-> Len(stream[<< parent_subnet_id, sn2 >>])]
        incoming_indices == [ sn2 \in SUBNET_ID |-> Len(stream[<< sn2, parent_subnet_id >>])]
      IN
        /\ \A s \in DOMAIN subnet: subnet[s].registry_version >= split_reg_version
        /\ splitting_procedure' = Set_Split_State(splitting_procedure, cs, 
            SPLIT_SUBNET_FLUSHING_PARENT_TO_AND_FROM_ALL(outgoing_indices, incoming_indices)
           )
    /\ UNCHANGED << registry, headers, stream, subnet, next_req_id, split_count, rescheduling_count >>

\* "Operator" event: start flushing the stream from the parent to the child
Start_Flush_To_Child(cs, parent_subnet_id, child_subnet_id) ==
    /\ cs \in DOMAIN splitting_procedure
    /\ Is_Split_Flushing_Parent_To_And_From_All(splitting_procedure[cs])
    /\ LET
        old_indices == VariantGetUnsafe("SubnetSplitFlushingParentToAndFromAll", splitting_procedure[cs])
        old_outgoing_indices == old_indices[1]
        old_incoming_indices == old_indices[2]
        new_outgoing_index == Len(stream[<< parent_subnet_id, child_subnet_id >>])
      IN
        /\ \A to \in DOMAIN old_outgoing_indices: subnet[parent_subnet_id].outgoing_index[to] >= old_outgoing_indices[to]
        /\ \A to \in DOMAIN old_incoming_indices: subnet[to].outgoing_index[parent_subnet_id] >= old_incoming_indices[to]
        /\ splitting_procedure' = Set_Split_State(splitting_procedure, cs, 
           SPLIT_SUBNET_FLUSHING_TO_CHILD(new_outgoing_index)
           )
    /\ UNCHANGED << registry, headers, stream, subnet, next_req_id, split_count, rescheduling_count >>


\* "Operator" event: finish the split
Finish_Split(old_subnet_id, new_subnet_id, cs) ==
    /\ cs \in DOMAIN splitting_procedure
    /\ Is_Split_Flushing_To_Child(splitting_procedure[cs])
    /\ LET
        index == VariantGetUnsafe("SubnetSplitFlushingToChild", splitting_procedure[cs])
      IN
        /\ subnet[old_subnet_id].outgoing_index[new_subnet_id] >= index
    /\ splitting_procedure' = Remove_Argument(splitting_procedure, cs)
    /\ split_count' = split_count + 1
    /\ registry' = Append(registry, 
        [
            routing_table |-> [ c \in cs |-> [ on |-> Current_Table[c].on, migration_list |-> << >> ] ]
                            @@ Current_Table,
            subnet_info |->  Current_Subnet_Info
        ]
       )
    /\ UNCHANGED << stream, subnet, next_req_id, headers, rescheduling_count >>

\* All "operator" events
Splitting_Procedure(from_subnet_id, to_subnet_id, cs) ==
    \/ Enact_Split_Subnet(cs, from_subnet_id, to_subnet_id)
    \/ Start_Flush_Parent_To_And_From_All(cs, from_subnet_id)
    \/ Start_Flush_To_Child(cs, from_subnet_id, to_subnet_id)
    \/ Finish_Split(from_subnet_id, to_subnet_id, cs)

Init ==
    /\ stream = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ registry = << [ routing_table |-> INIT_ROUTING_TABLE, subnet_info |-> INIT_SUBNET_INFO ] >>
    /\ headers = [ p \in SUBNET_ID \X SUBNET_ID |-> <<>> ]
    /\ subnet = [s \in INITIALLY_EXISTING_SUBNETS |-> Empty_Subnet_State(All_Hosted(INIT_ROUTING_TABLE, s) \intersect INITIAL_EXISTING) ]
    /\ splitting_procedure = SetAsFun({})
    /\ next_req_id = 1
    /\ split_count = 0
    /\ rescheduling_count = [ s \in SUBNET_ID |-> 0 ]

\* An additional event to explicitly idle when we are done with splitting,
\* so that we can turn on deadlock warnings.
Idle == 
    /\ split_count = MAX_SPLITS
    /\ UNCHANGED vars

non_execution_vars == << headers, splitting_procedure, split_count, rescheduling_count >>
non_induction_vars == << next_req_id, split_count, splitting_procedure >>
non_registry_vars == << headers, next_req_id, splitting_procedure, split_count, rescheduling_count >>

Next == \E s1, s2 \in SUBNET_ID: \E c1, c2 \in CANISTER_ID:
    \/ Execution!Send_Request(s1, s2, c1, c2) /\ UNCHANGED non_execution_vars
    \/ Execution!Send_Response(s1, s2, c1, c2) /\ UNCHANGED non_execution_vars
    \/ Execution!Process_Response(s1, c1) /\ UNCHANGED non_execution_vars
    \/ Execution!Start_Canister(c1, s1) /\ UNCHANGED non_execution_vars
    \/ Execution!Create_Canister(c1, s1) /\ UNCHANGED non_execution_vars
    \/ Induction!Induct_Message(s1, s2) /\ UNCHANGED non_induction_vars    
    \/ Induction!Induct_Signal(s1, s2) /\ UNCHANGED non_induction_vars    
    \/ RegistryOps!Update_Local_Registry(s1) /\ UNCHANGED non_registry_vars
    \/ \E cs \in DOMAIN(CANISTERS_TO_SPLIT_OFF): 
        Splitting_Procedure(CANISTERS_TO_SPLIT_OFF[cs].from, CANISTERS_TO_SPLIT_OFF[cs].to, cs)
    \/ Idle

\*************************************************
\* Sanity checks
\*************************************************\

\* Properties we don't expect to hold, but if they do, something is very wrong

Sanity_No_Responses_Exist == \A s \in DOMAIN subnet: \A c \in DOMAIN subnet[s].canister:
    \A msg \in To_Set(subnet[s].canister[c].queue): ~Is_Response(msg)

Sanity_Split_Never_Finishes ==
    [][DOMAIN splitting_procedure \subseteq DOMAIN splitting_procedure']_vars

Sanity_No_Canister_Ever_Moves ==
    [][\A s \in DOMAIN subnet: \A c \in DOMAIN subnet[s].canister:
        ~(\E s2 \in DOMAIN subnet' \ {s}: c \in DOMAIN subnet'[s2].canister)]_vars

Sanity_Migration_List_Never_Cleared ==
    [][\A c \in DOMAIN Current_Table: 
        Current_Table[c].migration_list # <<>>
         => Current_Table'[c].migration_list # <<>>
    ]_vars

\*************************************************
\* Properties
\*************************************************
Inv_Requests_Capped ==
    next_req_id <= MAX_REQUESTS + 1

Inv_Registry_Length_Capped ==
    Len(registry) <= 5 * MAX_SPLITS

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
\* Canister_Execution!Remove_Message).
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
    /\ \A s \in SUBNET_ID: WF_registry_ops_vars(RegistryOps!Update_Local_Registry(s))
    /\ \A s1, s2 \in SUBNET_ID:
        /\ WF_induction_vars(Induction!Induct_Message(s1, s2))
    /\ \A s1, s2 \in SUBNET_ID: \A c1, c2 \in CANISTER_ID:
        /\ WF_execution_vars(Execution!Send_Response(s1, s2, c1, c2))
    /\ \A s1, s2 \in SUBNET_ID:
        /\ WF_induction_vars(Induction!Induct_Signal(s1, s2))
    /\ \A cs \in DOMAIN CANISTERS_TO_SPLIT_OFF:
        /\ WF_vars(Enact_Split_Subnet(cs, CANISTERS_TO_SPLIT_OFF[cs].from, CANISTERS_TO_SPLIT_OFF[cs].to))

Spec == Init /\ []([Next]_vars) /\ Response_Fairness_Condition

\* "Live" (not garbage collected) part of the stream between two subnets
Live_Stream(from, to) ==
    LET
        s == stream[<<from, to>>]
        i == subnet[from].outgoing_index[to]
    IN
        SubSeq(s, i + 1, Len(s))

\* The guaranteed response property uses the "leads to" operator: A ~> B means
\* that whenever A happens, B must also happen at that time or later
Guaranteed_Response == \A from, to \in CANISTER_ID: \A i \in 1..MAX_REQUESTS:
      (\E s1, s2 \in DOMAIN subnet: 
        Request(from, to, i) \in To_Set(Live_Stream(s1, s2))) 
    ~>
      (\E s \in DOMAIN subnet: 
                /\ from \in DOMAIN subnet[s].canister
                /\ Response(to, from, i) \in To_Set(Queue_History(subnet[s].canister[from].queue)))

====
