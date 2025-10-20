---- MODULE Common ----
EXTENDS Apalache, Sequences, SequencesExt, Variants

\* @typeAlias: canisterId = Str;
\* @typeAlias: subnetId = Str;
\* @typeAlias: message = { type: Str, from: $canisterId, to: $canisterId, id: Int };
\* @typeAlias: signal = { type: Str, index: Int };
\* @typeAlias: canisterRunState = C_Running(UNIT) | C_Stopping(UNIT);
\* @typeAlias: subnetInfo = { is_halted: Bool };
_dummy_alias_constant == TRUE

\******************************************************
\* Named constants to help with readability/consistency
\* of the model
RUNNING == Variant("C_Running", UNIT)
STOPPING == Variant("C_Stopping", UNIT)

\******************************************************
\* General utility definitions
\* \* @type: (a -> b) => Set(b);
\* Range(f) == { f[x] : x \in DOMAIN f }
\* @type: Seq(a) => Set(a);
\* To_Set(seq) == ApaFoldSeqLeft(LAMBDA x, y: {y} \union x, {}, seq)
To_Set(X) == ToSet(X)

\* @type: ((a -> b), Set(a)) => a -> b;
Remove_Arguments(f, S) == [ y \in DOMAIN f \ S |-> f[y] ]
Remove_Argument(f, x) == Remove_Arguments(f, {x})
\* Last(seq) == seq[Len(seq)]

\* @type: ((a -> b), Set(a))

\* Map a function over a sequence
\* @type: (Seq(a), a => b) => Seq(b);
Map_Seq(s, f(_)) == MkSeq(Len(s), LAMBDA i: f(s[i]))

VARIABLES
    \* Directional inter-subnet streams
    \* @typeAlias: msgStreams = << $subnetId, $subnetId >> -> Seq($message);
    \* @type: $msgStreams;
    stream,
    \* A list of registries, one for each successive registry version
    \* @typeAlias: routingTable = $canisterId -> {on: $subnetId, migration_list: Seq($subnetId) };
    \* @typeAlias: registries = Seq({
    \*      routing_table: $routingTable,
    \*      subnet_info: $subnetId -> $subnetInfo,
    \* });
    \* @type: $registries;
    registry,
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
    subnet 

CONSTANT 
    \* @type: Seq($subnetId);
    SUBNET_ID_LIST,
    \* @type: Seq($canisterId);
    CANISTER_ID_LIST

SUBNET_ID == To_Set(SUBNET_ID_LIST)

CANISTER_ID == To_Set(CANISTER_ID_LIST)

Response(from, to, id) == [type |-> "RESP", from |-> from, to |-> to, id |-> id]
Request(from, to, id) == [type |-> "REQ", from |-> from, to |-> to, id |-> id]

\* @type: $message => Bool;
Is_Request(msg) == msg.type = "REQ"
\* @type: $message => Bool;
Is_Response(msg) == msg.type = "RESP"

Subnet_Thinks_Its_Stopped(subnet_id) ==
    \/ subnet_id \notin DOMAIN subnet
    \/ subnet_id \notin DOMAIN registry[subnet[subnet_id].registry_version].subnet_info
    \/ registry[subnet[subnet_id].registry_version].subnet_info[subnet_id].is_halted

Is_Running(subnet_id, c) ==
    /\ c \in DOMAIN subnet[subnet_id].canister
    /\ subnet[subnet_id].canister[c].state = RUNNING

\* @type: ($msgStreams, $subnetId, $subnetId, $message) => $msgStreams;
Extend_Stream(s, sending_subnet_id, receiving_subnet_id, msg) ==
    [ s EXCEPT 
        ![<< sending_subnet_id, receiving_subnet_id >>] = 
            Append(@, msg)
    ]

\* @type: ($routingTable, $canisterId) => $subnetId;
Hosting_Subnet(routing, canister_id) ==
    routing[canister_id].on

Hosted(routing, canister_id, subnet_id) ==
    Hosting_Subnet(routing, canister_id) = subnet_id

All_Hosted(routing, subnet_id) == { c \in CANISTER_ID: Hosted(routing, c, subnet_id) }

Current_Table == Last(registry).routing_table
Current_Subnet_Info == Last(registry).subnet_info

\* @type: ($routingTable, $canisterId) => Seq($subnetId);
Migration_List(routing, canister_id) ==
    routing[canister_id].migration_list


====