---- MODULE Scenario2 ----

EXTENDS TLC

SUBNET_ID_LIST == << "s1", "s2", "s3" >>
INITIALLY_EXISTING_SUBNETS == { "s1", "s2" }
CANISTER_ID_LIST == << "c1", "c2" >>

INIT_ROUTING_TABLE == 
  LET 
    s == SUBNET_ID_LIST
    c == CANISTER_ID_LIST
  IN
    c[1] :> [ on |-> s[1], migration_list |-> << >> ] 
    @@
    plit

INITIAL_EXISTING == 
  LET 
    s == SUBNET_ID_LIST
    c == CANISTER_ID_LIST
  IN
    {c[1], c[2]}

CANISTERS_TO_SPLIT_OFF == 
  LET 
    s == SUBNET_ID_LIST
    c == CANISTER_ID_LIST
  IN
    {c[1]} :> [ from |-> s[1], to |-> s[3]]

VARIABLE 
    stream,
    registry,
    headers,
    subnet, 
    next_req_id,
    migration_procedure,
    migration_count,
    rescheduling_count

INSTANCE Subnet_Splitting_v2


====