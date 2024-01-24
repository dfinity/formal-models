---- MODULE Governance_Apalache ----

(*
@typeAlias: PROC = Str;
@typeAlias: ACCOUNT = Str;
@typeAlias: REQ = Str;
@typeAlias: RESP = Str;
*)

Claim_Neuron_Process_Ids == {"P_claim_neuron_1", "P_claim_neuron_2"}
Refresh_Neuron_Process_Ids == {"P_refresh_neuron_1"}
Disburse_Neuron_Process_Ids == {"P_disburse_neuron_1", "P_disburse_neuron_2"}
Spawn_Neuron_Process_Ids == {"P_spawn_neuron_1", "P_spawn_neuron_2"}
Disburse_To_Neuron_Process_Ids == {"P_disburse_to_neuron_1", "P_disburse_to_neuron_2"}
Ledger_Process_Id == "P_ledger_process"
Change_Neuron_Fee_Process_Ids == {"P_change_neuron_fee_1"}
Increase_Neuron_Maturity_Process_Ids == {"P_increase_neuron_maturity_1"}
Merge_Maturity_Of_Neuron_Process_Ids == {"P_merge_maturity_of_neuron_process_1"}
Merge_Neurons_Process_Ids == {"P_merge_neurons_process_1"}
Split_Neuron_Process_Ids == {"P_split_neuron_1"}

Account_Ids == {"A_User_1", "A_Gov_1"}
Governance_Account_Ids == {"A_Gov_1"}
Minting_Account_Id == "A_Minting"

MIN_STAKE == 2
TRANSACTION_FEE == 2
INITIAL_MAX_BALANCE == 2
NUMBER_OF_TRANSFERS_CAP == 2
MAX_NEURON_FEE == 2
MAX_MATURITY == 2

OP_QUERY_BALANCE == "OP_QUERY_BALANCE"
OP_TRANSFER == "OP_TRANSFER"
TRANSFER_OK == "TRANSFER_OK"
TRANSFER_FAIL == "TRANSFER_FAIL"

VARIABLES
    \* @type: Int -> [cached_stake: Int, account : ACCOUNT, maturity: Int, fees: Int];
    neuron,
    \* @type: ACCOUNT -> Int;
    neuron_id_by_account,
    \* @type: Set(Int);
    locks,
    \* @type: Int;
    neuron_count, 
    \* @type: Int;
    total_rewards,
    \* @type: Int;
    minted,
    \* @type: Int;
    burned,
    \* @type: Seq([caller : PROC, type: REQ, args: [from: ACCOUNT, to: ACCOUNT, amount: Int, fee: Int, of_account: ACCOUNT ]]);
    governance_to_ledger,
    \* @type: Set([caller: PROC, response_value: [status: RESP, bal: Int]]);
    ledger_to_governance,
    \* @type: PROC -> Str;
    pc,
    \* @type: PROC -> ACCOUNT;
    account_id_,
    \* @type: PROC -> Int;
    neuron_id_,
    \* @type: PROC -> ACCOUNT;
    account_id,
    \* @type: PROC -> Int;
    neuron_id_R,
    \* @type: PROC -> Int;
    neuron_id_D,
    \* @type: PROC -> Int;
    amount_,
    \* @type: PROC -> ACCOUNT;
    to_account,
    \* @type: PROC -> Int;
    rewards_amount,
    \* @type: PROC -> Int;
    fees_amount,
    \* @type: PROC -> Bool;
    error,
    \* @type: PROC -> Int;
    parent_neuron_id_,
    \* @type: PROC -> Int;
    child_neuron_id_,
    \* @type: PROC -> Int;
    child_stake,
    \* @type: PROC -> ACCOUNT;
    child_account_id_,
    \* @type: PROC -> Int;
    parent_neuron_id_D,
    \* @type: PROC -> Int;
    disburse_amount,
    \* @type: PROC -> ACCOUNT;
    child_account_id_D,
    \* @type: PROC -> Int;
    child_neuron_id_D,
    \* @type: PROC -> Int;
    neuron_id,
    \* @type: PROC -> Int;
    maturity_to_merge,
    \* @type: PROC -> Int;
    parent_neuron_id,
    \* @type: PROC -> Int;
    amount,
    \* @type: PROC -> Int;
    child_neuron_id,
    \* @type: PROC -> ACCOUNT;
    child_account_id,
    \* @type: PROC -> Int;
    source_neuron_id,
    \* @type: PROC -> Int;
    target_neuron_id,
    \* @type: PROC -> Int;
    target_balance,
    \* @type: ACCOUNT -> Int;
    balances,
    \* @type: Int;
    nr_transfers

INSTANCE Governance
====
