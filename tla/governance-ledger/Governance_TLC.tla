---- MODULE Governance_TLC ----
EXTENDS Governance

Symmetry_Sets == { Claim_Neuron_Process_Ids, 
    Refresh_Neuron_Process_Ids, 
    Disburse_Neuron_Process_Ids, 
    Spawn_Neuron_Process_Ids,
    Disburse_To_Neuron_Process_Ids,
    Split_Neuron_Process_Ids,
    Governance_Account_Ids,
    Change_Neuron_Fee_Process_Ids,
    Increase_Neuron_Maturity_Process_Ids,
    User_Account_Ids
}
symmetry_permutations == UNION { Permutations(S) : S \in Symmetry_Sets }

====