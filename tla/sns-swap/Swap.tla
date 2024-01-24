A model of the SNS swap canister and its interactions with the ICP and SNS ledgers.

The model introduces several main simplifications in comparison with the code:

  - Ledger transaction fees are not modelled (i.e., they are assumed to be 0). This allows for a much
    simpler specification of the desired properties.

  - Scaling of SNS tokens is not implemented, to avoid having to deal with fractions.

  - Time is not modelled.

  - The special code paths for the community fund are not modelled.

  - Many constraints around state transitions are ignored (e.g., the minimum number of participants,
    or the minimum amount of ICP invested). Consequently, no such requirements are specified either.

The model has two different main properties analyzed:
1. correctness of commits, in that the correct amounts eventually appear on the ICP and SNS ledgers
2. correctness of refunds, in that the users don't lose money

The second property has slightly stronger assumptions; it requires the users to keep calling the refund
operation until it succeeds. As we don't want to introduce this assumption for the first property, we
also create two slightly different system specifications.

As of commit d13ea103f3fb978e77c73e21253115b3cac1b7a7, TLC verifies both properties on a model with two 
users, two concurrent calls to finalize, and only one concurrent call to everything else. The results are:

Checking 2 branches of temporal properties for the complete state space with 782838 total distinct states at (2022-10-05 11:23:36)
Finished checking temporal properties in 25s at 2022-10-05 11:24:02
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 5.7E-8
  based on the actual fingerprints:  val = 1.1E-8
3079750 states generated, 391419 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 44.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 7 and the 95th percentile is 3).
Finished in 01min 54s at (2022-10-05 11:24:09)

See ../README.md on how to run the analysis.
Useful cheat sheets:
https://github.com/tlaplus/PlusCalCheatSheet
https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html

---- MODULE Swap ----
EXTENDS TLC, Integers, Functions, FiniteSetsExt, Sequences, SequencesExt

CONSTANT 
    \* These parameters are specific to the model, and define the size of the model
    \* (i.e., total number of users analyzed)
    USERS,
    MAX_REFUND_AMOUNT,
    INITIAL_PER_USER_BALANCE,

    \* These parameters are defined by the implementation, but are not used by the
    \* model
    \* MIN_PARTICIPANTS,
    \* MIN_ICP_E8S,
    \* MAX_ICP_E8S,
    \* MIN_PARTICIPANT_ICP_E8S,
    \* MAX_PARTICIPANT_ICP_E8S,
    \* \* SWAP_DUE_TIMESTAMP_SECONDS,
    \* SNS_TOKEN_E8S,

    \* These are just some constants specifying the different stages of the process.
    OPEN,
    ABORTED,
    COMMITTED,

    \* Constants for the two special non-user principals.
    SWAP_PRINCIPAL,
    GOVERNANCE_PRINCIPAL,

    \* Process IDs for PlusCal processes with multiple instances; the cardinality of the sets
    \* determines the number of instances of each process. In practice, as we model each process
    \* as an infinite loop, this limits the number of parallel calls allowed to the corresponding 
    \* canister method). 
    \* For example, with two instances of Finalize and one instance of the other two, we allow two 
    \* parallel calls to finalize, but only one parallel call to refund or refresh token.
    PIDS_REFRESH_BUYER_TOKEN,
    PIDS_FINALIZE,
    PIDS_REFUND_ICP,

    \* Process ID constants for other single-instance processes.
    PID_ICP_USER_TRANSFER,
    PID_ICP_LEDGER_ERROR,
    PID_ICP_LEDGER,
    PID_SNS_LEDGER,
    PID_SNS_LEDGER_ERROR,
    PID_COMMIT,
    PID_ABORT

ASSUME 
    /\ SWAP_PRINCIPAL \notin USERS
    /\ GOVERNANCE_PRINCIPAL \notin USERS
    /\ SWAP_PRINCIPAL # GOVERNANCE_PRINCIPAL

\* Auxiliary definitions for manipulating inter-canister messages. In our model, each process
\* sends at most one message at a time, and blocks on the result, so we can effectively use the 
\* process IDs as call context IDs.
Error_Response(pid) == [ caller |-> pid, status |-> "Err" ]
Ok_Response(pid, result) == [ caller |-> pid, status |-> "Ok", result |-> result ]
Is_Error(response) == response.status = "Err"
Is_Ok(response) == response.status = "Ok"

Ask_Balance_Msg(pid, account) == [ caller |-> pid, type |-> "acc_bal", account |-> account]
Is_Ask_Balance_Msg(msg) == msg.type = "acc_bal"
Caller(msg) == msg.caller
Transfer_Msg(pid, from, to, amount) == [ caller |-> pid, type |-> "xfer", from |-> from, to |-> to, amount |-> amount]
Is_Transfer_Msg(msg) == msg.type = "xfer"

Escrow_Address(user) == << SWAP_PRINCIPAL, user >>

\* We'll initialize the balance of all relevant addresses to 0, so we can model transfers as just
\* function updates (as the values already exist).
Transfer(ledger, from, to, amount) == [ ledger EXCEPT ![from] = @ - amount, ![to] = @ + amount]

(* --algorithm Swap {

variables
    \* Relevant state of the swap canister
    lifecycle = OPEN;
    buyers = [ x \in {} |-> {} ];
    neuron_recipes = <<>>;
    \* Relevant state of the ICP ledger
    icp_balances = 
        [ x \in USERS |-> INITIAL_PER_USER_BALANCE] 
        @@ [ x \in { Escrow_Address(u) : u \in USERS } |-> 0 ]
        @@ GOVERNANCE_PRINCIPAL :> 0;
    \* Relevant state of the SNS ledger
    sns_balances = [ x \in USERS |-> 0 ];
    \* Buffers for in-flight inter-canister calls 
    \* (corresponding to the input/output canister queues and cross-net streams).
    \* Request buffers use sequences (ordered structures), response buffers use sets (unordered).
    \* This reflects IC's ordering guarantees on requests and responses.
    swap_to_icp_ledger = <<>>;
    icp_ledger_to_swap = {};
    swap_to_sns_ledger = <<>>;
    sns_ledger_to_swap = {};

macro send_to_icp_ledger(msg) {
    swap_to_icp_ledger := Append(swap_to_icp_ledger, msg)
}

macro icp_respond_to_swap(response) {
    icp_ledger_to_swap := icp_ledger_to_swap \union { response };
}

macro send_to_sns_ledger(msg) {
    swap_to_sns_ledger := Append(swap_to_sns_ledger, msg)
}

macro sns_respond_to_swap(response) {
    sns_ledger_to_swap := sns_ledger_to_swap \union { response };
}

\* We describe the ledger behavior using several processes:
\* 1. one that spontaneously transfers users accounts into the escrow account
\* 2. one that just gives out spontaneous errors, and 
\* 3. one that actually handles requests by the swap canister.
\* This split allows us to require fairness on processing swap canister requests.
\* Moreover, refund properties only hold if the users eventually stop transferring money to the
\* escrow accounts; the split also allows us to easily constrain such behavior.
process (ICP_User_Transfer = PID_ICP_USER_TRANSFER) {
ICP_User_Transfer_Loop:
    while(TRUE){
        with(user \in USERS; amount \in 0..icp_balances[user]) {
            icp_balances := Transfer(icp_balances, user, Escrow_Address(user), amount);
        }
    }
}

\* We allow the requests to the ICP ledger to fail spontaneously
process (ICP_Ledger_Error = PID_ICP_LEDGER_ERROR) {
ICP_Ledger_Error_Loop:
    while(TRUE) {
        await(swap_to_icp_ledger # <<>>);
        with(req = Head(swap_to_icp_ledger)) {
            swap_to_icp_ledger := Tail(swap_to_icp_ledger);
            icp_respond_to_swap(Error_Response(Caller(req)));
        }
    }
}

process (ICP_Ledger = PID_ICP_LEDGER) {
ICP_Ledger_Loop:
    while(TRUE){
        await(swap_to_icp_ledger # <<>>);
        with(req = Head(swap_to_icp_ledger)) {
            swap_to_icp_ledger := Tail(swap_to_icp_ledger);
            either {
                await(Is_Transfer_Msg(req));
                if(req.amount > icp_balances[req.from]) {
                    icp_respond_to_swap(Error_Response(Caller(req)));
                } else {
                    icp_balances := Transfer(icp_balances, req.from, req.to, req.amount);
                    icp_respond_to_swap(Ok_Response(Caller(req), {}));
                }
            } or {
                await(Is_Ask_Balance_Msg(req));
                icp_respond_to_swap(Ok_Response(Caller(req), icp_balances[req.account]));
            }        
        }
    }
}

\* Like with the ICP ledger, we split up the SNS ledger model into two processes:
\* 1. one that actually processes the requests
\* 2. one that fails all requests spontaneously
process (SNS_Ledger = PID_SNS_LEDGER) {
SNS_Ledger_Loop:
    while(TRUE){
        await(swap_to_sns_ledger # <<>>);
        with(req = Head(swap_to_sns_ledger)) {
            swap_to_sns_ledger := Tail(swap_to_sns_ledger);
            await(Is_Transfer_Msg(req));
            assert(req.from = defaultInitValue);
            sns_balances := [ sns_balances EXCEPT ![req.to] = @ + req.amount ];
            sns_respond_to_swap(Ok_Response(Caller(req), {}));
        }
    }

}

process (SNS_Ledger_Error = PID_SNS_LEDGER_ERROR) {
SNS_Ledger_Error_Loop:
    while(TRUE) {
        await(swap_to_sns_ledger # <<>>);
        with(req = Head(swap_to_sns_ledger)) {
            swap_to_sns_ledger := Tail(swap_to_sns_ledger);
            sns_respond_to_swap(Error_Response(Caller(req)));
        }
    }
}

\* Model of the commit call. In this model, we ignore the constraints around:
\* 1. sufficient participation
\* 2. swap due or target reached
\* However, this should be a safe overapproximation of the behavior of the actual system.
process (Commit = PID_COMMIT) {
Commit:
    await lifecycle = OPEN;
    \* We don't do any scaling here for the recipes, so that we don't have to deal with fractions in the model.
    \* Also, we use the same data structure for the recipes as for the buyers - map, instead of a vector 
    \* like in the implementation. 
    \* A map makes it more convenient to model (in TLA) the mutable aliasing that's effectively done by 
    \* the sns_sweep implementation later on.
    neuron_recipes := buyers;    
    lifecycle := COMMITTED;
}

\* Model of the abort call. In the model, we have no constraints on when this call
\* be called. This should be a safe overapproximation of the behavior of the actual system.
process (Abort = PID_ABORT) {
Abort:
    await lifecycle = OPEN;
    lifecycle := ABORTED;
}

\* Model of the refresh_buyer_token method. We model the method as a process as an infinite loop, with 
\* each iteration corresponding to a single call to the method. 
\* The call arguments are chosen at the start of the loop. 
\* This model allows infinitely many method calls to be considered in the model. 
\* The cardinality of the PIDS_REFRESH_BUYER_TOKEN then determines how many such calls can be
\* executed concurrently.
process (Refresh_Buyer_Token \in PIDS_REFRESH_BUYER_TOKEN) 
    variable account;
{
Refresh_Loop:
    await lifecycle = OPEN;
    \* The implementation aborts the call (without changing the state) if the ICP target is already reached. 
    \* We don't model this explicitly but this should be OK, as we get the same behavior 
    \* in the model by just not executing the corresponding TLA action.
    account := CHOOSE u \in USERS: TRUE;
    send_to_icp_ledger(Ask_Balance_Msg(self, Escrow_Address(account)));
Refresh_Await_Ledger_Answer:
    with(resp \in { r \in icp_ledger_to_swap: Caller(r) = self }) {
        icp_ledger_to_swap := icp_ledger_to_swap \ { resp };
        if(Is_Error(resp)) {
            goto Refresh_Loop;
        } else {
            with(amount = resp.result) {
                \* The implementation bails here if we have reached max_icp_e8s, or
                \* if the participant tried to send less than min_participant_ICP.
                \* Moreover, the implementation also doesn't change the state if the returned amount
                \* is not larger than the previously recorded amount for this buyer.
                \* We overapproximate these behaviors behavior by non-deterministically refusing to update
                \* the balance and going to the start of the loop (effectively ending the call).
                either {
                    goto Refresh_Loop;
                } or {
                    with(old_amount = IF account \in DOMAIN buyers THEN buyers[account].amount ELSE 0) {
                        await 
                            /\ lifecycle = OPEN
                            /\ old_amount < amount;
                        \* If adding the entire new amount would put the total amount of pledged icp over max_icp_e8s,
                        \* the implementation would only talk a part of what was received. We model this by non-deterministically
                        \* choosing a portion of the increase.
                        with(increase \in 1..(amount - old_amount)) {
                            buyers := account :> [ amount |-> old_amount + increase, 
                                transfer_started |-> FALSE, transfer_succeeded |-> FALSE ] @@ buyers;
                        };
                        goto Refresh_Loop;
                    }
                }
            }
        }
    }
}

\* Model of the finalize call. The same trick of using a loop as for refresh_buyer_token is used.
process (Finalize \in PIDS_FINALIZE) 
    variables 
        remaining_buyers = <<>>;
        next_buyer;
        remaining_investors = <<>>;
        next_investor;
{
Finalize_Swap_Loop:
    await(lifecycle = COMMITTED \/ lifecycle = ABORTED);
    \* We explicitly model the Rust iterator through the buyers map as remaining_buyers
    remaining_buyers := SetToSeq(DOMAIN buyers);
ICP_Sweep_Loop:
    while(remaining_buyers # <<>>) {
        next_buyer := Head(remaining_buyers);
        remaining_buyers := Tail(remaining_buyers);
        if(buyers[next_buyer].transfer_started) {
            goto ICP_Sweep_Loop;
        } else {
            buyers[next_buyer] := [ @ EXCEPT !.transfer_started = TRUE ];
            send_to_icp_ledger(Transfer_Msg(
                self, 
                Escrow_Address(next_buyer), 
                IF lifecycle = COMMITTED THEN GOVERNANCE_PRINCIPAL ELSE next_buyer,
                buyers[next_buyer].amount));
        };
      ICP_Sweep_Receive_Answer:
        with(resp \in { r \in icp_ledger_to_swap: Caller(r) = self}) {
            icp_ledger_to_swap := icp_ledger_to_swap \ { resp };
            if(Is_Ok(resp)) {
                buyers[next_buyer] := [ @ EXCEPT !.transfer_succeeded = TRUE];
            } else {
                buyers[next_buyer] := [ @ EXCEPT !.transfer_started = FALSE, !.transfer_succeeded = FALSE ];
            }
        }
    };
End_ICP_Sweep_Loop:
    \* Clean up the model state space a bit by setting next_buyer to the initial value.
    next_buyer := defaultInitValue;
    if(lifecycle # COMMITTED) {
        goto Finalize_Swap_Loop;
    } else {
        remaining_investors := SetToSeq(DOMAIN neuron_recipes);
    };
SNS_Sweep_Loop:
    while(remaining_investors # <<>>) {
        next_investor := Head(remaining_investors);
        remaining_investors := Tail(remaining_investors);
        if(neuron_recipes[next_investor].transfer_started) {
            goto SNS_Sweep_Loop;
        } else {
            neuron_recipes[next_investor] := [ @ EXCEPT !.transfer_started = TRUE ];
            send_to_sns_ledger(Transfer_Msg(self, defaultInitValue, next_investor, 
                neuron_recipes[next_investor].amount));
        };
      SNS_Sweep_Receive_Answer:
        with(resp \in { r \in sns_ledger_to_swap: Caller(r) = self}) {
            sns_ledger_to_swap := sns_ledger_to_swap \ { resp };
            if(Is_Ok(resp)) {
                neuron_recipes[next_investor] := [ @ EXCEPT !.transfer_succeeded = TRUE];
            } else {
                neuron_recipes[next_investor]  := [ @ EXCEPT !.transfer_started = FALSE, !.transfer_succeeded = FALSE ];
            }
        }
    };
End_SNS_Sweep_Loop:
    goto Finalize_Swap_Loop;
}

\* Model of the refund_icp call. We use the same loop approach as for swap finalization and refreshing
\* buyer tokens.
process (Refund_Icp \in PIDS_REFUND_ICP) 
\* We'd like to have the property "if a user keeps calling refund_icp, their escrow account eventually goes to 0".  
\* We'll express the precondition (user keeps calling) using a fairness constraint. To express that each user has 
\* to keep calling refund_icp with pluscal, we'll store the user who initiated the refund in the state (otherwise,
\* we could only enforce that refund is called infinitely often, but not that it's called for every user). This is
\* a bit hacky, but the best I could come up with with PlusCal.
variable refund_args; 
{
Refund_Icp_Loop:
    await(lifecycle = COMMITTED \/ lifecycle = ABORTED);
    with(
            user \in (USERS \ { u \in DOMAIN buyers: buyers[u].transfer_succeeded = FALSE });
            amount \in 1..MAX_REFUND_AMOUNT ) {
        refund_args := [ user |-> user, amount |-> amount];
        send_to_icp_ledger(Transfer_Msg(
            self,
            Escrow_Address(user),
            user,
            amount
        ));
    };
Refund_Await_Response:
    with(resp \in { r \in icp_ledger_to_swap: Caller(r) = self }) {
        icp_ledger_to_swap := icp_ledger_to_swap \ { resp };
    };
    refund_args := defaultInitValue;
    goto Refund_Icp_Loop;
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "e9864ef9" /\ chksum(tla) = "45e643e")
\* Label Commit of process Commit at line 242 col 5 changed to Commit_
\* Label Abort of process Abort at line 256 col 5 changed to Abort_
CONSTANT defaultInitValue
VARIABLES lifecycle, buyers, neuron_recipes, icp_balances, sns_balances, 
          swap_to_icp_ledger, icp_ledger_to_swap, swap_to_sns_ledger, 
          sns_ledger_to_swap, pc, account, remaining_buyers, next_buyer, 
          remaining_investors, next_investor, refund_args

vars == << lifecycle, buyers, neuron_recipes, icp_balances, sns_balances, 
           swap_to_icp_ledger, icp_ledger_to_swap, swap_to_sns_ledger, 
           sns_ledger_to_swap, pc, account, remaining_buyers, next_buyer, 
           remaining_investors, next_investor, refund_args >>

ProcSet == {PID_ICP_USER_TRANSFER} \cup {PID_ICP_LEDGER_ERROR} \cup {PID_ICP_LEDGER} \cup {PID_SNS_LEDGER} \cup {PID_SNS_LEDGER_ERROR} \cup {PID_COMMIT} \cup {PID_ABORT} \cup (PIDS_REFRESH_BUYER_TOKEN) \cup (PIDS_FINALIZE) \cup (PIDS_REFUND_ICP)

Init == (* Global variables *)
        /\ lifecycle = OPEN
        /\ buyers = [ x \in {} |-> {} ]
        /\ neuron_recipes = <<>>
        /\ icp_balances = [ x \in USERS |-> INITIAL_PER_USER_BALANCE]
                          @@ [ x \in { Escrow_Address(u) : u \in USERS } |-> 0 ]
                          @@ GOVERNANCE_PRINCIPAL :> 0
        /\ sns_balances = [ x \in USERS |-> 0 ]
        /\ swap_to_icp_ledger = <<>>
        /\ icp_ledger_to_swap = {}
        /\ swap_to_sns_ledger = <<>>
        /\ sns_ledger_to_swap = {}
        (* Process Refresh_Buyer_Token *)
        /\ account = [self \in PIDS_REFRESH_BUYER_TOKEN |-> defaultInitValue]
        (* Process Finalize *)
        /\ remaining_buyers = [self \in PIDS_FINALIZE |-> <<>>]
        /\ next_buyer = [self \in PIDS_FINALIZE |-> defaultInitValue]
        /\ remaining_investors = [self \in PIDS_FINALIZE |-> <<>>]
        /\ next_investor = [self \in PIDS_FINALIZE |-> defaultInitValue]
        (* Process Refund_Icp *)
        /\ refund_args = [self \in PIDS_REFUND_ICP |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = PID_ICP_USER_TRANSFER -> "ICP_User_Transfer_Loop"
                                        [] self = PID_ICP_LEDGER_ERROR -> "ICP_Ledger_Error_Loop"
                                        [] self = PID_ICP_LEDGER -> "ICP_Ledger_Loop"
                                        [] self = PID_SNS_LEDGER -> "SNS_Ledger_Loop"
                                        [] self = PID_SNS_LEDGER_ERROR -> "SNS_Ledger_Error_Loop"
                                        [] self = PID_COMMIT -> "Commit_"
                                        [] self = PID_ABORT -> "Abort_"
                                        [] self \in PIDS_REFRESH_BUYER_TOKEN -> "Refresh_Loop"
                                        [] self \in PIDS_FINALIZE -> "Finalize_Swap_Loop"
                                        [] self \in PIDS_REFUND_ICP -> "Refund_Icp_Loop"]

ICP_User_Transfer_Loop == /\ pc[PID_ICP_USER_TRANSFER] = "ICP_User_Transfer_Loop"
                          /\ \E user \in USERS:
                               \E amount \in 0..icp_balances[user]:
                                 icp_balances' = Transfer(icp_balances, user, Escrow_Address(user), amount)
                          /\ pc' = [pc EXCEPT ![PID_ICP_USER_TRANSFER] = "ICP_User_Transfer_Loop"]
                          /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                          sns_balances, swap_to_icp_ledger, 
                                          icp_ledger_to_swap, 
                                          swap_to_sns_ledger, 
                                          sns_ledger_to_swap, account, 
                                          remaining_buyers, next_buyer, 
                                          remaining_investors, next_investor, 
                                          refund_args >>

ICP_User_Transfer == ICP_User_Transfer_Loop

ICP_Ledger_Error_Loop == /\ pc[PID_ICP_LEDGER_ERROR] = "ICP_Ledger_Error_Loop"
                         /\ (swap_to_icp_ledger # <<>>)
                         /\ LET req == Head(swap_to_icp_ledger) IN
                              /\ swap_to_icp_ledger' = Tail(swap_to_icp_ledger)
                              /\ icp_ledger_to_swap' = (icp_ledger_to_swap \union { (Error_Response(Caller(req))) })
                         /\ pc' = [pc EXCEPT ![PID_ICP_LEDGER_ERROR] = "ICP_Ledger_Error_Loop"]
                         /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                         icp_balances, sns_balances, 
                                         swap_to_sns_ledger, 
                                         sns_ledger_to_swap, account, 
                                         remaining_buyers, next_buyer, 
                                         remaining_investors, next_investor, 
                                         refund_args >>

ICP_Ledger_Error == ICP_Ledger_Error_Loop

ICP_Ledger_Loop == /\ pc[PID_ICP_LEDGER] = "ICP_Ledger_Loop"
                   /\ (swap_to_icp_ledger # <<>>)
                   /\ LET req == Head(swap_to_icp_ledger) IN
                        /\ swap_to_icp_ledger' = Tail(swap_to_icp_ledger)
                        /\ \/ /\ (Is_Transfer_Msg(req))
                              /\ IF req.amount > icp_balances[req.from]
                                    THEN /\ icp_ledger_to_swap' = (icp_ledger_to_swap \union { (Error_Response(Caller(req))) })
                                         /\ UNCHANGED icp_balances
                                    ELSE /\ icp_balances' = Transfer(icp_balances, req.from, req.to, req.amount)
                                         /\ icp_ledger_to_swap' = (icp_ledger_to_swap \union { (Ok_Response(Caller(req), {})) })
                           \/ /\ (Is_Ask_Balance_Msg(req))
                              /\ icp_ledger_to_swap' = (icp_ledger_to_swap \union { (Ok_Response(Caller(req), icp_balances[req.account])) })
                              /\ UNCHANGED icp_balances
                   /\ pc' = [pc EXCEPT ![PID_ICP_LEDGER] = "ICP_Ledger_Loop"]
                   /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                   sns_balances, swap_to_sns_ledger, 
                                   sns_ledger_to_swap, account, 
                                   remaining_buyers, next_buyer, 
                                   remaining_investors, next_investor, 
                                   refund_args >>

ICP_Ledger == ICP_Ledger_Loop

SNS_Ledger_Loop == /\ pc[PID_SNS_LEDGER] = "SNS_Ledger_Loop"
                   /\ (swap_to_sns_ledger # <<>>)
                   /\ LET req == Head(swap_to_sns_ledger) IN
                        /\ swap_to_sns_ledger' = Tail(swap_to_sns_ledger)
                        /\ (Is_Transfer_Msg(req))
                        /\ Assert((req.from = defaultInitValue), 
                                  "Failure of assertion at line 217, column 13.")
                        /\ sns_balances' = [ sns_balances EXCEPT ![req.to] = @ + req.amount ]
                        /\ sns_ledger_to_swap' = (sns_ledger_to_swap \union { (Ok_Response(Caller(req), {})) })
                   /\ pc' = [pc EXCEPT ![PID_SNS_LEDGER] = "SNS_Ledger_Loop"]
                   /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                   icp_balances, swap_to_icp_ledger, 
                                   icp_ledger_to_swap, account, 
                                   remaining_buyers, next_buyer, 
                                   remaining_investors, next_investor, 
                                   refund_args >>

SNS_Ledger == SNS_Ledger_Loop

SNS_Ledger_Error_Loop == /\ pc[PID_SNS_LEDGER_ERROR] = "SNS_Ledger_Error_Loop"
                         /\ (swap_to_sns_ledger # <<>>)
                         /\ LET req == Head(swap_to_sns_ledger) IN
                              /\ swap_to_sns_ledger' = Tail(swap_to_sns_ledger)
                              /\ sns_ledger_to_swap' = (sns_ledger_to_swap \union { (Error_Response(Caller(req))) })
                         /\ pc' = [pc EXCEPT ![PID_SNS_LEDGER_ERROR] = "SNS_Ledger_Error_Loop"]
                         /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                         icp_balances, sns_balances, 
                                         swap_to_icp_ledger, 
                                         icp_ledger_to_swap, account, 
                                         remaining_buyers, next_buyer, 
                                         remaining_investors, next_investor, 
                                         refund_args >>

SNS_Ledger_Error == SNS_Ledger_Error_Loop

Commit_ == /\ pc[PID_COMMIT] = "Commit_"
           /\ lifecycle = OPEN
           /\ neuron_recipes' = buyers
           /\ lifecycle' = COMMITTED
           /\ pc' = [pc EXCEPT ![PID_COMMIT] = "Done"]
           /\ UNCHANGED << buyers, icp_balances, sns_balances, 
                           swap_to_icp_ledger, icp_ledger_to_swap, 
                           swap_to_sns_ledger, sns_ledger_to_swap, account, 
                           remaining_buyers, next_buyer, remaining_investors, 
                           next_investor, refund_args >>

Commit == Commit_

Abort_ == /\ pc[PID_ABORT] = "Abort_"
          /\ lifecycle = OPEN
          /\ lifecycle' = ABORTED
          /\ pc' = [pc EXCEPT ![PID_ABORT] = "Done"]
          /\ UNCHANGED << buyers, neuron_recipes, icp_balances, sns_balances, 
                          swap_to_icp_ledger, icp_ledger_to_swap, 
                          swap_to_sns_ledger, sns_ledger_to_swap, account, 
                          remaining_buyers, next_buyer, remaining_investors, 
                          next_investor, refund_args >>

Abort == Abort_

Refresh_Loop(self) == /\ pc[self] = "Refresh_Loop"
                      /\ lifecycle = OPEN
                      /\ account' = [account EXCEPT ![self] = CHOOSE u \in USERS: TRUE]
                      /\ swap_to_icp_ledger' = Append(swap_to_icp_ledger, (Ask_Balance_Msg(self, Escrow_Address(account'[self]))))
                      /\ pc' = [pc EXCEPT ![self] = "Refresh_Await_Ledger_Answer"]
                      /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                      icp_balances, sns_balances, 
                                      icp_ledger_to_swap, swap_to_sns_ledger, 
                                      sns_ledger_to_swap, remaining_buyers, 
                                      next_buyer, remaining_investors, 
                                      next_investor, refund_args >>

Refresh_Await_Ledger_Answer(self) == /\ pc[self] = "Refresh_Await_Ledger_Answer"
                                     /\ \E resp \in { r \in icp_ledger_to_swap: Caller(r) = self }:
                                          /\ icp_ledger_to_swap' = icp_ledger_to_swap \ { resp }
                                          /\ IF Is_Error(resp)
                                                THEN /\ pc' = [pc EXCEPT ![self] = "Refresh_Loop"]
                                                     /\ UNCHANGED buyers
                                                ELSE /\ LET amount == resp.result IN
                                                          \/ /\ pc' = [pc EXCEPT ![self] = "Refresh_Loop"]
                                                             /\ UNCHANGED buyers
                                                          \/ /\ LET old_amount == IF account[self] \in DOMAIN buyers THEN buyers[account[self]].amount ELSE 0 IN
                                                                  /\ /\ lifecycle = OPEN
                                                                     /\ old_amount < amount
                                                                  /\ \E increase \in 1..(amount - old_amount):
                                                                       buyers' = (      account[self] :> [ amount |-> old_amount + increase,
                                                                                  transfer_started |-> FALSE, transfer_succeeded |-> FALSE ] @@ buyers)
                                                                  /\ pc' = [pc EXCEPT ![self] = "Refresh_Loop"]
                                     /\ UNCHANGED << lifecycle, neuron_recipes, 
                                                     icp_balances, 
                                                     sns_balances, 
                                                     swap_to_icp_ledger, 
                                                     swap_to_sns_ledger, 
                                                     sns_ledger_to_swap, 
                                                     account, remaining_buyers, 
                                                     next_buyer, 
                                                     remaining_investors, 
                                                     next_investor, 
                                                     refund_args >>

Refresh_Buyer_Token(self) == Refresh_Loop(self)
                                \/ Refresh_Await_Ledger_Answer(self)

Finalize_Swap_Loop(self) == /\ pc[self] = "Finalize_Swap_Loop"
                            /\ (lifecycle = COMMITTED \/ lifecycle = ABORTED)
                            /\ remaining_buyers' = [remaining_buyers EXCEPT ![self] = SetToSeq(DOMAIN buyers)]
                            /\ pc' = [pc EXCEPT ![self] = "ICP_Sweep_Loop"]
                            /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                            icp_balances, sns_balances, 
                                            swap_to_icp_ledger, 
                                            icp_ledger_to_swap, 
                                            swap_to_sns_ledger, 
                                            sns_ledger_to_swap, account, 
                                            next_buyer, remaining_investors, 
                                            next_investor, refund_args >>

ICP_Sweep_Loop(self) == /\ pc[self] = "ICP_Sweep_Loop"
                        /\ IF remaining_buyers[self] # <<>>
                              THEN /\ next_buyer' = [next_buyer EXCEPT ![self] = Head(remaining_buyers[self])]
                                   /\ remaining_buyers' = [remaining_buyers EXCEPT ![self] = Tail(remaining_buyers[self])]
                                   /\ IF buyers[next_buyer'[self]].transfer_started
                                         THEN /\ pc' = [pc EXCEPT ![self] = "ICP_Sweep_Loop"]
                                              /\ UNCHANGED << buyers, 
                                                              swap_to_icp_ledger >>
                                         ELSE /\ buyers' = [buyers EXCEPT ![next_buyer'[self]] = [ @ EXCEPT !.transfer_started = TRUE ]]
                                              /\ swap_to_icp_ledger' = Append(swap_to_icp_ledger, (               Transfer_Msg(
                                                                       self,
                                                                       Escrow_Address(next_buyer'[self]),
                                                                       IF lifecycle = COMMITTED THEN GOVERNANCE_PRINCIPAL ELSE next_buyer'[self],
                                                                       buyers'[next_buyer'[self]].amount)))
                                              /\ pc' = [pc EXCEPT ![self] = "ICP_Sweep_Receive_Answer"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "End_ICP_Sweep_Loop"]
                                   /\ UNCHANGED << buyers, swap_to_icp_ledger, 
                                                   remaining_buyers, 
                                                   next_buyer >>
                        /\ UNCHANGED << lifecycle, neuron_recipes, 
                                        icp_balances, sns_balances, 
                                        icp_ledger_to_swap, swap_to_sns_ledger, 
                                        sns_ledger_to_swap, account, 
                                        remaining_investors, next_investor, 
                                        refund_args >>

ICP_Sweep_Receive_Answer(self) == /\ pc[self] = "ICP_Sweep_Receive_Answer"
                                  /\ \E resp \in { r \in icp_ledger_to_swap: Caller(r) = self}:
                                       /\ icp_ledger_to_swap' = icp_ledger_to_swap \ { resp }
                                       /\ IF Is_Ok(resp)
                                             THEN /\ buyers' = [buyers EXCEPT ![next_buyer[self]] = [ @ EXCEPT !.transfer_succeeded = TRUE]]
                                             ELSE /\ buyers' = [buyers EXCEPT ![next_buyer[self]] = [ @ EXCEPT !.transfer_started = FALSE, !.transfer_succeeded = FALSE ]]
                                  /\ pc' = [pc EXCEPT ![self] = "ICP_Sweep_Loop"]
                                  /\ UNCHANGED << lifecycle, neuron_recipes, 
                                                  icp_balances, sns_balances, 
                                                  swap_to_icp_ledger, 
                                                  swap_to_sns_ledger, 
                                                  sns_ledger_to_swap, account, 
                                                  remaining_buyers, next_buyer, 
                                                  remaining_investors, 
                                                  next_investor, refund_args >>

End_ICP_Sweep_Loop(self) == /\ pc[self] = "End_ICP_Sweep_Loop"
                            /\ next_buyer' = [next_buyer EXCEPT ![self] = defaultInitValue]
                            /\ IF lifecycle # COMMITTED
                                  THEN /\ pc' = [pc EXCEPT ![self] = "Finalize_Swap_Loop"]
                                       /\ UNCHANGED remaining_investors
                                  ELSE /\ remaining_investors' = [remaining_investors EXCEPT ![self] = SetToSeq(DOMAIN neuron_recipes)]
                                       /\ pc' = [pc EXCEPT ![self] = "SNS_Sweep_Loop"]
                            /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                            icp_balances, sns_balances, 
                                            swap_to_icp_ledger, 
                                            icp_ledger_to_swap, 
                                            swap_to_sns_ledger, 
                                            sns_ledger_to_swap, account, 
                                            remaining_buyers, next_investor, 
                                            refund_args >>

SNS_Sweep_Loop(self) == /\ pc[self] = "SNS_Sweep_Loop"
                        /\ IF remaining_investors[self] # <<>>
                              THEN /\ next_investor' = [next_investor EXCEPT ![self] = Head(remaining_investors[self])]
                                   /\ remaining_investors' = [remaining_investors EXCEPT ![self] = Tail(remaining_investors[self])]
                                   /\ IF neuron_recipes[next_investor'[self]].transfer_started
                                         THEN /\ pc' = [pc EXCEPT ![self] = "SNS_Sweep_Loop"]
                                              /\ UNCHANGED << neuron_recipes, 
                                                              swap_to_sns_ledger >>
                                         ELSE /\ neuron_recipes' = [neuron_recipes EXCEPT ![next_investor'[self]] = [ @ EXCEPT !.transfer_started = TRUE ]]
                                              /\ swap_to_sns_ledger' = Append(swap_to_sns_ledger, (               Transfer_Msg(self, defaultInitValue, next_investor'[self],
                                                                       neuron_recipes'[next_investor'[self]].amount)))
                                              /\ pc' = [pc EXCEPT ![self] = "SNS_Sweep_Receive_Answer"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "End_SNS_Sweep_Loop"]
                                   /\ UNCHANGED << neuron_recipes, 
                                                   swap_to_sns_ledger, 
                                                   remaining_investors, 
                                                   next_investor >>
                        /\ UNCHANGED << lifecycle, buyers, icp_balances, 
                                        sns_balances, swap_to_icp_ledger, 
                                        icp_ledger_to_swap, sns_ledger_to_swap, 
                                        account, remaining_buyers, next_buyer, 
                                        refund_args >>

SNS_Sweep_Receive_Answer(self) == /\ pc[self] = "SNS_Sweep_Receive_Answer"
                                  /\ \E resp \in { r \in sns_ledger_to_swap: Caller(r) = self}:
                                       /\ sns_ledger_to_swap' = sns_ledger_to_swap \ { resp }
                                       /\ IF Is_Ok(resp)
                                             THEN /\ neuron_recipes' = [neuron_recipes EXCEPT ![next_investor[self]] = [ @ EXCEPT !.transfer_succeeded = TRUE]]
                                             ELSE /\ neuron_recipes' = [neuron_recipes EXCEPT ![next_investor[self]] = [ @ EXCEPT !.transfer_started = FALSE, !.transfer_succeeded = FALSE ]]
                                  /\ pc' = [pc EXCEPT ![self] = "SNS_Sweep_Loop"]
                                  /\ UNCHANGED << lifecycle, buyers, 
                                                  icp_balances, sns_balances, 
                                                  swap_to_icp_ledger, 
                                                  icp_ledger_to_swap, 
                                                  swap_to_sns_ledger, account, 
                                                  remaining_buyers, next_buyer, 
                                                  remaining_investors, 
                                                  next_investor, refund_args >>

End_SNS_Sweep_Loop(self) == /\ pc[self] = "End_SNS_Sweep_Loop"
                            /\ pc' = [pc EXCEPT ![self] = "Finalize_Swap_Loop"]
                            /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                            icp_balances, sns_balances, 
                                            swap_to_icp_ledger, 
                                            icp_ledger_to_swap, 
                                            swap_to_sns_ledger, 
                                            sns_ledger_to_swap, account, 
                                            remaining_buyers, next_buyer, 
                                            remaining_investors, next_investor, 
                                            refund_args >>

Finalize(self) == Finalize_Swap_Loop(self) \/ ICP_Sweep_Loop(self)
                     \/ ICP_Sweep_Receive_Answer(self)
                     \/ End_ICP_Sweep_Loop(self) \/ SNS_Sweep_Loop(self)
                     \/ SNS_Sweep_Receive_Answer(self)
                     \/ End_SNS_Sweep_Loop(self)

Refund_Icp_Loop(self) == /\ pc[self] = "Refund_Icp_Loop"
                         /\ (lifecycle = COMMITTED \/ lifecycle = ABORTED)
                         /\ \E user \in (USERS \ { u \in DOMAIN buyers: buyers[u].transfer_succeeded = FALSE }):
                              \E amount \in 1..MAX_REFUND_AMOUNT:
                                /\ refund_args' = [refund_args EXCEPT ![self] = [ user |-> user, amount |-> amount]]
                                /\ swap_to_icp_ledger' = Append(swap_to_icp_ledger, (                   Transfer_Msg(
                                                             self,
                                                             Escrow_Address(user),
                                                             user,
                                                             amount
                                                         )))
                         /\ pc' = [pc EXCEPT ![self] = "Refund_Await_Response"]
                         /\ UNCHANGED << lifecycle, buyers, neuron_recipes, 
                                         icp_balances, sns_balances, 
                                         icp_ledger_to_swap, 
                                         swap_to_sns_ledger, 
                                         sns_ledger_to_swap, account, 
                                         remaining_buyers, next_buyer, 
                                         remaining_investors, next_investor >>

Refund_Await_Response(self) == /\ pc[self] = "Refund_Await_Response"
                               /\ \E resp \in { r \in icp_ledger_to_swap: Caller(r) = self }:
                                    icp_ledger_to_swap' = icp_ledger_to_swap \ { resp }
                               /\ refund_args' = [refund_args EXCEPT ![self] = defaultInitValue]
                               /\ pc' = [pc EXCEPT ![self] = "Refund_Icp_Loop"]
                               /\ UNCHANGED << lifecycle, buyers, 
                                               neuron_recipes, icp_balances, 
                                               sns_balances, 
                                               swap_to_icp_ledger, 
                                               swap_to_sns_ledger, 
                                               sns_ledger_to_swap, account, 
                                               remaining_buyers, next_buyer, 
                                               remaining_investors, 
                                               next_investor >>

Refund_Icp(self) == Refund_Icp_Loop(self) \/ Refund_Await_Response(self)

Next == ICP_User_Transfer \/ ICP_Ledger_Error \/ ICP_Ledger \/ SNS_Ledger
           \/ SNS_Ledger_Error \/ Commit \/ Abort
           \/ (\E self \in PIDS_REFRESH_BUYER_TOKEN: Refresh_Buyer_Token(self))
           \/ (\E self \in PIDS_FINALIZE: Finalize(self))
           \/ (\E self \in PIDS_REFUND_ICP: Refund_Icp(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

\**************************************************************
\* Sanity checks
\**************************************************************

\* The following properties serve as sanity checks on the model: we expect them to be violated
\* by our model. If they are not violated, our model doesn't exhibit enough behaviors.

Inv_Sanity_No_Buyers == DOMAIN buyers = {}
Inv_Sanity_Never_Committed == lifecycle # COMMITTED
Inv_Sanity_Never_Aborted == lifecycle # ABORTED
Inv_Sanity_All_Buyers_Zero == \A u \in DOMAIN buyers: buyers[u].amount = 0
Inv_Sanity_Governance_Stays_Zero == icp_balances[GOVERNANCE_PRINCIPAL] = 0

\**************************************************************
\* Invariants
\**************************************************************

Inv_Open_Amount == 
    lifecycle = OPEN => \A u \in DOMAIN buyers: buyers[u].amount <= icp_balances[Escrow_Address(u)]

\**************************************************************
\* Liveness requirements
\**************************************************************

Sum_Balances(S) == FoldFunctionOnSet(LAMBDA x, y: x + y, 0, icp_balances, S)

(****** Fairness constraints ********)

\* Liveness is always conditioned on some fairness assumptions. We specify those first.


\* The ledgers have to be allowed to returned errors when appropriate (e.g., when a user
\* asks for a refund that's bigger than the balance of the escrow amount). However, we want
\* to ban spontaneous errors from happening infinitely often, otherwise we can't guarantee
\* that any of our transfers will succeed, and thus we can't guarantee that our properties
\* will hold.
\* A spontaenous error is equivalent to
\* ICP_Ledger_Error /\ ~ICP_Ledger
\* (that is, it's a valid ICP_Ledger_Error action but that's NOT a valid ICP_Ledger action).
\* "Not always eventually" can be read as "not infinitely often".
Not_Constant_Spontaneous_Ledger_Errors == 
    /\ ~[]<><<(ICP_Ledger_Error /\ ~ICP_Ledger)>>_vars
    /\ ~[]<><<(SNS_Ledger_Error /\ ~SNS_Ledger)>>_vars

\* The first set of fairness constraints is relevant for all goals, and we include
\* in the specification. All of these should be satisfiable by any set of involved parties.
\* For example, finalize, commit, and abort can be called by any principal, so anyone
\* should be able to ensure the fairness of these. We'll embed other fairness conditions
\* directly in the properties. 
Fairness ==
    /\ WF_vars(ICP_Ledger)
    /\ WF_vars(SNS_Ledger)
    /\ Not_Constant_Spontaneous_Ledger_Errors
    /\ WF_vars(Commit)
    /\ WF_vars(Abort)
    /\ \A self \in PIDS_FINALIZE: WF_vars(Finalize(self))


Spec_Liveness ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* This is the main property from the perspective of the initiators of the swap.
ICP_Liveness_Commit == 
    \* First, entering the "COMMITTED" of lifecycle leads to the ICP and ledger
    \* balances eventually being in sync with the amounts in the buyers data structure.
    \* Namely, the (SNS) governance principal will eventually get the sum of all ICP 
    \* according to the "books" (buyers), and the users will each get their share of the SNS
    \* tokens.
    \* For the SNS ledger, this is a simplification, as in the model we don't scale the
    \* amounts as the implementation does.
    /\ lifecycle = COMMITTED ~>
       /\ icp_balances[GOVERNANCE_PRINCIPAL] = FoldFunction(LAMBDA x, y: x.amount + y, 0, buyers)
       /\ \A u \in  DOMAIN buyers: sns_balances[u] = buyers[u].amount
    \* Second, whenever we abort, we can be sure that there no SNS tokens will ever be issued.
    /\ [](lifecycle = ABORTED => [](\A u \in USERS: sns_balances[u] = 0))

\* From the users' perspective, they also want assurances about refunds, captured in the following
\* property.
ICP_Liveness_Refund == 
    \* We can't achieve our property if the users keep transfering their 
    \* ICP to the escrow accounts infinitely often.
    \* This is a stronger assumption that what we'd want, as it makes the guarantee for the user
    \* u depend on the behavior of all users. 
    \* But I chose to live with it, as 
    \* (a) there doesn't seem to be a mechanism by which a user U1 could prevent a user U2 from 
    \*     getting their refund by doing some transfers to the U1 escrow account.
    \* (b) I couldn't think of a nice simple way to state the weaker assumption with PlusCal.
    /\ ~[]<><<ICP_User_Transfer>>_vars
    => \A u \in USERS: 
        \* For the property to hold, the user may have to call refund infinitely often, and with
        \* "acceptable" arguments (lower than the current balance of their escrow address)
        /\ []<>(\E p \in PIDS_REFUND_ICP: 
                /\ refund_args[p] # defaultInitValue
                /\ refund_args[p].user = u 
                /\ refund_args[p].amount <= icp_balances[Escrow_Address(u)]) 
        /\ \A self \in PIDS_REFUND_ICP: WF_vars(Refund_Icp(self)) 
        =>
            \* Eventually, once the user's escrow account is emptied, the some of the ICP and SNS token
            \* balances will be the same sum that the user started off with (we don't have ledger fees
            \* in this model)
            /\ icp_balances[u] + sns_balances[u] = INITIAL_PER_USER_BALANCE
            \* If the swap is aborted, the user will eventually get their full refund (we don't have ledger
            \* fees in this model)
            /\ lifecycle = ABORTED ~> icp_balances[u] = INITIAL_PER_USER_BALANCE



====
