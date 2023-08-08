A high-level model of the interaction between the SNS governance and the ledger canisters.
The goal is to analyze the interleavings from multiple parallel calls to governance/ledger.
We're using PlusCal (aka +CAL) - more precisely, its C syntax - to specify the canister calls, as it takes care of process counters and local state in a readable fashion.

***********
Running TLC
***********

Here's how to invoke TLC from the command line (e.g., on the server):

java -cp <path-to-tla2tools.jar>  \
    -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet \
    -Dtlc2.tool.ModelChecker.BAQueue=true \
    -XX:+UseParallelGC \
    -Xmx100G tlc2.TLC \
    Governance_TLC.tla \
    -tool -modelcheck -config Governance_TLC.cfg -workers 54 -checkpoint 0

This:
    - uses the symmetry relation defined in Governance_TLC
    - runs TLC with 54 workers (i.e., 54 cores)
    - uses fingerprint set and queue implementations that are optimized for concurrency
    - allocates 100G heap to the JVM
    - disables checkpointing

Tip: use tmux or screen such that the analysis doesn't terminate if your SSH connection does

*****************************
Recommended Apalache Workflow
*****************************

Here's the current worfklow using Apalache:

- In VSCode, enable auto-parsing of TLA files on save: Command Palette/Preferences: Configure Language Specific Setting/TLA+/add: 
    "editor.codeActionsOnSave": { "source": true }
  TLA Toolbox probably does automatically
- Pull up all constant definitions before the algorithm in this file, and annotate them with types.
- Use the INSTANCE override in a separate file (Governance_Apalache.tla), and only add type annotations to variables in this file. 
  This way, the VARIABLE declarations don't get overwritten by the PlusCal transpiler.
- Use "apalache-mc typecheck Governance_Apalache.tla" to check the type annotations

Apalache caveats to keep in mind:

1. don't forget the semicolon at the end of each annotation
2. function type annotations use a single arrow ->, operator annotations use the double arrow =>
3. the type system doesn't have sum types (variants). 
   However, it's intentionally unsound to allow heterogeneous lists/sets, like the ones we use for message buffers.
   Both governance_to_ledger and ledger_to_governance can contain values of different types; we type this using a record
   whose fields are the union of all the fields used by the individual message types.

*************
Optimizations
*************

The model deviates from the Rust implementation by (among other things) employing some optimizations.
In particular, validity checks (e.g., in Merge_Maturity) over method parameters are often 
moved to the start of the action, such that the choice of the parameters is restricted immediately, 
rather adding an "await" at the same point as where the implementation performs its checks.
This shortens the time needed by TLC to figure out that an action is disabled in a particular state.
------------ MODULE Governance ------------
EXTENDS TLC, Sequences, Naturals, FiniteSets

\* IDs for processes. We'll use one process per governance call, to be able to control how many of each call we analyze. 
\* As we model ledger operations as atomic, we'll have just one ledger process.
CONSTANTS 
    \* @type: Set(PROC);
    Claim_Neuron_Process_Ids, 
    \* @type: Set(PROC);
    Refresh_Neuron_Process_Ids, 
    \* @type: Set(PROC);
    Disburse_Neuron_Process_Ids, 
    \* @type: Set(PROC);
    Disburse_Maturity_Process_Ids, 
    \* @type: Set(PROC);
    Merge_Maturity_Process_Ids,
    \* @type: Set(PROC);
    Split_Neuron_Process_Ids,
    \* @type: PROC;
    Ledger_Process_Id,
    \* @type: Set(PROC);
    Change_Neuron_Fee_Process_Ids,
    \* @type: Set(PROC);
    Increase_Neuron_Maturity_Process_Ids,
    \* @type: PROC;
    Idle_Process_Id

\* IDs for ledger accounts
CONSTANTS 
    \* @type: Set(ACCOUNT);
    Account_Ids, 
    \* @type: Set(ACCOUNT);
    Governance_Account_Ids, 
    \* @type: ACCOUNT;
    Minting_Account_Id

User_Account_Ids == Account_Ids \ (Governance_Account_Ids \union {Minting_Account_Id})

ASSUME Governance_Account_Ids \subseteq Account_Ids
ASSUME Minting_Account_Id \in Account_Ids

\* Check that we can allocate sufficiently many governance account IDs for the differenc processes
Neuron_Creating_Processes == UNION { Claim_Neuron_Process_Ids, Split_Neuron_Process_Ids, Disburse_Maturity_Process_Ids }
ASSUME Cardinality(Neuron_Creating_Processes) <= Cardinality(Governance_Account_Ids)

\* Constants from the actual code
CONSTANTS 
    \* Minimum stake a neuron can have
    \* @type: Int;
    MIN_STAKE,
    \* The transfer fee charged by the ledger canister
    \* @type: Int;
    TRANSACTION_FEE

\* Constants used to make our search space finite
CONSTANTS 
    \* The maximum balance of each (non-governance) account in the initial state of the ledger canister
    \* @type: Int;
    INITIAL_MAX_BALANCE,
    \* The cap on the total number of spontaneous transfers between ledger accounts
    \* that we want to consider in the analysis
    \* @type: Int;
    NUMBER_OF_TRANSFERS_CAP,
    \* A maximum management fee that can be charged for a neuron
    \* @type: Int;
    MAX_NEURON_FEE,
    \* The maximum maturity that a neuron can be given
    \* @type: Int;
    MAX_MATURITY

\* Setting MAX_NEURON_FEE <= TRANSACTION_FEE will prevent any fees from being levied ever.
\* We thus ask TLC to check that we can levy fees.
ASSUME MAX_NEURON_FEE > TRANSACTION_FEE

\* Setting MAX_MATURITY <= TRANSACTION_FEE will prevent any maturity from being paid out.
\* We thus ask TLC to check that we can pay maturity out.
ASSUME MAX_MATURITY > TRANSACTION_FEE

\* Similarly, constants we'll use to distinguish the message types for the inter-canister calls
CONSTANTS 
    \* @type: REQ;
    OP_QUERY_BALANCE,
    \* @type: REQ;
    OP_TRANSFER,
    \* @type: RESP;
    TRANSFER_OK,
    \* @type: RESP;
    TRANSFER_FAIL

Min(x, y) == IF x < y THEN x ELSE y
\* Wrappers to make creation of requests/responses a bit more convenient less error prone by giving names to parameters,
\* instead of fiddling with indices or string field names directly.
response(caller, response_val) == [caller |-> caller, response_value |-> response_val]
request(caller, request_type, request_args) == [caller |-> caller, type |-> request_type, args |-> request_args]
transfer(from, to, amount, fee) == [ from |-> from, to |-> to, amount |-> amount, fee |-> fee ]
balance_query(account) == [ of_account |-> account ]

saturating_sub(x, y) == IF x > y THEN x - y ELSE 0

calc_disburse_amount(amount, fees_amount) == LET
        diff == saturating_sub(amount, fees_amount)
    IN
        IF diff > TRANSACTION_FEE THEN diff - TRANSACTION_FEE ELSE diff


(* --algorithm Governance_Ledger_Interaction {

\* +Cal note: To be able to mutate variables from +Cal, it seems we have to define them in the algorithm block
\* +Cal note: "variable/variables" has to be lowercase (the TLA+ version is uppercase)
\* +Cal note: All of the following are variables

\* The neuron state kept by the governance canister. We're recording this as a global variable, and not a process
\* since we use processes to model method calls on the governance canister
variables neuron \in [{} -> {}];

\* The set of currently locked neurons
locks = {};

\* We use this counter to create fresh neuron IDs in claim_neuron
neuron_count = 0;

\* tracker variables for invariants
total_rewards = 0;
minted = 0;
burned = 0;

\* The queue of messages sent from the governance canister to the ledger canister
governance_to_ledger = <<>>;

\* The responses returned by the ledger canister to the calls made by the governance canister. 
\* We use a set instead of a queue for the responses, as we will process these responses in an arbitrary order.
\* This models the facts that:
\* 1. In the implementation, the call to the ledger canister may not be atomic.
\*    In particular, when asked to transfer something, the ledger canister might archive transactions, which
\*    introduces interleaving points.
\*    While the archiving is in progress, balance queries might get served in the meantime, meaning that the
\*    results of transfers and queries don't come in the order in which they were issued.
\* 2. The IC interface spec explicitly says that reponses might not be ordered. So while the current IC implementation 
\*    does use queues to order responses, it could change to not order them and still stay compliant to the spec.
ledger_to_governance = {};

macro send_request(caller_id, op_type, args) {
    governance_to_ledger := Append(governance_to_ledger, request(caller_id, op_type, args))
};

macro send_response(caller_id, resp) {
        ledger_to_governance := ledger_to_governance \union {response(caller_id, resp)}
};

macro update_fees(neuron_id, fees_amount) {
    if(neuron[neuron_id].cached_stake > fees_amount) {
        neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = @ - fees_amount, !.fees = 0]]
    } else {
        neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = 0, !.fees = 0]];
    };
}

macro add_neuron(account_id) {
    neuron := account_id :> [ cached_stake |-> 0, id |-> account_id, fees |-> 0, maturity |-> 0 ] @@ neuron;
}
macro remove_neuron(account_id) {
    neuron := [n \in DOMAIN(neuron) \ {account_id} |-> neuron[n] ];
}

macro update_stake(account_id, new_stake) {
    neuron := [ neuron EXCEPT ![account_id] = [@ EXCEPT !.cached_stake = new_stake ] ]
}

\* A Claim_Neuron process simulates a call to claim_neuron
process ( Claim_Neuron \in Claim_Neuron_Process_Ids )
    variable 
        \* The account_id is an argument to the canister call; we let it be chosen non-deteministically 
        account_id = Minting_Account_Id;
    { 
    ClaimNeuron1:
        with(aid \in  Governance_Account_Ids \ DOMAIN(neuron)) {
            account_id := aid;
            \* The Rust code tries to obtain a lock; this should always succeed, as the 
            \* neuron has just been created in the same atomic block. We'll call assert
            \* instead of await here, to check that
            assert account_id \notin locks;
            locks := locks \union {account_id};
            add_neuron(account_id);
            send_request(self, OP_QUERY_BALANCE, balance_query(account_id));
        };

    ClaimNeuron2:
        \* Note that the "with" construct implicitly awaits until the set of values to draw from is non-empty
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; b = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};
            if(b >= MIN_STAKE) {
                update_stake(account_id, b);
            } else {
                remove_neuron(account_id);
            };
            locks := locks \ {account_id};
        };
    }

process ( Refresh_Neuron \in Refresh_Neuron_Process_Ids )
    variable 
        account_id = Minting_Account_Id;
    {
    RefreshNeuron1:
        \* There are two ways that the user can invoke a neuron refresh: 
        \* 1. by specifying a (sub)account ID
        \* 2. by specifying an existing neuron ID
        \* As the neuron ID is derived from the (sub)account ID, we conflate the two.
        with(aid \in DOMAIN(neuron) \ locks) {
            account_id := aid;
            locks := locks \union {account_id};
            send_request(self, OP_QUERY_BALANCE, balance_query(account_id));
        };

    RefreshNeuron2:
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; b = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};
            if(b >= MIN_STAKE) {
                assert(b >= neuron[account_id].cached_stake);
                update_stake(account_id, b);
            };
            \* If b < MIN_STAKE, the code returns an error in this case, releasing the lock. 
            \* We model this with just a skip (i.e., the missing else branch)
            locks := locks \ {account_id};
        };
    }

process ( Disburse_Neuron \in Disburse_Neuron_Process_Ids )
    variable
        \* These model the parameters of the call
        account_id = Minting_Account_Id;
        amount = 0;
        to_account \in Account_Ids;
        \* The model the internal variables of the procedure.
        \* Since +Cal doesn't allow multiple assignments to the same variable in a single block,
        \* we also use temporary variables to simulate this and stay closer to the source code
        fees_amount = 0;
        \* Whether an error was returned by a call to a ledger canister
    {
    DisburseNeuron1:
        \* This models a few checks at the start of the Rust code.
        \* We currently omit the check that the neuron is dissolved, and we plan to add this later.
        \* We omit the other checks: who the caller is, whether the neuron is KYC verified, as well
        \* as a few well-formedness checks (of the neuron and recipient account) as everything in
        \* our model is well-formed.
        with(aid \in DOMAIN(neuron) \ locks; amt \in 0..neuron[aid].cached_stake) {
            account_id := aid;
            amount := amt;
            fees_amount := neuron[account_id].fees;
            \* The Rust code has a more elaborate code path to determine the disburse_amount, where the
            \* amount argument is left unspecified in the call, and a default value is computed instead.
            \* As this default value is in the range between 0 and the neuron's cached_stake, our 
            \* non-deterministic choice should cover this case.
            \* The Rust code throws an error here if the neuron is locked. Instead, we prevent the Disburse_Neuron process from running.
            \* This is OK since the Rust code doesn't change the canister's state before obtaining the lock (if it
            \* did, the model wouldn't capture this and we could miss behaviors).
            locks := locks \union {account_id};
            if(fees_amount > TRANSACTION_FEE) {
                send_request(self, OP_TRANSFER, transfer(account_id, Minting_Account_Id, fees_amount, 0));
            }
            else {
                \* There's some code duplication here, but having to have the with statement
                \* span entire blocks to please Apalache, I don't have a better solution at the moment
                update_fees(account_id, fees_amount);
                send_request(self, OP_TRANSFER, transfer(account_id, to_account, calc_disburse_amount(amount, fees_amount), TRANSACTION_FEE));
                goto DisburseNeuron3;
            };
        };
   
    DisburseNeuron2:
        \* Note that we're here only because the fees amount was larger than the
        \* transaction fee (otherwise, the goto above would have taken us to DisburseNeuron3)
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL){
                goto DisburseNeuronEnd;
            }
            else {
                update_fees(account_id, fees_amount);
                send_request(self, OP_TRANSFER, transfer(account_id, to_account, calc_disburse_amount(amount, fees_amount), TRANSACTION_FEE));
            };
        };

    DisburseNeuron3:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL) {
                goto DisburseNeuronEnd;
            } 
            else {
                neuron := [neuron EXCEPT ![account_id] = [@ EXCEPT !.cached_stake = saturating_sub(@, 
                    calc_disburse_amount(amount, fees_amount) + TRANSACTION_FEE) ]];
            };
        };

    \* This label introduces an additional interleaving point not present in
    \* the Rust code, but it doesn't interfere with the soundness of our abstraction.
    \* Worst case, we'll get some spurious counterexamples.
    DisburseNeuronEnd:
        locks := locks \ {account_id};
    }

process ( Merge_Maturity \in Merge_Maturity_Process_Ids )
    variable
        \* These model the parameters of the call
        account_id = 0;
        maturity_to_merge = 0;  \* it is given as a percentage in rust, but we simplify that here
    {
    MergeMaturity1:
        with(aid \in DOMAIN(neuron) \ locks; maturity_to_merge_tmp \in (TRANSACTION_FEE+1)..neuron[aid].maturity) {
            account_id := aid;
            maturity_to_merge := maturity_to_merge_tmp;
            locks := locks \union {account_id};
            send_request(self, OP_TRANSFER, transfer(Minting_Account_Id, account_id, maturity_to_merge, 0));
        };
    MergeMaturity2:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status # TRANSFER_FAIL) {
                \* the rust impl uses saturating arithmetic and unsigned ints.
                neuron := [neuron EXCEPT ![account_id] = [@ EXCEPT !.maturity = saturating_sub(@, maturity_to_merge), !.cached_stake = @ + maturity_to_merge]];
            };
            locks := locks \ {account_id};
        };
    };

process (Disburse_Maturity \in Disburse_Maturity_Process_Ids)
    variables
        account_id = Minting_Account_Id;
        to_account = Minting_Account_Id;
        amount = 0;
    {
    DisburseMaturityStart:
       with(aid \in DOMAIN(neuron) \ locks; 
                tid \in Account_Ids; 
                amt \in TRANSACTION_FEE + 1 .. neuron[aid].maturity ) {
            account_id := aid;
            to_account := tid;
            amount := amt;
            locks := locks \union {account_id};
            send_request(self, OP_TRANSFER, transfer(Minting_Account_Id, to_account, amount, 0));
        };

    DisburseMaturityEnd:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
                ledger_to_governance := ledger_to_governance \ {answer};
                neuron := [ neuron EXCEPT ![account_id] = [@ EXCEPT !.maturity = saturating_sub(@, amount) ] ];
                locks := locks \ {account_id};
        };
 
    }


process ( Split_Neuron \in Split_Neuron_Process_Ids )
    variable
        parent_account_id =  Minting_Account_Id;
        amount = 0;
        \* internal variables
        child_account_id = Minting_Account_Id;

    {
    SplitNeuron1:
        \* Need to make sure there is an element of Split_Neuron_Account_Ids for each
        \* member of Split_Neuron_Process_Ids
        with(aid \in DOMAIN(neuron) \ locks; 
             amt \in 0..neuron[aid].cached_stake; 
             cid \in Governance_Account_Ids) {
            \* This is checked by new_neuron_id in the implementation
            parent_account_id := aid;
            amount := amt;
            child_account_id := cid;

            await(amount >= MIN_STAKE + TRANSACTION_FEE 
                  /\ neuron[parent_account_id].cached_stake - neuron[parent_account_id].fees >= MIN_STAKE + amount);

            await(cid \notin DOMAIN(neuron));
            assert child_account_id \notin locks;  \* should be redundant
            \* Note that in the implementation this implies that child_account_id != parent_account_id,
            \* as the locks are taken sequentially there; here, we're sure that these neuron IDs differ,
            \* so we omit the extra check.
            locks := locks \union {parent_account_id, child_account_id};
            \* create empty child neuron
            add_neuron(child_account_id);

            governance_to_ledger := Append(governance_to_ledger, 
                request(self, OP_TRANSFER, transfer(parent_account_id, child_account_id, amount - TRANSACTION_FEE, TRANSACTION_FEE)));
        };
    SplitNeuron2:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL) {
                remove_neuron(child_account_id);
            } else {
                \* the rust impl should but does not use saturating arithmetic.
                neuron := [neuron EXCEPT ![parent_account_id] = [@ EXCEPT !.cached_stake = @ - amount], 
                                            ![child_account_id] = [@ EXCEPT !.cached_stake = amount - TRANSACTION_FEE]];
            };
            locks := locks \ {child_account_id, parent_account_id};
        };
    };

\* The ledger responds to calls by the governance canister.
\* We also allow it to spontaneously initiate transfers from the
\* user (non-governance) accounts to other accounts, as well as
\* to governance accounts. The total number of such spontaneous
\* transfer is limited, to get a finite state space to search.
process ( Ledger = Ledger_Process_Id )
    variables 
        balances = [a \in Governance_Account_Ids \union {Minting_Account_Id} |-> 0] @@ [a \in User_Account_Ids |-> INITIAL_MAX_BALANCE];
        \* How many spontaneous transfers have taken place so far
        nr_transfers = 0;

    {
    LedgerMainLoop:
        \* We'll do an infinite loop, in order to serve all calls to the ledger canister, without
        \* limiting their number.
        while(TRUE) {
            either {
                \* Respond to a query
                await(governance_to_ledger /= <<>>);
                with(req = Head(governance_to_ledger); t = req.type; arg = req.args; caller = req.caller) {
                    governance_to_ledger := Tail(governance_to_ledger);
                    assert(t \in {OP_QUERY_BALANCE, OP_TRANSFER});
                    if(t = OP_QUERY_BALANCE) {
                        send_response(caller, [bal |-> balances[arg.of_account]])
                    } 
                    else if(t = OP_TRANSFER) {
                        with(from_acc = arg.from;
                             to_acc = arg.to;
                             amnt = arg.amount;
                             fee = arg.fee;
                             is_invalid_transfer = 
                               \/
                                (/\ from_acc /= Minting_Account_Id
                                 /\ to_acc /= Minting_Account_Id
                                 /\ fee < TRANSACTION_FEE
                                )
                               \/ (from_acc = Minting_Account_Id /\ to_acc = Minting_Account_Id)
                               \/ (from_acc = Minting_Account_Id /\ fee /= 0)
                               \/ (to_acc = Minting_Account_Id /\ fee /= 0)
                               \/ (to_acc = Minting_Account_Id /\ amnt < TRANSACTION_FEE)
                               \/ fee + amnt > balances[from_acc]
                        ) {
                            \* In the Rust code, this is enforced by the unsigned type.
                            \* Assert here to make sure we haven't messed up in the model.
                            assert(fee >= 0);
                            if(is_invalid_transfer) {
                                send_response(caller, [status |-> TRANSFER_FAIL]);
                            }
                            else {
                                \* In the code, the fees are burnt by sending them to the Minting_Account_Id.
                                \* As we don't yet have any invariants over this, we purposefully omit modeling the 
                                \* balance of the Minting_Account_Id to reduce the number of states considered.
                                balances[from_acc] := balances[from_acc] - (fee + amnt) ||
                                    balances[to_acc] := balances[to_acc] + amnt;
                                send_response(caller, [status |-> TRANSFER_OK]);
                                burned := burned + fee + (IF to_acc = Minting_Account_Id THEN amnt ELSE 0);
                                if(from_acc = Minting_Account_Id)
                                    minted := minted + amnt;
                            };
                        }
                    }
                };
            } or {
                \* Randomly transfer money from one non-governance account to a governance one.
                \* We cap the total number of such "spontaneous" transfers.
                \* This isn't strictly necessary, as the total number of such reachable states by 
                \* spontaneous transfers is finite anyway. However, this might help to avoid 
                \* considering likely uninteresting states once we have processed all the calls to 
                \* the governance canister.
                await nr_transfers < NUMBER_OF_TRANSFERS_CAP;
                with(sender \in { a \in Account_Ids \ Governance_Account_Ids : balances[a] > 0 }; 
                    amnt \in 1..balances[sender]; 
                    recipient \in Governance_Account_Ids) {
                    
                    balances := [balances EXCEPT ![sender] = @ - amnt, ![recipient] = @ + amnt];
                    nr_transfers := nr_transfers + 1;
                }
            }
        }
    }

process (Change_Neuron_Fee \in Change_Neuron_Fee_Process_Ids)
    {
    Change_Neuron_Fee1:
        with(nid \in DOMAIN(neuron); 
            new_fee_value \in 0..Min(MAX_NEURON_FEE, neuron[nid].cached_stake)) {
            neuron := [neuron EXCEPT ![nid] = [@ EXCEPT !.fees = new_fee_value]];
        }
    }


process (Increase_Neuron_Maturity \in Increase_Neuron_Maturity_Process_Ids)
    {
    Increase_Neuron_Maturity1:
        with(nid \in DOMAIN(neuron); 
            new_maturity \in (neuron[nid].maturity+1)..MAX_MATURITY) {
            total_rewards := total_rewards + new_maturity - neuron[nid].maturity;
            neuron := [neuron EXCEPT ![nid] = [@ EXCEPT !.maturity = new_maturity]];
        }
    }

\* To be able to activate deadlock detection, allow us to idle when all governance calls have reached their 
\* end, or are unable to proceed further (e.g., we're in a state where a neuron can't be split)
process (Idle = Idle_Process_Id) 
    {
    Idle:
        await(
            /\ \A p \in Claim_Neuron_Process_Ids: pc[p] = "Done"
            /\ \A p \in Refresh_Neuron_Process_Ids: pc[p] = "Done"
            /\ \A p \in Disburse_Neuron_Process_Ids: pc[p] = "Done"
            /\ 
                \/ \A p \in Disburse_Maturity_Process_Ids: pc[p] = "Done"
                \/ \A n \in DOMAIN(neuron): neuron[n].maturity <= TRANSACTION_FEE
            /\ 
                \/ \A p \in Merge_Maturity_Process_Ids: pc[p] = "Done"
                \/ \A n \in DOMAIN(neuron): neuron[n].maturity <= TRANSACTION_FEE
            /\ 
                \/ \A p \in Split_Neuron_Process_Ids: pc[p] = "Done"
                \/ \A n \in DOMAIN(neuron): neuron[n].cached_stake - neuron[n].fees < 2 * MIN_STAKE + TRANSACTION_FEE
        );
        goto Idle;
    }


}

*)

\* BEGIN TRANSLATION (chksum(pcal) = "5c707e58" /\ chksum(tla) = "220602c7")
\* Label Idle of process Idle at line 567 col 9 changed to Idle_
\* Process variable account_id of process Claim_Neuron at line 232 col 9 changed to account_id_
\* Process variable account_id of process Refresh_Neuron at line 261 col 9 changed to account_id_R
\* Process variable account_id of process Disburse_Neuron at line 290 col 9 changed to account_id_D
\* Process variable amount of process Disburse_Neuron at line 291 col 9 changed to amount_
\* Process variable to_account of process Disburse_Neuron at line 292 col 9 changed to to_account_
\* Process variable account_id of process Merge_Maturity at line 365 col 9 changed to account_id_M
\* Process variable amount of process Disburse_Maturity at line 390 col 9 changed to amount_D
VARIABLES neuron, locks, neuron_count, total_rewards, minted, burned, 
          governance_to_ledger, ledger_to_governance, pc, account_id_, 
          account_id_R, account_id_D, amount_, to_account_, fees_amount, 
          account_id_M, maturity_to_merge, account_id, to_account, amount_D, 
          parent_account_id, amount, child_account_id, balances, nr_transfers

vars == << neuron, locks, neuron_count, total_rewards, minted, burned, 
           governance_to_ledger, ledger_to_governance, pc, account_id_, 
           account_id_R, account_id_D, amount_, to_account_, fees_amount, 
           account_id_M, maturity_to_merge, account_id, to_account, amount_D, 
           parent_account_id, amount, child_account_id, balances, 
           nr_transfers >>

ProcSet == (Claim_Neuron_Process_Ids) \cup (Refresh_Neuron_Process_Ids) \cup (Disburse_Neuron_Process_Ids) \cup (Merge_Maturity_Process_Ids) \cup (Disburse_Maturity_Process_Ids) \cup (Split_Neuron_Process_Ids) \cup {Ledger_Process_Id} \cup (Change_Neuron_Fee_Process_Ids) \cup (Increase_Neuron_Maturity_Process_Ids) \cup {Idle_Process_Id}

Init == (* Global variables *)
        /\ neuron \in [{} -> {}]
        /\ locks = {}
        /\ neuron_count = 0
        /\ total_rewards = 0
        /\ minted = 0
        /\ burned = 0
        /\ governance_to_ledger = <<>>
        /\ ledger_to_governance = {}
        (* Process Claim_Neuron *)
        /\ account_id_ = [self \in Claim_Neuron_Process_Ids |-> Minting_Account_Id]
        (* Process Refresh_Neuron *)
        /\ account_id_R = [self \in Refresh_Neuron_Process_Ids |-> Minting_Account_Id]
        (* Process Disburse_Neuron *)
        /\ account_id_D = [self \in Disburse_Neuron_Process_Ids |-> Minting_Account_Id]
        /\ amount_ = [self \in Disburse_Neuron_Process_Ids |-> 0]
        /\ to_account_ \in [Disburse_Neuron_Process_Ids -> Account_Ids]
        /\ fees_amount = [self \in Disburse_Neuron_Process_Ids |-> 0]
        (* Process Merge_Maturity *)
        /\ account_id_M = [self \in Merge_Maturity_Process_Ids |-> 0]
        /\ maturity_to_merge = [self \in Merge_Maturity_Process_Ids |-> 0]
        (* Process Disburse_Maturity *)
        /\ account_id = [self \in Disburse_Maturity_Process_Ids |-> Minting_Account_Id]
        /\ to_account = [self \in Disburse_Maturity_Process_Ids |-> Minting_Account_Id]
        /\ amount_D = [self \in Disburse_Maturity_Process_Ids |-> 0]
        (* Process Split_Neuron *)
        /\ parent_account_id = [self \in Split_Neuron_Process_Ids |-> Minting_Account_Id]
        /\ amount = [self \in Split_Neuron_Process_Ids |-> 0]
        /\ child_account_id = [self \in Split_Neuron_Process_Ids |-> Minting_Account_Id]
        (* Process Ledger *)
        /\ balances = [a \in Governance_Account_Ids \union {Minting_Account_Id} |-> 0] @@ [a \in User_Account_Ids |-> INITIAL_MAX_BALANCE]
        /\ nr_transfers = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Claim_Neuron_Process_Ids -> "ClaimNeuron1"
                                        [] self \in Refresh_Neuron_Process_Ids -> "RefreshNeuron1"
                                        [] self \in Disburse_Neuron_Process_Ids -> "DisburseNeuron1"
                                        [] self \in Merge_Maturity_Process_Ids -> "MergeMaturity1"
                                        [] self \in Disburse_Maturity_Process_Ids -> "DisburseMaturityStart"
                                        [] self \in Split_Neuron_Process_Ids -> "SplitNeuron1"
                                        [] self = Ledger_Process_Id -> "LedgerMainLoop"
                                        [] self \in Change_Neuron_Fee_Process_Ids -> "Change_Neuron_Fee1"
                                        [] self \in Increase_Neuron_Maturity_Process_Ids -> "Increase_Neuron_Maturity1"
                                        [] self = Idle_Process_Id -> "Idle_"]

ClaimNeuron1(self) == /\ pc[self] = "ClaimNeuron1"
                      /\ \E aid \in Governance_Account_Ids \ DOMAIN(neuron):
                           /\ account_id_' = [account_id_ EXCEPT ![self] = aid]
                           /\ Assert(account_id_'[self] \notin locks, 
                                     "Failure of assertion at line 240, column 13.")
                           /\ locks' = (locks \union {account_id_'[self]})
                           /\ neuron' = (account_id_'[self] :> [ cached_stake |-> 0, id |-> account_id_'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                           /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(account_id_'[self]))))
                      /\ pc' = [pc EXCEPT ![self] = "ClaimNeuron2"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, ledger_to_governance, 
                                      account_id_R, account_id_D, amount_, 
                                      to_account_, fees_amount, account_id_M, 
                                      maturity_to_merge, account_id, 
                                      to_account, amount_D, parent_account_id, 
                                      amount, child_account_id, balances, 
                                      nr_transfers >>

ClaimNeuron2(self) == /\ pc[self] = "ClaimNeuron2"
                      /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                           LET b == r.response_value.bal IN
                             /\ ledger_to_governance' = ledger_to_governance \ {r}
                             /\ IF b >= MIN_STAKE
                                   THEN /\ neuron' = [ neuron EXCEPT ![account_id_[self]] = [@ EXCEPT !.cached_stake = b ] ]
                                   ELSE /\ neuron' = [n \in DOMAIN(neuron) \ {account_id_[self]} |-> neuron[n] ]
                             /\ locks' = locks \ {account_id_[self]}
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, governance_to_ledger, 
                                      account_id_, account_id_R, account_id_D, 
                                      amount_, to_account_, fees_amount, 
                                      account_id_M, maturity_to_merge, 
                                      account_id, to_account, amount_D, 
                                      parent_account_id, amount, 
                                      child_account_id, balances, nr_transfers >>

Claim_Neuron(self) == ClaimNeuron1(self) \/ ClaimNeuron2(self)

RefreshNeuron1(self) == /\ pc[self] = "RefreshNeuron1"
                        /\ \E aid \in DOMAIN(neuron) \ locks:
                             /\ account_id_R' = [account_id_R EXCEPT ![self] = aid]
                             /\ locks' = (locks \union {account_id_R'[self]})
                             /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(account_id_R'[self]))))
                        /\ pc' = [pc EXCEPT ![self] = "RefreshNeuron2"]
                        /\ UNCHANGED << neuron, neuron_count, total_rewards, 
                                        minted, burned, ledger_to_governance, 
                                        account_id_, account_id_D, amount_, 
                                        to_account_, fees_amount, account_id_M, 
                                        maturity_to_merge, account_id, 
                                        to_account, amount_D, 
                                        parent_account_id, amount, 
                                        child_account_id, balances, 
                                        nr_transfers >>

RefreshNeuron2(self) == /\ pc[self] = "RefreshNeuron2"
                        /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                             LET b == r.response_value.bal IN
                               /\ ledger_to_governance' = ledger_to_governance \ {r}
                               /\ IF b >= MIN_STAKE
                                     THEN /\ Assert((b >= neuron[account_id_R[self]].cached_stake), 
                                                    "Failure of assertion at line 278, column 17.")
                                          /\ neuron' = [ neuron EXCEPT ![account_id_R[self]] = [@ EXCEPT !.cached_stake = b ] ]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED neuron
                               /\ locks' = locks \ {account_id_R[self]}
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                        burned, governance_to_ledger, 
                                        account_id_, account_id_R, 
                                        account_id_D, amount_, to_account_, 
                                        fees_amount, account_id_M, 
                                        maturity_to_merge, account_id, 
                                        to_account, amount_D, 
                                        parent_account_id, amount, 
                                        child_account_id, balances, 
                                        nr_transfers >>

Refresh_Neuron(self) == RefreshNeuron1(self) \/ RefreshNeuron2(self)

DisburseNeuron1(self) == /\ pc[self] = "DisburseNeuron1"
                         /\ \E aid \in DOMAIN(neuron) \ locks:
                              \E amt \in 0..neuron[aid].cached_stake:
                                /\ account_id_D' = [account_id_D EXCEPT ![self] = aid]
                                /\ amount_' = [amount_ EXCEPT ![self] = amt]
                                /\ fees_amount' = [fees_amount EXCEPT ![self] = neuron[account_id_D'[self]].fees]
                                /\ locks' = (locks \union {account_id_D'[self]})
                                /\ IF fees_amount'[self] > TRANSACTION_FEE
                                      THEN /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(account_id_D'[self], Minting_Account_Id, fees_amount'[self], 0))))
                                           /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron2"]
                                           /\ UNCHANGED neuron
                                      ELSE /\ IF neuron[account_id_D'[self]].cached_stake > fees_amount'[self]
                                                 THEN /\ neuron' = [neuron EXCEPT ![account_id_D'[self]] = [@ EXCEPT !.cached_stake = @ - fees_amount'[self], !.fees = 0]]
                                                 ELSE /\ neuron' = [neuron EXCEPT ![account_id_D'[self]] = [@ EXCEPT !.cached_stake = 0, !.fees = 0]]
                                           /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(account_id_D'[self], to_account_[self], calc_disburse_amount(amount_'[self], fees_amount'[self]), TRANSACTION_FEE))))
                                           /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron3"]
                         /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                         burned, ledger_to_governance, 
                                         account_id_, account_id_R, 
                                         to_account_, account_id_M, 
                                         maturity_to_merge, account_id, 
                                         to_account, amount_D, 
                                         parent_account_id, amount, 
                                         child_account_id, balances, 
                                         nr_transfers >>

DisburseNeuron2(self) == /\ pc[self] = "DisburseNeuron2"
                         /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                              /\ ledger_to_governance' = ledger_to_governance \ {answer}
                              /\ IF answer.response_value.status = TRANSFER_FAIL
                                    THEN /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                         /\ UNCHANGED << neuron, 
                                                         governance_to_ledger >>
                                    ELSE /\ IF neuron[account_id_D[self]].cached_stake > fees_amount[self]
                                               THEN /\ neuron' = [neuron EXCEPT ![account_id_D[self]] = [@ EXCEPT !.cached_stake = @ - fees_amount[self], !.fees = 0]]
                                               ELSE /\ neuron' = [neuron EXCEPT ![account_id_D[self]] = [@ EXCEPT !.cached_stake = 0, !.fees = 0]]
                                         /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(account_id_D[self], to_account_[self], calc_disburse_amount(amount_[self], fees_amount[self]), TRANSACTION_FEE))))
                                         /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron3"]
                         /\ UNCHANGED << locks, neuron_count, total_rewards, 
                                         minted, burned, account_id_, 
                                         account_id_R, account_id_D, amount_, 
                                         to_account_, fees_amount, 
                                         account_id_M, maturity_to_merge, 
                                         account_id, to_account, amount_D, 
                                         parent_account_id, amount, 
                                         child_account_id, balances, 
                                         nr_transfers >>

DisburseNeuron3(self) == /\ pc[self] = "DisburseNeuron3"
                         /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                              /\ ledger_to_governance' = ledger_to_governance \ {answer}
                              /\ IF answer.response_value.status = TRANSFER_FAIL
                                    THEN /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                         /\ UNCHANGED neuron
                                    ELSE /\ neuron' =       [neuron EXCEPT ![account_id_D[self]] = [@ EXCEPT !.cached_stake = saturating_sub(@,
                                                      calc_disburse_amount(amount_[self], fees_amount[self]) + TRANSACTION_FEE) ]]
                                         /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                         /\ UNCHANGED << locks, neuron_count, total_rewards, 
                                         minted, burned, governance_to_ledger, 
                                         account_id_, account_id_R, 
                                         account_id_D, amount_, to_account_, 
                                         fees_amount, account_id_M, 
                                         maturity_to_merge, account_id, 
                                         to_account, amount_D, 
                                         parent_account_id, amount, 
                                         child_account_id, balances, 
                                         nr_transfers >>

DisburseNeuronEnd(self) == /\ pc[self] = "DisburseNeuronEnd"
                           /\ locks' = locks \ {account_id_D[self]}
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << neuron, neuron_count, total_rewards, 
                                           minted, burned, 
                                           governance_to_ledger, 
                                           ledger_to_governance, account_id_, 
                                           account_id_R, account_id_D, amount_, 
                                           to_account_, fees_amount, 
                                           account_id_M, maturity_to_merge, 
                                           account_id, to_account, amount_D, 
                                           parent_account_id, amount, 
                                           child_account_id, balances, 
                                           nr_transfers >>

Disburse_Neuron(self) == DisburseNeuron1(self) \/ DisburseNeuron2(self)
                            \/ DisburseNeuron3(self)
                            \/ DisburseNeuronEnd(self)

MergeMaturity1(self) == /\ pc[self] = "MergeMaturity1"
                        /\ \E aid \in DOMAIN(neuron) \ locks:
                             \E maturity_to_merge_tmp \in (TRANSACTION_FEE+1)..neuron[aid].maturity:
                               /\ account_id_M' = [account_id_M EXCEPT ![self] = aid]
                               /\ maturity_to_merge' = [maturity_to_merge EXCEPT ![self] = maturity_to_merge_tmp]
                               /\ locks' = (locks \union {account_id_M'[self]})
                               /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(Minting_Account_Id, account_id_M'[self], maturity_to_merge'[self], 0))))
                        /\ pc' = [pc EXCEPT ![self] = "MergeMaturity2"]
                        /\ UNCHANGED << neuron, neuron_count, total_rewards, 
                                        minted, burned, ledger_to_governance, 
                                        account_id_, account_id_R, 
                                        account_id_D, amount_, to_account_, 
                                        fees_amount, account_id, to_account, 
                                        amount_D, parent_account_id, amount, 
                                        child_account_id, balances, 
                                        nr_transfers >>

MergeMaturity2(self) == /\ pc[self] = "MergeMaturity2"
                        /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                             /\ ledger_to_governance' = ledger_to_governance \ {answer}
                             /\ IF answer.response_value.status # TRANSFER_FAIL
                                   THEN /\ neuron' = [neuron EXCEPT ![account_id_M[self]] = [@ EXCEPT !.maturity = saturating_sub(@, maturity_to_merge[self]), !.cached_stake = @ + maturity_to_merge[self]]]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED neuron
                             /\ locks' = locks \ {account_id_M[self]}
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                        burned, governance_to_ledger, 
                                        account_id_, account_id_R, 
                                        account_id_D, amount_, to_account_, 
                                        fees_amount, account_id_M, 
                                        maturity_to_merge, account_id, 
                                        to_account, amount_D, 
                                        parent_account_id, amount, 
                                        child_account_id, balances, 
                                        nr_transfers >>

Merge_Maturity(self) == MergeMaturity1(self) \/ MergeMaturity2(self)

DisburseMaturityStart(self) == /\ pc[self] = "DisburseMaturityStart"
                               /\ \E aid \in DOMAIN(neuron) \ locks:
                                    \E tid \in Account_Ids:
                                      \E amt \in TRANSACTION_FEE + 1 .. neuron[aid].maturity:
                                        /\ account_id' = [account_id EXCEPT ![self] = aid]
                                        /\ to_account' = [to_account EXCEPT ![self] = tid]
                                        /\ amount_D' = [amount_D EXCEPT ![self] = amt]
                                        /\ locks' = (locks \union {account_id'[self]})
                                        /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(Minting_Account_Id, to_account'[self], amount_D'[self], 0))))
                               /\ pc' = [pc EXCEPT ![self] = "DisburseMaturityEnd"]
                               /\ UNCHANGED << neuron, neuron_count, 
                                               total_rewards, minted, burned, 
                                               ledger_to_governance, 
                                               account_id_, account_id_R, 
                                               account_id_D, amount_, 
                                               to_account_, fees_amount, 
                                               account_id_M, maturity_to_merge, 
                                               parent_account_id, amount, 
                                               child_account_id, balances, 
                                               nr_transfers >>

DisburseMaturityEnd(self) == /\ pc[self] = "DisburseMaturityEnd"
                             /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                                  /\ ledger_to_governance' = ledger_to_governance \ {answer}
                                  /\ neuron' = [ neuron EXCEPT ![account_id[self]] = [@ EXCEPT !.maturity = saturating_sub(@, amount_D[self]) ] ]
                                  /\ locks' = locks \ {account_id[self]}
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << neuron_count, total_rewards, 
                                             minted, burned, 
                                             governance_to_ledger, account_id_, 
                                             account_id_R, account_id_D, 
                                             amount_, to_account_, fees_amount, 
                                             account_id_M, maturity_to_merge, 
                                             account_id, to_account, amount_D, 
                                             parent_account_id, amount, 
                                             child_account_id, balances, 
                                             nr_transfers >>

Disburse_Maturity(self) == DisburseMaturityStart(self)
                              \/ DisburseMaturityEnd(self)

SplitNeuron1(self) == /\ pc[self] = "SplitNeuron1"
                      /\ \E aid \in DOMAIN(neuron) \ locks:
                           \E amt \in 0..neuron[aid].cached_stake:
                             \E cid \in Governance_Account_Ids:
                               /\ parent_account_id' = [parent_account_id EXCEPT ![self] = aid]
                               /\ amount' = [amount EXCEPT ![self] = amt]
                               /\ child_account_id' = [child_account_id EXCEPT ![self] = cid]
                               /\ (amount'[self] >= MIN_STAKE + TRANSACTION_FEE
                                   /\ neuron[parent_account_id'[self]].cached_stake - neuron[parent_account_id'[self]].fees >= MIN_STAKE + amount'[self])
                               /\ (cid \notin DOMAIN(neuron))
                               /\ Assert(child_account_id'[self] \notin locks, 
                                         "Failure of assertion at line 436, column 13.")
                               /\ locks' = (locks \union {parent_account_id'[self], child_account_id'[self]})
                               /\ neuron' = (child_account_id'[self] :> [ cached_stake |-> 0, id |-> child_account_id'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                               /\ governance_to_ledger' =                     Append(governance_to_ledger,
                                                          request(self, OP_TRANSFER, transfer(parent_account_id'[self], child_account_id'[self], amount'[self] - TRANSACTION_FEE, TRANSACTION_FEE)))
                      /\ pc' = [pc EXCEPT ![self] = "SplitNeuron2"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, ledger_to_governance, 
                                      account_id_, account_id_R, account_id_D, 
                                      amount_, to_account_, fees_amount, 
                                      account_id_M, maturity_to_merge, 
                                      account_id, to_account, amount_D, 
                                      balances, nr_transfers >>

SplitNeuron2(self) == /\ pc[self] = "SplitNeuron2"
                      /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                           /\ ledger_to_governance' = ledger_to_governance \ {answer}
                           /\ IF answer.response_value.status = TRANSFER_FAIL
                                 THEN /\ neuron' = [n \in DOMAIN(neuron) \ {child_account_id[self]} |-> neuron[n] ]
                                 ELSE /\ neuron' = [neuron EXCEPT ![parent_account_id[self]] = [@ EXCEPT !.cached_stake = @ - amount[self]],
                                                                     ![child_account_id[self]] = [@ EXCEPT !.cached_stake = amount[self] - TRANSACTION_FEE]]
                           /\ locks' = locks \ {child_account_id[self], parent_account_id[self]}
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, governance_to_ledger, 
                                      account_id_, account_id_R, account_id_D, 
                                      amount_, to_account_, fees_amount, 
                                      account_id_M, maturity_to_merge, 
                                      account_id, to_account, amount_D, 
                                      parent_account_id, amount, 
                                      child_account_id, balances, nr_transfers >>

Split_Neuron(self) == SplitNeuron1(self) \/ SplitNeuron2(self)

LedgerMainLoop == /\ pc[Ledger_Process_Id] = "LedgerMainLoop"
                  /\ \/ /\ (governance_to_ledger /= <<>>)
                        /\ LET req == Head(governance_to_ledger) IN
                             LET t == req.type IN
                               LET arg == req.args IN
                                 LET caller == req.caller IN
                                   /\ governance_to_ledger' = Tail(governance_to_ledger)
                                   /\ Assert((t \in {OP_QUERY_BALANCE, OP_TRANSFER}), 
                                             "Failure of assertion at line 482, column 21.")
                                   /\ IF t = OP_QUERY_BALANCE
                                         THEN /\ ledger_to_governance' = (ledger_to_governance \union {response(caller, ([bal |-> balances[arg.of_account]]))})
                                              /\ UNCHANGED << minted, burned, 
                                                              balances >>
                                         ELSE /\ IF t = OP_TRANSFER
                                                    THEN /\ LET from_acc == arg.from IN
                                                              LET to_acc == arg.to IN
                                                                LET amnt == arg.amount IN
                                                                  LET fee == arg.fee IN
                                                                    LET is_invalid_transfer == \/
                                                                                                (/\ from_acc /= Minting_Account_Id
                                                                                                 /\ to_acc /= Minting_Account_Id
                                                                                                 /\ fee < TRANSACTION_FEE
                                                                                                )
                                                                                               \/ (from_acc = Minting_Account_Id /\ to_acc = Minting_Account_Id)
                                                                                               \/ (from_acc = Minting_Account_Id /\ fee /= 0)
                                                                                               \/ (to_acc = Minting_Account_Id /\ fee /= 0)
                                                                                               \/ (to_acc = Minting_Account_Id /\ amnt < TRANSACTION_FEE)
                                                                                               \/ fee + amnt > balances[from_acc] IN
                                                                      /\ Assert((fee >= 0), 
                                                                                "Failure of assertion at line 505, column 29.")
                                                                      /\ IF is_invalid_transfer
                                                                            THEN /\ ledger_to_governance' = (ledger_to_governance \union {response(caller, ([status |-> TRANSFER_FAIL]))})
                                                                                 /\ UNCHANGED << minted, 
                                                                                                 burned, 
                                                                                                 balances >>
                                                                            ELSE /\ balances' = [balances EXCEPT ![from_acc] = balances[from_acc] - (fee + amnt),
                                                                                                                 ![to_acc] = balances[to_acc] + amnt]
                                                                                 /\ ledger_to_governance' = (ledger_to_governance \union {response(caller, ([status |-> TRANSFER_OK]))})
                                                                                 /\ burned' = burned + fee + (IF to_acc = Minting_Account_Id THEN amnt ELSE 0)
                                                                                 /\ IF from_acc = Minting_Account_Id
                                                                                       THEN /\ minted' = minted + amnt
                                                                                       ELSE /\ TRUE
                                                                                            /\ UNCHANGED minted
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << minted, 
                                                                         burned, 
                                                                         ledger_to_governance, 
                                                                         balances >>
                        /\ UNCHANGED nr_transfers
                     \/ /\ nr_transfers < NUMBER_OF_TRANSFERS_CAP
                        /\ \E sender \in { a \in Account_Ids \ Governance_Account_Ids : balances[a] > 0 }:
                             \E amnt \in 1..balances[sender]:
                               \E recipient \in Governance_Account_Ids:
                                 /\ balances' = [balances EXCEPT ![sender] = @ - amnt, ![recipient] = @ + amnt]
                                 /\ nr_transfers' = nr_transfers + 1
                        /\ UNCHANGED <<minted, burned, governance_to_ledger, ledger_to_governance>>
                  /\ pc' = [pc EXCEPT ![Ledger_Process_Id] = "LedgerMainLoop"]
                  /\ UNCHANGED << neuron, locks, neuron_count, total_rewards, 
                                  account_id_, account_id_R, account_id_D, 
                                  amount_, to_account_, fees_amount, 
                                  account_id_M, maturity_to_merge, account_id, 
                                  to_account, amount_D, parent_account_id, 
                                  amount, child_account_id >>

Ledger == LedgerMainLoop

Change_Neuron_Fee1(self) == /\ pc[self] = "Change_Neuron_Fee1"
                            /\ \E nid \in DOMAIN(neuron):
                                 \E new_fee_value \in 0..Min(MAX_NEURON_FEE, neuron[nid].cached_stake):
                                   neuron' = [neuron EXCEPT ![nid] = [@ EXCEPT !.fees = new_fee_value]]
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << locks, neuron_count, total_rewards, 
                                            minted, burned, 
                                            governance_to_ledger, 
                                            ledger_to_governance, account_id_, 
                                            account_id_R, account_id_D, 
                                            amount_, to_account_, fees_amount, 
                                            account_id_M, maturity_to_merge, 
                                            account_id, to_account, amount_D, 
                                            parent_account_id, amount, 
                                            child_account_id, balances, 
                                            nr_transfers >>

Change_Neuron_Fee(self) == Change_Neuron_Fee1(self)

Increase_Neuron_Maturity1(self) == /\ pc[self] = "Increase_Neuron_Maturity1"
                                   /\ \E nid \in DOMAIN(neuron):
                                        \E new_maturity \in (neuron[nid].maturity+1)..MAX_MATURITY:
                                          /\ total_rewards' = total_rewards + new_maturity - neuron[nid].maturity
                                          /\ neuron' = [neuron EXCEPT ![nid] = [@ EXCEPT !.maturity = new_maturity]]
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << locks, neuron_count, minted, 
                                                   burned, 
                                                   governance_to_ledger, 
                                                   ledger_to_governance, 
                                                   account_id_, account_id_R, 
                                                   account_id_D, amount_, 
                                                   to_account_, fees_amount, 
                                                   account_id_M, 
                                                   maturity_to_merge, 
                                                   account_id, to_account, 
                                                   amount_D, parent_account_id, 
                                                   amount, child_account_id, 
                                                   balances, nr_transfers >>

Increase_Neuron_Maturity(self) == Increase_Neuron_Maturity1(self)

Idle_ == /\ pc[Idle_Process_Id] = "Idle_"
         /\      (
                /\ \A p \in Claim_Neuron_Process_Ids: pc[p] = "Done"
                /\ \A p \in Refresh_Neuron_Process_Ids: pc[p] = "Done"
                /\ \A p \in Disburse_Neuron_Process_Ids: pc[p] = "Done"
                /\
                    \/ \A p \in Disburse_Maturity_Process_Ids: pc[p] = "Done"
                    \/ \A n \in DOMAIN(neuron): neuron[n].maturity <= TRANSACTION_FEE
                /\
                    \/ \A p \in Merge_Maturity_Process_Ids: pc[p] = "Done"
                    \/ \A n \in DOMAIN(neuron): neuron[n].maturity <= TRANSACTION_FEE
                /\
                    \/ \A p \in Split_Neuron_Process_Ids: pc[p] = "Done"
                    \/ \A n \in DOMAIN(neuron): neuron[n].cached_stake - neuron[n].fees < 2 * MIN_STAKE + TRANSACTION_FEE
            )
         /\ pc' = [pc EXCEPT ![Idle_Process_Id] = "Idle_"]
         /\ UNCHANGED << neuron, locks, neuron_count, total_rewards, minted, 
                         burned, governance_to_ledger, ledger_to_governance, 
                         account_id_, account_id_R, account_id_D, amount_, 
                         to_account_, fees_amount, account_id_M, 
                         maturity_to_merge, account_id, to_account, amount_D, 
                         parent_account_id, amount, child_account_id, balances, 
                         nr_transfers >>

Idle == Idle_

Next == Ledger \/ Idle
           \/ (\E self \in Claim_Neuron_Process_Ids: Claim_Neuron(self))
           \/ (\E self \in Refresh_Neuron_Process_Ids: Refresh_Neuron(self))
           \/ (\E self \in Disburse_Neuron_Process_Ids: Disburse_Neuron(self))
           \/ (\E self \in Merge_Maturity_Process_Ids: Merge_Maturity(self))
           \/ (\E self \in Disburse_Maturity_Process_Ids: Disburse_Maturity(self))
           \/ (\E self \in Split_Neuron_Process_Ids: Split_Neuron(self))
           \/ (\E self \in Change_Neuron_Fee_Process_Ids: Change_Neuron_Fee(self))
           \/ (\E self \in Increase_Neuron_Maturity_Process_Ids: Increase_Neuron_Maturity(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

\* A sanity check: we can actually get a non-zero stake in a neuron
Can_Stake_Sanity == \A n \in DOMAIN(neuron) : neuron[n].cached_stake = 0

Cached_Stake_Capped_By_Balance == \A n \in DOMAIN(neuron) :
    neuron[n].cached_stake <= balances[neuron[n].account]

Cached_Stake_Capped_By_Balance_When_Not_Locked == \A n \in DOMAIN(neuron) :
    n \notin locks => neuron[n].cached_stake <= balances[n]

FoldSet(op(_,_), base, S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == (CHOOSE y \in s: TRUE)
             IN  op(x, iter[s \ {x}])
  IN  iter[S]

Sum(S) == FoldSet(LAMBDA x, y: x + y, 0, S)

\* @type: (a -> b) => Set(b);
Range(f) == { f[x] : x \in DOMAIN f }

Regular_Balances_Sum == Sum(Range([a \in DOMAIN(balances) \ {Minting_Account_Id} |-> balances[a]]))
Total_Balance_Is_Constant_Modulo_Fees == Regular_Balances_Sum + burned - minted = Regular_Balances_Sum' + burned' - minted'

\* this should prevent double spending of maturity
Total_Minting_Does_Not_Exceed_Rewards == minted <= total_rewards


Cached_Stake_Not_Underflowing == \A n \in DOMAIN(neuron): neuron[n].cached_stake >= 0

Neurons_Have_At_Least_Min_Stake == \A n \in DOMAIN(neuron) :
    n \notin locks => neuron[n].cached_stake >= MIN_STAKE

Full_Invariant ==   /\ Cached_Stake_Capped_By_Balance_When_Not_Locked
                    /\ Total_Minting_Does_Not_Exceed_Rewards
                    /\ Cached_Stake_Not_Underflowing


\* Other properties we may want to check:
\* Model fees increase/decrease and maturity increase with non-deterministic events;
\* guard for fees increase: shouldn't go higher than cached_stake (and not <0)
\* Properties of claim + disburse (combination)? 
\* Fees of a neuron should be <= to the balance on the ledger
\* Fees of a neuron should be <= to the cached stake?
\* We should somehow make sure that all fees are paid
\* Rewards should not be lost (exception: if they are smaller than the transaction_fee, they can get lost right now)
============================================
