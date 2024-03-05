A high-level model of the interaction between the governance and the ledger canisters.
The goal is to analyze the interleavings from multiple parallel calls to governance/ledger.
We're using PlusCal (aka +CAL) - more precisely, its C syntax - to specify the canister calls, as it takes care of process counters and local state in a readable fashion.

What's been modelled so far:

- the claim_neuron call
- (spontaneous) ledger transfers between user accounts
- ledger responses to balance queries

Note that the model currently deadlocks, due to a infinite loop in the ledger canister that we use to respond to calls to this canister.
This loop gets starved once no further calls are made.
Thus, turn off deadlock checking in TLC when analyzing this.

**********
Benchmarks
**********

Some numbers for the analysis on my laptop (MacBook Pro '19, 16 inch / 6-core i7):

| Type of calls | # of calls | Constants                 | # of Gov accounts | # of user accounts | Max initial |   Min | Symmetry | # States found/    | Diameter |     Time |
| considered    |            |                           |                   |                    |     balance | stake |          | distinct (million) |          |          |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim         |          2 | 2                         |                 2 |                  2 |           2 |     1 | NO       | 0.14 / 0.04        |        9 |    00:02 |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim         |          2 | 2                         |                 3 |                  3 |           2 |     1 | NO       | 5 / 1              |        9 |    00:22 |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim         |          3 | 2                         |                 3 |                  3 |           2 |     1 | NO       | 143 / 27           |          |    10:00 |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim,        |          1 | Xfer cap = 2, max fee = 2 |                   |                    |             |       |          |                    |          |          |
| disburse,     |          1 | max matur = 2             |                 2 |                  2 |           2 |     1 | NO       | 239/36             |       18 |    21:13 |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim,        |          1 | Xfer cap = 2, max fee = 2 |                   |                    |             |       |          |                    |          |          |
| disburse      |          1 | max matur = 2             |                 2 |                  2 |           2 |     1 | YES      | 14/6               |       18 |    05:30 |
 

Here are numbers from fr-dll17. I haven't noted down the number of cores, but unfortunately it doesn't affect the results that much.


| Type of calls | # of calls | Constants                 | # of Gov accounts | # of user accounts | Max initial |   Min | Symmetry | # States found/    | Diameter |     Time |
| considered    |            |                           |                   |                    |     balance | stake |          | distinct (million) |          |          |
|---------------+------------+---------------------------+-------------------+--------------------+-------------+-------+----------+--------------------+----------+----------|
| claim,        |          2 | Xfer cap = 2, max fee = 2 |                 2 |                  2 |           2 |     1 | YES      | 22960/3964         |       29 | 10:17:00 |
| disburse,     |          2 | max matur = 2             |                   |                    |             |       |          |                    |          |          |


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
    -tool -modelcheck -config Governance.cfg -deadlock -workers 54 -checkpoint 0

This:
    - uses the symmetry relation defined in Governance_TLC
    - runs TLC with 54 workers (i.e., 54 cores)
    - uses fingerprint set and queue implementations that are optimized for concurrency
    - allocates 100G heap to the JVM
    - doesn't check for deadlock
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

\* TODO: this documentation should be updated to not refer to Merge_Maturity_Of_Neuron
The model deviates from the Rust implementation by (among other things) employing some optimizations.
In particular, validity checks (e.g., in Merge_Maturity_Of_Neuron) over method parameters are often 
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
    Spawn_Neuron_Process_Ids, 
    \* @type: Set(PROC);
    Disburse_To_Neuron_Process_Ids,
    \* @type: Set(PROC);
    Split_Neuron_Process_Ids,
    \* @type: Set(PROC);
    Merge_Neurons_Process_Ids,
    \* @type: PROC;
    Ledger_Process_Id,
    \* @type: Set(PROC);
    Change_Neuron_Fee_Process_Ids,
    \* @type: Set(PROC);
    Increase_Neuron_Maturity_Process_Ids

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
Neuron_Creating_Processes == UNION { Claim_Neuron_Process_Ids, Split_Neuron_Process_Ids, Spawn_Neuron_Process_Ids, Disburse_To_Neuron_Process_Ids }
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

calc_disburse_amount(amount, fees_amount) == LET
        diff == amount - fees_amount
    IN
        IF diff > TRANSACTION_FEE THEN diff - TRANSACTION_FEE ELSE diff

to_deduct(disb_amount) == disb_amount + TRANSACTION_FEE

(* --algorithm Governance_Ledger_Interaction {

\* +Cal note: To be able to mutate variables from +Cal, it seems we have to define them in the algorithm block
\* +Cal note: "variable/variables" has to be lowercase (the TLA+ version is uppercase)
\* +Cal note: All of the following are variables

\* The neuron state kept by the governance canister. We're recording this as a global variable, and not a process
\* since we use processes to model method calls on the governance canister
variables neuron \in [{} -> {}];

\* Used to decide whether we should refresh or claim a neuron
neuron_id_by_account \in [{} -> {}];

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

macro add_neuron(neuron_id, account_id) {
    neuron := neuron_id :> [ cached_stake |-> 0, account |-> account_id, fees |-> 0, maturity |-> 0 ] @@ neuron;
    neuron_id_by_account := account_id :> neuron_id @@ neuron_id_by_account;
}
macro remove_neuron(neuron_id, account_id) {
    neuron := [n \in DOMAIN(neuron) \ {neuron_id} |-> neuron[n] ];
    neuron_id_by_account := [a \in DOMAIN(neuron_id_by_account) \ {account_id} |-> neuron_id_by_account[a] ];
}

\* A Claim_Neuron process simulates a call to claim_neuron
process ( Claim_Neuron \in Claim_Neuron_Process_Ids )
    variable 
        \* The account_id is an argument to the canister call; we let it be chosen non-deteministically 
        account_id = Minting_Account_Id;
        \* The neuron_id will be set later on to a fresh value
        neuron_id = 0;
    { 
    ClaimNeuron1:
        with(aid \in  Governance_Account_Ids \ DOMAIN(neuron_id_by_account)) {
            account_id := aid;
            \* Get a fresh neuron ID
            neuron_id := neuron_count;
            neuron_count := neuron_count + 1;
            \* The Rust code tries to obtain a lock; this should always succeed, as the 
            \* neuron has just been created in the same atomic block. We'll call assert
            \* instead of await here, to check that
            assert neuron_id \notin locks;
            locks := locks \union {neuron_id};
            add_neuron(neuron_id, account_id);
            send_request(self, OP_QUERY_BALANCE, balance_query(account_id));
        };

    ClaimNeuron2:
        \* Note that the "with" construct implicitly awaits until the set of values to draw from is non-empty
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; b = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};
            if(b >= MIN_STAKE) {
                neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = b] ]
            } else {
                remove_neuron(neuron_id, account_id);
            };
            locks := locks \ {neuron_id};
        };
    }

process ( Refresh_Neuron \in Refresh_Neuron_Process_Ids )
    variable 
        account_id = Minting_Account_Id;
        neuron_id = 0;
    {
    RefreshNeuron1:
        \* There are two ways that the user can invoke a neuron refresh: 
        \* 1. by specifying an account ID
        \* 2. by specifying an existing neuron ID
        \* We only model the second option; the second should follow from the invariant that 
        \* \A nid aid : neuron_id_by_account[aid] = nid <=> neuron[nid].account = aid
        with(nid \in DOMAIN(neuron) \ locks) {
            neuron_id := nid;
            account_id := neuron[nid].account;
            locks := locks \union {neuron_id};
            send_request(self, OP_QUERY_BALANCE, balance_query(account_id));
        };

    RefreshNeuron2:
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; b = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};
            if(b >= MIN_STAKE) {
                assert(b >= neuron[neuron_id].cached_stake);
                neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = b] ];
            };
            \* If b < MIN_STAKE, the code returns an error in this case, releasing the lock. 
            \* We model this with just a skip (i.e., the missing else branch)
            locks := locks \ {neuron_id};
        };
    }

process ( Disburse_Neuron \in Disburse_Neuron_Process_Ids )
    variable
        \* These model the parameters of the call
        neuron_id = 0;
        amount = 0;
        to_account \in Account_Ids;
        \* The model the internal variables of the procedure.
        \* Since +Cal doesn't allow multiple assignments to the same variable in a single block,
        \* we also use temporary variables to simulate this and stay closer to the source code
        fees_amount = 0;
        \* Whether an error was returned by a call to a ledger canister
        error = FALSE;
    {
    DisburseNeuron1:
        \* This models a few checks at the start of the Rust code.
        \* We currently omit the check that the neuron is dissolved, and we plan to add this later.
        \* We omit the other checks: who the caller is, whether the neuron is KYC verified, as well
        \* as a few well-formedness checks (of the neuron and recipient account) as everything in
        \* our model is well-formed.
        with(nid \in DOMAIN(neuron) \ locks; amt \in 0..neuron[nid].cached_stake) {
            neuron_id := nid;
            amount := amt;
            fees_amount := neuron[neuron_id].fees;
            \* The Rust code has a more elaborate code path to determine the disburse_amount, where the
            \* amount argument is left unspecified in the call, and a default value is computed instead.
            \* As this default value is in the range between 0 and the neuron's cached_stake, our 
            \* non-deterministic choice should cover this case.
            \* The Rust code throws an error here if the neuron is locked. Instead, we prevent the Disburse_Neuron process from running.
            \* This is OK since the Rust code doesn't change the canister's state before obtaining the lock (if it
            \* did, the model wouldn't capture this and we could miss behaviors).
            locks := locks \union {neuron_id};
            if(fees_amount > TRANSACTION_FEE) {
                send_request(self, OP_TRANSFER, transfer(neuron[neuron_id].account, Minting_Account_Id, fees_amount, 0));
            }
            else {
                \* There's some code duplication here, but having to have the with statement
                \* span entire blocks to please Apalache, I don't have a better solution at the moment
                update_fees(neuron_id, fees_amount);
                send_request(self, OP_TRANSFER, transfer(neuron[neuron_id].account, to_account, calc_disburse_amount(amount, fees_amount), TRANSACTION_FEE));
                goto DisburseNeuron3;
            };
        };
   
    DisburseNeuron2:
        \* Note that we're here only because the fees amount was larger than the
        \* transaction fee (otherwise, the goto above would have taken us to DisburseNeuron3)
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL){
                error := TRUE;
                goto DisburseNeuronEnd;
            }
            else {
                update_fees(neuron_id, fees_amount);
                send_request(self, OP_TRANSFER, transfer(neuron[neuron_id].account, to_account, calc_disburse_amount(amount, fees_amount), TRANSACTION_FEE));
            };
        };

    DisburseNeuron3:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL) {
                error := TRUE;
                goto DisburseNeuronEnd;
            } 
            else {
                if(to_deduct(calc_disburse_amount(amount, fees_amount)) >= neuron[neuron_id].cached_stake) {
                    neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = 0]];
                } else {
                    neuron := [neuron EXCEPT ![neuron_id] = [@ EXCEPT !.cached_stake = @ - to_deduct(calc_disburse_amount(amount, fees_amount))]];
                };
            };
        };

    \* This label introduces an additional interleaving point not present in
    \* the Rust code, but it doesn't interfere with the soundness of our abstraction.
    \* Worst case, we'll get some spurious counterexamples.
    DisburseNeuronEnd:
        locks := locks \ {neuron_id};
    }

process (Spawn_Neuron \in Spawn_Neuron_Process_Ids)
    variables
        parent_neuron_id = 0;
        child_neuron_id = 0;
        child_stake = 0;
        child_account_id = Minting_Account_Id;

    {
    SpawnNeuronStart:
        \* A few checks are skipped here:
        \* 1. that the heap can grow
        \* 2. that the caller controls the parent neuron
        \* 3. That the child controller is valid
        with(nid \in DOMAIN(neuron) \ locks; c_acc_id \in Governance_Account_Ids \ {neuron[n].account : n \in DOMAIN(neuron)}) {
            parent_neuron_id := nid;
            child_account_id := c_acc_id;
            child_stake := neuron[parent_neuron_id].maturity;
            await child_stake >= MIN_STAKE;

            child_neuron_id := neuron_count;
            neuron_count := neuron_count + 1;

            add_neuron(child_neuron_id, child_account_id);
            \* The Rust code throws an error here if the neuron is locked. Instead, we prevent the Spawn_Neuron process from running.
            \* This is OK since the Rust code doesn't change the canister's state before obtaining the parant lock (if it
            \* did, the model wouldn't capture this state and we could miss behaviors).

            \* The code takes a lock on the child neuron. As this neuron should
            \* not be locked at this point, as a sanity check, we make this into
            \* an assertion in our model.
            assert child_neuron_id \notin locks;
            \* Note that in the implementation this implies that child_neuron_id != parent_neuron_id,
            \* as the locks are taken sequentially there; here, we're sure that these neuron IDs differ,
            \* so we omit the extra check.
            locks := locks \union {parent_neuron_id, child_neuron_id};
            send_request(self, OP_TRANSFER, transfer(Minting_Account_Id, child_account_id, child_stake, 0));
        };

    SpawnNeuronEnd:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
                ledger_to_governance := ledger_to_governance \ {answer};
                if(answer.response_value.status = TRANSFER_FAIL){
                    remove_neuron(child_neuron_id, child_account_id);
                } else {
                    neuron := [ neuron EXCEPT ![parent_neuron_id] = [@ EXCEPT !.maturity = @ - child_stake ],
                        ![child_neuron_id] = [@ EXCEPT !.cached_stake = child_stake] ];
                };
                locks := locks \ {parent_neuron_id, child_neuron_id};
        };
 
    }

process (Disburse_To_Neuron \in Disburse_To_Neuron_Process_Ids)
    variables
        parent_neuron_id = 0;
        disburse_amount = 0;
        child_account_id = Minting_Account_Id;
        child_neuron_id = 0;
    {
    DisburseToNeuron1:
        \* Skipping a few checks again:
        \* 1. authorization of the caller
        \* 2. that the parent neuron has been dissolved
        \* 3. kyc checks
        \* 4. checks on the presence and shape of new controller
        with(nid \in DOMAIN(neuron) \ locks; 
                parent_neuron = neuron[nid]; 
                amt \in (MIN_STAKE + TRANSACTION_FEE)..(parent_neuron.cached_stake - parent_neuron.fees - MIN_STAKE);
                c_acc_id \in Governance_Account_Ids \ { neuron[n].account : n \in DOMAIN(neuron)};
            ) {
            parent_neuron_id := nid;
            disburse_amount := amt;
            await parent_neuron.maturity <= TRANSACTION_FEE;
            child_account_id := c_acc_id;
            child_neuron_id := neuron_count;
            neuron_count := neuron_count + 1;
            add_neuron(child_neuron_id, child_account_id);
            \* The Rust code throws an error here if the parent neuron is locked. Instead, we prevent the Disburse_To_Neuron process from running.
            \* This is OK since the Rust code doesn't change the canister's state before obtaining the parant lock (if it
            \* did, the model wouldn't capture this state and we could miss behaviors).
            assert child_neuron_id \notin locks;
            \* Note that in the implementation this implies that child_neuron_id != parent_neuron_id,
            \* as the locks are taken sequentially there; here, we're sure that these neuron IDs differ,
            \* so we omit the extra check.
            locks := locks \union {parent_neuron_id, child_neuron_id};
            send_request(self, OP_TRANSFER, transfer(parent_neuron.account, child_account_id, disburse_amount - TRANSACTION_FEE, TRANSACTION_FEE));
        };
    DisburseToNeuronEnd:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
                ledger_to_governance := ledger_to_governance \ {answer};
                if(answer.response_value.status = TRANSFER_FAIL){
                    remove_neuron(child_neuron_id, child_account_id);
                } else {
                    neuron := [ neuron EXCEPT ![parent_neuron_id] = [@ EXCEPT !.cached_stake = @ - disburse_amount ],
                        ![child_neuron_id] = [@ EXCEPT !.cached_stake = disburse_amount - TRANSACTION_FEE] ];
                };
                locks := locks \ {parent_neuron_id, child_neuron_id};
        };
 
    }

process ( Split_Neuron \in Split_Neuron_Process_Ids )
    variable
        parent_neuron_id = 0;
        amount = 0;

        \* internal variables
        child_neuron_id = 0;
        child_account_id = Minting_Account_Id;

    {
    SplitNeuron1:
        \* Need to make sure there is an element of Split_Neuron_Account_Ids for each
        \* member of Split_Neuron_Process_Ids
        with(nid \in DOMAIN(neuron) \ locks; 
             amt \in 0..neuron[nid].cached_stake; 
             fresh_account_id \in Governance_Account_Ids \ {neuron[n].account : n \in DOMAIN(neuron)}) {
            parent_neuron_id := nid;
            amount := amt;
            child_account_id := fresh_account_id;

            \* Get a fresh neuron ID
            child_neuron_id := neuron_count;
            neuron_count := neuron_count + 1;
            assert child_neuron_id \notin locks;  \* should be redundant

            \* create empty child neuron
            add_neuron(child_neuron_id, child_account_id);

            await(amount >= MIN_STAKE + TRANSACTION_FEE /\ neuron[parent_neuron_id].cached_stake - neuron[parent_neuron_id].fees >= MIN_STAKE + amount);
            \* Note that in the implementation this implies that child_neuron_id != parent_neuron_id,
            \* as the locks are taken sequentially there; here, we're sure that these neuron IDs differ,
            \* so we omit the extra check.
            locks := locks \union {parent_neuron_id, child_neuron_id};

            governance_to_ledger := Append(governance_to_ledger, 
                request(self, OP_TRANSFER, transfer(neuron[parent_neuron_id].account, neuron[child_neuron_id].account, amount - TRANSACTION_FEE, TRANSACTION_FEE)));
        };
    SplitNeuron2:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL) {
                remove_neuron(child_neuron_id, child_account_id);
            } else {
                \* the rust impl should but does not use saturating arithmetic.
                neuron := [neuron EXCEPT ![parent_neuron_id] = [@ EXCEPT !.cached_stake = @ - amount], 
                                            ![child_neuron_id] = [@ EXCEPT !.cached_stake = amount - TRANSACTION_FEE]];
            };
            locks := locks \ {child_neuron_id, parent_neuron_id};
        };
    };

\* https://gitlab.com/dfinity-lab/core/ic/-/merge_requests/1184/diffs
process ( Merge_Neurons \in Merge_Neurons_Process_Ids )
    variable
        \* These model the parameters of the call
        source_neuron_id = 0;
        target_neuron_id = 0;

        \* internal variables
        fees_amount = 0;
        target_balance = 0;
    {
    MergeNeurons1:
        with(source_nid \in DOMAIN(neuron) \ locks; target_nid \in DOMAIN(neuron) \ locks) {
            \* stopgap error handling; for now we simply stop the process where an error would be returned
            await source_nid /= target_nid;
            source_neuron_id := source_nid;
            target_neuron_id := target_nid;

            \* Note that in the implementation this implies that child_neuron_id != parent_neuron_id,
            \* as the locks are taken sequentially there; here, we're sure that these neuron IDs differ,
            \* We have the explicit check earlier in this method that covers this.
            locks := locks \union {source_neuron_id, target_neuron_id};

            \* here the impl has a few guards:
            \* - caller must be controller of both source and target.
            \* - source must be younger than target
            \* - kyc_verified must match for both source and target
            \* - not_for_profit must match for both source and target
            \* - source neuron cannot be dedicated to community fund

            \* total stake cannot equal 0
            await (neuron[source_neuron_id].cached_stake - neuron[source_neuron_id].fees) +
                (neuron[target_neuron_id].cached_stake - neuron[target_neuron_id].fees) /= 0;

            fees_amount := neuron[source_neuron_id].fees;
            if(fees_amount > TRANSACTION_FEE) {
                send_request(self, OP_TRANSFER, transfer(neuron[source_neuron_id].account, Minting_Account_Id, fees_amount, 0));
            }
            else {
                \* There's some code duplication here, but having to have the with statement
                \* span entire blocks to please Apalache, I don't have a better solution at the moment
                update_fees(neuron_id, fees_amount);
                send_request(self, OP_TRANSFER,
                        transfer(neuron[source_neuron_id].account,
                            neuron[target_neuron_id].account,
                            (neuron[source_neuron_id].cached_stake - neuron[source_neuron_id].fees) - TRANSACTION_FEE,
                            TRANSACTION_FEE));
                goto MergeNeurons3;
            };
        };
    MergeNeurons2:
        \* Note that we're here only because the fees amount was larger than the
        \* transaction fee (otherwise, the goto above would have taken us to MergeNeurons3)
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL){
                error := TRUE;
                goto MergeNeurons6;
            }
            else {
                update_fees(neuron_id, fees_amount);
                send_request(self, OP_TRANSFER,
                        transfer(neuron[source_neuron_id].account,
                            neuron[target_neuron_id].account,
                            (neuron[source_neuron_id].cached_stake - neuron[source_neuron_id].fees) - TRANSACTION_FEE,
                            TRANSACTION_FEE));
            };
        };

    MergeNeurons3:
        with(answer \in { resp \in ledger_to_governance: resp.caller = self}) {
            ledger_to_governance := ledger_to_governance \ {answer};
            if(answer.response_value.status = TRANSFER_FAIL) {
                goto MergeNeurons5;
            } else {
                send_request(self, OP_QUERY_BALANCE, balance_query(neuron[target_neuron_id].account));
            };
        };
    MergeNeurons4:
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; b = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};
            target_balance := b;
            send_request(self, OP_QUERY_BALANCE, balance_query(neuron[source_neuron_id].account));
        };
    MergeNeurons5:
        with(r \in { r2 \in ledger_to_governance : r2.caller = self }; source_balance = r.response_value.bal ) {
            ledger_to_governance := ledger_to_governance \ {r};

            if (target_balance /= (
                    (neuron[source_neuron_id].cached_stake - neuron[source_neuron_id].fees)
                    + (neuron[target_neuron_id].cached_stake - neuron[target_neuron_id].fees)
                    - TRANSACTION_FEE)
                \/ source_balance /= 0) {
                \* This error path causes an exploitable violation of Cached_Stake_Capped_By_Balance_When_Not_Locked.
                \* This error path should be reachable by the following:
                \* - having nonzero fees on the target neuron
                \* - sending tokens to the target or source neuron after MergeNeurons1 but before MergeNeruons2 or MergeNeurons3.
                goto MergeNeurons6;
            } else {
                \* There seems to be a bug in the impl that the source fees are not reset. User is at disadvantage since fees
                \* will be double-counted.
                neuron := [neuron EXCEPT
                    ![target_neuron_id] = [@ EXCEPT !.cached_stake = @ +
                        (neuron[source_neuron_id].cached_stake - neuron[source_neuron_id].fees) - TRANSACTION_FEE,
                        !.maturity = @ + neuron[source_neuron_id].maturity],
                    ![source_neuron_id] = [@ EXCEPT !.cached_stake = 0, !.maturity = 0]];
            };
        };
    MergeNeurons6:
        locks := locks \ {source_neuron_id, target_neuron_id};
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
        \* limiting their number. An unfortunate side-effect of this is that the model deadlocks once
        \* all the governance canister calls have been processed.
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
}

*)

\* BEGIN TRANSLATION (chksum(pcal) = "633ab0bc" /\ chksum(tla) = "5068426")
\* Process variable account_id of process Claim_Neuron at line 278 col 9 changed to account_id_
\* Process variable neuron_id of process Claim_Neuron at line 280 col 9 changed to neuron_id_
\* Process variable neuron_id of process Refresh_Neuron at line 313 col 9 changed to neuron_id_R
\* Process variable neuron_id of process Disburse_Neuron at line 344 col 9 changed to neuron_id_D
\* Process variable amount of process Disburse_Neuron at line 345 col 9 changed to amount_
\* Process variable parent_neuron_id of process Spawn_Neuron at line 445 col 9 changed to parent_neuron_id_
\* Process variable child_neuron_id of process Spawn_Neuron at line 446 col 9 changed to child_neuron_id_
\* Process variable child_account_id of process Spawn_Neuron at line 448 col 9 changed to child_account_id_
\* Process variable parent_neuron_id of process Disburse_To_Neuron at line 497 col 9 changed to parent_neuron_id_D
\* Process variable child_account_id of process Disburse_To_Neuron at line 499 col 9 changed to child_account_id_D
\* Process variable child_neuron_id of process Disburse_To_Neuron at line 500 col 9 changed to child_neuron_id_D
VARIABLES neuron, neuron_id_by_account, locks, neuron_count, total_rewards, 
          minted, burned, governance_to_ledger, ledger_to_governance, pc, 
          account_id_, neuron_id_, account_id, neuron_id_R, neuron_id_D, 
          amount_, to_account, rewards_amount, fees_amount, error, 
          parent_neuron_id_, child_neuron_id_, child_stake, child_account_id_, 
          parent_neuron_id_D, disburse_amount, child_account_id_D, 
          child_neuron_id_D, neuron_id, maturity_to_merge, parent_neuron_id, 
          amount, child_neuron_id, child_account_id, source_neuron_id, 
          target_neuron_id, target_balance, balances, nr_transfers

vars == << neuron, neuron_id_by_account, locks, neuron_count, total_rewards, 
           minted, burned, governance_to_ledger, ledger_to_governance, pc, 
           account_id_, neuron_id_, account_id, neuron_id_R, neuron_id_D, 
           amount_, to_account, rewards_amount, fees_amount, error, 
           parent_neuron_id_, child_neuron_id_, child_stake, 
           child_account_id_, parent_neuron_id_D, disburse_amount, 
           child_account_id_D, child_neuron_id_D, neuron_id, 
           maturity_to_merge, parent_neuron_id, amount, child_neuron_id, 
           child_account_id, source_neuron_id, target_neuron_id, 
           target_balance, balances, nr_transfers >>

ProcSet == (Claim_Neuron_Process_Ids) \cup (Refresh_Neuron_Process_Ids) \cup (Disburse_Neuron_Process_Ids) \cup (Spawn_Neuron_Process_Ids) \cup (Disburse_To_Neuron_Process_Ids) \cup (Merge_Maturity_Of_Neuron_Process_Ids) \cup (Split_Neuron_Process_Ids) \cup (Merge_Neurons_Process_Ids) \cup {Ledger_Process_Id} \cup (Change_Neuron_Fee_Process_Ids) \cup (Increase_Neuron_Maturity_Process_Ids)

Init == (* Global variables *)
        /\ neuron \in [{} -> {}]
        /\ neuron_id_by_account \in [{} -> {}]
        /\ locks = {}
        /\ neuron_count = 0
        /\ total_rewards = 0
        /\ minted = 0
        /\ burned = 0
        /\ governance_to_ledger = <<>>
        /\ ledger_to_governance = {}
        (* Process Claim_Neuron *)
        /\ account_id_ = [self \in Claim_Neuron_Process_Ids |-> Minting_Account_Id]
        /\ neuron_id_ = [self \in Claim_Neuron_Process_Ids |-> 0]
        (* Process Refresh_Neuron *)
        /\ account_id = [self \in Refresh_Neuron_Process_Ids |-> Minting_Account_Id]
        /\ neuron_id_R = [self \in Refresh_Neuron_Process_Ids |-> 0]
        (* Process Disburse_Neuron *)
        /\ neuron_id_D = [self \in Disburse_Neuron_Process_Ids |-> 0]
        /\ amount_ = [self \in Disburse_Neuron_Process_Ids |-> 0]
        /\ to_account \in [Disburse_Neuron_Process_Ids -> Account_Ids]
        /\ rewards_amount = [self \in Disburse_Neuron_Process_Ids |-> 0]
        /\ fees_amount = [self \in Disburse_Neuron_Process_Ids |-> 0]
        /\ error = [self \in Disburse_Neuron_Process_Ids |-> FALSE]
        (* Process Spawn_Neuron *)
        /\ parent_neuron_id_ = [self \in Spawn_Neuron_Process_Ids |-> 0]
        /\ child_neuron_id_ = [self \in Spawn_Neuron_Process_Ids |-> 0]
        /\ child_stake = [self \in Spawn_Neuron_Process_Ids |-> 0]
        /\ child_account_id_ = [self \in Spawn_Neuron_Process_Ids |-> Minting_Account_Id]
        (* Process Disburse_To_Neuron *)
        /\ parent_neuron_id_D = [self \in Disburse_To_Neuron_Process_Ids |-> 0]
        /\ disburse_amount = [self \in Disburse_To_Neuron_Process_Ids |-> 0]
        /\ child_account_id_D = [self \in Disburse_To_Neuron_Process_Ids |-> Minting_Account_Id]
        /\ child_neuron_id_D = [self \in Disburse_To_Neuron_Process_Ids |-> 0]
        (* Process Merge_Maturity_Of_Neuron *)
        /\ neuron_id = [self \in Merge_Maturity_Of_Neuron_Process_Ids |-> 0]
        /\ maturity_to_merge = [self \in Merge_Maturity_Of_Neuron_Process_Ids |-> 0]
        (* Process Split_Neuron *)
        /\ parent_neuron_id = [self \in Split_Neuron_Process_Ids |-> 0]
        /\ amount = [self \in Split_Neuron_Process_Ids |-> 0]
        /\ child_neuron_id = [self \in Split_Neuron_Process_Ids |-> 0]
        /\ child_account_id = [self \in Split_Neuron_Process_Ids |-> Minting_Account_Id]
        (* Process Merge_Neurons *)
        /\ source_neuron_id = [self \in Merge_Neurons_Process_Ids |-> 0]
        /\ target_neuron_id = [self \in Merge_Neurons_Process_Ids |-> 0]
        /\ target_balance = [self \in Merge_Neurons_Process_Ids |-> 0]
        (* Process Ledger *)
        /\ balances = [a \in Governance_Account_Ids \union {Minting_Account_Id} |-> 0] @@ [a \in User_Account_Ids |-> INITIAL_MAX_BALANCE]
        /\ nr_transfers = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Claim_Neuron_Process_Ids -> "ClaimNeuron1"
                                        [] self \in Refresh_Neuron_Process_Ids -> "RefreshNeuron1"
                                        [] self \in Disburse_Neuron_Process_Ids -> "DisburseNeuron1"
                                        [] self \in Spawn_Neuron_Process_Ids -> "SpawnNeuronStart"
                                        [] self \in Disburse_To_Neuron_Process_Ids -> "DisburseToNeuron1"
                                        [] self \in Merge_Maturity_Of_Neuron_Process_Ids -> "MergeMaturityOfNeuron1"
                                        [] self \in Split_Neuron_Process_Ids -> "SplitNeuron1"
                                        [] self \in Merge_Neurons_Process_Ids -> "MergeNeurons1"
                                        [] self = Ledger_Process_Id -> "LedgerMainLoop"
                                        [] self \in Change_Neuron_Fee_Process_Ids -> "Change_Neuron_Fee1"
                                        [] self \in Increase_Neuron_Maturity_Process_Ids -> "Increase_Neuron_Maturity1"]

ClaimNeuron1(self) == /\ pc[self] = "ClaimNeuron1"
                      /\ \E aid \in Governance_Account_Ids \ DOMAIN(neuron_id_by_account):
                           /\ account_id_' = [account_id_ EXCEPT ![self] = aid]
                           /\ neuron_id_' = [neuron_id_ EXCEPT ![self] = neuron_count]
                           /\ neuron_count' = neuron_count + 1
                           /\ Assert(neuron_id_'[self] \notin locks, 
                                     "Failure of assertion at line 291, column 13.")
                           /\ locks' = (locks \union {neuron_id_'[self]})
                           /\ neuron' = (neuron_id_'[self] :> [ cached_stake |-> 0, account |-> account_id_'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                           /\ neuron_id_by_account' = (account_id_'[self] :> neuron_id_'[self] @@ neuron_id_by_account)
                           /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(account_id_'[self]))))
                      /\ pc' = [pc EXCEPT ![self] = "ClaimNeuron2"]
                      /\ UNCHANGED << total_rewards, minted, burned, 
                                      ledger_to_governance, account_id, 
                                      neuron_id_R, neuron_id_D, amount_, 
                                      to_account, rewards_amount, fees_amount, 
                                      error, parent_neuron_id_, 
                                      child_neuron_id_, child_stake, 
                                      child_account_id_, parent_neuron_id_D, 
                                      disburse_amount, child_account_id_D, 
                                      child_neuron_id_D, neuron_id, 
                                      maturity_to_merge, parent_neuron_id, 
                                      amount, child_neuron_id, 
                                      child_account_id, source_neuron_id, 
                                      target_neuron_id, target_balance, 
                                      balances, nr_transfers >>

ClaimNeuron2(self) == /\ pc[self] = "ClaimNeuron2"
                      /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                           LET b == r.response_value.bal IN
                             /\ ledger_to_governance' = ledger_to_governance \ {r}
                             /\ IF b >= MIN_STAKE
                                   THEN /\ neuron' = [neuron EXCEPT ![neuron_id_[self]] = [@ EXCEPT !.cached_stake = b] ]
                                        /\ UNCHANGED neuron_id_by_account
                                   ELSE /\ neuron' = [n \in DOMAIN(neuron) \ {neuron_id_[self]} |-> neuron[n] ]
                                        /\ neuron_id_by_account' = [a \in DOMAIN(neuron_id_by_account) \ {account_id_[self]} |-> neuron_id_by_account[a] ]
                             /\ locks' = locks \ {neuron_id_[self]}
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, governance_to_ledger, 
                                      account_id_, neuron_id_, account_id, 
                                      neuron_id_R, neuron_id_D, amount_, 
                                      to_account, rewards_amount, fees_amount, 
                                      error, parent_neuron_id_, 
                                      child_neuron_id_, child_stake, 
                                      child_account_id_, parent_neuron_id_D, 
                                      disburse_amount, child_account_id_D, 
                                      child_neuron_id_D, neuron_id, 
                                      maturity_to_merge, parent_neuron_id, 
                                      amount, child_neuron_id, 
                                      child_account_id, source_neuron_id, 
                                      target_neuron_id, target_balance, 
                                      balances, nr_transfers >>

Claim_Neuron(self) == ClaimNeuron1(self) \/ ClaimNeuron2(self)

RefreshNeuron1(self) == /\ pc[self] = "RefreshNeuron1"
                        /\ \E nid \in DOMAIN(neuron) \ locks:
                             /\ neuron_id_R' = [neuron_id_R EXCEPT ![self] = nid]
                             /\ account_id' = [account_id EXCEPT ![self] = neuron[nid].account]
                             /\ locks' = (locks \union {neuron_id_R'[self]})
                             /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(account_id'[self]))))
                        /\ pc' = [pc EXCEPT ![self] = "RefreshNeuron2"]
                        /\ UNCHANGED << neuron, neuron_id_by_account, 
                                        neuron_count, total_rewards, minted, 
                                        burned, ledger_to_governance, 
                                        account_id_, neuron_id_, neuron_id_D, 
                                        amount_, to_account, rewards_amount, 
                                        fees_amount, error, parent_neuron_id_, 
                                        child_neuron_id_, child_stake, 
                                        child_account_id_, parent_neuron_id_D, 
                                        disburse_amount, child_account_id_D, 
                                        child_neuron_id_D, neuron_id, 
                                        maturity_to_merge, parent_neuron_id, 
                                        amount, child_neuron_id, 
                                        child_account_id, source_neuron_id, 
                                        target_neuron_id, target_balance, 
                                        balances, nr_transfers >>

RefreshNeuron2(self) == /\ pc[self] = "RefreshNeuron2"
                        /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                             LET b == r.response_value.bal IN
                               /\ ledger_to_governance' = ledger_to_governance \ {r}
                               /\ IF b >= MIN_STAKE
                                     THEN /\ Assert((b >= neuron[neuron_id_R[self]].cached_stake), 
                                                    "Failure of assertion at line 332, column 17.")
                                          /\ neuron' = [neuron EXCEPT ![neuron_id_R[self]] = [@ EXCEPT !.cached_stake = b] ]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED neuron
                               /\ locks' = locks \ {neuron_id_R[self]}
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << neuron_id_by_account, neuron_count, 
                                        total_rewards, minted, burned, 
                                        governance_to_ledger, account_id_, 
                                        neuron_id_, account_id, neuron_id_R, 
                                        neuron_id_D, amount_, to_account, 
                                        rewards_amount, fees_amount, error, 
                                        parent_neuron_id_, child_neuron_id_, 
                                        child_stake, child_account_id_, 
                                        parent_neuron_id_D, disburse_amount, 
                                        child_account_id_D, child_neuron_id_D, 
                                        neuron_id, maturity_to_merge, 
                                        parent_neuron_id, amount, 
                                        child_neuron_id, child_account_id, 
                                        source_neuron_id, target_neuron_id, 
                                        target_balance, balances, nr_transfers >>

Refresh_Neuron(self) == RefreshNeuron1(self) \/ RefreshNeuron2(self)

DisburseNeuron1(self) == /\ pc[self] = "DisburseNeuron1"
                         /\ \E nid \in DOMAIN(neuron) \ locks:
                              \E amt \in 0..neuron[nid].cached_stake:
                                /\ neuron_id_D' = [neuron_id_D EXCEPT ![self] = nid]
                                /\ amount_' = [amount_ EXCEPT ![self] = amt]
                                /\ rewards_amount' = [rewards_amount EXCEPT ![self] = neuron[neuron_id_D'[self]].maturity]
                                /\ fees_amount' = [fees_amount EXCEPT ![self] = neuron[neuron_id_D'[self]].fees]
                                /\ locks' = (locks \union {neuron_id_D'[self]})
                                /\ IF fees_amount'[self] > TRANSACTION_FEE
                                      THEN /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(neuron[neuron_id_D'[self]].account, Minting_Account_Id, fees_amount'[self], 0))))
                                           /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron2"]
                                           /\ UNCHANGED neuron
                                      ELSE /\ IF neuron[neuron_id_D'[self]].cached_stake > fees_amount'[self]
                                                 THEN /\ neuron' = [neuron EXCEPT ![neuron_id_D'[self]] = [@ EXCEPT !.cached_stake = @ - fees_amount'[self], !.fees = 0]]
                                                 ELSE /\ neuron' = [neuron EXCEPT ![neuron_id_D'[self]] = [@ EXCEPT !.cached_stake = 0, !.fees = 0]]
                                           /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(neuron'[neuron_id_D'[self]].account, to_account[self], calc_disburse_amount(amount_'[self], fees_amount'[self]), TRANSACTION_FEE))))
                                           /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron3"]
                         /\ UNCHANGED << neuron_id_by_account, neuron_count, 
                                         total_rewards, minted, burned, 
                                         ledger_to_governance, account_id_, 
                                         neuron_id_, account_id, neuron_id_R, 
                                         to_account, error, parent_neuron_id_, 
                                         child_neuron_id_, child_stake, 
                                         child_account_id_, parent_neuron_id_D, 
                                         disburse_amount, child_account_id_D, 
                                         child_neuron_id_D, neuron_id, 
                                         maturity_to_merge, parent_neuron_id, 
                                         amount, child_neuron_id, 
                                         child_account_id, source_neuron_id, 
                                         target_neuron_id, target_balance, 
                                         balances, nr_transfers >>

DisburseNeuron2(self) == /\ pc[self] = "DisburseNeuron2"
                         /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                              /\ ledger_to_governance' = ledger_to_governance \ {answer}
                              /\ IF answer.response_value.status = TRANSFER_FAIL
                                    THEN /\ error' = [error EXCEPT ![self] = TRUE]
                                         /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                         /\ UNCHANGED << neuron, 
                                                         governance_to_ledger >>
                                    ELSE /\ IF neuron[neuron_id_D[self]].cached_stake > fees_amount[self]
                                               THEN /\ neuron' = [neuron EXCEPT ![neuron_id_D[self]] = [@ EXCEPT !.cached_stake = @ - fees_amount[self], !.fees = 0]]
                                               ELSE /\ neuron' = [neuron EXCEPT ![neuron_id_D[self]] = [@ EXCEPT !.cached_stake = 0, !.fees = 0]]
                                         /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(neuron'[neuron_id_D[self]].account, to_account[self], calc_disburse_amount(amount_[self], fees_amount[self]), TRANSACTION_FEE))))
                                         /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron3"]
                                         /\ error' = error
                         /\ UNCHANGED << neuron_id_by_account, locks, 
                                         neuron_count, total_rewards, minted, 
                                         burned, account_id_, neuron_id_, 
                                         account_id, neuron_id_R, neuron_id_D, 
                                         amount_, to_account, rewards_amount, 
                                         fees_amount, parent_neuron_id_, 
                                         child_neuron_id_, child_stake, 
                                         child_account_id_, parent_neuron_id_D, 
                                         disburse_amount, child_account_id_D, 
                                         child_neuron_id_D, neuron_id, 
                                         maturity_to_merge, parent_neuron_id, 
                                         amount, child_neuron_id, 
                                         child_account_id, source_neuron_id, 
                                         target_neuron_id, target_balance, 
                                         balances, nr_transfers >>

DisburseNeuron3(self) == /\ pc[self] = "DisburseNeuron3"
                         /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                              /\ ledger_to_governance' = ledger_to_governance \ {answer}
                              /\ IF answer.response_value.status = TRANSFER_FAIL
                                    THEN /\ error' = [error EXCEPT ![self] = TRUE]
                                         /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                         /\ UNCHANGED << neuron, 
                                                         governance_to_ledger >>
                                    ELSE /\ IF to_deduct(calc_disburse_amount(amount_[self], fees_amount[self])) >= neuron[neuron_id_D[self]].cached_stake
                                               THEN /\ neuron' = [neuron EXCEPT ![neuron_id_D[self]] = [@ EXCEPT !.cached_stake = 0]]
                                               ELSE /\ neuron' = [neuron EXCEPT ![neuron_id_D[self]] = [@ EXCEPT !.cached_stake = @ - to_deduct(calc_disburse_amount(amount_[self], fees_amount[self]))]]
                                         /\ IF rewards_amount[self] > TRANSACTION_FEE
                                               THEN /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(Minting_Account_Id, to_account[self], rewards_amount[self], 0))))
                                                    /\ pc' = [pc EXCEPT ![self] = "DisburseNeuron4"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                                    /\ UNCHANGED governance_to_ledger
                                         /\ error' = error
                         /\ UNCHANGED << neuron_id_by_account, locks, 
                                         neuron_count, total_rewards, minted, 
                                         burned, account_id_, neuron_id_, 
                                         account_id, neuron_id_R, neuron_id_D, 
                                         amount_, to_account, rewards_amount, 
                                         fees_amount, parent_neuron_id_, 
                                         child_neuron_id_, child_stake, 
                                         child_account_id_, parent_neuron_id_D, 
                                         disburse_amount, child_account_id_D, 
                                         child_neuron_id_D, neuron_id, 
                                         maturity_to_merge, parent_neuron_id, 
                                         amount, child_neuron_id, 
                                         child_account_id, source_neuron_id, 
                                         target_neuron_id, target_balance, 
                                         balances, nr_transfers >>

DisburseNeuron4(self) == /\ pc[self] = "DisburseNeuron4"
                         /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                              /\ ledger_to_governance' = ledger_to_governance \ {answer}
                              /\ IF answer.response_value.status = TRANSFER_FAIL
                                    THEN /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "DisburseNeuronEnd"]
                         /\ UNCHANGED << neuron, neuron_id_by_account, locks, 
                                         neuron_count, total_rewards, minted, 
                                         burned, governance_to_ledger, 
                                         account_id_, neuron_id_, account_id, 
                                         neuron_id_R, neuron_id_D, amount_, 
                                         to_account, rewards_amount, 
                                         fees_amount, error, parent_neuron_id_, 
                                         child_neuron_id_, child_stake, 
                                         child_account_id_, parent_neuron_id_D, 
                                         disburse_amount, child_account_id_D, 
                                         child_neuron_id_D, neuron_id, 
                                         maturity_to_merge, parent_neuron_id, 
                                         amount, child_neuron_id, 
                                         child_account_id, source_neuron_id, 
                                         target_neuron_id, target_balance, 
                                         balances, nr_transfers >>

DisburseNeuronEnd(self) == /\ pc[self] = "DisburseNeuronEnd"
                           /\ IF ~error[self]
                                 THEN /\ neuron' = [neuron EXCEPT ![neuron_id_D[self]] = [@ EXCEPT !.maturity = 0]]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED neuron
                           /\ locks' = locks \ {neuron_id_D[self]}
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << neuron_id_by_account, neuron_count, 
                                           total_rewards, minted, burned, 
                                           governance_to_ledger, 
                                           ledger_to_governance, account_id_, 
                                           neuron_id_, account_id, neuron_id_R, 
                                           neuron_id_D, amount_, to_account, 
                                           rewards_amount, fees_amount, error, 
                                           parent_neuron_id_, child_neuron_id_, 
                                           child_stake, child_account_id_, 
                                           parent_neuron_id_D, disburse_amount, 
                                           child_account_id_D, 
                                           child_neuron_id_D, neuron_id, 
                                           maturity_to_merge, parent_neuron_id, 
                                           amount, child_neuron_id, 
                                           child_account_id, source_neuron_id, 
                                           target_neuron_id, target_balance, 
                                           balances, nr_transfers >>

Disburse_Neuron(self) == DisburseNeuron1(self) \/ DisburseNeuron2(self)
                            \/ DisburseNeuron3(self)
                            \/ DisburseNeuron4(self)
                            \/ DisburseNeuronEnd(self)

SpawnNeuronStart(self) == /\ pc[self] = "SpawnNeuronStart"
                          /\ \E nid \in DOMAIN(neuron) \ locks:
                               \E c_acc_id \in Governance_Account_Ids \ {neuron[n].account : n \in DOMAIN(neuron)}:
                                 /\ parent_neuron_id_' = [parent_neuron_id_ EXCEPT ![self] = nid]
                                 /\ child_account_id_' = [child_account_id_ EXCEPT ![self] = c_acc_id]
                                 /\ child_stake' = [child_stake EXCEPT ![self] = neuron[parent_neuron_id_'[self]].maturity]
                                 /\ child_stake'[self] >= MIN_STAKE
                                 /\ child_neuron_id_' = [child_neuron_id_ EXCEPT ![self] = neuron_count]
                                 /\ neuron_count' = neuron_count + 1
                                 /\ neuron' = (child_neuron_id_'[self] :> [ cached_stake |-> 0, account |-> child_account_id_'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                                 /\ neuron_id_by_account' = (child_account_id_'[self] :> child_neuron_id_'[self] @@ neuron_id_by_account)
                                 /\ Assert(child_neuron_id_'[self] \notin locks, 
                                           "Failure of assertion at line 473, column 13.")
                                 /\ locks' = (locks \union {parent_neuron_id_'[self], child_neuron_id_'[self]})
                                 /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(Minting_Account_Id, child_account_id_'[self], child_stake'[self], 0))))
                          /\ pc' = [pc EXCEPT ![self] = "SpawnNeuronEnd"]
                          /\ UNCHANGED << total_rewards, minted, burned, 
                                          ledger_to_governance, account_id_, 
                                          neuron_id_, account_id, neuron_id_R, 
                                          neuron_id_D, amount_, to_account, 
                                          rewards_amount, fees_amount, error, 
                                          parent_neuron_id_D, disburse_amount, 
                                          child_account_id_D, 
                                          child_neuron_id_D, neuron_id, 
                                          maturity_to_merge, parent_neuron_id, 
                                          amount, child_neuron_id, 
                                          child_account_id, source_neuron_id, 
                                          target_neuron_id, target_balance, 
                                          balances, nr_transfers >>

SpawnNeuronEnd(self) == /\ pc[self] = "SpawnNeuronEnd"
                        /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                             /\ ledger_to_governance' = ledger_to_governance \ {answer}
                             /\ IF answer.response_value.status = TRANSFER_FAIL
                                   THEN /\ neuron' = [n \in DOMAIN(neuron) \ {child_neuron_id_[self]} |-> neuron[n] ]
                                        /\ neuron_id_by_account' = [a \in DOMAIN(neuron_id_by_account) \ {child_account_id_[self]} |-> neuron_id_by_account[a] ]
                                   ELSE /\ neuron' =       [ neuron EXCEPT ![parent_neuron_id_[self]] = [@ EXCEPT !.maturity = @ - child_stake[self] ],
                                                     ![child_neuron_id_[self]] = [@ EXCEPT !.cached_stake = child_stake[self]] ]
                                        /\ UNCHANGED neuron_id_by_account
                             /\ locks' = locks \ {parent_neuron_id_[self], child_neuron_id_[self]}
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                        burned, governance_to_ledger, 
                                        account_id_, neuron_id_, account_id, 
                                        neuron_id_R, neuron_id_D, amount_, 
                                        to_account, rewards_amount, 
                                        fees_amount, error, parent_neuron_id_, 
                                        child_neuron_id_, child_stake, 
                                        child_account_id_, parent_neuron_id_D, 
                                        disburse_amount, child_account_id_D, 
                                        child_neuron_id_D, neuron_id, 
                                        maturity_to_merge, parent_neuron_id, 
                                        amount, child_neuron_id, 
                                        child_account_id, source_neuron_id, 
                                        target_neuron_id, target_balance, 
                                        balances, nr_transfers >>

Spawn_Neuron(self) == SpawnNeuronStart(self) \/ SpawnNeuronEnd(self)

DisburseToNeuron1(self) == /\ pc[self] = "DisburseToNeuron1"
                           /\ \E nid \in DOMAIN(neuron) \ locks:
                                LET parent_neuron == neuron[nid] IN
                                  \E amt \in (MIN_STAKE + TRANSACTION_FEE)..(parent_neuron.cached_stake - MIN_STAKE):
                                    \E c_acc_id \in Governance_Account_Ids \ { neuron[n].account : n \in DOMAIN(neuron)}:
                                      /\ parent_neuron_id_D' = [parent_neuron_id_D EXCEPT ![self] = nid]
                                      /\ disburse_amount' = [disburse_amount EXCEPT ![self] = amt]
                                      /\ parent_neuron.maturity <= TRANSACTION_FEE
                                      /\ child_account_id_D' = [child_account_id_D EXCEPT ![self] = c_acc_id]
                                      /\ child_neuron_id_D' = [child_neuron_id_D EXCEPT ![self] = neuron_count]
                                      /\ neuron_count' = neuron_count + 1
                                      /\ neuron' = (child_neuron_id_D'[self] :> [ cached_stake |-> 0, account |-> child_account_id_D'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                                      /\ neuron_id_by_account' = (child_account_id_D'[self] :> child_neuron_id_D'[self] @@ neuron_id_by_account)
                                      /\ Assert(child_neuron_id_D'[self] \notin locks, 
                                                "Failure of assertion at line 523, column 13.")
                                      /\ locks' = (locks \union {parent_neuron_id_D'[self], child_neuron_id_D'[self]})
                                      /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(parent_neuron.account, child_account_id_D'[self], disburse_amount'[self] - TRANSACTION_FEE, TRANSACTION_FEE))))
                           /\ pc' = [pc EXCEPT ![self] = "DisburseToNeuronEnd"]
                           /\ UNCHANGED << total_rewards, minted, burned, 
                                           ledger_to_governance, account_id_, 
                                           neuron_id_, account_id, neuron_id_R, 
                                           neuron_id_D, amount_, to_account, 
                                           rewards_amount, fees_amount, error, 
                                           parent_neuron_id_, child_neuron_id_, 
                                           child_stake, child_account_id_, 
                                           neuron_id, maturity_to_merge, 
                                           parent_neuron_id, amount, 
                                           child_neuron_id, child_account_id, 
                                           source_neuron_id, target_neuron_id, 
                                           target_balance, balances, 
                                           nr_transfers >>

DisburseToNeuronEnd(self) == /\ pc[self] = "DisburseToNeuronEnd"
                             /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                                  /\ ledger_to_governance' = ledger_to_governance \ {answer}
                                  /\ IF answer.response_value.status = TRANSFER_FAIL
                                        THEN /\ neuron' = [n \in DOMAIN(neuron) \ {child_neuron_id_D[self]} |-> neuron[n] ]
                                             /\ neuron_id_by_account' = [a \in DOMAIN(neuron_id_by_account) \ {child_account_id_D[self]} |-> neuron_id_by_account[a] ]
                                        ELSE /\ neuron' =       [ neuron EXCEPT ![parent_neuron_id_D[self]] = [@ EXCEPT !.cached_stake = @ - disburse_amount[self] ],
                                                          ![child_neuron_id_D[self]] = [@ EXCEPT !.cached_stake = disburse_amount[self] - TRANSACTION_FEE] ]
                                             /\ UNCHANGED neuron_id_by_account
                                  /\ locks' = locks \ {parent_neuron_id_D[self], child_neuron_id_D[self]}
                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << neuron_count, total_rewards, 
                                             minted, burned, 
                                             governance_to_ledger, account_id_, 
                                             neuron_id_, account_id, 
                                             neuron_id_R, neuron_id_D, amount_, 
                                             to_account, rewards_amount, 
                                             fees_amount, error, 
                                             parent_neuron_id_, 
                                             child_neuron_id_, child_stake, 
                                             child_account_id_, 
                                             parent_neuron_id_D, 
                                             disburse_amount, 
                                             child_account_id_D, 
                                             child_neuron_id_D, neuron_id, 
                                             maturity_to_merge, 
                                             parent_neuron_id, amount, 
                                             child_neuron_id, child_account_id, 
                                             source_neuron_id, 
                                             target_neuron_id, target_balance, 
                                             balances, nr_transfers >>

Disburse_To_Neuron(self) == DisburseToNeuron1(self)
                               \/ DisburseToNeuronEnd(self)

MergeMaturityOfNeuron1(self) == /\ pc[self] = "MergeMaturityOfNeuron1"
                                /\ \E nid \in DOMAIN(neuron) \ locks:
                                     \E maturity_to_merge_tmp \in (TRANSACTION_FEE+1)..neuron[nid].maturity:
                                       /\ neuron_id' = [neuron_id EXCEPT ![self] = nid]
                                       /\ maturity_to_merge' = [maturity_to_merge EXCEPT ![self] = maturity_to_merge_tmp]
                                       /\ locks' = (locks \union {neuron_id'[self]})
                                       /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(Minting_Account_Id, neuron[neuron_id'[self]].account, maturity_to_merge'[self], 0))))
                                /\ pc' = [pc EXCEPT ![self] = "MergeMaturityOfNeuron2"]
                                /\ UNCHANGED << neuron, neuron_id_by_account, 
                                                neuron_count, total_rewards, 
                                                minted, burned, 
                                                ledger_to_governance, 
                                                account_id_, neuron_id_, 
                                                account_id, neuron_id_R, 
                                                neuron_id_D, amount_, 
                                                to_account, rewards_amount, 
                                                fees_amount, error, 
                                                parent_neuron_id_, 
                                                child_neuron_id_, child_stake, 
                                                child_account_id_, 
                                                parent_neuron_id_D, 
                                                disburse_amount, 
                                                child_account_id_D, 
                                                child_neuron_id_D, 
                                                parent_neuron_id, amount, 
                                                child_neuron_id, 
                                                child_account_id, 
                                                source_neuron_id, 
                                                target_neuron_id, 
                                                target_balance, balances, 
                                                nr_transfers >>

MergeMaturityOfNeuron2(self) == /\ pc[self] = "MergeMaturityOfNeuron2"
                                /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                                     /\ ledger_to_governance' = ledger_to_governance \ {answer}
                                     /\ IF answer.response_value.status # TRANSFER_FAIL
                                           THEN /\ neuron' = [neuron EXCEPT ![neuron_id[self]] = [@ EXCEPT !.maturity = @ - maturity_to_merge[self], !.cached_stake = @ + maturity_to_merge[self]]]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED neuron
                                     /\ locks' = locks \ {neuron_id[self]}
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << neuron_id_by_account, 
                                                neuron_count, total_rewards, 
                                                minted, burned, 
                                                governance_to_ledger, 
                                                account_id_, neuron_id_, 
                                                account_id, neuron_id_R, 
                                                neuron_id_D, amount_, 
                                                to_account, rewards_amount, 
                                                fees_amount, error, 
                                                parent_neuron_id_, 
                                                child_neuron_id_, child_stake, 
                                                child_account_id_, 
                                                parent_neuron_id_D, 
                                                disburse_amount, 
                                                child_account_id_D, 
                                                child_neuron_id_D, neuron_id, 
                                                maturity_to_merge, 
                                                parent_neuron_id, amount, 
                                                child_neuron_id, 
                                                child_account_id, 
                                                source_neuron_id, 
                                                target_neuron_id, 
                                                target_balance, balances, 
                                                nr_transfers >>

Merge_Maturity_Of_Neuron(self) == MergeMaturityOfNeuron1(self)
                                     \/ MergeMaturityOfNeuron2(self)

SplitNeuron1(self) == /\ pc[self] = "SplitNeuron1"
                      /\ \E nid \in DOMAIN(neuron) \ locks:
                           \E amt \in 0..neuron[nid].cached_stake:
                             \E fresh_account_id \in Governance_Account_Ids \ {neuron[n].account : n \in DOMAIN(neuron)}:
                               /\ parent_neuron_id' = [parent_neuron_id EXCEPT ![self] = nid]
                               /\ amount' = [amount EXCEPT ![self] = amt]
                               /\ child_account_id' = [child_account_id EXCEPT ![self] = fresh_account_id]
                               /\ child_neuron_id' = [child_neuron_id EXCEPT ![self] = neuron_count]
                               /\ neuron_count' = neuron_count + 1
                               /\ Assert(child_neuron_id'[self] \notin locks, 
                                         "Failure of assertion at line 591, column 13.")
                               /\ neuron' = (child_neuron_id'[self] :> [ cached_stake |-> 0, account |-> child_account_id'[self], fees |-> 0, maturity |-> 0 ] @@ neuron)
                               /\ neuron_id_by_account' = (child_account_id'[self] :> child_neuron_id'[self] @@ neuron_id_by_account)
                               /\ (amount'[self] >= MIN_STAKE + TRANSACTION_FEE /\ neuron'[parent_neuron_id'[self]].cached_stake - neuron'[parent_neuron_id'[self]].fees >= MIN_STAKE + amount'[self])
                               /\ locks' = (locks \union {parent_neuron_id'[self], child_neuron_id'[self]})
                               /\ governance_to_ledger' =                     Append(governance_to_ledger,
                                                          request(self, OP_TRANSFER, transfer(neuron'[parent_neuron_id'[self]].account, neuron'[child_neuron_id'[self]].account, amount'[self] - TRANSACTION_FEE, TRANSACTION_FEE)))
                      /\ pc' = [pc EXCEPT ![self] = "SplitNeuron2"]
                      /\ UNCHANGED << total_rewards, minted, burned, 
                                      ledger_to_governance, account_id_, 
                                      neuron_id_, account_id, neuron_id_R, 
                                      neuron_id_D, amount_, to_account, 
                                      rewards_amount, fees_amount, error, 
                                      parent_neuron_id_, child_neuron_id_, 
                                      child_stake, child_account_id_, 
                                      parent_neuron_id_D, disburse_amount, 
                                      child_account_id_D, child_neuron_id_D, 
                                      neuron_id, maturity_to_merge, 
                                      source_neuron_id, target_neuron_id, 
                                      target_balance, balances, nr_transfers >>

SplitNeuron2(self) == /\ pc[self] = "SplitNeuron2"
                      /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                           /\ ledger_to_governance' = ledger_to_governance \ {answer}
                           /\ IF answer.response_value.status = TRANSFER_FAIL
                                 THEN /\ neuron' = [n \in DOMAIN(neuron) \ {child_neuron_id[self]} |-> neuron[n] ]
                                      /\ neuron_id_by_account' = [a \in DOMAIN(neuron_id_by_account) \ {child_account_id[self]} |-> neuron_id_by_account[a] ]
                                 ELSE /\ neuron' = [neuron EXCEPT ![parent_neuron_id[self]] = [@ EXCEPT !.cached_stake = @ - amount[self]],
                                                                     ![child_neuron_id[self]] = [@ EXCEPT !.cached_stake = amount[self] - TRANSACTION_FEE]]
                                      /\ UNCHANGED neuron_id_by_account
                           /\ locks' = locks \ {child_neuron_id[self], parent_neuron_id[self]}
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << neuron_count, total_rewards, minted, 
                                      burned, governance_to_ledger, 
                                      account_id_, neuron_id_, account_id, 
                                      neuron_id_R, neuron_id_D, amount_, 
                                      to_account, rewards_amount, fees_amount, 
                                      error, parent_neuron_id_, 
                                      child_neuron_id_, child_stake, 
                                      child_account_id_, parent_neuron_id_D, 
                                      disburse_amount, child_account_id_D, 
                                      child_neuron_id_D, neuron_id, 
                                      maturity_to_merge, parent_neuron_id, 
                                      amount, child_neuron_id, 
                                      child_account_id, source_neuron_id, 
                                      target_neuron_id, target_balance, 
                                      balances, nr_transfers >>

Split_Neuron(self) == SplitNeuron1(self) \/ SplitNeuron2(self)

MergeNeurons1(self) == /\ pc[self] = "MergeNeurons1"
                       /\ \E source_nid \in DOMAIN(neuron) \ locks:
                            \E target_nid \in DOMAIN(neuron) \ locks:
                              /\ source_nid /= target_nid
                              /\ source_neuron_id' = [source_neuron_id EXCEPT ![self] = source_nid]
                              /\ target_neuron_id' = [target_neuron_id EXCEPT ![self] = target_nid]
                              /\ locks' = (locks \union {source_neuron_id'[self], target_neuron_id'[self]})
                              /\   (neuron[source_neuron_id'[self]].cached_stake - neuron[source_neuron_id'[self]].fees) +
                                 (neuron[target_neuron_id'[self]].cached_stake - neuron[target_neuron_id'[self]].fees) /= 0
                              /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_TRANSFER, (transfer(neuron[source_neuron_id'[self]].account,
                                                                                                                      neuron[target_neuron_id'[self]].account,
                                                                                                                      (neuron[source_neuron_id'[self]].cached_stake - neuron[source_neuron_id'[self]].fees) - TRANSACTION_FEE,
                                                                                                                      TRANSACTION_FEE))))
                       /\ pc' = [pc EXCEPT ![self] = "MergeNeurons2"]
                       /\ UNCHANGED << neuron, neuron_id_by_account, 
                                       neuron_count, total_rewards, minted, 
                                       burned, ledger_to_governance, 
                                       account_id_, neuron_id_, account_id, 
                                       neuron_id_R, neuron_id_D, amount_, 
                                       to_account, rewards_amount, fees_amount, 
                                       error, parent_neuron_id_, 
                                       child_neuron_id_, child_stake, 
                                       child_account_id_, parent_neuron_id_D, 
                                       disburse_amount, child_account_id_D, 
                                       child_neuron_id_D, neuron_id, 
                                       maturity_to_merge, parent_neuron_id, 
                                       amount, child_neuron_id, 
                                       child_account_id, target_balance, 
                                       balances, nr_transfers >>

MergeNeurons2(self) == /\ pc[self] = "MergeNeurons2"
                       /\ \E answer \in { resp \in ledger_to_governance: resp.caller = self}:
                            /\ ledger_to_governance' = ledger_to_governance \ {answer}
                            /\ IF answer.response_value.status = TRANSFER_FAIL
                                  THEN /\ pc' = [pc EXCEPT ![self] = "MergeNeurons5"]
                                       /\ UNCHANGED governance_to_ledger
                                  ELSE /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(neuron[target_neuron_id[self]].account))))
                                       /\ pc' = [pc EXCEPT ![self] = "MergeNeurons3"]
                       /\ UNCHANGED << neuron, neuron_id_by_account, locks, 
                                       neuron_count, total_rewards, minted, 
                                       burned, account_id_, neuron_id_, 
                                       account_id, neuron_id_R, neuron_id_D, 
                                       amount_, to_account, rewards_amount, 
                                       fees_amount, error, parent_neuron_id_, 
                                       child_neuron_id_, child_stake, 
                                       child_account_id_, parent_neuron_id_D, 
                                       disburse_amount, child_account_id_D, 
                                       child_neuron_id_D, neuron_id, 
                                       maturity_to_merge, parent_neuron_id, 
                                       amount, child_neuron_id, 
                                       child_account_id, source_neuron_id, 
                                       target_neuron_id, target_balance, 
                                       balances, nr_transfers >>

MergeNeurons3(self) == /\ pc[self] = "MergeNeurons3"
                       /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                            LET b == r.response_value.bal IN
                              /\ ledger_to_governance' = ledger_to_governance \ {r}
                              /\ target_balance' = [target_balance EXCEPT ![self] = b]
                              /\ governance_to_ledger' = Append(governance_to_ledger, request(self, OP_QUERY_BALANCE, (balance_query(neuron[source_neuron_id[self]].account))))
                       /\ pc' = [pc EXCEPT ![self] = "MergeNeurons4"]
                       /\ UNCHANGED << neuron, neuron_id_by_account, locks, 
                                       neuron_count, total_rewards, minted, 
                                       burned, account_id_, neuron_id_, 
                                       account_id, neuron_id_R, neuron_id_D, 
                                       amount_, to_account, rewards_amount, 
                                       fees_amount, error, parent_neuron_id_, 
                                       child_neuron_id_, child_stake, 
                                       child_account_id_, parent_neuron_id_D, 
                                       disburse_amount, child_account_id_D, 
                                       child_neuron_id_D, neuron_id, 
                                       maturity_to_merge, parent_neuron_id, 
                                       amount, child_neuron_id, 
                                       child_account_id, source_neuron_id, 
                                       target_neuron_id, balances, 
                                       nr_transfers >>

MergeNeurons4(self) == /\ pc[self] = "MergeNeurons4"
                       /\ \E r \in { r2 \in ledger_to_governance : r2.caller = self }:
                            LET source_balance == r.response_value.bal IN
                              /\ ledger_to_governance' = ledger_to_governance \ {r}
                              /\ IF target_balance[self] /= (
                                        (neuron[source_neuron_id[self]].cached_stake - neuron[source_neuron_id[self]].fees)
                                        + (neuron[target_neuron_id[self]].cached_stake - neuron[target_neuron_id[self]].fees)
                                        - TRANSACTION_FEE)
                                    \/ source_balance /= 0
                                    THEN /\ pc' = [pc EXCEPT ![self] = "MergeNeurons5"]
                                         /\ UNCHANGED neuron
                                    ELSE /\ neuron' =       [neuron EXCEPT
                                                      ![target_neuron_id[self]] = [@ EXCEPT !.cached_stake = @ +
                                                          (neuron[source_neuron_id[self]].cached_stake - neuron[source_neuron_id[self]].fees) - TRANSACTION_FEE,
                                                          !.maturity = @ + neuron[source_neuron_id[self]].maturity],
                                                      ![source_neuron_id[self]] = [@ EXCEPT !.cached_stake = 0, !.maturity = 0]]
                                         /\ pc' = [pc EXCEPT ![self] = "MergeNeurons5"]
                       /\ UNCHANGED << neuron_id_by_account, locks, 
                                       neuron_count, total_rewards, minted, 
                                       burned, governance_to_ledger, 
                                       account_id_, neuron_id_, account_id, 
                                       neuron_id_R, neuron_id_D, amount_, 
                                       to_account, rewards_amount, fees_amount, 
                                       error, parent_neuron_id_, 
                                       child_neuron_id_, child_stake, 
                                       child_account_id_, parent_neuron_id_D, 
                                       disburse_amount, child_account_id_D, 
                                       child_neuron_id_D, neuron_id, 
                                       maturity_to_merge, parent_neuron_id, 
                                       amount, child_neuron_id, 
                                       child_account_id, source_neuron_id, 
                                       target_neuron_id, target_balance, 
                                       balances, nr_transfers >>

MergeNeurons5(self) == /\ pc[self] = "MergeNeurons5"
                       /\ locks' = locks \ {source_neuron_id[self], target_neuron_id[self]}
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << neuron, neuron_id_by_account, 
                                       neuron_count, total_rewards, minted, 
                                       burned, governance_to_ledger, 
                                       ledger_to_governance, account_id_, 
                                       neuron_id_, account_id, neuron_id_R, 
                                       neuron_id_D, amount_, to_account, 
                                       rewards_amount, fees_amount, error, 
                                       parent_neuron_id_, child_neuron_id_, 
                                       child_stake, child_account_id_, 
                                       parent_neuron_id_D, disburse_amount, 
                                       child_account_id_D, child_neuron_id_D, 
                                       neuron_id, maturity_to_merge, 
                                       parent_neuron_id, amount, 
                                       child_neuron_id, child_account_id, 
                                       source_neuron_id, target_neuron_id, 
                                       target_balance, balances, nr_transfers >>

Merge_Neurons(self) == MergeNeurons1(self) \/ MergeNeurons2(self)
                          \/ MergeNeurons3(self) \/ MergeNeurons4(self)
                          \/ MergeNeurons5(self)

LedgerMainLoop == /\ pc[Ledger_Process_Id] = "LedgerMainLoop"
                  /\ \/ /\ (governance_to_ledger /= <<>>)
                        /\ LET req == Head(governance_to_ledger) IN
                             LET t == req.type IN
                               LET arg == req.args IN
                                 LET caller == req.caller IN
                                   /\ governance_to_ledger' = Tail(governance_to_ledger)
                                   /\ Assert((t \in {OP_QUERY_BALANCE, OP_TRANSFER}), 
                                             "Failure of assertion at line 724, column 21.")
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
                                                                                "Failure of assertion at line 747, column 29.")
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
                  /\ UNCHANGED << neuron, neuron_id_by_account, locks, 
                                  neuron_count, total_rewards, account_id_, 
                                  neuron_id_, account_id, neuron_id_R, 
                                  neuron_id_D, amount_, to_account, 
                                  rewards_amount, fees_amount, error, 
                                  parent_neuron_id_, child_neuron_id_, 
                                  child_stake, child_account_id_, 
                                  parent_neuron_id_D, disburse_amount, 
                                  child_account_id_D, child_neuron_id_D, 
                                  neuron_id, maturity_to_merge, 
                                  parent_neuron_id, amount, child_neuron_id, 
                                  child_account_id, source_neuron_id, 
                                  target_neuron_id, target_balance >>

Ledger == LedgerMainLoop

Change_Neuron_Fee1(self) == /\ pc[self] = "Change_Neuron_Fee1"
                            /\ \E nid \in DOMAIN(neuron):
                                 \E new_fee_value \in 0..Min(MAX_NEURON_FEE, neuron[nid].cached_stake):
                                   neuron' = [neuron EXCEPT ![nid] = [@ EXCEPT !.fees = new_fee_value]]
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << neuron_id_by_account, locks, 
                                            neuron_count, total_rewards, 
                                            minted, burned, 
                                            governance_to_ledger, 
                                            ledger_to_governance, account_id_, 
                                            neuron_id_, account_id, 
                                            neuron_id_R, neuron_id_D, amount_, 
                                            to_account, rewards_amount, 
                                            fees_amount, error, 
                                            parent_neuron_id_, 
                                            child_neuron_id_, child_stake, 
                                            child_account_id_, 
                                            parent_neuron_id_D, 
                                            disburse_amount, 
                                            child_account_id_D, 
                                            child_neuron_id_D, neuron_id, 
                                            maturity_to_merge, 
                                            parent_neuron_id, amount, 
                                            child_neuron_id, child_account_id, 
                                            source_neuron_id, target_neuron_id, 
                                            target_balance, balances, 
                                            nr_transfers >>

Change_Neuron_Fee(self) == Change_Neuron_Fee1(self)

Increase_Neuron_Maturity1(self) == /\ pc[self] = "Increase_Neuron_Maturity1"
                                   /\ \E nid \in DOMAIN(neuron):
                                        \E new_maturity \in (neuron[nid].maturity+1)..MAX_MATURITY:
                                          /\ total_rewards' = total_rewards + new_maturity - neuron[nid].maturity
                                          /\ neuron' = [neuron EXCEPT ![nid] = [@ EXCEPT !.maturity = new_maturity]]
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << neuron_id_by_account, locks, 
                                                   neuron_count, minted, 
                                                   burned, 
                                                   governance_to_ledger, 
                                                   ledger_to_governance, 
                                                   account_id_, neuron_id_, 
                                                   account_id, neuron_id_R, 
                                                   neuron_id_D, amount_, 
                                                   to_account, rewards_amount, 
                                                   fees_amount, error, 
                                                   parent_neuron_id_, 
                                                   child_neuron_id_, 
                                                   child_stake, 
                                                   child_account_id_, 
                                                   parent_neuron_id_D, 
                                                   disburse_amount, 
                                                   child_account_id_D, 
                                                   child_neuron_id_D, 
                                                   neuron_id, 
                                                   maturity_to_merge, 
                                                   parent_neuron_id, amount, 
                                                   child_neuron_id, 
                                                   child_account_id, 
                                                   source_neuron_id, 
                                                   target_neuron_id, 
                                                   target_balance, balances, 
                                                   nr_transfers >>

Increase_Neuron_Maturity(self) == Increase_Neuron_Maturity1(self)

Next == Ledger
           \/ (\E self \in Claim_Neuron_Process_Ids: Claim_Neuron(self))
           \/ (\E self \in Refresh_Neuron_Process_Ids: Refresh_Neuron(self))
           \/ (\E self \in Disburse_Neuron_Process_Ids: Disburse_Neuron(self))
           \/ (\E self \in Spawn_Neuron_Process_Ids: Spawn_Neuron(self))
           \/ (\E self \in Disburse_To_Neuron_Process_Ids: Disburse_To_Neuron(self))
           \/ (\E self \in Merge_Maturity_Of_Neuron_Process_Ids: Merge_Maturity_Of_Neuron(self))
           \/ (\E self \in Split_Neuron_Process_Ids: Split_Neuron(self))
           \/ (\E self \in Merge_Neurons_Process_Ids: Merge_Neurons(self))
           \/ (\E self \in Change_Neuron_Fee_Process_Ids: Change_Neuron_Fee(self))
           \/ (\E self \in Increase_Neuron_Maturity_Process_Ids: Increase_Neuron_Maturity(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

\* A sanity check: we can actually get a non-zero stake in a neuron
Can_Stake_Sanity == \A n \in DOMAIN(neuron) : neuron[n].cached_stake = 0

Cached_Stake_Capped_By_Balance == \A n \in DOMAIN(neuron) :
    neuron[n].cached_stake <= balances[neuron[n].account]

Cached_Stake_Capped_By_Balance_When_Not_Locked == \A n \in DOMAIN(neuron) :
    n \notin locks => neuron[n].cached_stake <= balances[neuron[n].account]

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


Neurons_Have_Unique_Accounts == \A n1, n2 \in DOMAIN(neuron) :
    n1 /= n2 => neuron[n1].account /= neuron[n2].account

Neuron_And_Account_Id_By_Neuron_Coherent == \A n \in DOMAIN(neuron), a \in DOMAIN(neuron_id_by_account):
    /\ neuron_id_by_account[neuron[n].account] = n
    /\ neuron[neuron_id_by_account[a]].account = a

Cached_Stake_Not_Underflowing == \A n \in DOMAIN(neuron): neuron[n].cached_stake >= 0

Neurons_Have_At_Least_Min_Stake == \A n \in DOMAIN(neuron) :
    n \notin locks => neuron[n].cached_stake >= MIN_STAKE

Full_Invariant ==   /\ Cached_Stake_Capped_By_Balance_When_Not_Locked
                    /\ Neuron_And_Account_Id_By_Neuron_Coherent
                    /\ Total_Minting_Does_Not_Exceed_Rewards
                    /\ Neurons_Have_Unique_Accounts
                    /\ Cached_Stake_Not_Underflowing

\* TODO: we can do disbursing (sanity check)
\* Options:
\* 1. initial state with a neuron with cached stake; 2. first do a claim_neuron

\* Model fees increase/decrease and maturity increase with non-deterministic events;
\* guard for fees increase: shouldn't go higher than cached_stake (and not <0)
\* Properties of claim + disburse (combination)? 
\* Fees of a neuron should be <= to the balance on the ledger
\* Fees of a neuron should be <= to the cached stake?
\* We should somehow make sure that all fees are paid
\* Rewards should not be lost (exception: if they are smaller than the transaction_fee, they can get lost right now)
============================================
