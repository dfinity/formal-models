A high-level model of the interaction between the ledger and the archive node canisters.
The goal is to analyze the interleavings from multiple parallel calls to the ledger.
We're using PlusCal (aka +CAL) - more precisely, its C syntax - to specify the canister calls, as it takes care of process counters and local state in a readable fashion.

What's been modelled so far:
- the send call
- spawning archiving nodes, retreiving their remaining capacity, and sending blocks to them

We don't model the lookup of transactions in an archive. The justification is that a bug
in the lookup part is somewhat less severe, as the data would still be there - we would only
need to fix the lookup.

The model is a heavily abstracted version of the source code. The similarity to the source code
is particularly lost where the code uses awaits placed inside of loops.

Run the analysis without deadlock checking, as proper idling transitions haven't been added yet.

To optimally check the model from the command line:
1. add the property (or properties) you'd want to check to Ledger_TLC.cfg
2. check the choice of constants in Ledger_TLC.tla
3. run TLC; the following options are currently optimal for a multi-core setting:
   java -cp <path-to-tla2tools.jar> -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -XX:+UseParallelGC -Xmx200G tlc2.TLC Ledger_TLC.tla -config Ledge
r_TLC.cfg -deadlock -workers 54 -checkpoint 0 -difftrace -gzip
   modify the Xmx and workers option above to control the maximum heap size and number of worker threads used (shouldn't be more than the number of cores you have)

---- MODULE Ledger ----
EXTENDS Integers, Sequences, SequencesExt, FiniteSets, FiniteSetsExt, Functions, TLC

CONSTANTS 
    \* @type: Set(PROC);
    Send_Process_Ids,
    \* @type: Seq(PROC);
    Archive_Node_Ids,
    \* A transaction can be accompanied by a memo. This is the set of possible memos.
    \* @type: Set(Int);
    Memos,
    \* @type: Set(ACCOUNT);
    Accounts,
    \* @type: ACCOUNT;
    Minting_Account,
    \* A model constraint: the maximum amount that can be sent from one account to another.
    \* @type: Int;
    MAX_SEND_AMOUNT,
    \* An implementation constant: the minimal amount that can be burnt.
    \* @type: Int;
    MIN_BURN_AMOUNT,
    \* An implementation constant: the transaction fee.
    \* @type: Int;
    TRANSACTION_FEE,
    \* A model constraint. Initially, the balance of all accounts on the ledger is set to this value.
    \* @type: Int;
    INITIAL_BALANCE,
    \* An implementation constant: the time for which transactions are de-duplicated. 
    \* @type: Int;
    TRANSACTION_WINDOW,
    \* A model constraint: set of integers listing the possible time differences (in an unnamed unit, same as transaction window) 
    \* between two calls to the send method
    \* @type: Set(Int);
    TIME_INCREMENTS,
    \* An implementation constant: how far in the future can a transaction be timestamped
    \* @type: Int;
    PERMITTED_DRIFT,
    \* An implementation constant: a limit on the number of accounts that the ledger can hold.
    \* Once the limit is exceeded, the ledger deletes the accounts with the lowest balance
    \* @type: Int;
    \*  @type: Int;
    MAX_NUMBER_OF_ACCOUNTS,
    \* A model constant: the default memo used for transactions (e.g., when creating burn transactions
    \* to cull the number of ledger accounts)
    \*  @type: Int;
    DEFAULT_MEMO,
    \* An implementation constant: the limit on how many blocks (transactions) are kept in the ledger canister's
    \* memory before being sent to the archive.
    \* @type: Int;
    ARCHIVE_THRESHOLD,
    \* An implementation constant: how many blocks are to be sent to the archive when the archive threshold
    \* is exceeded.
    \* @type: Int;
    NUM_BLOCKS_TO_ARCHIVE,
    \* An implementation constant: when blocks are sent to the archive, they are sent in chunks; this limits
    \* the size of chunks.
    \* @type: Int;
    ARCHIVE_CHUNK_SIZE,
    \* An implementation constant: the capacity of an archive node. The semantics differ between the model
    \* and the implementation; the implementation has a byte limit, whereas the model expresses the limit
    \* in the number of blocks.
    \* @type: Int;
    ARCHIVE_CAPACITY,
    \* A model constant: the sentinel value for the archive guard, when it's not taken
    \* (must be comparable to a Send_Process_Id by TLC)
    \* @type: PROC
    EMPTY_ARCHIVE_GUARD

ASSUME Minting_Account \in Accounts

\* Some generic auxiliary functions on sequences and sets
DropWhile(s, p(_)) ==
  LET Helper(seqAndFound, x) == 
    IF seqAndFound[2] \/ ~p(x)
    THEN << Append(seqAndFound[1], x), TRUE >>
    ELSE seqAndFound
  IN FoldLeft( Helper, << <<>>, FALSE >>, s)[1]

Take(s, n) == SubSeq(s, 1, n)
Drop(s, n) == SubSeq(s, n + 1, Len(s))

\* @type: (a -> b, Set(a)) => a -> b;
RestrictToComplement(f, S) == [x \in DOMAIN(f) \ S |-> f[x]]

\* Some auxiliary definitions for the ledger model

transaction(memo, from, to, amount, fee, timestamp) == 
    [ memo |-> memo, from |-> from, to |-> to, amount |-> amount, fee |-> fee, timestamp |-> timestamp ]

block_from_transaction(tx, parent, timestamp) == [ transaction |-> tx, parent |-> parent, timestamp |-> timestamp]

\* This reflects the current code. To make No_Duplicate_Transactions hold, we should add the permitted drift here:
\*  DropWhile(transactions, LAMBDA t: t + TRANSACTION_WINDOW + PERMITTED_DRIFT <= now)
purge_old_transactions(transactions, now) == 
    DropWhile(transactions, LAMBDA t: t.timestamp + TRANSACTION_WINDOW <= now)

\* This doesn't cause problems even if from = to or similar, as it desugars into multiple function updates.
\* However, it will not complain if the from account is temporarily overdrawn, by sending from
\* the from account to itself an amount that's larger than the account's balance. Thus, this check
\* should happen elsewhere.
balances_add_payment(balances, from, to, amount, fee) ==
    [ balances EXCEPT ![from] = @ - amount - fee, ![to] = @ + amount, ![Minting_Account] = @ + fee]

add_block(blockchain, tx, parent, timestamp) == 
    Append(blockchain, block_from_transaction(tx, parent, timestamp))

\* Return the (possibly empty) set of smallest balances to trim, such that the number
\* of other balances doesn't exceed max_num
to_trim(balances, max_num) == 
    LET
        SmallerBalance(acc1, acc2) == balances[acc1] < balances[acc2]
    IN ToSet(Take(SetToSortSeq(DOMAIN(balances), SmallerBalance), Cardinality(DOMAIN(balances)) - max_num))

capacity_message == [type |-> "capacity"]

(* --algorithm Archive_Ledger {


\* The implementation uses the following main data structures:
\* - balances: a mapping from account identifiers to the number of tokens. 
\*   Internally, the balances are kept in a map, except for the minting account which is kept separately
\* - blockchain: a chain of blocks. A block consists of a transaction, a "now" timestamp (when it was added), and a hash of the previous block
\* - transactions_by_height: a list of block timestamps ("now" timestamps) with a transaction hash.
\* - transactions_by_hash: a map from a transaction hash to a height. Together with transactions_by_height, used to de-duplicate transactions.
variables
    balances = [a \in Accounts |-> INITIAL_BALANCE];
    \* We model only transactions_by_height, as transactions_by_hash is used just to de-duplicate
    \* transactions. So we'll assume that transactions_by_height and transactions_by_hash are correctly kept in sync
    \* by the code, and do the deduplication check bu a sequential lookup through transactions
    transactions_by_height = <<>>;
    blockchain = <<>>;
    \* This models the last_hash of the ledger's blockchain. This is a bit loose of a model, as the actual hash
    \* embodies the entire preceding chain of blocks, whereas this model just captures the last transaction.
    \* This is mostly important for our Blockchain_Is_A_Chain predicate. Our modeling could miss errors where
    \* a block points to a block with the same payload but a different parent, but we do check that the sequence of blocks
    \* forms a chain, so even we do miss an error, this should only be a minor issue.
    \* The implementation uses a None value as the sentinel for the start of the chain; we'll use a record with a dummy field.
    last_hash = [ start |-> {} ];
    \* Models current time
    now = 0;
    \* The implementation uses a lock to ensure that at any time only a single send call is talking to the archive 
    archive_guard = EMPTY_ARCHIVE_GUARD;
    \* This models the inter-canister streams
    ledger_to_archive = [x \in ToSet(Archive_Node_Ids) |-> <<>>];
    archive_to_ledger = [x \in ToSet(Archive_Node_Ids) |-> <<>>];
    \* The implementation keeps a vector of created archive nodes. Our model pre-creates all archive nodes,
    \* but as the implementation only talks to one node at a time, this models the (index of the) "active" archive node.
    \* Also doubles as a message to create an archive node canister. We model archive canister
    \* IDs as numbers; an archive node canister +Cal process starts running once the "create
    \* signal" (modeled through last_node) reaches the canister's ID
    last_node = 0;

macro ask_capacity(node_id) {
    ledger_to_archive := [ ledger_to_archive EXCEPT ![Archive_Node_Ids[node_id]] = Append(@, capacity_message) ];
}

macro archive_respond(archive_node, msg) {
    archive_to_ledger[archive_node] := Append(archive_to_ledger[archive_node], msg);
}

macro create_node_and_ask_capacity(){
    last_node := last_node + 1;
    ask_capacity(last_node);
    goto Receive_Capacity;
}

macro append_blocks(node_id, blocks) {
    ledger_to_archive[Archive_Node_Ids[node_id]] := Append(ledger_to_archive[Archive_Node_Ids[node_id]], [ type |-> "append_blocks", blocks |-> blocks ]);
}

process ( Send \in Send_Process_Ids )
    variable
        blocks_to_archive = <<>>;
        first_blocks = <<>>;
        num_sent_blocks = 0;
        chunk_len = 0;
    {
    Send_Begin:
        \* This models a non-deterministic choice of arguments to the send call, together with
        \* the timestamp assigned to the call by the IC (as the result of the ic_time canister call).
        \* As we must make the state space finite (and reasonably small) in order to run the analysis, 
        \* we must limit the choice of arguments in some way. We try to allow all "legal" arguments
        \* (that are not rejected by the checks in the code), as well as a small number of "illegal" ones
        \* (e.g., just exceeding the permitted drift), to get some confidence that the checks eliminate
        \* such arguments correctly.
        with(new_now \in {now + inc: inc \in TIME_INCREMENTS };
            created_timestamp \in (new_now - TRANSACTION_WINDOW - 1)..(new_now + PERMITTED_DRIFT + 1);
            from \in Accounts;
            to \in Accounts;
            amount \in 1..MAX_SEND_AMOUNT;
            fee \in {0} \union (TRANSACTION_FEE - 1..TRANSACTION_FEE + 1);
            memo \in Memos;
        ) {
            now := new_now;
            await from = Minting_Account => fee = 0;
            await from = Minting_Account => to # Minting_Account;
            await to = Minting_Account => fee = 0 /\ amount >= MIN_BURN_AMOUNT;
            await (from # Minting_Account /\ to # Minting_Account) => fee = TRANSACTION_FEE;
            \* As there can be multiple assignments to transactions (and later balances) in this block, use a with
            \* construct to store the intermediate values (as +Cal doesn't allow us to do multiple assignments
            \* to the same variable within a single atomic block)
            with(tmp_transactions = purge_old_transactions(transactions_by_height, now); 
                tx = transaction(memo, from, to, amount, fee, created_timestamp) ) 
            {
                if(created_timestamp + TRANSACTION_WINDOW < now 
                    \/ created_timestamp > now + PERMITTED_DRIFT
                    \* This models the check that the transaction isn't duplicated. Two things to note.
                    \* First, the implementation looks through transactions_by_hash, but we don't keep those.
                    \* Instead, we search sequentially through transactions_by_height, which is less
                    \* efficient, but should be equivalent, as the implementation should ensure that transactions_by_hash
                    \* and transactions_by_height contain the exact same transaction hashes.
                    \* Second, we model hashing as just the identity functions, since we only rely on
                    \* collision-resistance.
                    \/ \E i \in 1..Len(tmp_transactions): tmp_transactions[i].transaction = tx
                    \/ balances[from] < amount + fee) 
                {
                    transactions_by_height := tmp_transactions;
                    goto Send_End
                } else {
                    with(tmp_balances = balances_add_payment(balances, from, to, amount, fee);
                        \* The implementation removes all accounts with a zero balance from memory. We'll keep them around to simplify the model,
                        \* but don't take them into account when counting the number of accounts
                        nonzero_balances_without_minting = RestrictToComplement(tmp_balances, {Minting_Account} \union {a \in DOMAIN tmp_balances: tmp_balances[a] = 0});
                        tmp_blockchain = add_block(blockchain, tx, last_hash, now)) 
                    {
                        transactions_by_height := Append(tmp_transactions, [ transaction |-> tx, timestamp |-> now ]);
                        \* In the implementation, the minting account is kept separately (as the token_pool);
                        \* don't take it into account when looking at the total number of accounts, and don't
                        \* trim it.
                        if(Cardinality(DOMAIN nonzero_balances_without_minting) > MAX_NUMBER_OF_ACCOUNTS) {
                            with(balances_to_trim = to_trim(nonzero_balances_without_minting, MAX_NUMBER_OF_ACCOUNTS)) {
                                \* Unlike the Rust code, we don't explicitly delete balances, as, when queried, 
                                \* the Rust code returns 0 for balances of missing accounts; we just burn their balance instead
                                balances := FoldRight(
                                    LAMBDA account, bs:
                                        balances_add_payment(bs, account, Minting_Account, bs[account], 0),
                                    SetToSeq(balances_to_trim),
                                    tmp_balances
                                );
                                \* This definition is a bit complicated, but it adds a transaction corresponding to each of the above burns,
                                \* and sets its parent to the transaction preceding it
                                with(blockchain_and_last_hash = 
                                    FoldLeft(LAMBDA chain_and_last_hash, account:
                                          LET burn_tx == transaction(DEFAULT_MEMO, account, Minting_Account, tmp_balances[account], 0, now)
                                          IN
                                            << add_block(
                                                    chain_and_last_hash[1], 
                                                    burn_tx, 
                                                    chain_and_last_hash[2],
                                                    now),
                                                [ transaction |-> burn_tx, timestamp |-> now ] >>
                                        ,
                                        << tmp_blockchain, [ transaction |-> Last(tmp_blockchain).transaction, timestamp |-> Last(tmp_blockchain).timestamp ] >>,
                                        SetToSeq(balances_to_trim)
                                    )){
                                    blockchain := blockchain_and_last_hash[1];
                                    last_hash := blockchain_and_last_hash[2];
                                };
                            }
                        }
                        else {
                            balances := tmp_balances;
                            blockchain := tmp_blockchain;
                            last_hash := [ transaction |-> Last(blockchain).transaction, timestamp |-> Last(blockchain).timestamp ];
                        }
                    };
                    \* The remainder of our send call model reflects the call to archive_blocks
                    if(archive_guard # EMPTY_ARCHIVE_GUARD \/ Len(blockchain) < ARCHIVE_THRESHOLD) {
                        goto Send_End;
                    } else {
                        archive_guard := self;
                        blocks_to_archive := Take(blockchain, NUM_BLOCKS_TO_ARCHIVE);
                        if(last_node = 0) {
                            \* The ledger implementation: takes several steps to complete this: creating a canister, installing code,
                            \* and setting the controllers. All these steps are calls to the management canister, and as such are
                            \* non-atomic. However, in between making these calls, the ledger implementation does not change its 
                            \* internal state (other than the local program counter). Once the calls successfully complete, the ledger
                            \* adds the archive node to its internal vector of nodes, and proceeds to ask it for capacity.
                            \* We add a single interleaving point here (instead of multiple like the implementation), but this should
                            \* be equivalent to the behavior of the implementation.
                            \* Moreover, these calls to the management canister could fail. However, we leave modeling of such failures
                            \* as TODO for the moment.
                            goto Create_Node_And_Ask_Capacity;
                        } else {
                            \* In the implementation, if two different invocations of the ledger's send method both trigger a call to 
                            \* the same archive node to ask how much capacity it has, the
                            \* responses they receive cannot be confused, because each invocation of send gets a different
                            \* call context for its call. The model doesn't explicitly distinguish between call contexts,
                            \* but we rely on the archive guard above to ensure that at most one call from send to the archive
                            \* can be running at any point in time. This modeling is also conservative; even if the guard wasn't
                            \* sufficient to ensure that there are never two simultaneous calls, the consequence would be that 
                            \* the model would exhibit more behaviors than the implementation, so worst case we just get spurious
                            \* traces.
                            ask_capacity(last_node);
                            goto Receive_Capacity;
                        }
                    }
                }
            }
        };
    Create_Node_And_Ask_Capacity:
        create_node_and_ask_capacity();
    \* The implementation of archive_blocks uses awaits inside of loops. This needs some pretty heavy transformations
    \* of control flow to get to a TLA model.
    Receive_Capacity:
        await(archive_to_ledger[Archive_Node_Ids[last_node]] # <<>> /\ Head(archive_to_ledger[Archive_Node_Ids[last_node]]).type = "capacity");
        with(capacity = Head(archive_to_ledger[Archive_Node_Ids[last_node]]).remaining) {
            archive_to_ledger[Archive_Node_Ids[last_node]] := Tail(archive_to_ledger[Archive_Node_Ids[last_node]]);
            if(capacity = 0) {
                goto Create_Node_And_Ask_Capacity;
            } else {
                first_blocks := Take(blocks_to_archive, capacity);
                blocks_to_archive := Drop(blocks_to_archive, capacity);
            };
        };
    \* The interleaving here is an artifact of the model, as we need a label to jump to with the TLA goto to simulate the Rust loop.
    Send_Loop:
        with(chunk = Take(first_blocks, ARCHIVE_CHUNK_SIZE)) {
            first_blocks := Drop(first_blocks, ARCHIVE_CHUNK_SIZE);
            chunk_len := Len(chunk);
            append_blocks(last_node, chunk);
        };
    Response:
        await(archive_to_ledger[Archive_Node_Ids[last_node]] # <<>> /\ Head(archive_to_ledger[Archive_Node_Ids[last_node]]).type = "append_blocks");
        \* The implementation does check for errors, but there shouldn't be any
        \* TODO: add the possibility for the archive to reject blocks non-deterministically
        \*       but assume that append_blocks either appends all blocks or none
        archive_to_ledger[Archive_Node_Ids[last_node]] := Tail(archive_to_ledger[Archive_Node_Ids[last_node]]);
        num_sent_blocks := num_sent_blocks + chunk_len;
        \* TODO: check what it would take to record the assignment of block heights
        \* to archive nodes and make sure it stays consistent; this problem has happened
        \* in the past
        if(first_blocks # <<>>) {
            goto Send_Loop
        } else {
            if(blocks_to_archive # <<>>) {
                create_node_and_ask_capacity();
            } else {
                goto Purge_Blocks;
            }
        };
    Purge_Blocks:
        blockchain := Drop(blockchain, num_sent_blocks);
    Send_End:
        if(archive_guard = self){
            archive_guard := EMPTY_ARCHIVE_GUARD
        };
        \* Reset method local variables to defaults to cut down on the state space
        blocks_to_archive := <<>>;
        first_blocks := <<>>;
        num_sent_blocks := 0;
        chunk_len := 0;
    }

    process (Archive_Node \in ToSet(Archive_Node_Ids)) 
        variable
            blocks = <<>>;
    {
        Create_Archive_Node:
            await(last_node > 0 /\ Archive_Node_Ids[last_node] = self);
       Archive_Loop:
            while(TRUE) {
                either
                    {
                        await(ledger_to_archive[self] # <<>> /\ Head(ledger_to_archive[self]).type = "capacity");
                        ledger_to_archive[self] := Tail(ledger_to_archive[self]);
                        archive_respond(self, [ type |-> "capacity", remaining |-> ARCHIVE_CAPACITY - Len(blocks)]);
                    }
                or
                    {
                        await(ledger_to_archive[self] # <<>> /\ Head(ledger_to_archive[self]).type = "append_blocks");
                        with(blocks_to_append = Head(ledger_to_archive[self]).blocks) {
                            ledger_to_archive[self] := Tail(ledger_to_archive[self]);
                            blocks := blocks \o blocks_to_append;
                            archive_respond(self, [ type |-> "append_blocks"]);
                        };
                    };
            }
    }

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "2764ba7b" /\ chksum(tla) = "39ecfdf0")
VARIABLES balances, transactions_by_height, blockchain, last_hash, now, 
          archive_guard, ledger_to_archive, archive_to_ledger, last_node, pc, 
          blocks_to_archive, first_blocks, num_sent_blocks, chunk_len, blocks

vars == << balances, transactions_by_height, blockchain, last_hash, now, 
           archive_guard, ledger_to_archive, archive_to_ledger, last_node, pc, 
           blocks_to_archive, first_blocks, num_sent_blocks, chunk_len, 
           blocks >>

ProcSet == (Send_Process_Ids) \cup (ToSet(Archive_Node_Ids))

Init == (* Global variables *)
        /\ balances = [a \in Accounts |-> INITIAL_BALANCE]
        /\ transactions_by_height = <<>>
        /\ blockchain = <<>>
        /\ last_hash = [ start |-> {} ]
        /\ now = 0
        /\ archive_guard = EMPTY_ARCHIVE_GUARD
        /\ ledger_to_archive = [x \in ToSet(Archive_Node_Ids) |-> <<>>]
        /\ archive_to_ledger = [x \in ToSet(Archive_Node_Ids) |-> <<>>]
        /\ last_node = 0
        (* Process Send *)
        /\ blocks_to_archive = [self \in Send_Process_Ids |-> <<>>]
        /\ first_blocks = [self \in Send_Process_Ids |-> <<>>]
        /\ num_sent_blocks = [self \in Send_Process_Ids |-> 0]
        /\ chunk_len = [self \in Send_Process_Ids |-> 0]
        (* Process Archive_Node *)
        /\ blocks = [self \in ToSet(Archive_Node_Ids) |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Send_Process_Ids -> "Send_Begin"
                                        [] self \in ToSet(Archive_Node_Ids) -> "Create_Archive_Node"]

Send_Begin(self) == /\ pc[self] = "Send_Begin"
                    /\ \E new_now \in {now + inc: inc \in TIME_INCREMENTS }:
                         \E created_timestamp \in (new_now - TRANSACTION_WINDOW - 1)..(new_now + PERMITTED_DRIFT + 1):
                           \E from \in Accounts:
                             \E to \in Accounts:
                               \E amount \in 1..MAX_SEND_AMOUNT:
                                 \E fee \in {0} \union (TRANSACTION_FEE - 1..TRANSACTION_FEE + 1):
                                   \E memo \in Memos:
                                     /\ now' = new_now
                                     /\ from = Minting_Account => fee = 0
                                     /\ from = Minting_Account => to # Minting_Account
                                     /\ to = Minting_Account => fee = 0 /\ amount >= MIN_BURN_AMOUNT
                                     /\ (from # Minting_Account /\ to # Minting_Account) => fee = TRANSACTION_FEE
                                     /\ LET tmp_transactions == purge_old_transactions(transactions_by_height, now') IN
                                          LET tx == transaction(memo, from, to, amount, fee, created_timestamp) IN
                                            IF created_timestamp + TRANSACTION_WINDOW < now'
                                                \/ created_timestamp > now' + PERMITTED_DRIFT
                                               
                                               
                                               
                                               
                                               
                                               
                                               
                                                \/ \E i \in 1..Len(tmp_transactions): tmp_transactions[i].transaction = tx
                                                \/ balances[from] < amount + fee
                                               THEN /\ transactions_by_height' = tmp_transactions
                                                    /\ pc' = [pc EXCEPT ![self] = "Send_End"]
                                                    /\ UNCHANGED << balances, 
                                                                    blockchain, 
                                                                    last_hash, 
                                                                    archive_guard, 
                                                                    ledger_to_archive, 
                                                                    blocks_to_archive >>
                                               ELSE /\ LET tmp_balances == balances_add_payment(balances, from, to, amount, fee) IN
                                                         LET nonzero_balances_without_minting == RestrictToComplement(tmp_balances, {Minting_Account} \union {a \in DOMAIN tmp_balances: tmp_balances[a] = 0}) IN
                                                           LET tmp_blockchain == add_block(blockchain, tx, last_hash, now') IN
                                                             /\ transactions_by_height' = Append(tmp_transactions, [ transaction |-> tx, timestamp |-> now' ])
                                                             /\ IF Cardinality(DOMAIN nonzero_balances_without_minting) > MAX_NUMBER_OF_ACCOUNTS
                                                                   THEN /\ LET balances_to_trim == to_trim(nonzero_balances_without_minting, MAX_NUMBER_OF_ACCOUNTS) IN
                                                                             /\ balances' =             FoldRight(
                                                                                                LAMBDA account, bs:
                                                                                                    balances_add_payment(bs, account, Minting_Account, bs[account], 0),
                                                                                                SetToSeq(balances_to_trim),
                                                                                                tmp_balances
                                                                                            )
                                                                             /\ LET blockchain_and_last_hash == FoldLeft(LAMBDA chain_and_last_hash, account:
                                                                                                                      LET burn_tx == transaction(DEFAULT_MEMO, account, Minting_Account, tmp_balances[account], 0, now')
                                                                                                                      IN
                                                                                                                        << add_block(
                                                                                                                                chain_and_last_hash[1],
                                                                                                                                burn_tx,
                                                                                                                                chain_and_last_hash[2],
                                                                                                                                now'),
                                                                                                                            [ transaction |-> burn_tx, timestamp |-> now' ] >>
                                                                                                                    ,
                                                                                                                    << tmp_blockchain, [ transaction |-> Last(tmp_blockchain).transaction, timestamp |-> Last(tmp_blockchain).timestamp ] >>,
                                                                                                                    SetToSeq(balances_to_trim)
                                                                                                                ) IN
                                                                                  /\ blockchain' = blockchain_and_last_hash[1]
                                                                                  /\ last_hash' = blockchain_and_last_hash[2]
                                                                   ELSE /\ balances' = tmp_balances
                                                                        /\ blockchain' = tmp_blockchain
                                                                        /\ last_hash' = [ transaction |-> Last(blockchain').transaction, timestamp |-> Last(blockchain').timestamp ]
                                                    /\ IF archive_guard # EMPTY_ARCHIVE_GUARD \/ Len(blockchain') < ARCHIVE_THRESHOLD
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "Send_End"]
                                                               /\ UNCHANGED << archive_guard, 
                                                                               ledger_to_archive, 
                                                                               blocks_to_archive >>
                                                          ELSE /\ archive_guard' = self
                                                               /\ blocks_to_archive' = [blocks_to_archive EXCEPT ![self] = Take(blockchain', NUM_BLOCKS_TO_ARCHIVE)]
                                                               /\ IF last_node = 0
                                                                     THEN /\ pc' = [pc EXCEPT ![self] = "Create_Node_And_Ask_Capacity"]
                                                                          /\ UNCHANGED ledger_to_archive
                                                                     ELSE /\ ledger_to_archive' = [ ledger_to_archive EXCEPT ![Archive_Node_Ids[last_node]] = Append(@, capacity_message) ]
                                                                          /\ pc' = [pc EXCEPT ![self] = "Receive_Capacity"]
                    /\ UNCHANGED << archive_to_ledger, last_node, first_blocks, 
                                    num_sent_blocks, chunk_len, blocks >>

Create_Node_And_Ask_Capacity(self) == /\ pc[self] = "Create_Node_And_Ask_Capacity"
                                      /\ last_node' = last_node + 1
                                      /\ ledger_to_archive' = [ ledger_to_archive EXCEPT ![Archive_Node_Ids[last_node']] = Append(@, capacity_message) ]
                                      /\ pc' = [pc EXCEPT ![self] = "Receive_Capacity"]
                                      /\ UNCHANGED << balances, 
                                                      transactions_by_height, 
                                                      blockchain, last_hash, 
                                                      now, archive_guard, 
                                                      archive_to_ledger, 
                                                      blocks_to_archive, 
                                                      first_blocks, 
                                                      num_sent_blocks, 
                                                      chunk_len, blocks >>

Receive_Capacity(self) == /\ pc[self] = "Receive_Capacity"
                          /\ (archive_to_ledger[Archive_Node_Ids[last_node]] # <<>> /\ Head(archive_to_ledger[Archive_Node_Ids[last_node]]).type = "capacity")
                          /\ LET capacity == Head(archive_to_ledger[Archive_Node_Ids[last_node]]).remaining IN
                               /\ archive_to_ledger' = [archive_to_ledger EXCEPT ![Archive_Node_Ids[last_node]] = Tail(archive_to_ledger[Archive_Node_Ids[last_node]])]
                               /\ IF capacity = 0
                                     THEN /\ pc' = [pc EXCEPT ![self] = "Create_Node_And_Ask_Capacity"]
                                          /\ UNCHANGED << blocks_to_archive, 
                                                          first_blocks >>
                                     ELSE /\ first_blocks' = [first_blocks EXCEPT ![self] = Take(blocks_to_archive[self], capacity)]
                                          /\ blocks_to_archive' = [blocks_to_archive EXCEPT ![self] = Drop(blocks_to_archive[self], capacity)]
                                          /\ pc' = [pc EXCEPT ![self] = "Send_Loop"]
                          /\ UNCHANGED << balances, transactions_by_height, 
                                          blockchain, last_hash, now, 
                                          archive_guard, ledger_to_archive, 
                                          last_node, num_sent_blocks, 
                                          chunk_len, blocks >>

Send_Loop(self) == /\ pc[self] = "Send_Loop"
                   /\ LET chunk == Take(first_blocks[self], ARCHIVE_CHUNK_SIZE) IN
                        /\ first_blocks' = [first_blocks EXCEPT ![self] = Drop(first_blocks[self], ARCHIVE_CHUNK_SIZE)]
                        /\ chunk_len' = [chunk_len EXCEPT ![self] = Len(chunk)]
                        /\ ledger_to_archive' = [ledger_to_archive EXCEPT ![Archive_Node_Ids[last_node]] = Append(ledger_to_archive[Archive_Node_Ids[last_node]], [ type |-> "append_blocks", blocks |-> chunk ])]
                   /\ pc' = [pc EXCEPT ![self] = "Response"]
                   /\ UNCHANGED << balances, transactions_by_height, 
                                   blockchain, last_hash, now, archive_guard, 
                                   archive_to_ledger, last_node, 
                                   blocks_to_archive, num_sent_blocks, blocks >>

Response(self) == /\ pc[self] = "Response"
                  /\ (archive_to_ledger[Archive_Node_Ids[last_node]] # <<>> /\ Head(archive_to_ledger[Archive_Node_Ids[last_node]]).type = "append_blocks")
                  /\ archive_to_ledger' = [archive_to_ledger EXCEPT ![Archive_Node_Ids[last_node]] = Tail(archive_to_ledger[Archive_Node_Ids[last_node]])]
                  /\ num_sent_blocks' = [num_sent_blocks EXCEPT ![self] = num_sent_blocks[self] + chunk_len[self]]
                  /\ IF first_blocks[self] # <<>>
                        THEN /\ pc' = [pc EXCEPT ![self] = "Send_Loop"]
                             /\ UNCHANGED << ledger_to_archive, last_node >>
                        ELSE /\ IF blocks_to_archive[self] # <<>>
                                   THEN /\ last_node' = last_node + 1
                                        /\ ledger_to_archive' = [ ledger_to_archive EXCEPT ![Archive_Node_Ids[last_node']] = Append(@, capacity_message) ]
                                        /\ pc' = [pc EXCEPT ![self] = "Receive_Capacity"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Purge_Blocks"]
                                        /\ UNCHANGED << ledger_to_archive, 
                                                        last_node >>
                  /\ UNCHANGED << balances, transactions_by_height, blockchain, 
                                  last_hash, now, archive_guard, 
                                  blocks_to_archive, first_blocks, chunk_len, 
                                  blocks >>

Purge_Blocks(self) == /\ pc[self] = "Purge_Blocks"
                      /\ blockchain' = Drop(blockchain, num_sent_blocks[self])
                      /\ pc' = [pc EXCEPT ![self] = "Send_End"]
                      /\ UNCHANGED << balances, transactions_by_height, 
                                      last_hash, now, archive_guard, 
                                      ledger_to_archive, archive_to_ledger, 
                                      last_node, blocks_to_archive, 
                                      first_blocks, num_sent_blocks, chunk_len, 
                                      blocks >>

Send_End(self) == /\ pc[self] = "Send_End"
                  /\ IF archive_guard = self
                        THEN /\ archive_guard' = EMPTY_ARCHIVE_GUARD
                        ELSE /\ TRUE
                             /\ UNCHANGED archive_guard
                  /\ blocks_to_archive' = [blocks_to_archive EXCEPT ![self] = <<>>]
                  /\ first_blocks' = [first_blocks EXCEPT ![self] = <<>>]
                  /\ num_sent_blocks' = [num_sent_blocks EXCEPT ![self] = 0]
                  /\ chunk_len' = [chunk_len EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << balances, transactions_by_height, blockchain, 
                                  last_hash, now, ledger_to_archive, 
                                  archive_to_ledger, last_node, blocks >>

Send(self) == Send_Begin(self) \/ Create_Node_And_Ask_Capacity(self)
                 \/ Receive_Capacity(self) \/ Send_Loop(self)
                 \/ Response(self) \/ Purge_Blocks(self) \/ Send_End(self)

Create_Archive_Node(self) == /\ pc[self] = "Create_Archive_Node"
                             /\ (last_node > 0 /\ Archive_Node_Ids[last_node] = self)
                             /\ pc' = [pc EXCEPT ![self] = "Archive_Loop"]
                             /\ UNCHANGED << balances, transactions_by_height, 
                                             blockchain, last_hash, now, 
                                             archive_guard, ledger_to_archive, 
                                             archive_to_ledger, last_node, 
                                             blocks_to_archive, first_blocks, 
                                             num_sent_blocks, chunk_len, 
                                             blocks >>

Archive_Loop(self) == /\ pc[self] = "Archive_Loop"
                      /\ \/ /\ (ledger_to_archive[self] # <<>> /\ Head(ledger_to_archive[self]).type = "capacity")
                            /\ ledger_to_archive' = [ledger_to_archive EXCEPT ![self] = Tail(ledger_to_archive[self])]
                            /\ archive_to_ledger' = [archive_to_ledger EXCEPT ![self] = Append(archive_to_ledger[self], ([ type |-> "capacity", remaining |-> ARCHIVE_CAPACITY - Len(blocks[self])]))]
                            /\ UNCHANGED blocks
                         \/ /\ (ledger_to_archive[self] # <<>> /\ Head(ledger_to_archive[self]).type = "append_blocks")
                            /\ LET blocks_to_append == Head(ledger_to_archive[self]).blocks IN
                                 /\ ledger_to_archive' = [ledger_to_archive EXCEPT ![self] = Tail(ledger_to_archive[self])]
                                 /\ blocks' = [blocks EXCEPT ![self] = blocks[self] \o blocks_to_append]
                                 /\ archive_to_ledger' = [archive_to_ledger EXCEPT ![self] = Append(archive_to_ledger[self], ([ type |-> "append_blocks"]))]
                      /\ pc' = [pc EXCEPT ![self] = "Archive_Loop"]
                      /\ UNCHANGED << balances, transactions_by_height, 
                                      blockchain, last_hash, now, 
                                      archive_guard, last_node, 
                                      blocks_to_archive, first_blocks, 
                                      num_sent_blocks, chunk_len >>

Archive_Node(self) == Create_Archive_Node(self) \/ Archive_Loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Send_Process_Ids: Send(self))
           \/ (\E self \in ToSet(Archive_Node_Ids): Archive_Node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


Archive_Nodes_Not_Overflowing == \A i \in DOMAIN(Archive_Node_Ids):
    Len(blocks[Archive_Node_Ids[i]]) <= ARCHIVE_CAPACITY 

Balance_Sum(bs) == FoldFunction(LAMBDA i, j: i + j, 0, bs)
Constant_Balance_Sum == Balance_Sum(balances') = Balance_Sum(balances)

not_duplicates(block1, block2) == 
    \/ block1.transaction # block2.transaction
    \/ block1.transaction.to = Minting_Account

\* This property currently doesn't hold, because purging of old transactions is too aggressive
No_Duplicate_Transactions ==
    /\ \A an1 \in ToSet(Archive_Node_Ids), an2 \in ToSet(Archive_Node_Ids):
        /\ \A i1 \in 1..Len(blocks[an1]), i2 \in 1..Len(blocks[an2]):
            an1 # an2 \/ i1 # i2 => not_duplicates(blocks[an1][i1], blocks[an2][i2])
        /\ archive_guard = EMPTY_ARCHIVE_GUARD => \A i1 \in 1..Len(blocks[an1]), i2 \in 1..Len(blockchain):
            not_duplicates(blocks[an1][i1], blockchain[i2])
    /\ \A i \in 1..Len(blockchain), j \in 1..Len(blockchain): i # j => not_duplicates(blockchain[i], blockchain[j])


nonzero_accounts(bs) ==
    Cardinality({x \in DOMAIN(bs) : bs[x] > 0 })

\* In the initial state, the number of accounts with non-zero balances can be larger than
\* the limit. However, once the number goes under the limit, it never exceeds it again.
Nonminting_Number_Stays_Limited == LET 
        count_nonzero(b) == nonzero_accounts(RestrictToComplement(b, {Minting_Account}))
    IN 
        count_nonzero(balances) <= MAX_NUMBER_OF_ACCOUNTS 
        => count_nonzero(balances') <= MAX_NUMBER_OF_ACCOUNTS

Blockchain_Is_A_Chain == \A i \in DOMAIN(Archive_Node_Ids):
    \* Check that the blocks in a node are a sequence
    /\ DOMAIN(blocks[Archive_Node_Ids[i]]) = 1..Len(blocks[Archive_Node_Ids[i]])
    /\ \A j \in DOMAIN(blocks[Archive_Node_Ids[i]]):
        /\ j > 1 => blocks[Archive_Node_Ids[i]][j].parent.transaction = blocks[Archive_Node_Ids[i]][j-1].transaction
        /\ j > 1 => blocks[Archive_Node_Ids[i]][j].parent.timestamp = blocks[Archive_Node_Ids[i]][j-1].timestamp
    /\ i > 1 /\ blocks[Archive_Node_Ids[i]] # <<>> => 
        /\ blocks[Archive_Node_Ids[i]][1].parent.transaction = blocks[Archive_Node_Ids[i-1]][Len(blocks[Archive_Node_Ids[i-1]])].transaction
        /\ blocks[Archive_Node_Ids[i]][1].parent.timestamp = blocks[Archive_Node_Ids[i-1]][Len(blocks[Archive_Node_Ids[i-1]])].timestamp

Full_Invariant == [][
        /\ Blockchain_Is_A_Chain
        /\ Nonminting_Number_Stays_Limited
        /\ Constant_Balance_Sum
        /\ Archive_Nodes_Not_Overflowing
\*        /\ No_Duplicate_Transactions
    ]_vars

\************************************************
\* Sanity-checking invariants; we should be able to invalidate them
Archive_Sanity == \A an \in ToSet(Archive_Node_Ids):
    blocks[an] = <<>>

Can_Fill_Two_Archives == blocks[Archive_Node_Ids[2]] = <<>>

Nothing_In_Blockchain == \A s \in Send_Process_Ids:
    blockchain = <<>>

No_Messages_To_Archive == \A an \in ToSet(Archive_Node_Ids):
    ledger_to_archive[an] = <<>>

Send_Sanity == \A s \in Send_Process_Ids:
    pc[s] # "Send_End"

Test_Dropwhile == DropWhile(<< 0, 1, 2, 3, 4, 5, 6>>, LAMBDA x: x < 3) = << 3, 4, 5, 6 >>

====
