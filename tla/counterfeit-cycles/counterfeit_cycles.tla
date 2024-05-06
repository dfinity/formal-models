------------------------- MODULE counterfeit_cycles -------------------------
EXTENDS TLC, Integers, Sequences, SequencesExt, FiniteSets, FiniteSetsExt

CONSTANT SUBNETS, \* The set of subnets.
         STARTING_BALANCE_PER_SUBNET,
         MAX_DISHONEST_TRANSFERS,
         MAX_TRANSFERS,
         MAX_COUNTERFEIT_CYCLES

ASSUME MAX_TRANSFERS >= MAX_DISHONEST_TRANSFERS

VARIABLE ledger, subnets, subnetMsgs, numDishonestActions, numTransfers

TOTAL_SUPPLY == STARTING_BALANCE_PER_SUBNET * Cardinality(SUBNETS)
TRANSFER == "transfer"
APPROVE == "approve"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

SubnetsInit ==
    \* Initialize the state of subnets.
    /\ subnets = [
        s \in SUBNETS |-> [
            \* The true balance of (finalized) cycles on the subnet.
            \* In this model, subnets do not maliciously manipulate this balance.
            \* Note that the balance can be negative if the subnet maliciously
            \* sends more cycles than it has.

            \* The balance of (finalized) cycles on the subnet.
            \* In this model, subnets do not maliciously manipulate this balance.
            balance |-> STARTING_BALANCE_PER_SUBNET,

            \* The unfinalized cycles received from other subnets.
            \* Cycles received from other subnets are initially unfinalized
            \* until they are approved by the ledger.
            unfinalized |-> [sb \in SUBNETS |-> 0],

            \* A queue of outgoing messages from the subnet to the ledger.
            msgsToLedger |-> <<>>,

            \* Whether or not the subnet is honest. This isn't strictly required
            \* in this model.
            \* Initially, all subnets behave honestly.
            honest |-> TRUE
         ]
     ]
    /\ subnetMsgs = {}
    /\ numDishonestActions = 0
    /\ numTransfers = 0

LedgerInit ==
  \* Initialize the state of the ledger.
  ledger = [
    \* The balance of each subnet.
    balances |-> [s \in SUBNETS |-> STARTING_BALANCE_PER_SUBNET],

    \* The queue of messages to be processed.
    msgs |-> [s \in SUBNETS |-> <<>>]
  ]

Init ==
  /\ LedgerInit
  /\ SubnetsInit

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type checks                                                             *)
(***************************************************************************)

TransferMessage ==
  \* A message to transfer cycles between subnets.
  [id: Nat, type : {TRANSFER}, from : SUBNETS, to : SUBNETS, amount : Nat \ {0}]

\* The set of all possible messages that are sent/received by subnets.
SubnetMessages ==
  \* Transferring cycles from one subnet to another.
  TransferMessage
    \union

  \* Approving a cycles transfer.
  \* This message is sent by the ledger to indicate that the `amount` sent is
  \* now finalized.
  [id: Nat, type : {APPROVE}, from : SUBNETS, to : SUBNETS, amount : Nat \ {0}]

LedgerMessages ==
  \* The set of all possible messages that can be received by the Ledger.
  TransferMessage

SubnetsTypeOK ==
  /\ \A s \in subnetMsgs: s \in SubnetMessages
  /\ subnets \in [SUBNETS -> [
        balance: Int,
        unfinalized: [SUBNETS -> Nat],
        msgsToLedger: Seq(LedgerMessages),
        honest: {TRUE, FALSE}
     ]]

LedgerTypesOK ==
  \* Type-correctness invariant.
  /\ DOMAIN ledger.balances = SUBNETS
  /\ \A s \in SUBNETS: ledger.balances[s] >= 0
  /\ \A i \in DOMAIN ledger.msgs: ToSet(ledger.msgs[i]) \subseteq LedgerMessages

TypesOK ==
  \* Type-correctness invariant.
  /\ LedgerTypesOK
  /\ SubnetsTypeOK

-----------------------------------------------------------------------------
(***************************************************************************)
(* Subnet actions                                                          *)
(***************************************************************************)

SubnetSendTransfer ==
  (* Honestly sends a transfers cycles from one subnet to another. *)
  numTransfers < MAX_TRANSFERS

  \* Choose two subnets.
  /\ \E sender, receiver \in SUBNETS: sender /= receiver

    \* Choose an amount that's within the subnet's balance.
    /\ \E amount \in 1..subnets[sender].balance:

        \* Send a transfer to the receiver.
        /\ subnetMsgs' = subnetMsgs \union {[
                id |-> numTransfers,
                type |-> TRANSFER,
                from |-> sender,
                to |-> receiver,
                amount |-> amount
            ]}

        \* Subtract amount from sender's balance.
        /\ subnets' = [subnets EXCEPT ![sender].balance = @ - amount]

        \* Limit the number of transfers to keep the state space bounded.
        /\ numTransfers' = numTransfers + 1

        /\ UNCHANGED<<ledger, numDishonestActions>>

SubnetDishonestSendTransfer ==
    (* Maliciously transfers more cycles than the subnet's own balance. *)
    numTransfers < MAX_TRANSFERS
    /\ numDishonestActions < MAX_DISHONEST_TRANSFERS
    /\ \E sender, receiver \in SUBNETS:
        /\ sender /= receiver

        \* Limit the number of dishonest actions to keep the state space bounded.
        /\ numDishonestActions' = numDishonestActions + 1
        /\ numTransfers' = numTransfers + 1

        \* Choose an amount that's greater than the balance.
        /\ \E counterfeit_cycles \in 1..MAX_COUNTERFEIT_CYCLES:
            /\ LET amount == Max({subnets[sender].balance + counterfeit_cycles, 1}) IN
                \* Send a transfer to the receiver.
                /\ subnetMsgs' = subnetMsgs \union {[
                        id |-> numTransfers,
                        type |-> TRANSFER,
                        from |-> sender,
                        to |-> receiver,
                        amount |-> amount
                    ]}

                \* Mark subnet as dishonest and subtract balance.
                /\ subnets' = [subnets EXCEPT ![sender].honest = FALSE,
                                              ![sender].balance = @ - amount]

                /\ UNCHANGED<<ledger>>

SubnetReceiveTransfer ==
  \E msg \in subnetMsgs:
      msg.type = TRANSFER
      /\ subnets' = [
                         \* Add amount in transfer to the unfinalized balance.
          subnets EXCEPT ![msg.to].unfinalized[msg.from] = @ + msg.amount,
                         \* Add message to ledger outgoing queue.
                         ![msg.to].msgsToLedger = Append(@, msg)
         ]
      \* Remove message from subnet messages.
      /\ subnetMsgs' = subnetMsgs \ {msg}
      /\ UNCHANGED<<ledger, numDishonestActions, numTransfers>>

LedgerPoll ==
  \E s \in SUBNETS: Len(subnets[s].msgsToLedger) > 0
    /\ LET msg == Head(subnets[s].msgsToLedger) IN
      \* Send message to ledger.
      /\ ledger' = [ledger EXCEPT !["msgs"][s] = Append(@,
          [id |-> msg.id, type |-> TRANSFER, from |-> msg.from, to |-> msg.to, amount |-> msg.amount]
        )]
      \* Remove message from the queue.
      /\ subnets' = [
            subnets EXCEPT ![s].msgsToLedger = Tail(@)
         ]
      /\ UNCHANGED<<subnetMsgs, numDishonestActions, numTransfers>>

SubnetReceiveApprove ==
  \E msg \in subnetMsgs:
      msg.type = APPROVE
      /\ subnets' = [
        subnets EXCEPT ![msg.to].unfinalized[msg.from] = @ - msg.amount,
                       ![msg.to].balance = @ + msg.amount
      ]
      \* Remove message from subnet messages.
      /\ subnetMsgs' = subnetMsgs \ {msg}
      /\ UNCHANGED<<ledger, numDishonestActions, numTransfers>>

LedgerReceiveTransferMessage ==
  \* If a transfer message is received and there is enough balance, then update the
  \* balances and send the approval to the subnet.
  \E s \in SUBNETS: Len(ledger.msgs[s]) > 0
    /\ LET msg == Head(ledger.msgs[s]) IN
        /\ msg.type = TRANSFER
        /\ msg.amount <= ledger.balances[msg.from]
        /\ ledger' = [
            ledger EXCEPT
            \* Transaction is valid. Update ledger balances.
            !["balances"][msg.from] = @ - msg.amount,
            !["balances"][msg.to] = @ + msg.amount,

            \* Remove msg from queue.
            !["msgs"][s] = Tail(@)]
        /\ subnetMsgs'= subnetMsgs \union {[
            id |-> msg.id,
            type |-> APPROVE,
            from |-> msg.from,
            to |-> msg.to,
            amount |-> msg.amount
            ]}
        /\ UNCHANGED<<subnets, numDishonestActions, numTransfers>>

Idle ==
    \* Do nothing.
    \* Once the maximum number of transfers is reached, the system is idle.
    \* This is added to prevent TLA from thinking that it's stuck in a deadlock.
    /\ (numTransfers >= MAX_TRANSFERS \/ numDishonestActions >= MAX_DISHONEST_TRANSFERS)
    /\ UNCHANGED<<ledger, subnets, subnetMsgs, numDishonestActions, numTransfers>>

Next ==
  \/ SubnetSendTransfer
  \/ SubnetReceiveTransfer
  \/ SubnetReceiveApprove
  \/ SubnetDishonestSendTransfer
  \/ LedgerReceiveTransferMessage
  \/ LedgerPoll
  \/ Idle

BalancesNonNegative ==
  (*************************************************************************)
  (* Invariant to ensure that all subnet balances are non-negative.        *)
  (*************************************************************************)
  \A s \in SUBNETS: subnets[s].balance >= 0

RECURSIVE RecordToSeq(_,_)
RecordToSeq(f, ks) ==
  \* Helper method to transform a record's values into a sequence.
  IF ks = {} THEN << >>
  ELSE << f[CHOOSE k \in ks: TRUE] >> \o RecordToSeq(f, ks \ {CHOOSE k \in ks: TRUE})

RECURSIVE SumSeq(_)
SumSeq(s) ==
  \* Helper method to sum a sequence
  IF Len(s) = 0 THEN 0
  ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE SumBalance(_)
SumBalance(s) ==
  \* Helper method to sum a sequence
  IF Len(s) = 0 THEN 0
  ELSE Head(s).balance + SumBalance(Tail(s))

TotalSupplyInLedgerRemainsConstant ==
    SumSeq(RecordToSeq(ledger.balances, SUBNETS)) = TOTAL_SUPPLY

NoFakeCyclesAreCreated ==
  \* The total supply of cycles that each subnet thinks it has is capped.
  /\ SumBalance(RecordToSeq(subnets, SUBNETS)) <= TOTAL_SUPPLY

SubnetNeverHasMoreBalanceThanLedger ==
  \* The subnet's true balance is at most the balance stored in the ledger
  \* for that subnet.
  \A s \in SUBNETS: subnets[s].balance <= ledger.balances[s]

\* TODO: is this invariant evaluated ever?
LedgerAndSubnetBalancesMatchAfterMsgProcessing ==
  \* Ledger and subnets have the same balances whenever all messages are
  \* processed.
  /\ (\A s \in SUBNETS: Len(ledger.msgs[s]) = 0)
    /\ (\A s \in SUBNETS: Len(subnets[s].msgsToLedger) = 0)
    /\ Cardinality(subnetMsgs) = 0
  => \A sn \in SUBNETS: ledger.balances[sn] = subnets[sn].balance

=============================================================================
