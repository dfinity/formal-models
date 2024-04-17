------------------------- MODULE counterfeit_cycles -------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT SUBNETS, \* The set of subnets.
         STARTING_BALANCE_PER_SUBNET

VARIABLE ledger, subnets, subnetMsgs


-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

SubnetsInit ==
  \* Initialize the state of subnets.
  /\ subnets = [
         s \in SUBNETS |-> [
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
  /\ subnetMsgs = <<>>
  
LedgerInit ==
  \* Initialize the state of the ledger.
  ledger = [
    \* The balance of each subnet.
    balances |-> [s \in SUBNETS |-> STARTING_BALANCE_PER_SUBNET],
    
    \* The queue of messages to be processed.
    msgs |-> <<>>,
    
    \* The set of subnets that the ledger thinks is dishonest.
    \* NOTE: I think this is redundant and is not needed for this model.
    dishonestSubnets |-> {}
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
  [type : {"transfer"}, from : SUBNETS, to : SUBNETS, amount : Nat \ {0}]

\* The set of all possible messages that are sent/received by subnets.
SubnetMessages ==
  \* Transferring cycles from one subnet to another.
  TransferMessage
    \union
    
  \* Approving a cycles transfer.
  \* This message is sent by the ledger to indicate that the `amount` sent is
  \* now finalized.
  [type : {"approve"}, from : SUBNETS, to : SUBNETS, amount : Nat \ {0}]  

LedgerMessages ==
  \* The set of all possible messages that can be received by the Ledger.
  TransferMessage

SubnetsTypeOK ==
  /\ \A i \in DOMAIN subnetMsgs: {subnetMsgs[i]} \subseteq SubnetMessages
  /\ subnets \in [SUBNETS -> [
        balance: Nat,
        unfinalized: [SUBNETS -> Nat],
        msgsToLedger: Seq(LedgerMessages),
        honest: {TRUE, FALSE}
     ]]

LedgerTypesOK ==
  \* Type-correctness invariant.
  /\ DOMAIN ledger.balances = SUBNETS
  /\ \A s \in SUBNETS: ledger.balances[s] >= 0
  /\ ledger.dishonestSubnets \subseteq SUBNETS
  /\ \A i \in DOMAIN ledger.msgs: {ledger.msgs[i]} \subseteq LedgerMessages
  
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
  
  \* Choose two subnets.
  \E sender, receiver \in SUBNETS: sender /= receiver
  /\ subnets[sender].balance > 0
  
  \* Choose an amount that's within the subnet's balance.
  /\ \E amount \in 1..subnets[sender].balance:
  
  \* Send a transfer to the receiver.
  /\ subnetMsgs' = Append(subnetMsgs, [
        type |-> "transfer",
        from |-> sender,
        to |-> receiver,
        amount |-> amount
     ])
     
  \* Subtract amount from sender's balance.
  /\ subnets' = [subnets EXCEPT ![sender].balance = @ - amount]
  
  /\ UNCHANGED<<ledger>>

SubnetDishonestSendTransfer ==
  (* Maliciously transfers more cycles than the subnet's own balance. *)
  
  \E sender, receiver \in SUBNETS: sender /= receiver

  \* To keep the state space bounded, a subnet can make a dishonest
  \* transfer at most once.
  /\ subnets[sender].honest
  
  \* Send a transfer to the receiver.
  /\ subnetMsgs' = Append(subnetMsgs, [
        type |-> "transfer",
        from |-> sender,
        to |-> receiver,
        \* Choose an amount that's greater than the balance.
        amount |-> subnets[sender].balance + 10
  ])
  
  \* Mark subnet as dishonest to avoid repeating this transfer again.
  /\ subnets' = [subnets EXCEPT ![sender].honest = FALSE]
  
  /\ UNCHANGED<<ledger>>


SubnetReceiveTransfer ==
  /\ Len(subnetMsgs) > 0
  /\ LET msg == Head(subnetMsgs) IN
      /\ msg.type = "transfer"
      /\ subnets' = [
                         \* Add amount in transfer to the unfinalized balance.
          subnets EXCEPT ![msg.to].unfinalized[msg.from] = @ + msg.amount,
                         \* Add message to ledger outgoing queue.
                         ![msg.to].msgsToLedger = Append(@, msg)
         ]
      \* Remove message from subnet messages.
      /\ subnetMsgs' = Tail(subnetMsgs)
      /\ UNCHANGED<<ledger>>
      
LedgerPoll ==
  \E s \in SUBNETS: Len(subnets[s].msgsToLedger) > 0
    /\ LET msg == Head(subnets[s].msgsToLedger) IN
      \* Send message to ledger.
      /\ ledger' = [ledger EXCEPT !["msgs"] = Append(@,
          [type |-> "transfer", from |-> msg.from, to |-> msg.to, amount |-> msg.amount]
        )]
      \* Remove message from the queue.
      /\ subnets' = [
            subnets EXCEPT ![s].msgsToLedger = Tail(@)
         ]
      /\ UNCHANGED<<subnetMsgs>>

SubnetReceiveApprove == 
  /\ Len(subnetMsgs) > 0
  /\ LET msg == Head(subnetMsgs) IN
      msg.type = "approve"
      /\ subnets' = [
        subnets EXCEPT ![msg.to].unfinalized[msg.from] = @ - msg.amount,
                       ![msg.to].balance = @ + msg.amount
      ]
      \* Remove message from subnet messages.
      /\ subnetMsgs' = Tail(subnetMsgs)
      /\ UNCHANGED<<ledger>>

LedgerReceiveMessage ==
  \* If a message is there and the balance checks out, then update it and
  \* send approval to the subnet. If they don't check out, add sender to
  \* the dishonestSubnets set and don't update balances.
  LET
    msg == Head(ledger.msgs)
  IN
   /\ Len(ledger.msgs) > 0
   
   /\ IF msg.amount > ledger.balances[msg.from] THEN
        
        
        /\ ledger' = [ledger EXCEPT
               \* Remove msg from queue.
               !["msgs"] = Tail(@),
               
               \* Subnet spent more than it has. Mark it as a bad subnet.
               !["dishonestSubnets"] = @ \union {msg.from}
           ]
        /\ UNCHANGED<<subnets, subnetMsgs>>
      ELSE
        /\ ledger' = [
            ledger EXCEPT
              \* Transaction is valid. Update ledger balances.
              !["balances"][msg.from] = @ - msg.amount,
              !["balances"][msg.to] = @ + msg.amount,
              
              \* Remove msg from queue.
              !["msgs"] = Tail(@)
            ]
        /\ subnetMsgs'= Append(subnetMsgs,
            [type |-> "approve", from |-> msg.from, to |-> msg.to, amount |-> msg.amount]
           )
        /\ UNCHANGED<<subnets>>

Next ==
  \/ SubnetSendTransfer
  \/ SubnetReceiveTransfer
  \/ SubnetReceiveApprove
  \/ SubnetDishonestSendTransfer
  \/ LedgerReceiveMessage
  \/ LedgerPoll

BalancesNonNegative ==
  (*************************************************************************)
  (* Invariant to ensure that all subnet balances are non-negative.        *)
  (*************************************************************************)
  \A s \in SUBNETS: subnets[s].balance >= 0


LedgerIdentifiesAllDishonestSubnets ==
  {s \in SUBNETS: ~subnets[s].honest} = ledger.dishonestSubnets

LedgerIdentifiesAllDishonestSubnetsEventually ==
  \* A temporal property ensuring that all dishonest subnets are,
  \* eventually, identified by the ledger.
  \*
  \* NOTE: I think this invariant is not relevant anymore and can be removed.
  <>[][LedgerIdentifiesAllDishonestSubnets]_<<subnets, subnetMsgs, ledger>>

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

NoFakeCyclesAreCreated ==
  \* The total supply of finalized cycles in the ledger remains constant.
  /\ SumSeq(RecordToSeq(ledger.balances, SUBNETS)) = STARTING_BALANCE_PER_SUBNET * Cardinality(SUBNETS)
  \* The total supply of cycles that each subnet thinks it has is capped.
  /\ SumBalance(RecordToSeq(subnets, SUBNETS)) <= STARTING_BALANCE_PER_SUBNET * Cardinality(SUBNETS)

SubnetNeverHasMoreBalanceThanLedger ==
  \* The subnet's true balance is at most the balance stored in the ledger
  \* for that subnet.
  \A s \in SUBNETS: subnets[s].balance <= ledger.balances[s] 

LedgerAndSubnetBalancesMatchAfterMsgProcessing ==
  \* Ledger and subnets have the same balances whenever all messages are
  \* processed.
  Len(ledger.msgs) = 0
    /\ (\A s \in SUBNETS: Len(subnets[s].msgsToLedger) = 0)
    /\ Len(subnetMsgs) = 0
  => \A sn \in SUBNETS: ledger.balances[sn] = subnets[sn].balance

=============================================================================
\* Modification History
\* Last modified Mon Apr 15 06:14:14 EET 2024 by ielashi
\* Created Wed Mar 27 13:39:53 CET 2024 by ielashi