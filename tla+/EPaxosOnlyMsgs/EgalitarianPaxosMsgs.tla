-------------------------- MODULE EgalitarianPaxosMsgs--------------------------

EXTENDS Integers, FiniteSets, TLAPS, TLC

-----------------------------------------------------------------------------

Max(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i


(*********************************************************************************)
(* Constant parameters:                                                          *)
(*       Commands: the set of all possible commands                              *)
(*       Replicas: the set of all EPaxos replicas                                *)
(*       FastQuorums(r): the set of all fast quorums where r is a command leader *)
(*       SlowQuorums(r): the set of all slow quorums where r is a command leader *)
(*********************************************************************************)

CONSTANTS Commands, Replicas, FastQuorums(_), SlowQuorums(_), MaxBallot

Ballots == Nat \X Replicas

Quorums(r) == SlowQuorums(r) \* \cup FastQuorums(r)

ASSUME IsFiniteSet(Replicas)


(***************************************************************************)
(* Quorum conditions:                                                      *)
(*  (simplified)                                                           *)
(***************************************************************************)


ASSUME SlowQuorumAssumption == \A r \in Replicas:
                                  /\ SlowQuorums(r) \subseteq SUBSET Replicas
                                  /\ \A SQ \in SlowQuorums(r): 
                                    /\ r \in SQ
                                    /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1

ASSUME QuorumAssumption == SlowQuorumAssumption 

LEMMA QuorumNonEmpty == \A r \in Replicas : \A Q \in Quorums(r) : Q # {}
BY QuorumAssumption DEF Quorums

    
(***************************************************************************)
(* Special none command                                                    *)
(***************************************************************************)

none == CHOOSE c : c \notin Commands


(***************************************************************************)
(* The instance space                                                      *)
(***************************************************************************)

Instances == Replicas \X (1..Cardinality(Commands))

(***************************************************************************)
(* The possible status of a command in the log of a replica.               *)
(***************************************************************************)


Status == {"not-seen", "pre-accepted", "accepted", "committed"}

(***************************************************************************)
(* All possible protocol messages:                                         *)
(***************************************************************************)

Types == {"not-seen", "pre-accept", "pre-accept-reply", "accept", "accept-reply", "prepare", "prepare-reply", "commit"}

Message == SUBSET [type: Types,
                    src: Replicas,
                    dst: Replicas,
                    inst: Instances,
                    ballot: Nat \X Replicas,
                    status: Types,
                    cmd: Commands \cup {none},
                    deps: SUBSET Instances,
                    seq: Nat,
                    vbal: Nat \X Replicas,
                    read: BOOLEAN,
                    id: Nat]  

(*******************************************************************************)
(* Variables:                                                                  *)
(*                                                                             *)
(*          proposed = command that have been proposed                         *)
(*          executed = the log of executed commands at each replica            *)
(*          sentMsg = sent (but not yet received) messages                     *)
(*          crtInst = the next instance available for a command                *)
(*                    leader                                                   *)
(*          leaderOfInst = the set of instances each replica has               *)
(*                         started but not yet finalized                       *)
(*          committed = maps commands to set of commit attributs               *)
(*                      tuples                                                 *)
(*          ballots = largest ballot number used by any                        *)
(*                    replica                                                  *)
(*          preparing = set of instances that each replica is                  *)
(*                      currently preparing (i.e. recovering)                  *) 
(*                                                                             *)
(*                                                                             *)
(*******************************************************************************)

 
VARIABLES cmdLog, proposed, executed, sentMsg, crtInst, leaderOfInst,
          committed, ballots, preparing, msgId, msgs
          
TypeOK ==   /\ cmdLog \in [Replicas -> SUBSET [inst: Instances, 
                                       status: Status,
                                       ballot: Nat \X Replicas,
                                       cmd: Commands \cup {none},
                                       deps: SUBSET Instances,
                                       seq: Nat,
                                       vbal: Nat \cup {-1} \X Replicas]]
            /\ proposed \in SUBSET Commands
            /\ executed \in [Replicas -> SUBSET (Nat \X Commands)]
            /\ crtInst \in [Replicas -> Nat]
            /\ leaderOfInst \in [Replicas -> SUBSET Instances]
            /\ committed \in [Instances -> SUBSET ((Commands \cup {none}) \X
                                                   (SUBSET Instances) \X 
                                                   Nat)]
            /\ ballots \in Nat
            /\ preparing \in [Replicas -> SUBSET Instances]
            \* History vars
            /\ msgs \in Message  
            /\ msgId \in [Replicas -> Nat]   
                        
            
vars == << cmdLog, proposed, executed, sentMsg, crtInst, leaderOfInst, 
           committed, ballots, preparing, msgs, msgId >>
           
           
(***************************************************************************)
(* History vars                                                            *)
(***************************************************************************)
(* Sending a message m *) 

Send(m) ==  /\  m.id = msgId[m.src]
            /\  msgs' = msgs \cup {m}
            /\  msgId' = [msgId EXCEPT ![m.src] = @ + 1]

(***************************************************************************)
(* All the messages seen by a replica.                                     *)
(***************************************************************************)

OldMsg(replica, inst) == {m \in msgs : m.inst = inst /\ \/  m.src = replica
                                                        \/  m.dst = replica /\ m.read = TRUE}


(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)

Init ==
  /\ sentMsg = {}
  /\ cmdLog = [r \in Replicas |-> {}]
  /\ proposed = {}
  /\ executed = [r \in Replicas |-> {}]
  /\ crtInst = [r \in Replicas |-> 1]
  /\ leaderOfInst = [r \in Replicas |-> {}]
  /\ committed = [i \in Instances |-> {}]
  /\ ballots = 1
  /\ preparing = [r \in Replicas |-> {}]
  \* History vars
  /\ msgs = {}
  /\ msgId = [r \in Replicas |-> 0]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

StartPhase1(C, cleader, Q, inst, ballot) == 
    \E m \in Message : 
        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
        /\ LET newDeps == {rec.inst: rec \in OldMsg(cleader, inst)} 
               newSeq == 1 + Max({t.seq: t \in OldMsg(cleader, inst)}) IN
                /\ m = [type   |-> "pre-accept", \* History variable
                                      src       |-> cleader,
                                      dst       |-> Q,
                                      inst      |-> inst,
                                      ballot    |-> ballot,
                                      cmd       |-> C,
                                      deps      |-> newDeps,
                                      seq       |-> newSeq,
                                      vbal      |-> ballot,
                                      read      |-> FALSE]
                /\ Send(m)
                    

Propose(C, cleader) ==
    \E Q \in SlowQuorums(cleader) : 
        /\ proposed' = proposed \cup {C}
        /\  LET newInst == <<cleader, crtInst[cleader]>> 
                newBallot == <<0, cleader>> 
            IN  /\  StartPhase1(C, cleader, Q, newInst, newBallot)
                /\ crtInst' = [crtInst EXCEPT ![cleader] = @ + 1]
                /\ UNCHANGED << executed, committed, ballots, preparing >>



Phase1Reply(replica) ==
    \E m \in Message : 
        \E msg \in msgs:
            /\ msg.type = "pre-accept"
            /\ msg.dst = replica
            /\ msg.read = FALSE
            /\ LET oldMsg == OldMsg(replica, msg.inst) IN
                /\ (\A mmm \in oldMsg : 
                    (mmm.ballot = msg.ballot \/ m.ballot[1] < msg.ballot[1]))
                /\ LET newDeps == msg.deps \cup 
                                ({t.inst: t \in oldMsg} \ {msg.inst})
                       newSeq == Max({msg.seq, 
                                      1 + Max({t.seq: t \in oldMsg})})
                       instCom == {t.inst: t \in {tt \in msgs :
                                  tt.status \in {"commit", "execute"} /\ tt.src = replica}} IN
                    /\ m =   [type  |-> "pre-accept-reply",
                              src   |-> replica,
                              dst   |-> msg.src,
                              inst  |-> msg.inst,
                              ballot|-> msg.ballot,
                              cmd   |-> msg.cmd,
                              deps  |-> newDeps,
                              seq   |-> newSeq,
                              committed|-> instCom,
                              vbal  |-> msg.ballot,
                              read  |-> FALSE]
                    /\ Send(m)
                    /\ msg'.read = TRUE
                    /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                                    committed, ballots, preparing >>

Phase1Slow(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E m \in Message : 
        /\ \E record \in msgs:
            /\ record.src = cleader
            /\ record.dst = cleader
            /\ record.inst = i
            /\ record.status = "pre-accept-reply"
            /\ record.read = FALSE
            /\ LET replies == {msg \in msgs: 
                                    /\ msg.inst = i 
                                    /\ msg.type = "pre-accept-reply" 
                                    /\ msg.dst = cleader 
                                    /\ msg.src \in Q
                                    /\ msg.ballot = record.ballot
                                    /\ msg.read = FALSE} IN
                /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: msg.src = replica)
                /\ LET finalDeps == UNION {msg.deps : msg \in replies}
                       finalSeq == Max({msg.seq : msg \in replies}) IN    
                    /\ \E SQ \in SlowQuorums(cleader):
                       /\ m = [type    |-> "accept",
                                src     |-> cleader,
                                dst     |-> SQ,
                                inst    |-> i,
                                ballot  |-> record.ballot,
                                cmd     |-> record.cmd,
                                deps    |-> finalDeps,
                                seq     |-> finalSeq,
                                vbal    |-> record.vbal,
                                read    |-> FALSE]
                       /\ Send(m)
                    /\ record'.read = TRUE
                    /\ \A msg \in replies : msg'.read = TRUE
                    /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
                                    committed, ballots, preparing >>
                
Phase2Reply(replica) ==
    \E m \in Message :
        \E msg \in msgs: 
            /\ msg.type = "accept"
            /\ msg.dst = replica
            /\ msg.read = FALSE
            /\ LET oldMsg == OldMsg(replica, msg.inst) IN
                /\ (\A mm \in oldMsg : 
                    (mm.ballot = msg.ballot \/ m.ballot[1] < msg.ballot[1]))
                /\ m = [type  |-> "accept-reply",
                                      src   |-> replica,
                                      dst   |-> msg.src,
                                      inst  |-> msg.inst,
                                      ballot|-> msg.ballot,
                                      cmd   |-> msg.cmd,
                                      deps  |-> msg.deps,
                                      seq   |-> msg.seq,
                                      vbal  |-> msg.ballot,
                                      read  |-> FALSE]
                /\ Send(m)
                /\ msg'.read = TRUE
                /\ \A mm \in oldMsg : mm'.read = TRUE
                /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                                committed, ballots, preparing >>


Phase2Finalize(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E m \in Message : 
        /\ \E record \in msgs: 
            /\ record.src = cleader
            /\ record.inst = i
            /\ record.type = "accept-reply"
            /\ record.read = FALSE
            /\ LET replies == {msg \in msgs: 
                                    /\ msg.type = "accept-reply" 
                                    /\ msg.src \in Q
                                    /\ msg.dst = cleader 
                                    /\ msg.inst = i 
                                    /\ msg.ballot = record.ballot
                                    /\ msg.cmd = record.cmd
                                    /\ msg.deps = record.deps
                                    /\ msg.seq = record.seq
                                    /\ msg.vbal = record.vbal
                                    /\ msg.read = FALSE} IN
                /\ (\A replica \in Q: \E msg \in replies: msg.src = replica)
                /\ m = [type  |-> "commit",
                        src     |-> cleader,
                        dst     |-> Q,
                        inst    |-> i,
                        ballot  |-> record.ballot,
                        cmd     |-> record.cmd,
                        deps    |-> record.deps,
                        seq     |-> record.seq,
                        vbal    |-> record.vbal,
                        read    |-> FALSE]
                /\ Send(m)
                /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
                /\ record'.read = TRUE  \* Not necessary as record is included in replies
                /\ \A msg \in replies: msg'.read = TRUE
                /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing, committed >>

Commit(replica, cmsg) ==
    LET oldMsg == OldMsg(replica, cmsg.inst) IN
        /\ \A msg \in oldMsg : (msg.type \notin {"commit", "execute"} /\ 
                                msg.ballot[1] <= cmsg.ballot[1])
        /\ committed' = [committed EXCEPT ![cmsg.inst] = @ \cup 
                               {<<cmsg.cmd, cmsg.deps, cmsg.seq>>}]
        /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
                        sentMsg, ballots, preparing, msgs >>


(***************************************************************************)
(* Recovery actions                                                        *)
(***************************************************************************)

SendPrepare(replica, i, Q) ==
    /\ i \notin leaderOfInst[replica]
    \*/\ i \notin preparing[replica]
    /\ ballots <= MaxBallot
    /\ ~(\E rec \in OldMsg(replica, i) : rec.status \in {"committed", "executed"})
    /\ \E m \in Message : 
        /\ m = [type        |-> "prepare",
                     src    |-> replica,
                     dst    |-> Q,
                     inst   |-> i,
                     ballot |-> << ballots, replica >>]
        /\ Send(m)
    /\ ballots' = ballots + 1
    /\ preparing' = [preparing EXCEPT ![replica] = @ \cup {i}]
    /\ UNCHANGED << cmdLog, proposed, executed, crtInst,
                    leaderOfInst, committed >>
    
ReplyPrepare(replica) ==
    \E msg \in msgs : 
        /\ msg.type = "prepare"
        /\ msg.dst = replica
        /\ msg.read = FALSE
        /\ \/ \E rec \in OldMsg(replica, msg.inst) : 
                /\ msg.ballot[1] > rec.ballot[1]
                /\ \E m \in Message : /\ m = [type  |-> "prepare-reply",
                                              src   |-> replica,
                                              dst   |-> msg.src,
                                              inst  |-> rec.inst,
                                              ballot|-> msg.ballot,
                                              status|-> rec.type,
                                              cmd   |-> rec.cmd,
                                              deps  |-> rec.deps,
                                              seq   |-> rec.seq,
                                              vbal  |-> rec.vbal,
                                              READ  |-> FALSE]
                                      /\ Send(m)
                 /\ IF rec.inst \in leaderOfInst[replica] THEN
                        /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = 
                                                                @ \ {rec.inst}]
                        /\ UNCHANGED << proposed, executed, committed,
                                        crtInst, ballots, preparing >>
                    ELSE UNCHANGED << proposed, executed, committed, crtInst,
                                      ballots, preparing, leaderOfInst >>
                        
           \/ /\ (\E rec \in OldMsg(replica, msg.inst)  : FALSE)
              /\ \E m \in Message : /\ m = [type  |-> "prepare-reply",
                                          src   |-> replica,
                                          dst   |-> msg.src,
                                          inst  |-> msg.inst,
                                          ballot|-> msg.ballot,
                                          status|-> "not-seen",
                                          cmd   |-> none,
                                          deps  |-> {},
                                          seq   |-> 0,
                                          vbal  |-> << -1, replica >>,
                                          READ  |-> FALSE]
                                    /\ Send(m)
              /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
                              leaderOfInst, preparing >> 
    
PrepareFinalize(replica, i, Q) ==
    \/   /\ i \in preparing[replica]
         /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
           /\ LET replies == {msg \in msgs : 
                            /\ msg.inst = i
                            /\ msg.type = "prepare-reply"
                            /\ msg.dst = replica
                            /\ msg.ballot = rec.ballot
                            /\ msg.read = FALSE} IN
                /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                /\  \/ \E com \in replies :
                            /\ (com.status \in {"commit"})
                            /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                            /\ \A m \in replies : m.read = TRUE
                            /\ UNCHANGED << msgs, proposed, executed, crtInst, leaderOfInst,
                                            committed, ballots >>
    \/  /\ i \in preparing[replica]
        /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
           /\ LET replies == {msg \in msgs : 
                            /\ msg.inst = i
                            /\ msg.type = "prepare-reply"
                            /\ msg.dst = replica
                            /\ msg.ballot = rec.ballot
                            /\ msg.read = FALSE} IN
                /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                /\ ~(\E msg \in replies : msg.status \in {"commit"})
                    /\ \E m \in Message : 
                        /\ \E acc \in replies :
                            /\ acc.status = "accept-reply"
                            /\ (\A msg \in (replies \ {acc}) : 
                                (msg.prev_ballot[1] <= acc.prev_ballot[1] \/ 
                                 msg.status # "accept-reply"))
                            /\ m = [type        |-> "accept",
                                      src       |-> replica,
                                      dst       |-> Q,
                                      inst      |-> i,
                                      ballot    |-> rec.ballot,
                                      cmd       |-> acc.cmd,
                                      deps      |-> acc.deps,
                                      seq       |-> acc.seq,
                                      vbal      |-> rec.ballot,
                                      read      |-> FALSE]
                             /\ Send(m)
                             /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                             /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                             /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
    \/
        \/  /\ i \in preparing[replica]
            /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
               /\ LET replies == {msg \in msgs : 
                                /\ msg.inst = i
                                /\ msg.type = "prepare-reply"
                                /\ msg.dst = replica
                                /\ msg.ballot = rec.ballot
                                /\ msg.read = FALSE} IN
                    /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                    /\ ~(\E msg \in replies : 
                            msg.status \in {"accept-reply", "commit"})
                       /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                       /\ \A p1, p2 \in preaccepts :
                                    p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                       /\ ~(\E pl \in preaccepts : pl.src = i[1])
                       /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                       /\ \E m \in Message : 
                            /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                 /\ m = [type       |-> "accept",
                                          src       |-> replica,
                                          dst       |-> Q,
                                          inst      |-> i,
                                          ballot    |-> rec.ballot,
                                          cmd       |-> pac.cmd,
                                          deps      |-> pac.deps,
                                          seq       |-> pac.seq,
                                          vbal      |-> rec.ballot,
                                          read      |-> FALSE]
                                 /\ Send(m)
                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                 /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                 /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
        \/  /\ i \in preparing[replica]
            /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
               /\ LET replies == {msg \in msgs : 
                                /\ msg.inst = i
                                /\ msg.type = "prepare-reply"
                                /\ msg.dst = replica
                                /\ msg.ballot = rec.ballot
                                /\ msg.read = FALSE} IN
                    /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                    /\ ~(\E msg \in replies : 
                            msg.status \in {"accept-reply", "commit"})
                       /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                       /\      \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/ 
                                                             p1.deps # p2.deps \/
                                                             p1.seq # p2.seq
                               \/ \E pl \in preaccepts : pl.src = i[1]
                               \* Next condition was previously handled by try-pre-accept (but no fast path anymore)
                               \* I chose to make it apparent instead of simply removing the \E p1,p2 above
                               \/ \A pp1, pp2 \in preaccepts : pp1.cmd = pp2.cmd /\ 
                                                             pp1.deps = pp2.deps /\
                                                             pp1.seq = pp2.seq
\*                             \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                            /\ preaccepts # {}
                            /\ \E pac \in preaccepts :
                                /\ pac.cmd # none
                                /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot) 
                                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
    \/  /\ i \in preparing[replica]
        /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
           /\ LET replies == {msg \in msgs : 
                            /\ msg.inst = i
                            /\ msg.type = "prepare-reply"
                            /\ msg.dst = replica
                            /\ msg.ballot = rec.ballot
                            /\ msg.read = FALSE} IN
                /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)   
                /\ \A msg \in replies : msg.status = "not-seen"
                /\ StartPhase1(none, replica, Q, i, rec.ballot)
                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
                        

(***************************************************************************)
(* Action groups                                                           *)
(***************************************************************************)        

CommandLeaderAction ==
    \/ (\E C \in (Commands \ proposed) :
            \E cleader \in Replicas : Propose(C, cleader))
    \/ (\E cleader \in Replicas : \E inst \in leaderOfInst[cleader] :
\*            \/ (\E Q \in FastQuorums(cleader) : Phase1Fast(cleader, inst, Q))
            \/ (\E Q \in SlowQuorums(cleader) : Phase1Slow(cleader, inst, Q))
            \/ (\E Q \in SlowQuorums(cleader) : Phase2Finalize(cleader, inst, Q)))
\*           \/ (\E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)))
            
ReplicaAction ==
    \E replica \in Replicas :
        (\/ Phase1Reply(replica)
         \/ Phase2Reply(replica)
         \/ \E cmsg \in msgs : (cmsg.type = "commit" /\ Commit(replica, cmsg))
         \/ \E i \in Instances : 
            /\ crtInst[i[1]] > i[2] (* This condition states that the instance has *) 
                                    (* been started by its original owner          *)
            /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
         \/ ReplyPrepare(replica)
         \/ \E i \in preparing[replica] :
            \E Q \in SlowQuorums(replica) : PrepareFinalize(replica, i, Q))
\*         \/ ReplyTryPreaccept(replica))


(***************************************************************************)
(* Next action                                                             *)
(***************************************************************************)

Next == \/ CommandLeaderAction
        \/ ReplicaAction
        

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

Nontriviality ==
    \A i \in Instances :
        [](\A C \in committed[i] : C \in proposed \/ C = none)

Stability ==
    \A replica \in Replicas :
        \A i \in Instances :
            \A C \in Commands :
                []((\E rec1 \in cmdLog[replica] :
                    /\ rec1.inst = i
                    /\ rec1.cmd = C
                    /\ rec1.status \in {"committed", "executed"}) =>
                    [](\E rec2 \in cmdLog[replica] :
                        /\ rec2.inst = i
                        /\ rec2.cmd = C
                        /\ rec2.status \in {"committed", "executed"}))

Consistency ==
    \A i \in Instances :
        [](Cardinality(committed[i]) <= 1)
        
        
(***************************************************************************)
(* Start of the proof                                                      *)
(***************************************************************************)


(***************************************************************************)
(* Auxiliary predicates                                                    *)
(***************************************************************************)

Accept(D,c,i,Q,b) == \A p \in Q:
                        \E m \in msgs: 
                           [type: "accept-reply",
                            src: p,
                            inst: i,
                            ballot: b,
                            cmd: c,
                            deps: D,
                            vbal: b]  
                                                                 
Committable(D,c,i,Q,b) == Accept(D,c,i,Q,b) \* No Fast Path in this version of EPaxos

\* Redefinition of IsCommitted with var committed to make it simpler
IsCommitted(D,c) == \E rec \in committed'\committed : \E seq \in Nat : rec = <<c, D, seq>> 
                         
(***************************************************************************)
(* Assumptions on Messages                                                 *)
(***************************************************************************)    

\* For any replica, message ids are unique
LEMMA UniqueId == \A m1,m2 \in Message: (m1.src = m2.src) => (m1.id # m2.id)

LEMMA UniqueMsgs == \A m1, m2 \in Message : m1 # m2
BY UniqueId
                             
LEMMA msgsMonotonicity == \A m \in msgs : m \in msgs'             
                           
(***************************************************************************)
(* Invariant on Messages                                                   *)
(***************************************************************************)

LEMMA Phase2FinalizeInv == \A cleader \in Replicas, i \in Instances :
                             \A Q \in Quorums(cleader) :
                                Phase2Finalize(cleader,i,Q) => 
                                    (\E D \in SUBSET Instances, c \in Commands, b \in ballots :
                                        Accept(D,c,i,Q,b))
BY DEF Accept, Phase2Finalize


MsgInv == \A m \in msgs :
              /\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                         Accept(m.deps, m.cmd, m.inst, Q, m.ballot)
                    
THEOREM Invariant == Spec => []MsgInv
    <1> USE DEF MsgInv
    <1>1 Init => MsgInv
        BY DEF Init
    <1>2 MsgInv /\ [Next]_vars => MsgInv'
      <2> SUFFICES ASSUME MsgInv,
                          [Next]_vars
                   PROVE  MsgInv'
        OBVIOUS
      <2>1. ASSUME NEW C \in Commands \ proposed,
                   NEW cleader \in Replicas,
                   Propose(C, cleader)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader_1 \in Replicas : \E Q \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader_1 \in Replicas : \E Q \in Quorums(cleader_1) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 PICK Q \in SlowQuorums(cleader) : 
                        /\  LET newInst == <<cleader, crtInst[cleader]>> 
                                newBallot == <<0, cleader>> 
                            IN StartPhase1(C, cleader, Q, newInst, newBallot)
                BY Propose(C, cleader) DEF Propose
            <4>2 PICK msg \in Message : 
                        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {<<cleader, crtInst[cleader]>> }]
                        /\ LET newDeps == {rec.inst: rec \in OldMsg(cleader, <<cleader, crtInst[cleader]>> )} 
                               newSeq == 1 + Max({t.seq: t \in OldMsg(cleader, <<cleader, crtInst[cleader]>> )}) IN
                                /\ msg = [type   |-> "pre-accept", \* History variable
                                                      src       |-> cleader,
                                                      dst       |-> Q,
                                                      inst      |-> <<cleader, crtInst[cleader]>> ,
                                                      ballot    |-> <<0, cleader>> ,
                                                      cmd       |-> C,
                                                      deps      |-> newDeps,
                                                      seq       |-> newSeq,
                                                      vbal      |-> <<0, cleader>> ,
                                                      read      |-> FALSE]
                                /\ Send(msg)
                BY <4>1 DEF StartPhase1
            <4>3 msgs' = msgs \cup {msg}
                BY <4>2 DEF Send
            <4>4 \A mm \in msgs : mm \in msgs'
                BY <4>3
            <4>5 m \notin msgs => m = msg /\ m.type = "pre-accept"
                BY <4>3, <4>2
            <4>6 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>4 DEF Accept
            <4> QED BY <4>5, <4>6
        <3>2. QED
          BY <3>1
      <2>2. ASSUME NEW cleader \in Replicas,
                   NEW inst \in leaderOfInst[cleader],
                   NEW Q \in SlowQuorums(cleader),
                   Phase1Slow(cleader, inst, Q)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader_1 \in Replicas : \E Q_1 \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader_1 \in Replicas : \E Q_1 \in Quorums(cleader_1) :
                                       Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
            <4>1 PICK mm \in Message : 
                        /\ \E record \in msgs:
                            /\ record.src = cleader
                            /\ record.dst = cleader
                            /\ record.inst = inst
                            /\ record.status = "pre-accept-reply"
                            /\ record.read = FALSE
                            /\ LET replies == {msg \in msgs: 
                                                    /\ msg.inst = inst
                                                    /\ msg.type = "pre-accept-reply" 
                                                    /\ msg.dst = cleader 
                                                    /\ msg.src \in Q
                                                    /\ msg.ballot = record.ballot
                                                    /\ msg.read = FALSE} IN
                                /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: msg.src = replica)
                                /\ LET finalDeps == UNION {msg.deps : msg \in replies}
                                       finalSeq == Max({msg.seq : msg \in replies}) IN    
                                    /\ \E SQ \in SlowQuorums(cleader):
                                       /\ mm = [type    |-> "accept",
                                                src     |-> cleader,
                                                dst     |-> SQ,
                                                inst    |-> inst,
                                                ballot  |-> record.ballot,
                                                cmd     |-> record.cmd,
                                                deps    |-> finalDeps,
                                                seq     |-> finalSeq,
                                                vbal    |-> record.vbal,
                                                read    |-> FALSE]
                                       /\ Send(mm)
                BY Phase1Slow(cleader, inst, Q) DEF Phase1Slow
            <4>2 msgs' = msgs \cup {mm}
                BY <4>1 DEF Send
            <4>3 \A mmm \in msgs : mmm \in msgs'
                BY <4>2
            <4>4 m \notin msgs => m = mm /\ m.type = "accept"
                BY <4>1, <4>2, <4>3
            <4>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>3 DEF Accept
            <4> QED BY <4>4, <4>5
        <3>2. QED
          BY <3>1
      <2>3. ASSUME NEW cleader \in Replicas,
                   NEW inst \in leaderOfInst[cleader],
                   NEW Q \in SlowQuorums(cleader),
                   Phase2Finalize(cleader, inst, Q)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader_1 \in Replicas : \E Q_1 \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader_1 \in Replicas : \E Q_1 \in Quorums(cleader_1) :
                                       Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
            <4>1 PICK mm \in Message : 
                    /\ \E record \in msgs: 
                        /\ record.src = cleader
                        /\ record.inst = inst
                        /\ record.type = "accept-reply"
                        /\ record.read = FALSE
                        /\ LET replies == {msg \in msgs: 
                                                /\ msg.type = "accept-reply" 
                                                /\ msg.src \in Q
                                                /\ msg.dst = cleader 
                                                /\ msg.inst = inst
                                                /\ msg.ballot = record.ballot
                                                /\ msg.cmd = record.cmd
                                                /\ msg.deps = record.deps
                                                /\ msg.seq = record.seq
                                                /\ msg.vbal = record.vbal
                                                /\ msg.read = FALSE} IN
                            /\ (\A replica \in Q: \E msg \in replies: msg.src = replica)
                            /\ mm = [type  |-> "commit",
                                    src     |-> cleader,
                                    dst     |-> Q,
                                    inst    |-> inst,
                                    ballot  |-> record.ballot,
                                    cmd     |-> record.cmd,
                                    deps    |-> record.deps,
                                    seq     |-> record.seq,
                                    vbal    |-> record.vbal,
                                    read    |-> FALSE]
                            /\ Send(mm)
                            /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {inst}]
                            /\ record'.read = TRUE  \* Not necessary as record is included in replies
                            /\ \A msg \in replies: msg'.read = TRUE
                            /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing, committed >>
                BY Phase2Finalize(cleader, inst, Q) DEF Phase2Finalize
            <4>2 msgs' = msgs \cup {mm}
                BY <4>1 DEF Send
            <4>3 \A mmm \in msgs : mmm \in msgs'
                BY <4>2
            <4>4 m \notin msgs => m = mm /\ \E cleader_1 \in Replicas : \E Q_1 \in Quorums(cleader_1) :
                                                Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot)'
                BY <4>1, <4>2, <4>3 DEF Accept
            <4>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>3 DEF Accept
            <4> QED BY <4>4, <4>5
        <3>2. QED
          BY <3>1
      <2>4. ASSUME NEW replica \in Replicas,
                   Phase1Reply(replica)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 PICK mm \in Message : 
                    \E msg \in msgs:
                        /\ msg.type = "pre-accept"
                        /\ msg.dst = replica
                        /\ msg.read = FALSE
                        /\ LET oldMsg == OldMsg(replica, msg.inst) IN
                            /\ (\A mmm \in oldMsg : 
                                (mmm.ballot = msg.ballot \/ m.ballot[1] < msg.ballot[1]))
                            /\ LET newDeps == msg.deps \cup 
                                            ({t.inst: t \in oldMsg} \ {msg.inst})
                                   newSeq == Max({msg.seq, 
                                                  1 + Max({t.seq: t \in oldMsg})})
                                   instCom == {t.inst: t \in {tt \in msgs :
                                              tt.status \in {"commit", "execute"} /\ tt.src = replica}} IN
                                /\ m =   [type  |-> "pre-accept-reply",
                                          src   |-> replica,
                                          dst   |-> msg.src,
                                          inst  |-> msg.inst,
                                          ballot|-> msg.ballot,
                                          cmd   |-> msg.cmd,
                                          deps  |-> newDeps,
                                          seq   |-> newSeq,
                                          committed|-> instCom,
                                          vbal  |-> msg.ballot,
                                          read  |-> FALSE]
                                /\ Send(m)
                                /\ msg'.read = TRUE
                                /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                                                committed, ballots, preparing >>
                BY Phase1Reply(replica) DEF Phase1Reply
            <4>2 msgs' = msgs \cup {mm}
                BY <4>1 DEF Send
            <4>3 \A mmm \in msgs : mmm \in msgs'
                BY <4>2
            <4>4 m \notin msgs => m = mm /\ m.type = "pre-accept-reply"
                BY <4>1, <4>2, <4>3
            <4>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>3 DEF Accept
            <4> QED BY <4>4, <4>5
        <3>2. QED
          BY <3>1
      <2>5. ASSUME NEW replica \in Replicas,
                   Phase2Reply(replica)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 PICK mm \in Message :
                    \E msg \in msgs: 
                        /\ msg.type = "accept"
                        /\ msg.dst = replica
                        /\ msg.read = FALSE
                        /\ LET oldMsg == OldMsg(replica, msg.inst) IN
                            /\ (\A mmm \in oldMsg : 
                                (mmm.ballot = msg.ballot \/ m.ballot[1] < msg.ballot[1]))
                            /\ m = [type  |-> "accept-reply",
                                                  src   |-> replica,
                                                  dst   |-> msg.src,
                                                  inst  |-> msg.inst,
                                                  ballot|-> msg.ballot,
                                                  cmd   |-> msg.cmd,
                                                  deps  |-> msg.deps,
                                                  seq   |-> msg.seq,
                                                  vbal  |-> msg.ballot,
                                                  read  |-> FALSE]
                            /\ Send(m)
                            /\ msg'.read = TRUE
                            /\ \A mmm \in oldMsg : mmm'.read = TRUE
                            /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                                            committed, ballots, preparing >>
                BY Phase2Reply(replica) DEF Phase2Reply
            <4>2 msgs' = msgs \cup {mm}
                BY <4>1 DEF Send
            <4>3 \A mmm \in msgs : mmm \in msgs'
                BY <4>2
            <4>4 m \notin msgs => m = mm /\ m.type = "accept-reply"
                BY <4>1, <4>2, <4>3
            <4>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>3 DEF Accept
            <4> QED BY <4>4, <4>5
        <3>2. QED
          BY <3>1
      <2>6. ASSUME NEW replica \in Replicas,
                   NEW cmsg \in msgs,
                   cmsg.type = "commit" /\ Commit(replica, cmsg)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 UNCHANGED msgs
             BY cmsg.type = "commit" /\ Commit(replica, cmsg) DEF Commit
            <4>2 m \in msgs 
                BY <4>1
            <4>3 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>1 DEF Accept
            <4> QED BY <4>2, <4>3
        <3>2. QED
          BY <3>1
      <2>7. ASSUME NEW replica \in Replicas,
                   NEW i \in Instances,
                   /\ crtInst[i[1]] > i[2] (* This condition states that the instance has *) 
                                           (* been started by its original owner          *)
                   /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 PICK Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
                BY <2>7
            <4>2 PICK mm \in Message : 
                    /\ mm = [type        |-> "prepare",
                                 src    |-> replica,
                                 dst    |-> Q,
                                 inst   |-> i,
                                 ballot |-> << ballots, replica >>]
                    /\ Send(mm)
                BY SendPrepare(replica, i, Q) DEF SendPrepare
            <4>3 msgs' = msgs \cup {mm}
                BY <4>2 DEF Send
            <4>4 \A mmm \in msgs : mmm \in msgs'
                BY <4>3
            <4>5 m \notin msgs => m = mm /\ m.type = "prepare"
                BY <4>2, <4>3, <4>4
            <4>6 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>4 DEF Accept
            <4> QED BY <4>5, <4>6
        <3>2. QED
          BY <3>1
      <2>8. ASSUME NEW replica \in Replicas,
                   ReplyPrepare(replica)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q, m.ballot))'
            <4>1 PICK mm \in Message : /\ mm.type = "prepare-reply"
                                       /\ Send(mm)
                BY ReplyPrepare(replica) DEF ReplyPrepare
            <4>2 msgs' = msgs \cup {mm}
                BY <4>1 DEF Send
            <4>3 \A mmm \in msgs : mmm \in msgs'
                BY <4>2
            <4>4 m \notin msgs => m = mm /\ m.type = "prepare-reply"
                BY <4>1, <4>2, <4>3
            <4>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <4>3 DEF Accept
            <4> QED BY <4>4, <4>5
        <3>2. QED
          BY <3>1
      <2>9. ASSUME NEW replica \in Replicas,
                   NEW i \in preparing[replica],
                   NEW Q \in SlowQuorums(replica),
                   PrepareFinalize(replica, i, Q)
            PROVE  MsgInv'
        <3> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\ m.type = "commit" => \E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                                        Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
          BY DEF MsgInv
        <3>1. (m.type = "commit" => \E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                       Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
          <4>1. CASE /\ i \in preparing[replica]
                     /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                       /\ LET replies == {msg \in msgs : 
                                        /\ msg.inst = i
                                        /\ msg.type = "prepare-reply"
                                        /\ msg.dst = replica
                                        /\ msg.ballot = rec.ballot
                                        /\ msg.read = FALSE} IN
                            /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                            /\  \/ \E com \in replies :
                                        /\ (com.status \in {"commit"})
                                        /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                        /\ \A mm \in replies : mm.read = TRUE
                                        /\ UNCHANGED << msgs, proposed, executed, crtInst, leaderOfInst,
                                                        committed, ballots >>
            <5> SUFFICES ASSUME NEW rec \in OldMsg(replica, i),
                                                                 rec.status \notin {"commit"}
                                /\ LET replies == {msg \in msgs : 
                                                 /\ msg.inst = i
                                                 /\ msg.type = "prepare-reply"
                                                 /\ msg.dst = replica
                                                 /\ msg.ballot = rec.ballot
                                                 /\ msg.read = FALSE} IN
                                     /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                     /\  \/ \E com \in replies :
                                                 /\ (com.status \in {"commit"})
                                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                 /\ \A mm \in replies : mm.read = TRUE
                                                 /\ UNCHANGED << msgs, proposed, executed, crtInst, leaderOfInst,
                                                                 committed, ballots >>,
                                (m.type = "commit")'
                         PROVE  (\E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                    Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
              BY <4>1 
            <5>1 UNCHANGED msgs
                BY <4>1
            <5>2 m \in msgs
                BY <5>1
            <5>3 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                            Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <5>1 DEF Accept
            <5> QED BY <5>2, <5>3
          <4>2. CASE /\ i \in preparing[replica]
                     /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                        /\ LET replies == {msg \in msgs : 
                                         /\ msg.inst = i
                                         /\ msg.type = "prepare-reply"
                                         /\ msg.dst = replica
                                         /\ msg.ballot = rec.ballot
                                         /\ msg.read = FALSE} IN
                             /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                             /\ ~(\E msg \in replies : msg.status \in {"commit"})
                                 /\ \E mm \in Message : 
                                     /\ \E acc \in replies :
                                         /\ acc.status = "accept-reply"
                                         /\ (\A msg \in (replies \ {acc}) : 
                                             (msg.prev_ballot[1] <= acc.prev_ballot[1] \/ 
                                              msg.status # "accept-reply"))
                                         /\ mm = [type        |-> "accept",
                                                   src       |-> replica,
                                                   dst       |-> Q,
                                                   inst      |-> i,
                                                   ballot    |-> rec.ballot,
                                                   cmd       |-> acc.cmd,
                                                   deps      |-> acc.deps,
                                                   seq       |-> acc.seq,
                                                   vbal      |-> rec.ballot,
                                                   read      |-> FALSE]
                                          /\ Send(mm)
                                          /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                          /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                          /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
            <5> SUFFICES ASSUME NEW rec \in OldMsg(replica, i),
                                                                rec.status \notin {"commit"}
                                /\ LET replies == {msg \in msgs : 
                                                 /\ msg.inst = i
                                                 /\ msg.type = "prepare-reply"
                                                 /\ msg.dst = replica
                                                 /\ msg.ballot = rec.ballot
                                                 /\ msg.read = FALSE} IN
                                     /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                     /\ ~(\E msg \in replies : msg.status \in {"commit"})
                                         /\ \E mm \in Message : 
                                             /\ \E acc \in replies :
                                                 /\ acc.status = "accept-reply"
                                                 /\ (\A msg \in (replies \ {acc}) : 
                                                     (msg.prev_ballot[1] <= acc.prev_ballot[1] \/ 
                                                      msg.status # "accept-reply"))
                                                 /\ mm = [type        |-> "accept",
                                                           src       |-> replica,
                                                           dst       |-> Q,
                                                           inst      |-> i,
                                                           ballot    |-> rec.ballot,
                                                           cmd       |-> acc.cmd,
                                                           deps      |-> acc.deps,
                                                           seq       |-> acc.seq,
                                                           vbal      |-> rec.ballot,
                                                           read      |-> FALSE]
                                                  /\ Send(mm)
                                                  /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                  /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                                  /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>,
                                (m.type = "commit")'
                         PROVE  (\E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                    Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
              BY <4>2
            <5>1 PICK mm \in Message : 
                     /\ mm.type = "accept"
                     /\ Send(mm)
                BY <4>2 
            <5>2 msgs' = msgs \cup {mm}
                BY <5>1 DEF Send
            <5>3 \A mmm \in msgs : mmm \in msgs'
                BY <5>2
            <5>4 m \notin msgs => m = mm /\ m.type = "accept"
                BY <5>1, <5>2, <5>3
            <5>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <5>4 DEF Accept
            <5> QED BY <5>4, <5>5
          <4>3. CASE         \/  /\ i \in preparing[replica]
                                 /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                                    /\ LET replies == {msg \in msgs : 
                                                     /\ msg.inst = i
                                                     /\ msg.type = "prepare-reply"
                                                     /\ msg.dst = replica
                                                     /\ msg.ballot = rec.ballot
                                                     /\ msg.read = FALSE} IN
                                         /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                         /\ ~(\E msg \in replies : 
                                                 msg.status \in {"accept-reply", "commit"})
                                            /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                            /\ \A p1, p2 \in preaccepts :
                                                         p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                                            /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                                            /\ \E mm \in Message : 
                                                 /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                                      /\ mm = [type       |-> "accept",
                                                               src       |-> replica,
                                                               dst       |-> Q,
                                                               inst      |-> i,
                                                               ballot    |-> rec.ballot,
                                                               cmd       |-> pac.cmd,
                                                               deps      |-> pac.deps,
                                                               seq       |-> pac.seq,
                                                               vbal      |-> rec.ballot,
                                                               read      |-> FALSE]
                                                      /\ Send(mm)
                                                      /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                      /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                                      /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
                             \/  /\ i \in preparing[replica]
                                 /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                                    /\ LET replies == {msg \in msgs : 
                                                     /\ msg.inst = i
                                                     /\ msg.type = "prepare-reply"
                                                     /\ msg.dst = replica
                                                     /\ msg.ballot = rec.ballot
                                                     /\ msg.read = FALSE} IN
                                         /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                         /\ ~(\E msg \in replies : 
                                                 msg.status \in {"accept-reply", "commit"})
                                            /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                            /\      \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/ 
                                                                                  p1.deps # p2.deps \/
                                                                                  p1.seq # p2.seq
                                                    \/ \E pl \in preaccepts : pl.src = i[1]
                                                    \* Next condition was previously handled by try-pre-accept (but no fast path anymore)
                                                    \* I chose to make it apparent instead of simply removing the \E p1,p2 above
                                                    \/ \A pp1, pp2 \in preaccepts : pp1.cmd = pp2.cmd /\ 
                                                                                  pp1.deps = pp2.deps /\
                                                                                  pp1.seq = pp2.seq
                     \*                             \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                                                 /\ preaccepts # {}
                                                 /\ \E pac \in preaccepts :
                                                     /\ pac.cmd # none
                                                     /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot) 
                                                     /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                     /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
            <5>1. CASE /\ i \in preparing[replica]
                                 /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                                    /\ LET replies == {msg \in msgs : 
                                                     /\ msg.inst = i
                                                     /\ msg.type = "prepare-reply"
                                                     /\ msg.dst = replica
                                                     /\ msg.ballot = rec.ballot
                                                     /\ msg.read = FALSE} IN
                                         /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                         /\ ~(\E msg \in replies : 
                                                 msg.status \in {"accept-reply", "commit"})
                                            /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                            /\ \A p1, p2 \in preaccepts :
                                                         p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                                            /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                                            /\ \E mm \in Message : 
                                                 /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                                      /\ mm = [type       |-> "accept",
                                                               src       |-> replica,
                                                               dst       |-> Q,
                                                               inst      |-> i,
                                                               ballot    |-> rec.ballot,
                                                               cmd       |-> pac.cmd,
                                                               deps      |-> pac.deps,
                                                               seq       |-> pac.seq,
                                                               vbal      |-> rec.ballot,
                                                               read      |-> FALSE]
                                                      /\ Send(mm)
                                                      /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                      /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                                      /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
              <6> SUFFICES ASSUME NEW rec \in OldMsg(replica, i),
                                                                  rec.status \notin {"commit"}
                                  /\ LET replies == {msg \in msgs : 
                                                   /\ msg.inst = i
                                                   /\ msg.type = "prepare-reply"
                                                   /\ msg.dst = replica
                                                   /\ msg.ballot = rec.ballot
                                                   /\ msg.read = FALSE} IN
                                       /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                       /\ ~(\E msg \in replies : 
                                               msg.status \in {"accept-reply", "commit"})
                                          /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                          /\ \A p1, p2 \in preaccepts :
                                                       p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                                          /\ ~(\E pl \in preaccepts : pl.src = i[1])
                                          /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                                          /\ \E mm \in Message : 
                                               /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                                    /\ mm = [type       |-> "accept",
                                                             src       |-> replica,
                                                             dst       |-> Q,
                                                             inst      |-> i,
                                                             ballot    |-> rec.ballot,
                                                             cmd       |-> pac.cmd,
                                                             deps      |-> pac.deps,
                                                             seq       |-> pac.seq,
                                                             vbal      |-> rec.ballot,
                                                             read      |-> FALSE]
                                                    /\ Send(mm)
                                                    /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                    /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                                    /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>,
                                  (m.type = "commit")'
                           PROVE  (\E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                      Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
                BY <5>1
            <6>1 PICK mm \in Message : 
                     /\ mm.type = "accept"
                     /\ Send(mm)
                BY <5>1
            <6>2 msgs' = msgs \cup {mm}
                BY <6>1 DEF Send
            <6>3 \A mmm \in msgs : mmm \in msgs'
                BY <6>2
            <6>4 m \notin msgs => m = mm /\ m.type = "accept"
                BY <6>1, <6>2, <6>3
            <6>5 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <6>4 DEF Accept
            <6> QED BY <6>4, <6>5

            <5>2. CASE  /\ i \in preparing[replica]
                                 /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                                    /\ LET replies == {msg \in msgs : 
                                                     /\ msg.inst = i
                                                     /\ msg.type = "prepare-reply"
                                                     /\ msg.dst = replica
                                                     /\ msg.ballot = rec.ballot
                                                     /\ msg.read = FALSE} IN
                                         /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                         /\ ~(\E msg \in replies : 
                                                 msg.status \in {"accept-reply", "commit"})
                                            /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                            /\      \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/ 
                                                                                  p1.deps # p2.deps \/
                                                                                  p1.seq # p2.seq
                                                    \/ \E pl \in preaccepts : pl.src = i[1]
                                                    \* Next condition was previously handled by try-pre-accept (but no fast path anymore)
                                                    \* I chose to make it apparent instead of simply removing the \E p1,p2 above
                                                    \/ \A pp1, pp2 \in preaccepts : pp1.cmd = pp2.cmd /\ 
                                                                                  pp1.deps = pp2.deps /\
                                                                                  pp1.seq = pp2.seq
                     \*                             \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                                                 /\ preaccepts # {}
                                                 /\ \E pac \in preaccepts :
                                                     /\ pac.cmd # none
                                                     /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot) 
                                                     /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                     /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>             
              <6> SUFFICES ASSUME NEW rec \in OldMsg(replica, i), rec.status \notin {"commit"}
                                                 /\ LET replies == {msg \in msgs : 
                                                                  /\ msg.inst = i
                                                                  /\ msg.type = "prepare-reply"
                                                                  /\ msg.dst = replica
                                                                  /\ msg.ballot = rec.ballot
                                                                  /\ msg.read = FALSE} IN
                                                      /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
                                                      /\ ~(\E msg \in replies : 
                                                              msg.status \in {"accept-reply", "commit"})
                                                         /\ LET preaccepts == {msg \in replies : msg.status = "pre-accept-reply"} IN
                                                         /\      \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/ 
                                                                                               p1.deps # p2.deps \/
                                                                                               p1.seq # p2.seq
                                                                 \/ \E pl \in preaccepts : pl.src = i[1]
                                                                 \* Next condition was previously handled by try-pre-accept (but no fast path anymore)
                                                                 \* I chose to make it apparent instead of simply removing the \E p1,p2 above
                                                                 \/ \A pp1, pp2 \in preaccepts : pp1.cmd = pp2.cmd /\ 
                                                                                               pp1.deps = pp2.deps /\
                                                                                               pp1.seq = pp2.seq
                                  \*                             \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                                                         /\ preaccepts # {}
                                                         /\ \E pac \in preaccepts :
                                                              /\ pac.cmd # none
                                                              /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot) 
                                                              /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                                              /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
                           PROVE  (m.type = "commit" => \E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                                           Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
                BY <5>2
              <6>1 PICK replies \in SUBSET msgs : replies = {msg \in msgs : 
                                                                  /\ msg.inst = i
                                                                  /\ msg.type = "prepare-reply"
                                                                  /\ msg.dst = replica
                                                                  /\ msg.ballot = rec.ballot
                                                                  /\ msg.read = FALSE}
                BY <5>2
              <6>2 PICK preaccepts \in SUBSET replies : preaccepts = {msg \in replies : msg.status = "pre-accept-reply"} 
                BY <5>2, <6>1
              <6>3 PICK pac \in preaccepts : 
                      /\ pac.cmd # none
                      /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot) 
                      /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                      /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
                BY <5>2, <6>1, <6>2
              <6>4 PICK msg \in Message :
                         /\ leaderOfInst'= [leaderOfInst EXCEPT ![replica] = leaderOfInst[replica] \cup {i}]
                         /\ msg = [type |-> "pre-accept",
                                    src |-> replica, dst |-> Q,
                                   inst |-> i, 
                                 ballot |-> rec.ballot, 
                                    cmd |-> pac.cmd,
                                   deps |-> {rec_1.inst : rec_1 \in OldMsg(replica, i)},
                                    seq |-> 1 + Max({t.seq : t \in OldMsg(replica, i)}),
                                   vbal |-> rec.ballot,
                                   read |-> FALSE]
                         /\ Send(msg)
                BY <6>3 DEF StartPhase1
              <6>5 msgs' = msgs \cup {msg}
                BY <6>4 DEF Send
              <6>6 \A mm \in msgs : mm \in msgs'
                BY <6>5
              <6>7 m \notin msgs => m = msg /\ m.type = "pre-accept"
                BY <6>5, <6>4
              <6>8 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
                BY MsgInv, <6>6 DEF Accept
              <6> QED BY <6>7, <6>8
            <5>3. QED BY <4>3, <5>1, <5>2
          <4>4. CASE /\ i \in preparing[replica]
                     /\ \E rec \in OldMsg(replica, i) : rec.status \notin {"commit"}
                        /\ LET replies == {msg \in msgs : 
                                         /\ msg.inst = i
                                         /\ msg.type = "prepare-reply"
                                         /\ msg.dst = replica
                                         /\ msg.ballot = rec.ballot
                                         /\ msg.read = FALSE} IN
                             /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)   
                             /\ \A msg \in replies : msg.status = "not-seen"
                             /\ StartPhase1(none, replica, Q, i, rec.ballot)
                             /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                             /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
            <5> SUFFICES ASSUME NEW rec \in OldMsg(replica, i),
                                                                rec.status \notin {"commit"}
                                /\ LET replies == {msg \in msgs : 
                                                 /\ msg.inst = i
                                                 /\ msg.type = "prepare-reply"
                                                 /\ msg.dst = replica
                                                 /\ msg.ballot = rec.ballot
                                                 /\ msg.read = FALSE} IN
                                     /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)   
                                     /\ \A msg \in replies : msg.status = "not-seen"
                                     /\ StartPhase1(none, replica, Q, i, rec.ballot)
                                     /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                     /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>,
                                (m.type = "commit")'
                         PROVE  (\E cleader \in Replicas : \E Q_1 \in Quorums(cleader) :
                                    Accept(m.deps, m.cmd, m.inst, Q_1, m.ballot))'
              BY <4>4 
            <5>1 StartPhase1(none, replica, Q, i, rec.ballot)
                BY <4>4
            <5>2 PICK msg \in Message :
                  /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = leaderOfInst[replica] \cup {i}]
                  /\ msg = [type |-> "pre-accept", 
                             src |-> replica, 
                             dst |-> Q,
                            inst |-> i, 
                          ballot |-> rec.ballot, 
                             cmd |-> none,
                            deps |-> {rec_1.inst : rec_1 \in OldMsg(replica, i)},
                             seq |-> 1 + Max({t.seq : t \in OldMsg(replica, i)}),
                            vbal |-> rec.ballot, 
                            read |-> FALSE]
                     /\ Send(msg) 
                BY <5>1 DEF StartPhase1
            <5>3 msgs' = msgs \cup {msg}
                BY <5>2 DEF Send
            <5>4 \A mm \in msgs : mm \in msgs'
                BY <5>3
            <5>5 m \notin msgs => m = msg /\ m.type = "pre-accept"
            BY <5>2, <5>3
            <5>6 m \in msgs /\ m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                    Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
            BY MsgInv, <5>5 DEF Accept
            <5> QED BY <5>5, <5>6
          <4>5. QED
            BY <2>9, <4>1, <4>2, <4>3, <4>4 DEF PrepareFinalize
            
        <3>2. QED
          BY <3>1
      <2>10. CASE UNCHANGED vars
        <3>1 msgs' = msgs
            BY <2>10 DEF vars
        <3>2 \A m \in msgs : m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
            BY MsgInv, <3>1 DEF Accept
        <3>3 \A m \in msgs' : m.type = "commit"  => \E cleader_1 \in Replicas : \E QQ \in Quorums(cleader_1) :
                                                        Accept(m.deps, m.cmd, m.inst, QQ, m.ballot)'
            BY <3>2, <3>1
        <3> QED BY <3>2, <3>3
      <2>11. QED
        BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF CommandLeaderAction, Next, ReplicaAction
       
    <1> QED BY PTL, <1>1, <1>2 DEF Spec


THEOREM Spec => ([]TypeOK) /\ Nontriviality /\ Stability /\ Consistency
                                                   




=============================================================================
\* Modification History
\* Last modified Mon Apr 05 12:13:35 CEST 2021 by alexis51151
\* Last modified Sun Apr 04 23:40:54 CEST 2021 by alexis51151z
\* Last modified Sat Aug 24 12:25:28 EDT 2013 by iulian
\* Created Tue Apr 30 11:49:57 EDT 2013 by iulian