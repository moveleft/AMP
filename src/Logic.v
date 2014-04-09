Require Import ILogic ILInsts SepAlgMap Maps Rel SepAlg BILogic BILInsts.
Require Import MapInterface MapFacts.
Require Import UUSepAlg SepAlgInsts.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Definition myLogic := nat -> bool -> Prop.

Instance myLogicOps : ILogicOps myLogic := _.
Instance myLogicIL : ILogic myLogic := _.


Lemma test1 : forall P Q R, P //\\ Q //\\ R |-- Q //\\ R //\\ P.
Proof.
  intros.
  repeat apply landR.
  + apply landL2. apply landL1. reflexivity.
  + apply landL2. apply landL2. reflexivity.
  + apply landL1. reflexivity.
Qed.

(* You can make this connectives in the logic transparent by using this command. It is generally recommended 
   that you do this as little as possible. You will in effect be reasoning in the model of the logic and not
   in the logic itself. Still, it is often necessary when proving the soundness of Hoare triples for instance.
*)
Transparent ILFun_Ops.

Lemma test2 : forall P Q R, P //\\ Q //\\ R |-- Q //\\ R //\\ P.
Proof.
  intros.
  intros n b H; simpl in *.
  intuition. 
Qed.

(* Here the connectives are made opaque again. *)
Opaque ILFun_Ops.


(* Separation logic *)

Definition heap := Map [nat, nat].

Definition heap_unit : heap := @map_unit _ _ _ nat.

Local Existing Instance MapSepAlgOps.
Local Existing Instance MapSepAlg.
Local Existing Instance MapEquiv.
Local Existing Instance EquivPreorder.
Local Existing Instance UUMapSepAlg.
Local Existing Instance SepAlgOps_prod.
Local Existing Instance SepAlg_prod.
Local Existing Instance UUSepAlg_prod.

Instance RelHeap : Rel heap := _.
Instance HeapSepAlgOps : SepAlgOps heap := _.
Instance SepAlgHeap : SepAlg heap := _.
Instance UUSepAlgHeap : UUSepAlg heap := _.
Instance PreorderHeap : PreOrder (@rel heap RelHeap) := _.

Local Existing Instance ILPre_Ops.

Definition mySepLogic := ILPreFrm (@rel heap RelHeap) Prop. 

Local Existing Instance ILPre_Ops.
Local Existing Instance SABIOps.
Local Existing Instance SABILogic.

Instance mySepLogicOps : BILOperators mySepLogic := _.
Instance mySepLogicBI : BILogic mySepLogic := _.

Lemma test3 : forall P Q R : mySepLogic, P ** Q |-- Q ** P.
Proof.
   intros.
   rewrite sepSPC1.
   apply bilsep.
   + reflexivity.
Qed.