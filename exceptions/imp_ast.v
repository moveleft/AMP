Require Export helper.
Require Import Coq.Arith.Peano_dec.

Inductive id : Type :=
  | Id : nat -> id.

Inductive exid : Type :=
  | ExId : nat -> exid.

Inductive exn : Type :=
  | Exn : exid * list nat -> exn.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Theorem eq_exid_dec : forall e1 e2 : exid, {e1 = e2} + {e1 <> e2}.
Proof.
   intros e1 e2.
   destruct e1 as [n1]. destruct e2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CThrow : exid -> list aexp -> com
  | CTry : com -> exid -> list id -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'THROW' ex ',' aexps" :=
  (CThrow ex aexps) (at level 60).
Notation "'TRY' c1 'CATCH' ex ',' ids 'DO' c2 'END'" :=
  (CTry c1 ex ids c2) (at level 80, right associativity).