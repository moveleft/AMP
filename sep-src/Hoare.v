Require Export ILogic ILInsts.

Require Import MapInterface MapNotations.
Require Import BILogic SepAlgMap.
Require Import MapFacts.
Require Export Imp.

Definition heap := Map [nat, nat].

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAlloc : id ->com
  | CRead : id -> aexp -> com
  | CWrite : aexp -> aexp -> com
  | CFree : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "ALLOC"
  | Case_aux c "READ" | Case_aux c "WRITE" | Case_aux c "FREE"].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "x <-: 'ALLOC'" :=
  (CAlloc x) (at level 80).
Notation "x '<-*' '[' a ']'" :=
  (CRead x a) (at level 80).
Notation "'[' a ']' '<-@' b" :=
  (CWrite a b) (at level 80).
Notation "'FREE' a" :=
  (CFree a) (at level 80).

Inductive ceval : com -> state -> heap -> state -> heap -> Prop :=
  | E_Skip : forall st h,
      ceval SKIP st h st h
  | E_Ass  : forall st a1 n x h,
      aeval st a1 = n ->
      ceval (x ::= a1) st h (update st x n) h
  | E_Seq : forall c1 c2 st st' st'' h h' h'',
      ceval c1 st h st' h'->
      ceval c2 st' h' st'' h''->
      ceval (c1 ;; c2) st h st'' h''
  | E_IfTrue : forall st st' b c1 c2 h h',
      beval st b = true ->
      ceval c1 st h  st' h'->
      ceval (IFB b THEN c1 ELSE c2 FI) st h st' h'
  | E_IfFalse : forall st st' b c1 c2 h h',
      beval st b = false ->
      ceval c2 st h st' h' ->
      ceval (IFB b THEN c1 ELSE c2 FI) st h st' h'
  | E_WhileEnd : forall b st c h,
      beval st b = false ->
      ceval (WHILE b DO c END) st h  st h
  | E_WhileLoop : forall st st' st'' b c h h' h'',
      beval st b = true ->
      ceval c st h st' h' ->
      ceval (WHILE b DO c END) st' h' st'' h'' ->
      ceval (WHILE b DO c END) st h st'' h''
  | E_Alloc : forall st x addr h,
      ~ In addr h ->
      ceval (x <-: ALLOC) st h (update st x addr) (add addr 0 h)
  | E_Read : forall st x a addr v h,
      aeval st a = addr ->
      find addr h = Some (aeval st v)->
      ceval (x <-* [ a ]) st h (update st x (aeval st v)) h
  | E_Write : forall st a b addr value v h,
      aeval st a = addr ->
      aeval st b = value ->
      find addr h = Some v ->
      ceval ([ a ] <-@ b) st h st (add addr value (remove addr h))
  | E_Free : forall st (h:heap) addr (v:aexp) (x:id),
      st x = addr ->
      find addr h = Some (aeval st v) ->
      ceval (FREE x) st h st (remove addr h)


  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
  | Case_aux c "E_Alloc" | Case_aux c "E_Read" | Case_aux c "E_Write"
  | Case_aux c "E_Free"].
   
Definition Assertion := state -> heap -> Prop.       

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st' h h',
  P st h ->
  ceval c st h st' h' ->
  Q st' h'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90).

(* emp *)
Definition emp : Assertion :=
  fun st h => Empty h.

Definition point_to_val (x : id)(v : aexp) : Assertion :=
  fun st h => find (st x) h = Some (aeval st v) /\ forall l l', st x = l' -> l' <> l -> find l h = None.

Definition look_up_val (e v : aexp) : Assertion :=
  fun st h => find (aeval st e) h = Some (aeval st v).
  
Definition ass_val (x:id)(v:aexp) : Assertion :=
  fun st h => st x = aeval st v.
  
Notation "x '|->' v" :=
  (point_to_val x v) (at level 80).
  
Notation "e '|~>' v" := 
  (look_up_val e v) (at level 80).

Notation "x '|*~>' v" :=
  (ass_val x v) (at level 80).

Theorem hoare_alloc : forall x,
  {{ emp }} x <-: ALLOC {{ x |-> ANum 0 }}.
Proof.
  split.
  inversion H0. 
  subst.
  rewrite add_eq_o.
  simpl. 
  reflexivity.
  unfold update.
  rewrite eq_id.
  reflexivity.
  intros.
  inversion H0.
  subst.
  unfold update in H2.
  rewrite eq_id in H2.
  assert (diff_addr : forall (m:heap) (a b e :nat), a<>b -> find b (add a e m) = None).
  admit.
  rewrite diff_addr.
  reflexivity.
  apply H2.
Qed.

Theorem hoare_read : forall e v x,
  {{ e |~> v }} x <-* [ e ] {{ x |*~> v }}.
Proof.
  intros e v x st.
  intros.
  unfold ass_val.
  inversion H0.
  unfold look_up_val in H.
  rewrite H3 in H.
  rewrite <-H7 in H8.
  rewrite H in H8.
  assert (same_val : forall st v v', Some(aeval st v) = Some(aeval st v') -> v=v').
  admit.
  apply same_val in H8.
  rewrite <- H8 in H6.
  rewrite <- H8.
  rewrite H6.
  assert (update_stack : forall st st' v, update st x (aeval st v) = st' -> st' x = (aeval st' v)).
  admit.
  apply update_stack in H6.
  apply H6.
Qed.

Theorem hoare_write : forall e v v',
  {{ e |~> v }} [ e ] <-@ v' {{ e |~> v' }}.
Proof.
  intros e v v' st.
  intros.
  unfold look_up_val.
  inversion H0.
  subst.
  assert (add_remove : forall (m:heap) (e v :nat), 
  find e (add e v (remove e m)) = Some v).
  admit.
  rewrite add_remove.
  reflexivity.
Qed.

Theorem hoare_free : forall x v,
  {{ x |-> v }} FREE x {{ emp }}.
Proof.
  intros x v st.
  intros.
  unfold emp.
  unfold Empty.
  unfold not.
  intros.
  inversion H0.
  subst.
  unfold point_to_val in H.
  inversion H.
  apply remove_mapsto_iff in H1.
  inversion H1.
  apply H3 in H5.
  assert (not_mapsto_in_iff : forall (m:heap) (x e:nat), find x m = None -> MapsTo x e m -> False).
  admit.
  apply not_mapsto_in_iff in H6.
  apply H6.
  apply H5.
  reflexivity.
Qed.
