Require Export imp.
Require Import FunctionalExtensionality.

Definition Assertion := option exn -> state -> heap -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall ex st h, P ex st h -> Q ex st h.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : program -> Prop :=
  fun env =>
    forall st ex h st' h',
         ceval c env st h st' h' ex ->
         P None st h ->
         Q ex st' h'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition emp : Assertion :=
  fun ex st h => Empty h.
Definition point_to_val (x : id)(v : aexp) : Assertion :=
  fun ex st h => find (st x) h = Some (aeval st v) /\ forall l l', st x = l' -> l' <> l -> find l h = None.
Definition look_up_val (e v : aexp) : Assertion :=
  fun ex st h => find (aeval st e) h = Some (aeval st v).
Definition ass_val (x:id)(v:aexp) : Assertion :=
  fun ex st h => st x = (aeval st v).
Notation "x '|->' v" :=
  (point_to_val x v) (at level 80).
Notation "e '|~>' v" := 
  (look_up_val e v) (at level 80).
Notation "x '|*~>' v" :=
  (ass_val x v) (at level 80).

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c env,
  {{P'}} c {{Q}} env ->
  P ->> P' ->
  {{P}} c {{Q}} env.
Proof.
  intros P P' Q c env Hhoare Himp.
  intros st ex h st' h' Hc HP. apply (Hhoare st ex h st' h').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c env,
  {{P}} c {{Q'}} env ->
  Q' ->> Q ->
  {{P}} c {{Q}} env.
Proof.
  intros P Q Q' c env Hhoare Himp.
  intros st ex h st' h' Hc HP.
  apply Himp.
  apply (Hhoare st ex h st' h').
  assumption. assumption.
Qed.

(*** ASSIGNMENT ***)

Definition assn_sub X a P : Assertion :=
  fun ex st => P ex (update st X (aeval st a)).

Theorem hoare_asgn : forall Q X a env,
  {{assn_sub X a Q}} (X ::= a) {{fun ex st h => Q ex st h /\ ex = None}} env.
Proof.
  unfold hoare_triple.
  intros Q X a env st ex h st' h' HE HQ.
  inversion HE. subst. split.
  unfold assn_sub in HQ. assumption.
  reflexivity.
Qed.

(*** SKIP ***)

Theorem hoare_skip : forall P env,
  {{P}} SKIP {{fun ex st h => P ex st h /\ ex = None}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

(*** SEQUENCE ***)

Theorem hoare_seq : forall (P Q R : Assertion) c1 c2 env,
  {{Q}} c2 {{R}} env ->
  {{P}} c1 {{fun ex st h => Q ex st h /\ ex = None}} env ->
  {{P}} c1 ;; c2 {{R}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  Case "Standard sequence".
    specialize (H3 env).
    specialize (H10).
    apply (H st'0 ex h'0 st' h'). assumption.
    apply (H0 st None h st'0 h'0); assumption.
  Case "Exception in c1 (contradiction)".
    apply H0 in H9. specialize (H9 HP).
    inversion H9. congruence.
Qed.

Theorem hoare_seq_exn : forall (P Q : Assertion) c1 c2 env,
  {{P}} c1 {{fun ex st h => Q ex st h /\ ex <> None}} env ->
  {{P}} c1 ;; c2 {{Q}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  Case "Standard sequence (contradiction)".
    apply H in H2. specialize (H2 HP).
    inversion H2. contradiction H1. reflexivity.
  Case "Exception in c1".
    apply (H st (Some ex0) h st' h'); assumption.
Qed.

(*** IF THEN ELSE ***)

Definition bassn b : Assertion :=
  fun _ st _ => (beval st b = true).
Lemma bexp_eval_true : forall b st ex h,
  beval st b = true -> (bassn b) ex st h.
Proof.
  intros b ex st h Hbe.
  unfold bassn. assumption.
Qed.
Lemma bexp_eval_false : forall b st ex h,
  beval st b = false -> ~ ((bassn b) ex st h).
Proof.
  intros b ex st h Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if : forall (P Q : Assertion) b c1 c2 env,
  {{fun ex st h => P ex st h /\ bassn b ex st h}} c1 {{Q}} env ->
  {{fun ex st h => P ex st h /\ ~(bassn b ex st h)}} c2 {{Q}} env ->
  {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  Case "If true".
    apply (H st ex h st' h').
    assumption. split. assumption.
    apply bexp_eval_true. assumption.
  Case "If false".
    apply (H0 st ex h st' h').
    assumption. split. assumption.
    apply bexp_eval_false. assumption.
Qed.

(*** WHILE ***)

Theorem hoare_while : forall P b c env,
  {{fun ex st h => P ex st h /\ bassn b ex st h}} c {{P}} env ->
  {{P}} WHILE b DO c END {{fun ex st h => P ex st h /\ (ex = None -> ~(bassn b ex st h))}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  remember (WHILE b DO c END) as wcom eqn:Hwcom.
  induction Hc; try inversion Hwcom; subst; clear Hwcom.
  Case "While End".
    split. assumption. intros. apply bexp_eval_false. assumption.
  Case "While Loop".
    apply (H4 env H). reflexivity.
    apply (H st None h st' h'). apply H1.
    split. assumption. apply bexp_eval_true. assumption.
  Case "While Exception".
    split. apply (H st (Some ex) h st' h'). assumption.
    split. assumption. apply bexp_eval_true. assumption.
    intros. apply bexp_eval_false. congruence.
Qed.

(*** EXCEPTIONS ***)

Theorem hoare_throw : forall P e aexps env,
  {{P}}
    THROW e, aexps
  {{fun ex st h => P None st h /\ ex = (Some (Exn (e, (fold_right (fun a acc => cons (aeval st a) acc) nil aexps)))) }} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

Theorem hoare_try : forall (P Q : Assertion) c1 c2 e ids env,
  {{P}} c1 {{fun ex st h => Q ex st h /\ match ex with
                                       | Some (Exn (e', _)) => e <> e'
                                       | None => True
                                     end
           }} env ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  Case "Try".
    apply (H st None h st' h'); assumption.
  Case "Catch (contradiction)".
    apply H in H10. specialize (H10 HP).
    inversion H10. congruence.
  Case "Try exception".
    apply (H st (Some (Exn (e0, ns))) h st' h'); assumption.
Qed.

Theorem hoare_try_exn : forall (P Q : Assertion) c1 c2 e ns ids env,
  {{fun ex st h => exists st', P ex st' h /\ st = (update_many st' ids ns)}} c2 {{Q}} env ->
  {{P}} c1 {{fun ex st h => ex = (Some (Exn (e, ns)))}} env ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}} env.
Proof.
  intros.
  intros st ex h st' h' Hc HP.
  inversion Hc; subst.
  Case "Try (contradiction)".
    apply H0 in H11. specialize (H11 HP).
    inversion H11.
  Case "Catch".
    apply (H (update_many st ids ns0) ex h st' h'). assumption.
    apply ex_intro with (st).
    split. assumption.
    assert (ns = ns0).
    SCase "Proof of assertion".
      specialize (H0 st (Some (Exn (e, ns0))) h st'0 h'0).
      specialize (H0 H11 HP). congruence. 
    rewrite H1. reflexivity.
  Case "Try exception (contradiction)".
    apply H0 in H12. specialize (H12 HP).
    inversion H12. subst. congruence.
Qed.

(*** Call ***)

Lemma update_retrieve : forall st X v,
  update st X v X = v.
Proof.
  intros.
  unfold update.
  destruct eq_id_dec; [ reflexivity | congruence].
Qed.

Theorem hoare_call : forall (program : program) f X args P Q body params rexp r,
	program f = (body,params,rexp) ->
	{{ P }}
	  body
	{{ fun e st h => Q e st h /\ r = aeval st rexp }} program ->
	{{ fun e st h => P e (zip_state st empty_state params args) h }}
	  CCall f X args
    {{ fun e st h => st X = r }} program
	.
Proof.
  unfold hoare_triple.
  intros.
  inversion H1; rewrite H6 in H; inversion H; subst.
  remember (update st X (aeval st'' rexp)) as st'''.
  specialize (H0 _ _ _ _ _ H18 H2).
  destruct H0.
  subst.
  rewrite update_retrieve.
  reflexivity.
Qed.

Theorem hoare_call_exn : forall (program : program) f X args P body params rexp ex,
	program f = (body,params,rexp) ->
	{{ P }}
	  body
	{{ fun e st h => e = ex }} program ->
	{{ fun e st h => P e (zip_state st empty_state params args) h }}
	  CCall f X args
    {{ fun e st h => e = ex }} program
	.
Proof.
  intro.
  intros.
  intro. intros.  
  inversion H1; rewrite H6 in H; inversion H; subst.
  remember (update st X (aeval st'' rexp)) as st'''.
  unfold hoare_triple in H0.
  remember ((zip_state st empty_state params args)) as st''''.
  apply (H0 st'''' _ h st'' h').
  assumption.
  assumption.
Qed.

Theorem hoare_alloc : forall x,
  {{ emp }} x <-# ALLOC {{ x |-> ANum 0 }}.
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
  subst.
  assert (current_stack : forall st x v, st x = aeval st v).
  admit.
  apply current_stack.
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
  assert (not_mapsto_in_iff : forall (m:heap) (x e:nat), find x m = None -> MapsTo x e m -> False).
  admit.
  apply not_mapsto_in_iff in H1.
  apply H1.
  assert (empty_find_in : forall (m:heap) (a:nat), find a m = None <-> is_empty m = true).
  admit.
  apply empty_find_in in H4.
  apply empty_find_in.
  apply H4.
Qed.
