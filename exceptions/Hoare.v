Require Export imp.

Definition Assertion := option exn -> state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall ex st, P ex st -> Q ex st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st' ex,
       ceval c st st' ex ->
       P None st ->
       Q ex st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' ex' Hc HP. apply (Hhoare st st' ex').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' ex' Hc HP.
  apply Himp.
  apply (Hhoare st st' ex').
  assumption. assumption.
Qed.

(*** ASSIGNMENT ***)

Definition assn_sub X a P : Assertion :=
  fun ex st => P ex (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{fun ex st => Q ex st /\ ex = None}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' ex' HE HQ.
  inversion HE. subst. split.
  unfold assn_sub in HQ. assumption.
  reflexivity.
Qed.

(*** SKIP ***)

Theorem hoare_skip : forall P,
  {{P}} SKIP {{fun ex st => P ex st /\ ex = None}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

(*** SEQUENCE ***)

Theorem hoare_seq : forall (P Q R : Assertion) c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{fun ex st => Q ex st /\ ex = None}} ->
  {{P}} c1 ;; c2 {{R}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
(*  inversion HP. clear HP. rename H1 into HP. clear H2.*)
  inversion Hc; subst.
  Case "Standard sequence".
    apply (H st'0 st'). assumption.
    apply (H0 st st'0); assumption.
  Case "Exception in c1 (contradiction)".
    apply H0 in H6. specialize (H6 HP).
    inversion H6. congruence.
  Case "Exception in c2".
    apply (H st'0 st'). assumption.
    apply (H0 st st'0); assumption.
Qed.

Theorem hoare_seq_exn : forall (P Q : Assertion) c1 c2,
  {{P}} c1 {{fun ex st => Q ex st /\ ex <> None}} ->
  {{P}} c1 ;; c2 {{Q}}.
Proof.
  intros.
  intros st st' ex Hc HP.
  inversion Hc; subst.
  Case "Standard sequence (contradiction)".
    apply H in H2. specialize (H2 HP).
    inversion H2. contradiction H1. reflexivity.
  Case "Exception in c1".
    apply (H st st' (Some ex0)); assumption.
  Case "Exception in c2 (contradiction)".
    apply H in H2. specialize (H2 HP).
    inversion H2. contradiction H1. reflexivity.
Qed.

(*** IF THEN ELSE ***)

Definition bassn b : Assertion :=
  fun _ st => (beval st b = true).
Lemma bexp_eval_true : forall b st ex,
  beval st b = true -> (bassn b) ex st.
Proof.
  intros b ex st Hbe.
  unfold bassn. assumption.
Qed.
Lemma bexp_eval_false : forall b st ex,
  beval st b = false -> ~ ((bassn b) ex st).
Proof.
  intros b ex st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if : forall (P Q : Assertion)  b c1 c2,
  {{fun ex st => P ex st /\ bassn b ex st}} c1 {{Q}} ->
  {{fun ex st => P ex st /\ ~(bassn b ex st)}} c2 {{Q}} ->
  {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "If true".
    apply (H st st' ex').
    assumption. split. assumption.
    apply bexp_eval_true. assumption.
  Case "If false".
    apply (H0 st st' ex').
    assumption. split. assumption.
    apply bexp_eval_false. assumption.
Qed.
 
(*** EXCEPTIONS ***)

Theorem hoare_throw : forall P e aexps,
  {{P}}
    THROW e, aexps
  {{fun ex st => P None st /\ ex = (Some (Exn (e, (map (fun a => aeval st a) aexps))))}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

Theorem hoare_try : forall (P Q : Assertion) c1 c2 e ids,
  {{P}} c1 {{fun ex st => Q ex st /\ match ex with
                                       | Some (Exn (e', _)) => e <> e'
                                       | None => True
                                     end
           }} ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "Try".
    apply (H st st' None); assumption.
  Case "Catch (contradiction)".
    apply H in H7. specialize (H7 HP).
    inversion H7. congruence.
  Case "Try exception".
    apply (H st st'); assumption.
  Case "Catch exception (contradiction)".
    apply H in H7. specialize (H7 HP).
    inversion H7. congruence.
Qed.

Theorem hoare_try_exn : forall (P Q : Assertion) c1 c2 e ns ids,
  {{fun ex st => exists st', P ex st' /\ st = (update_many st' ids ns)}} c2 {{Q}} ->
  {{P}} c1 {{fun ex st => ex = (Some (Exn (e, ns)))}} ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}}.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "Try (contradiction)".
    apply H0 in H8. specialize (H8 HP).
    inversion H8.
  Case "Catch".
    apply (H (update_many st ids ns0) st'). assumption.
    apply ex_intro with (st).
    split. assumption.
    assert (ns = ns0).
    SCase "Proof of assertion".
      specialize (H0 st st'0 (Some (Exn (e, ns0)))).
      specialize (H0 H8 HP). congruence. 
    rewrite H1. reflexivity.
  Case "Try exception (contradiction)".
    apply H0 in H9. specialize (H9 HP).
    inversion H9. subst. congruence.
  Case "Catch exception".
    apply (H (update_many st ids ns0) st'). assumption.
    apply ex_intro with (st).
    split. assumption.
    assert (ns = ns0).
    SCase "Proof of assertion".
      specialize (H0 st st'0 (Some (Exn (e, ns0)))).
      specialize (H0 H8 HP). congruence.
    rewrite H1. reflexivity.
Qed.