Require Export imp_state.
Require Export imp.
Require Import FunctionalExtensionality.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).
     
Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Definition assn_sub_list' xs axs P : Assertion :=
  fun (st : state) =>
    let st' := zip_state st st xs axs in
    P st'.
  
Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : program -> Prop :=
  fun program =>
    forall st st' s,
       c ; program / st || s / st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.
  
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c env,
  {{P'}} c {{Q}} env ->
  P ->> P' ->
  {{P}} c {{Q}} env.
Proof.
  intros P P' Q c E Hhoare Himp.
  intros st st' s Hc HP. apply (Hhoare st st' s).
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c env,
  {{P}} c {{Q'}} env ->
  Q' ->> Q ->
  {{P}} c {{Q}} env.
Proof.
  intros P Q Q' c env Hhoare Himp.
  intros st st' s' Hc HP.
  apply Himp.
  apply (Hhoare st st' s'); assumption.
Qed.

Fixpoint ls_disjoint (xs : list id) ys : Prop :=
	match xs with
	| x::xs' =>
	    False = (List.Exists (fun y => y = x) ys)
	    /\
	    ls_disjoint xs' ys
	| nil => True
	end.
	
Lemma update_retrieve : forall st X v,
  update st X v X = v.
Proof.
  intros.
  unfold update.
  destruct eq_id_dec; [ reflexivity | congruence].
Qed.

Lemma update_retrieve_eq : forall st X v v',
  v = v' ->
  update st X v X = v'.
Proof.
  intros.
  unfold update.
  destruct eq_id_dec; [ assumption | congruence].
Qed.

Lemma update_retrieve_dif : forall st X Y v,
  X <> Y ->
  update st X v Y = st Y.
Proof.
  intros.
  unfold update.
  destruct eq_id_dec; [ congruence | reflexivity ].
Qed.
  
(*** Call ***)
Theorem hoare_call : forall (program : program) f X args P Q body params rexp r,
	program f = (body,params,rexp) ->
	{{ P }}
	  body
	{{ fun st => Q st /\ r = aeval st rexp }} program ->
	{{ fun st => P (zip_state st empty_state params args) }}
	  CCall f X args
    {{ fun st => st X = r }} program
	.
Proof.
  unfold hoare_triple.
  intros.
  inversion H1; rewrite H6 in H; inversion H; subst.
  remember (update st X (aeval st'' rexp)) as st'''.
  specialize (H0 _ _ _ H16 H2).
  destruct H0.
  subst.
  rewrite update_retrieve.
  reflexivity.
Qed.

(*** ASSIGNMENT ***)

Theorem hoare_asgn : forall Q X a env,
  {{Q [X |-> a]}} (X ::= a) {{ Q }} env.
Proof.
  unfold hoare_triple.
  intros.
  inversion H ; subst.
  unfold assn_sub in H0.
  assumption.
Qed.

(*** IF THEN ELSE ***)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.
Qed.
Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if : forall (P Q : Assertion)  b c1 c2 env,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} env ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} env ->
  {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} env.
Proof.
  intros.
  intros st st' s Hc HP.
  inversion Hc; subst.
  Case "If true".
    apply (H st st' s).
    assumption. split. assumption.
    apply bexp_eval_true. assumption.
  Case "If false".
    apply (H0 st st' s).
    assumption. split. assumption.
    apply bexp_eval_false. assumption.
Qed.

(*******************
 * EXAMPLE 1       *
 *******************)

Definition body : com := 
  Y ::= APlus (AId X) (ANum 1).
  
Definition env : program :=
  fun id =>
    if eq_id_dec F id
    then (body, [X], (APlus (AId X) (ANum 1)))
    else (CSkip, [], ANum 0)
    .

Lemma body_p : forall Q X Y,
  Q = (fun st => st Y = st X + 1) ->
  {{ Q[Y |-> (APlus (AId X) (ANum 1))] }}
    Y ::= APlus (AId X) (ANum 1)
  {{ Q }} env.
Proof.
  intros Q X Y H.
  rewrite H.
  apply hoare_asgn.
Qed.

Theorem prog_correct :
  {{fun st => True}}
    CCall F Z [ANum 2]
  {{fun st => st Z = 3}} env.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_call with (params := [X]) (Q := fun st => st Y = 3)
                  (body := body) (rexp := (APlus (AId X) (ANum 1))).
  unfold env. simpl. reflexivity.
  apply hoare_asgn.
  intro. intros _.
  unfold assn_sub.
  simpl.
  split; try rewrite update_retrieve; reflexivity.
Qed.

(*******************
 * EXAMPLE 2       *
 ******************* )

Definition Fbody : com := 
  IFB (BEq (ANum 0) (AId X))
  THEN Z ::= APlus (AId Y) (ANum 1)
  ELSE CCall G Z [AId Y]
  FI.
  
Definition Gbody : com := 
  Z ::= APlus (AId Y) (ANum 1) ;;
  Z ::= APlus (AId Z) (ANum 1)
  .
  
Definition env'' : program :=
  fun id =>
    if eq_id_dec F id
    then (Fbody, cons X (cons Y nil), (APlus (AId X) (AId Y)))
    else if eq_id_dec G id
    then (Gbody, [X], (APlus (AId X) (ANum 2)))
    else (CSkip, [], ANum 0)  
  .
  
Theorem prog_correct'' :
  {{fun st => True}}
    CCall F Z (cons (ANum 10) (cons (ANum 10) nil))
  {{fun st => st Z = 20}} env''.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_call with (params := cons X (cons Y nil))
			      (Q := fun st => st Z = st X + st Y)
                  (body := Fbody) (rexp := (APlus (AId X) (AId Y)))
                  (P := fun st => st X + st Y = st X + st Y /\ st X = 10 /\ st Y = 10).
  unfold env''. simpl. reflexivity.
  eapply hoare_consequence_post with (Q' := fun st => st Z = st X + st Y /\ st X = 10 /\ st Y = 10).
  eapply hoare_consequence_pre with (P' := fun st => True).
  unfold body''.
  apply b''.
  intro; intros; apply I.
  intro; intros.
  destruct H.
  split. assumption.
  unfold aeval. destruct H0; rewrite H0, H1; reflexivity.
  intros st _. simpl.
  split. reflexivity.
  rewrite update_retrieve_dif, update_retrieve, update_retrieve.
  split; reflexivity.
  unfold Y, X, not; intro; congruence.
Qed. *)

Definition body'' : com := 
  IFB (BEq (ANum 1) (AId X))
  THEN Z ::= APlus (AId Y) (AId X)
  ELSE CCall F Z (cons (AMinus (AId X) (ANum 1))
				   (cons (APlus (AId Y) (ANum 1))
 					 nil))
  FI.
(*  
Definition env'' : program :=
  fun id =>
    if eq_id_dec F id
    then (body'', cons X (cons Y nil), (APlus (AId X) (AId Y)))
    else (CSkip, [], ANum 0)
    .

( * 
  {{ fun st => st X > 0 }} env
  IFB (BEq (ANum 1) (AId X)) THEN
    {{ fun st => st X = 1 /\ st X + Y = st X + Y }} env ->>
    {{ fun st => st X + Y = st X + Y }} env
    Z ::= APlus (AId X) (AId Y)
    {{ fun st => st Z = st X + Y }} env
  ELSE
    {{ fun st => st X > 1 /\ st X + st Y = st X + st Y }} env
    CCall F Z (cons (AMinus (AId X) (ANum 1))
		   		 (cons (APlus (AId Y) (ANum 1))
 					nil))
 	{{ fun st => st X > 1 /\ st Z = st X + st Y }} env ->>
 	{{ fun st => st Z = st X + st Y }} env
  FI.
  {{ fun st => st Z = st X + st Y }} env * )

Lemma b'' : forall X Y Z x y z env,
  z = x + y ->
  {{ (fun st => z = st Z /\ x = st X /\ y = st Y)[Z |-> APlus (AId Y) (AId X)] }}
  IFB (BEq (ANum 1) (AId X))
  THEN Z ::= APlus (AId Y) (AId X)
  ELSE CCall F Z (cons (AMinus (AId X) (ANum 1))
				   (cons (APlus (AId Y) (ANum 1))
 					 nil))
  FI
  {{ fun st => st Z = st X + st Y }} env.
Proof.
  intros X Y Z x y z env H.
  apply hoare_if.
  eapply hoare_consequence_post
	with (Q' := fun st : state => st Z = st X + st Y).
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  intro. intros.
  unfold assn_sub in *.
  destruct H0; destruct H0; destruct H2.
  rewrite <- H0; rewrite <- H2; rewrite <- H3.
  assumption.
  intro; intros.
  assumption.
Admitted.

Theorem prog_correct'' :
  {{fun st => True}}
    CCall F Z (cons (ANum 10) (cons (ANum 10) nil))
  {{fun st => st Z = 20}} env''.
Proof.
  eapply hoare_consequence_pre.
  apply call with (params := cons X (cons Y nil))
			      (Q := fun st => st Z = st X + st Y)
                  (body := body'') (rexp := (APlus (AId X) (AId Y)))
                  (P := fun st => st X + st Y = st X + st Y /\ st X = 10 /\ st Y = 10).
  unfold env''. simpl. reflexivity.
  eapply hoare_consequence_post with (Q' := fun st => st Z = st X + st Y /\ st X = 10 /\ st Y = 10).
  eapply hoare_consequence_pre with (P' := fun st => True).
  unfold body''.
  apply b''.
  intro; intros; apply I.
  intro; intros.
  destruct H.
  split. assumption.
  unfold aeval. destruct H0; rewrite H0, H1; reflexivity.
  intros st _. simpl.
  split. reflexivity.
  rewrite update_retrieve_dif, update_retrieve, update_retrieve.
  split; reflexivity.
  unfold Y, X, not; intro; congruence.
Qed. *)
