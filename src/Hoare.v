Require Export imp.
Require Import FunctionalExtensionality.

Definition Assertion := option exn -> state -> heap -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall ex st, P ex st -> Q ex st.

Definition safe c st h := ~ (ceval c st h empty_state h). 

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
  
Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : program -> Prop :=
  fun env =>
    forall st st' ex,
         safe c st h /\ forall st' h', ceval c env st h st' h' ex ->
         P None st h->
         Q ex st' h'.
  
Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c env,
  {{P'}} c {{Q}} env ->
  P ->> P' ->
  {{P}} c {{Q}} env.
Proof.
  intros P P' Q c env Hhoare Himp.
  intros st st' ex' Hc HP. apply (Hhoare st st' ex').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c env,
  {{P}} c {{Q'}} env ->
  Q' ->> Q ->
  {{P}} c {{Q}} env.
Proof.
  intros P Q Q' c env Hhoare Himp.
  intros st st' ex' Hc HP.
  apply Himp.
  apply (Hhoare st st' ex').
  assumption. assumption.
Qed.

(*** ASSIGNMENT ***)

Definition assn_sub X a P : Assertion :=
  fun ex st => P ex (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

(* TODO used?
Definition assn_sub_list' xs axs P : Assertion :=
  fun (st : state) =>
    let st' := zip_state st st xs axs in
    P st'.
*)

Theorem hoare_asgn : forall Q X a env,
  {{Q [X |-> a]}} (X ::= a) {{fun ex st => Q ex st /\ ex = None}} env.
Proof.
  unfold hoare_triple.
  intros Q X a env st st' ex' HE HQ.
  inversion HE. subst. split.
  unfold assn_sub in HQ. assumption.
  reflexivity.
Qed.

(*** SKIP ***)

Theorem hoare_skip : forall P env,
  {{P}} SKIP {{fun ex st => P ex st /\ ex = None}} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

(*** SEQUENCE ***)

Theorem hoare_seq : forall (P Q R : Assertion) c1 c2 env,
  {{Q}} c2 {{R}} env ->
  {{P}} c1 {{fun ex st => Q ex st /\ ex = None}} env ->
  {{P}} c1 ;; c2 {{R}} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "Standard sequence".
    specialize (H3 env).
    specialize (H8).
    apply (H st'0 st'). assumption.
    apply (H0 st st'0); assumption.
  Case "Exception in c1 (contradiction)".
    apply H0 in H7. specialize (H7 HP).
    inversion H7. congruence.
Qed.

Theorem hoare_seq_exn : forall (P Q : Assertion) c1 c2 env,
  {{P}} c1 {{fun ex st => Q ex st /\ ex <> None}} env ->
  {{P}} c1 ;; c2 {{Q}} env.
Proof.
  intros.
  intros st st' ex Hc HP.
  inversion Hc; subst.
  Case "Standard sequence (contradiction)".
    apply H in H2. specialize (H2 HP).
    inversion H2. contradiction H1. reflexivity.
  Case "Exception in c1".
    apply (H st st' (Some ex0)); assumption.
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

Theorem hoare_if : forall (P Q : Assertion)  b c1 c2 env,
  {{fun ex st => P ex st /\ bassn b ex st}} c1 {{Q}} env ->
  {{fun ex st => P ex st /\ ~(bassn b ex st)}} c2 {{Q}} env ->
  {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} env.
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

(*** WHILE ***)

Theorem hoare_while : forall P b c env,
  {{fun ex st => P ex st /\ bassn b ex st}} c {{P}} env ->
  {{P}} WHILE b DO c END {{fun ex st => P ex st /\ (ex = None -> ~(bassn b ex st))}} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  remember (WHILE b DO c END) as wcom eqn:Hwcom.
  induction Hc; try inversion Hwcom; subst; clear Hwcom.
  Case "While End".
    split. assumption. intros. apply bexp_eval_false. assumption.
  Case "While Loop".
    apply (H4 env H). reflexivity.
    apply (H st st'). apply H1.
    split. assumption. apply bexp_eval_true. assumption.
  Case "While Exception".
    split. apply (H st st' (Some ex)). assumption.
    split. assumption. apply bexp_eval_true. assumption.
    intros. apply bexp_eval_false. congruence.
Qed.

(*** EXCEPTIONS ***)

Theorem hoare_throw : forall P e aexps env,
  {{P}}
    THROW e, aexps
  {{fun ex st => P None st /\ ex = (Some (Exn (e, (map (fun a => aeval st a) aexps)))) }} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  split. assumption. reflexivity.
Qed.

Theorem hoare_try : forall (P Q : Assertion) c1 c2 e ids env,
  {{P}} c1 {{fun ex st => Q ex st /\ match ex with
                                       | Some (Exn (e', _)) => e <> e'
                                       | None => True
                                     end
           }} env ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "Try".
    apply (H st st' None); assumption.
  Case "Catch (contradiction)".
    apply H in H8. specialize (H8 HP).
    inversion H8. congruence.
  Case "Try exception".
    apply (H st st'); assumption.
Qed.

Theorem hoare_try_exn : forall (P Q : Assertion) c1 c2 e ns ids env,
  {{fun ex st => exists st', P ex st' /\ st = (update_many st' ids ns)}} c2 {{Q}} env ->
  {{P}} c1 {{fun ex st => ex = (Some (Exn (e, ns)))}} env ->
  {{P}} TRY c1 CATCH e, ids DO c2 END {{Q}} env.
Proof.
  intros.
  intros st st' ex' Hc HP.
  inversion Hc; subst.
  Case "Try (contradiction)".
    apply H0 in H9. specialize (H9 HP).
    inversion H9.
  Case "Catch".
    apply (H (update_many st ids ns0) st'). assumption.
    apply ex_intro with (st).
    split. assumption.
    assert (ns = ns0).
    SCase "Proof of assertion".
      specialize (H0 st st'0 (Some (Exn (e, ns0)))).
      specialize (H0 H9 HP). congruence. 
    rewrite H1. reflexivity.
  Case "Try exception (contradiction)".
    apply H0 in H10. specialize (H10 HP).
    inversion H10. subst. congruence.
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
	{{ fun e st => Q e st /\ r = aeval st rexp }} program ->
	{{ fun e st => P e (zip_state st empty_state params args) }}
	  CCall f X args
    {{ fun e st => st X = r }} program
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

Theorem hoare_call_exn : forall (program : program) f X args P body params rexp ex,
	program f = (body,params,rexp) ->
	{{ P }}
	  body
	{{ fun e st => e = ex }} program ->
	{{ fun e st => P e (zip_state st empty_state params args) }}
	  CCall f X args
    {{ fun e st => e = ex }} program
	.
Proof.
  intro.
  intros.
  intro. intros.  
  inversion H1; rewrite H6 in H; inversion H; subst.
  remember (update st X (aeval st'' rexp)) as st'''.
  unfold hoare_triple in H0.
  remember ((zip_state st empty_state params args)) as st''''.
  apply (H0 st'''' st'').
  assumption.
  assumption.
Qed.

Theorem hoare_alloc : forall x,
  {{ emp }} x <-# ALLOC {{ x |-> ANum 0 }}.
Proof.
  split.
  unfold safe.
  unfold not.
  intros.
  inversion H0.
  assert (not_in_add : forall (m:heap) (a e :nat),
  ~ In a (add a e m) -> False).
  admit.
  apply not_in_add in H5.
  apply H5.
  intros.
  unfold point_to_val.
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
  intros.
  split.
  unfold safe.
  unfold not.
  intros.
  inversion H0.
  assert (update_val : forall (m:heap) (a v:nat) st (x:id), 
  update st x v = empty_state -> False).
  admit.
  apply update_val in H3.
  apply H3.
  apply h.
  apply addr.
  unfold look_up_val in H.
  rewrite <- H6 in H3.
  rewrite H3 in H.
  assert (find_exsit : forall (m:heap)(a v:nat),
  find a m = Some v -> ~ In a m -> False).
  admit.
  apply find_exsit in H.
  apply H.
  apply H8.
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
  intros.
  split.
  unfold safe.
  unfold not.
  intros.
  inversion H0.
  assert (not_change_st : forall st,
  st = empty_state -> False).
  admit.
  apply not_change_st in H7.
  apply H7.
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
  intros.
  split.
  unfold safe.
  unfold not.
  intros.
  inversion H0.
  assert (remove_false : forall (m:heap) (e v : nat),
  find e (remove e h) = Some v -> False).
  admit.
  apply remove_false in H3.
  apply H3.
  apply h.
  assert (not_addr : forall (x:id)(e:nat),
  empty_state x = e -> False).
  admit.
  apply not_addr in H2.
  apply H2.
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
  assert (empty_find_in : forall (m:heap) (a:nat), find a m = None -> is_empty m = true).
  admit.
  apply empty_find_in in H4.
  assert (empty_map : forall (m:heap) (a:nat), is_empty m = true -> find a m = None).
  admit.
  apply empty_map.
  apply H4.
Qed.

(*******************
 * EXAMPLE 1       *
 *******************)

Definition body : com := 
  Y ::= APlus (AId X) (ANum 1).
  
Definition env : program :=
  fun id =>
    if eq_funid_dec F id
    then (body, [X], (APlus (AId X) (ANum 1)))
    else (CSkip, [], ANum 0)
    .

Lemma body_p : forall X Y,
  {{ (fun e st => st Y = st X + 1)[Y |-> (APlus (AId X) (ANum 1))] }}
    Y ::= APlus (AId X) (ANum 1)
  {{ (fun e st => st Y = st X + 1) }} env.
Proof.
  intros X Y.
  apply hoare_consequence_post with (Q' := fun e st => st Y = st X + 1 /\ e = None).
  eapply hoare_asgn.
  intro; intros.
  destruct H; assumption.
Qed.

(* Theorem prog_correct :
  {{fun e st => True}}
    CCall F Z [ANum 2]
  {{fun e st => st Z = 3}} env.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_call with (params := [X]) (Q := fun e st => st Y = st X + 1)
                  (body := body) (rexp := (APlus (AId X) (ANum 1)))
                  (P := fun e st => st X = 2).
  unfold env. simpl. reflexivity.
  eapply hoare_consequence_pre.
  apply hoare_consequence_post with (Q' := fun e st => st Y = st X + 1).
  eapply body_p.
  intro; intros.
  simpl.
  apply hoare_consequence_post
  	with (Q' := fun e st => st Y = 3 /\ 3 = aeval st (APlus (AId X) (ANum 1)) /\ e = None).
  apply hoare_asgn.
  intro. intros _.
  unfold assn_sub.
  simpl.
  split; try rewrite update_retrieve; reflexivity.
Qed.

( *******************
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
