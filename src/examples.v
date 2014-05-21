Require Export Hoare.
Require Import FunctionalExtensionality.

(*******************
 * EXAMPLE 1       *
 *******************)
Definition body := Z ::= APlus (AId X) (AId Y).

Definition env : program :=
  fun id =>
    if eq_funid_dec F id
    then Some(body, cons X (cons Y nil), AId Z)
    else None
    .
    
Theorem prog_correct :
  {{fun e st h => True}}
    CCall F X (cons (ANum 1) (cons (ANum 2) nil))
  {{fun e st h => st X = 3}} env.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_call with (params := cons X (cons Y nil)) (Q := fun e st h => st Z = st X + st Y)
                  (body := body) (rexp := AId Z)
                  (P := fun e st h => st X = 1 /\ st Y = 2).
  unfold env; reflexivity.
  unfold body.
  remember (fun (ex : option exn) st (h : heap) => st Z = st X + st Y /\ st X = 1 /\ st Y = 2) as Q.
  eapply hoare_consequence_pre with (P' := assn_sub Z (APlus (AId X) (AId Y)) Q).
  eapply hoare_consequence_post with (Q' := fun ex st h => Q ex st h /\ ex = None).
  apply hoare_asgn.
  intro. intros.
  rewrite HeqQ in H.
  destruct H; destruct H; destruct H1.
  split; try assumption.
  rewrite H1 in H. rewrite H2 in H.
  unfold aeval.
  rewrite H. reflexivity.
  
  intro. intros.
  unfold assn_sub. simpl.
  assert (update st Z (st X + st Y) X = st X).
  apply update_retrieve_dif; unfold Z, X; intro; congruence.
  assert (update st Z (st X + st Y) Y = st Y).
  apply update_retrieve_dif; unfold Z, Y; intro; congruence.
  assert (update st Z (st X + st Y) Z = st X + st Y).
  apply update_retrieve.
  rewrite HeqQ, H0, H1, H2.
  destruct H.
  split; try reflexivity; split; assumption.
  
  intro. intros.
  unfold zip_state; simpl.
  split.
  apply update_retrieve_dif; unfold Y,X; intro. congruence.
  apply update_retrieve.
Qed.

(* Complex example *)
(* Body of the function F *)
Definition cx_body :=
Y ::= AId X;;
TRY
  Y ::= ANum 4;;
  THROW T, cons (AMinus (ANum 21) (AId Y)) nil;;
  THROW U, nil
CATCH T, cons Z nil DO
  X ::= APlus (AId Y) (AId Z)
END
.

(* The environment, containing a single function F witch
   takes a parameter and has the body defined above.
   The return value is the value of X, in the scope of the 
   body after its execution *)
Definition cx_env :=
fun id =>
    if eq_funid_dec F id
    then Some(cx_body, cons X nil, AId X)
    else None
.

(* The program entry point *)
Theorem cx_prog_correct :
{{ fun _ _ _ => True }}
X ::= ANum 5;;
CCall F X (cons (AId X) nil)
{{ fun _ st _ => st X = 22 }} cx_env
.
Proof.
  apply hoare_seq with (Q := fun _ st _ => st X = 5).
  eapply hoare_consequence_pre.
  apply hoare_call with (params := cons X nil) (Q := fun e st h => st X = 22)
                    (body := cx_body) (rexp := AId X)
                    (P := fun e st h => st X = 5).
  reflexivity.
  unfold cx_body.
  Case "Sequence".
    eapply hoare_seq with (Q := fun _ st _ => st Y = 5).
    SCase "Try".
      eapply hoare_try_exn with (ns := cons 17 nil).
      SSCase "Catch".
        apply hoare_consequence_post with (fun ex st h => (st X = 22 /\ st Z = 17) /\ ex = None).
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        intro; intros.
        unfold assn_sub, aeval, update.
        inversion H; inversion H0.
        unfold eq_id_dec, update_many in *; simpl in *.
        assert(update x Z 17 Y = x Y).
          apply update_retrieve_dif; unfold not, Y, Z; intro; congruence.
        rewrite H2, H3, H1, update_retrieve.
        split; reflexivity.
        intro; intros.
        destruct H; destruct H.
        simpl; rewrite H; split; reflexivity.
      apply hoare_seq with (Q := fun _ st _ => st Y = 4).
      apply hoare_seq_exn.
      eapply hoare_consequence_post.
      apply hoare_throw.
      intro; intros.
      inversion H. split.
      rewrite H1.
      unfold fold_right, aeval; rewrite H0; reflexivity.
      unfold not; intro; congruence.
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intro; intros.
      unfold assn_sub; rewrite update_retrieve; reflexivity.
    apply hoare_consequence_post with (Q' := fun ex st _ => (st Y = 5 /\ st X = 5) /\ ex = None).
    eapply hoare_consequence_pre.
    apply hoare_asgn.  
    intro; intros.
    unfold assn_sub.
    assert(update st Y (aeval st (AId X)) Y = st X).
      apply update_retrieve.
    assert(update st Y (aeval st (AId X)) X = st X).
      apply update_retrieve_dif; unfold not, X, Y; intro; congruence.
    split; assumption.
    intro; intros.
    destruct H; destruct H.
    split; assumption.
    intro; intros.
    unfold zip_state.
    rewrite update_retrieve; simpl; rewrite H; reflexivity.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intro;intros.
    unfold assn_sub; rewrite update_retrieve; reflexivity.
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

(**********************
 * EXCEPTION EXAMPLES *
 **********************)

Definition example1 : com :=
	(* { True } -> *)
	(* { 3 = 3 } *)
  X ::= ANum 3;;
	(* { X = 3 } *)
  TRY
	(* { X = 3 } -> *)
	(* { 4 = 4 } *)
    X ::= ANum 4;;
	(* { X = 4 } *)
    THROW T, cons (AMinus (ANum 21) (AId X)) nil;; (* Demonstrating the hoare_seq rule. *)
	(* { fun ex st h => ex = Some (Exn (T, [17])) } *)
    THROW U, nil (* Demonstrating the hoare_seq_exn rule. *)
	(* { fun ex st h => ex = Some (Exn (T, [17])) } *)
  CATCH T, cons Y nil DO (* Demonstrating the hoare_try_exn rule. *)
	(* { fun ex st h => exists st', st' X = 3 /\ st = st'[Y |-> 17]} -> *)
	(* { X = 3 /\ Y = 17 } -> *)
	(* { X + Y = 20 /\ Y = 17 } *)
    X ::= APlus (AId X) (AId Y)
	(* {X = 20 /\ Y = 17} *)
  END.
	(* {X = 20 /\ Y = 17} *)

Definition example2 : com :=
  X ::= ANum 2;;
  TRY
    X ::= ANum 18
  CATCH T, cons Y nil DO (* Demonstrating the hoare_try rule. *)
    X ::= AId Y
  END. (* {X = 18} *)

Definition example3 : com :=
  X ::= ANum 2;;
  TRY
    X ::= ANum 18;;
    THROW T, cons (ANum 4) (cons (ANum 3) nil)
  CATCH U, cons Y (cons Z nil) DO (* Demonstrating the hoare_try rule with propagated exception. *)
    X ::= APlus (AId Y) (AId Z)
  END. (* {X = 2 /\ ex = Some (Exn (T, [4; 3]))} *)

Theorem example1_correct :
  {{fun ex st h => True}}
    example1
  {{fun ex st h => st X = 20 /\ st Y = 17}} env.
Proof.
  unfold example1.
  eapply hoare_consequence_pre.
  apply hoare_seq with (Q:=fun ex st h => st X = 3).
  apply hoare_try_exn with (ns:=cons 17 nil).
  apply hoare_consequence_post with (fun ex st h => (st X = 20 /\ st Y = 17) /\ ex = None).
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros ex st h P.
  unfold assn_sub. unfold aeval. unfold update.
  inversion P. inversion H. clear H. split.
  destruct (eq_id_dec X X).
    rewrite H1. unfold update_many. simpl. unfold update.
    destruct (eq_id_dec Y X). destruct (eq_id_dec Y Y).
    inversion e0. congruence.
    destruct (eq_id_dec Y Y). rewrite H0. reflexivity.
    congruence. congruence.
  destruct (eq_id_dec X Y).
    rewrite H1. unfold update_many. simpl. unfold update.
    destruct (eq_id_dec Y X). destruct (eq_id_dec Y Y).
    inversion e0. congruence.
    destruct (eq_id_dec Y Y); congruence.
    rewrite H1. unfold update_many. simpl. unfold update.
    destruct (eq_id_dec Y Y). reflexivity. congruence.
  intros ex st h P. omega.
  apply hoare_seq with (fun ex st h => st X = 4).
  apply hoare_seq_exn.
  eapply hoare_consequence_post. apply hoare_throw.
  intros ex st h P.
  inversion P. clear P.
  unfold fold_right in H0. unfold aeval in H0. rewrite H in H0.
  split. assumption. congruence.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros ex st h P.
  unfold assn_sub. unfold aeval. reflexivity.
  apply hoare_asgn.
  intros ex st h P. unfold assn_sub. reflexivity.
Qed.