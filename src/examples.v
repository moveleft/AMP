Require Export Hoare.

(*******************
 * EXAMPLE 1       *
 *******************)

Definition body : com := 
  Y ::= APlus (AId X) (ANum 1).

Definition env : program :=
  fun id =>
    if eq_funid_dec F id
    then (body, cons X nil, (APlus (AId X) (ANum 1)))
    else (CSkip, nil, ANum 0)
    .

Lemma body_p : forall X Y,
  {{ assn_sub Y ((APlus (AId X) (ANum 1))) (fun e st h => st Y = st X + 1) }}
    Y ::= APlus (AId X) (ANum 1)
  {{ (fun e st h => st Y = st X + 1) }} env.
Proof.
  intros X Y.
  apply hoare_consequence_post with (Q' := fun e st h => st Y = st X + 1 /\ e = None).
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