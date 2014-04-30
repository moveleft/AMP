Require Export Hoare.

Definition example1 : com :=
  X ::= ANum 3;;
  TRY
    X ::= ANum 4;;
    THROW T, [AMinus (ANum 21) (AId X)];; (* Demonstrating the hoare_seq rule. *)
    THROW U, [] (* Demonstrating the hoare_seq_exn rule. *)
  CATCH T, [Y] DO (* Demonstrating the hoare_try_exn rule. *)
    X ::= APlus (AId X) (AId Y)
  END. (* {X = 20 /\ Y = 17} *)

Definition example2 : com :=
  X ::= ANum 2;;
  TRY
    X ::= ANum 18
  CATCH T, [Y] DO (* Demonstrating the hoare_try rule. *)
    X ::= AId Y
  END. (* {X = 18} *)

Definition example3 : com :=
  X ::= ANum 2;;
  TRY
    X ::= ANum 18;;
    THROW T, [ANum 4; ANum 3]
  CATCH U, [Y; Z] DO (* Demonstrating the hoare_try rule with propagated exception. *)
    X ::= APlus (AId Y) (AId Z)
  END. (* {X = 2 /\ ex = Some (Exn (T, [4; 3]))} *)

Theorem example1_correct :
  {{fun ex st => True}}
    example1
  {{fun ex st => st X = 20 /\ st Y = 17}}.
Proof.
  unfold example1.
  eapply hoare_consequence_pre.
  apply hoare_seq with (Q:=fun ex st => st X = 3).
  apply hoare_try_exn with (ns:=[17]).
  apply hoare_consequence_post with (fun ex st => (st X = 20 /\ st Y = 17) /\ ex = None).
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros ex st P.
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
  intros ex st P. omega.
  apply hoare_seq with (fun ex st => st X = 4).
  apply hoare_seq_exn.
  eapply hoare_consequence_post. apply hoare_throw.
  intros ex st P.
  inversion P. clear P.
  unfold map in H0. unfold aeval in H0. rewrite H in H0.
  split. assumption. congruence.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros ex st P.
  unfold assn_sub. unfold aeval. reflexivity.
  apply hoare_asgn.
  intros ex st P. unfold assn_sub. reflexivity.
Qed.