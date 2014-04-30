Require Export imp_state.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition T := ExId 1.
Definition U := ExId 2.
Definition V := ExId 3.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
    | ANum n        => n
    | AId x         => st x
    | APlus a1 a2   => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
    | AMult a1 a2   => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2   => ble_nat (aeval  st a1) (aeval st a2)
    | BNot b1     => negb (beval st b1)
    | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Reserved Notation "c1 '/' st '||' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> option exn -> Prop :=
  | E_Skip : forall st,
      CSkip / st || st
  | E_Ass : forall st st' ident a n,
      aeval st a = n ->
      update st ident n = st' ->
      CAss ident a / st || st'
  | E_If_True : forall st st' ex b c1 c2,
      beval st b = true ->
      ceval c1 st st' ex ->
      ceval (CIf b c1 c2) st st' ex
  | E_If_False : forall st st' ex b c1 c2,
      beval st b = false ->
      ceval c2 st st' ex ->
      ceval (CIf b c1 c2) st st' ex
  | E_Seq : forall st st' st'' c1 c2,
      c1 / st || st' ->
      c2 / st' || st'' ->
      CSeq c1 c2 / st || st''
  | E_While_False : forall st b c,
      beval st b = false ->
      CWhile b c / st || st
  | E_While_True : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      CWhile b c / st' || st'' ->
      CWhile b c / st || st''
(* Evidence for throwing and catching exceptions. *)
  | E_Throw : forall st e aexps ns,
      map (fun a => aeval st a) aexps = ns ->
      ceval (CThrow e aexps) st st (Some (Exn (e, ns)))
  | E_Try : forall c1 c2 st st' e ids,
      c1 / st || st' ->
      CTry c1 e ids c2 / st || st'
  | E_Catch : forall c1 c2 st st' st'' e ns ids,
      ceval c1 st st' (Some (Exn (e, ns))) ->
      c2 / update_many st ids ns || st'' ->
      CTry c1 e ids c2 / st || st''
(* Evidence for propagating exceptions out of previously declared constructions. *)
  | E_Seq1_Exn : forall st st' c1 c2 ex,
      ceval c1 st st' (Some ex) ->
      ceval (CSeq c1 c2) st st' (Some ex)
  | E_Seq2_Exn : forall st st' st'' c1 c2 ex,
      c1 / st || st' ->
      ceval c2 st' st'' (Some ex) ->
      ceval (CSeq c1 c2) st st'' (Some ex)
  | E_While_Exn : forall st st' b c ex,
      beval st b = true ->
      ceval c st st' (Some ex) ->
      ceval (CWhile b c) st st' (Some ex)
  | E_Try_Exn : forall c1 c2 st st' e e' ns ids,
      e <> e' ->
      ceval c1 st st' (Some (Exn (e, ns))) ->
      ceval (CTry c1 e' ids c2) st st' (Some (Exn (e, ns)))
  | E_Catch_Exn : forall c1 c2 st st' st'' e ns ids ex,
      ceval c1 st st' (Some (Exn (e, ns))) ->
      ceval c2 (update_many st ids ns) st'' (Some ex) ->
      ceval (CTry c1 e ids c2) st st'' (Some ex)
  where "c1 '/' st '||' st'" := (ceval c1 st st' None).