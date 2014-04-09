Require Export imp_state.
Require Export Logic.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition F : id := Id 3.
Definition G : id := Id 4.
Definition H : id := Id 5.

Definition RET : id := Id 6.


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 =>
      (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  =>
      (aeval st a1) - (aeval st a2)
  | AMult a1 a2 =>
      (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   =>
      beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   =>
      ble_nat (aeval  st a1) (aeval st a2)
  | BNot b1     =>
      negb (beval st b1)
  | BAnd b1 b2  =>
      andb (beval st b1) (beval st b2)
  end.  
  
Fixpoint zip_state (st : state) (ids : list id) (vs : list nat) : state :=
  match ids with
  | i::ids' => 
  	match vs with
  	| v::vs' =>
  		let st' := update st i v in
  		zip_state st' ids' vs'
  	| [] => st
  	end
  | [] => st
  end.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).
  
Inductive ceval' : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st || SContinue / st
  | E_Break: forall st,
      CBreak / st || SBreak / st
  | E_Ass : forall st st' ident a n,
      aeval st a = n ->
      update st ident n = st' ->
      CAss ident a / st || SContinue / st'
  | E_If_True : forall st st' b status c1 c2,
      beval st b = true ->
      c1 / st || status / st' ->
      CIf b c1 c2 / st || status / st'
  | E_If_False : forall st st' b status c1 c2,
      beval st b = false ->
      c2 / st || status / st' ->
      CIf b c1 c2 / st || status / st'
  | E_Seq : forall st st' st'' c1 c2 status,
      c1 / st || SContinue / st' ->
      c2 / st' || status / st'' ->
      CSeq c1 c2 / st || status / st''
  | E_Seq_Break : forall st st' c1 c2,
      c1 / st || SBreak / st' ->
      CSeq c1 c2 / st || SBreak / st'
  | E_While_Break : forall st st' b c,
      beval st b = true ->
      c / st || SBreak / st' ->
      CWhile b c / st || SContinue / st'
  | E_While_False : forall st b c,
      beval st b = false ->
      CWhile b c / st || SContinue / st
  | E_While_True : forall st st' st'' b c,
      beval st b = true ->
      c / st || SContinue / st' ->
      CWhile b c / st' || SContinue / st'' ->
      CWhile b c / st || SContinue / st''
  | E_Call : forall st st' st'' ident status p program c rexp params args entry_st,
      program p = (c, params, rexp) ->
      length params = length args ->
      entry_st = zip_state empty_state params args ->
      c / entry_st || status / st ->
      st'' = update st' ident (aeval st rexp) ->
      CCall ident p args / st' || SContinue / st''

  where "c1 '/' st '||' s '/' st'" := (ceval' c1 st s st').