Require Export imp_state.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition F := FunId 1.
Definition G := FunId 2.
Definition H := FunId 3.

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

Fixpoint zip_state (steval st : state) (ids : list id) (vs : list aexp) : state :=
  match ids with
  | i::ids' => 
  	match vs with
  	| v::vs' =>
  		let st' := update st i (aeval steval v) in
  		zip_state steval st' ids' vs'
  	| nil => st
  	end
  | nil => st
  end.
  
Fixpoint assigned_vars (c : com) (vars : list id): list id :=
	match c with
	| CAss i _ =>
		i::vars
	| CSeq c1 c2
	| CIf _ c1 c2 =>
		let vars' := assigned_vars c1 vars in
		assigned_vars c2 vars'
	| CWhile _ c' =>
		assigned_vars c' vars
	| _ => vars
	end.
  
Inductive ls_disjoint : list id -> list id -> Prop :=
  | LSD_n: forall ys, ls_disjoint [] ys
  | LSD_S: forall x xs ys, ls_disjoint xs ys ->
              not (Exists (fun x' => x = x') ys) -> 
              ls_disjoint (x::xs) ys.

Inductive list_unique_items {T : Type} : (list T) -> Prop :=
  | LUI_n: list_unique_items []
  | LUI_S: forall xs x, Exists (fun x' => x = x') xs = False -> list_unique_items (x::xs). 

Reserved Notation "c1 '/' st '||' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> program -> state -> state -> option exn -> Prop :=
  | E_Skip : forall st,
      CSkip / st || st
  | E_Ass : forall st st' ident a n,
      aeval st a = n ->
      update st ident n = st' ->
      CAss ident a / st || st'
  | E_If_True : forall st st' ex b c1 c2 env,
      beval st b = true ->
      ceval c1 env st st' ex ->
      ceval (CIf b c1 c2) env st st' ex
  | E_If_False : forall st st' ex b c1 c2 env,
      beval st b = false ->
      ceval c2 env st st' ex ->
      ceval (CIf b c1 c2) env st st' ex
  | E_Seq : forall st st' st'' c1 c2 ex env,
      c1 / st || st' ->
      ceval c2 env st' st'' ex ->
      ceval (CSeq c1 c2) env st st'' ex
  | E_While_False : forall st b c,
      beval st b = false ->
      CWhile b c / st || st
  | E_While_True : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      CWhile b c / st' || st'' ->
      CWhile b c / st || st''
(* Evidence for throwing and catching exceptions. *)
  | E_Throw : forall st e aexps ns env,
      map (fun a => aeval st a) aexps = ns ->
      ceval (CThrow e aexps) env st st (Some (Exn (e, ns)))
  | E_Try : forall c1 c2 st st' e ids env,
      ceval c1 env st st' None ->
      ceval (CTry c1 e ids c2) env st st' None
  | E_Catch : forall c1 c2 st st' st'' e ns ids ex env,
      ceval c1 env st st' (Some (Exn (e, ns))) ->
      ceval c2 env (update_many st ids ns) st'' ex ->
      ceval (CTry c1 e ids c2) env st st'' ex
(* Evidence for propagating exceptions out of previously declared constructions. *)
  | E_Seq_Exn : forall st st' c1 c2 ex env,
      ceval c1 env st st' (Some ex) ->
      ceval (CSeq c1 c2) env st st' (Some ex)
  | E_While_Exn : forall st st' b c ex env,
      beval st b = true ->
      ceval c env st st' (Some ex) ->
      ceval (CWhile b c) env st st' (Some ex)
  | E_Try_Exn : forall c1 c2 st st' e e' ns ids env,
      e <> e' ->
      ceval c1 env st st' (Some (Exn (e, ns))) ->
      ceval (CTry c1 e' ids c2) env st st' (Some (Exn (e, ns)))
  | E_Call : forall st st' st'' entry_st f (env : program) body params args X ex rexp,
      env f = (body, params, rexp) ->
      list_unique_items params ->
      list_unique_items args ->
      length params = length args ->
      ls_disjoint params (assigned_vars body []) ->
      entry_st = zip_state st empty_state params args -> 
      ceval body env entry_st st'' ex ->
      st' = update st X (aeval st'' rexp) ->
      ceval (CCall f X args) env st st' ex
  where "c1 '/' st '||' st'" := (forall env, (ceval c1 env st st' None)).