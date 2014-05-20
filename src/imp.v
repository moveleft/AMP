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
  | LSD_n: forall ys, ls_disjoint nil ys
  | LSD_S: forall x xs ys, ls_disjoint xs ys ->
              not (Exists (fun x' => x = x') ys) -> 
              ls_disjoint (x::xs) ys.

Inductive list_unique_items {T : Type} : (list T) -> Prop :=
  | LUI_n: list_unique_items nil
  | LUI_S: forall xs x, Exists (fun x' => x = x') xs = False -> list_unique_items (x::xs). 

Reserved Notation "c1 '/' st ',' h '||' st' ',' h'"
                  (at level 40, st, h at level 39).

Inductive ceval : com -> program -> state -> heap -> state -> heap -> option exn -> Prop :=
  | E_Skip : forall st h,
      CSkip / st, h || st, h
  | E_Ass : forall st st' ident a n h,
      aeval st a = n ->
      update st ident n = st' ->
      CAss ident a / st, h || st', h
  | E_If_True : forall st st' ex b c1 c2 env h h',
      beval st b = true ->
      ceval c1 env st h st' h' ex ->
      ceval (CIf b c1 c2) env st h st' h' ex
  | E_If_False : forall st st' ex b c1 c2 env h h',
      beval st b = false ->
      ceval c2 env st h st' h' ex ->
      ceval (CIf b c1 c2) env st h st' h' ex
  | E_Seq : forall st st' st'' c1 c2 ex env h h' h'',
      c1 / st, h || st', h' ->
      ceval c2 env st' h' st'' h'' ex ->
      ceval (CSeq c1 c2) env st h st'' h'' ex
  | E_While_False : forall st b c h,
      beval st b = false ->
      CWhile b c / st, h || st, h
  | E_While_True : forall st st' st'' b c h h' h'',
      beval st b = true ->
      c / st, h || st', h' ->
      CWhile b c / st', h' || st'', h'' ->
      CWhile b c / st, h || st'', h''
(* Evidence for throwing and catching exceptions. *)
  | E_Throw : forall st e aexps ns env h,
      fold_right (fun a acc => cons (aeval st a) acc) nil aexps = ns ->
      ceval (CThrow e aexps) env st h st h (Some (Exn (e, ns)))
  | E_Try : forall c1 c2 st st' e ids env h h',
      ceval c1 env st h st' h' None ->
      ceval (CTry c1 e ids c2) env st h st' h' None
  | E_Catch : forall c1 c2 st st' st'' e ns ids ex env h h' h'',
      ceval c1 env st h st' h' (Some (Exn (e, ns))) ->
      ceval c2 env (update_many st ids ns) h st'' h'' ex ->
      ceval (CTry c1 e ids c2) env st h st'' h'' ex
(* Evidence for propagating exceptions out of previously declared constructions. *)
  | E_Seq_Exn : forall st st' c1 c2 ex env h h',
      ceval c1 env st h st' h' (Some ex) ->
      ceval (CSeq c1 c2) env st h st' h' (Some ex)
  | E_While_Exn : forall st st' b c ex env h h',
      beval st b = true ->
      ceval c env st h st' h' (Some ex) ->
      ceval (CWhile b c) env st h st' h' (Some ex)
  | E_Try_Exn : forall c1 c2 st st' e e' ns ids env h h',
      e <> e' ->
      ceval c1 env st h st' h' (Some (Exn (e, ns))) ->
      ceval (CTry c1 e' ids c2) env st h st' h' (Some (Exn (e, ns)))
(* Function calls *)
  | E_Call : forall st st' st'' entry_st f (env : program) body params args X ex rexp h h',
      env f = (body, params, rexp) ->
      list_unique_items params ->
      list_unique_items args ->
      length params = length args ->
      ls_disjoint params (assigned_vars body nil) ->
      entry_st = zip_state st empty_state params args -> 
      ceval body env entry_st h st'' h' ex ->
      st' = update st X (aeval st'' rexp) ->
      ceval (CCall f X args) env st h st' h' ex
(* Heap *)
  | E_Alloc : forall st x addr h env,
      ~ In addr h ->
      ceval (x <-# ALLOC) env st h (update st x addr) (add addr 0 h) None
  | E_Read : forall st x a addr v h env,
      aeval st a = addr ->
      find addr h = Some (aeval st v)->
      ceval (x <-* [ a ]) env st h (update st x (aeval st v)) h None
  | E_ReadError : forall st x a addr h env,
      aeval st a = addr ->
      ~ In addr h->
      ceval (x <-* [ a ]) env st h st h None
  | E_Write : forall st a b addr value v h env,
      aeval st a = addr ->
      aeval st b = value ->
      find addr h = Some v ->
      ceval ([ a ] <-@ b) env st h st (add addr value (remove addr h)) None
  | E_Free : forall st (h:heap) addr (v:aexp) (x:id) env,
      st x = addr ->
      find addr h = Some (aeval st v) ->
      ceval (FREE x) env st h st (remove addr h) None
  | E_FreeError : forall st (h:heap) addr (v:aexp) (x:id) env,
      st x = addr ->
      find addr h = None ->
      ceval (FREE x) env st h st h None
  where "c1 '/' st ',' h '||' st' ',' h'" := (forall env, (ceval c1 env st h st' h' None)).