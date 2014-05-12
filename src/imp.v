Require Export imp_state.

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
  
Fixpoint zip_state (steval st : state) (ids : list id) (vs : list aexp) : state :=
  match ids with
  | i::ids' => 
  	match vs with
  	| v::vs' =>
  		let st' := update st i (aeval steval v) in
  		zip_state steval st' ids' vs'
  	| [] => st
  	end
  | [] => st
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
  
Lemma zip_state_tr : forall steval st st' p q ids r s vs,
  p <> q ->
  st = zip_state steval st' (p::q::ids) (r::s::vs) ->
  st = zip_state steval st' (q::p::ids) (s::r::vs).
Proof.
  intros.
  unfold zip_state. fold zip_state.
  unfold zip_state in H1. fold zip_state in H1.
Admitted.

Inductive entry_state : state -> state -> list id -> list aexp -> Prop :=
  | ES_n: forall steval, entry_state steval empty_state nil nil
  | ES_S: forall steval st p ps v vs,
  			entry_state steval st ps vs ->
  			entry_state steval (update st p (aeval steval v)) (p::ps) (v::vs).
  
Inductive list_unique_items {T : Type} : (list T) -> Prop :=
  | LUI_n: list_unique_items []
  | LUI_S: forall xs x, Exists (fun x' => x = x') xs = False -> list_unique_items (x::xs). 

Reserved Notation "c1 ';' program '/' st '||' s '/' st'"
                  (at level 40, program, st, s at level 39).
  
Inductive ceval : com -> program -> state -> status -> state -> Prop :=
  | E_Skip : forall st program,
      CSkip ; program / st || SContinue / st
  | E_Break: forall st program,
      CBreak ; program / st || SBreak / st
  | E_Ass : forall st st' ident a n program,
      aeval st a = n ->
      update st ident n = st' ->
      CAss ident a ; program / st || SContinue / st'
  | E_If_True : forall st st' b status c1 c2 program,
      beval st b = true ->
      c1 ; program / st || status / st' ->
      CIf b c1 c2 ; program / st || status / st'
  | E_If_False : forall st st' b status c1 c2 program,
      beval st b = false ->
      c2 ; program / st || status / st' ->
      CIf b c1 c2 ; program / st || status / st'
  | E_Seq : forall st st' st'' c1 c2 status program,
      c1 ; program / st || SContinue / st' ->
      c2 ; program / st' || status / st'' ->
      CSeq c1 c2 ; program / st || status / st''
  | E_Seq_Break : forall st st' c1 c2 program,
      c1 ; program / st || SBreak / st' ->
      CSeq c1 c2 ; program / st || SBreak / st'
  | E_While_Break : forall st st' b c program,
      beval st b = true ->
      c ; program / st || SBreak / st' ->
      CWhile b c ; program / st || SContinue / st'
  | E_While_False : forall st b c program,
      beval st b = false ->
      CWhile b c ; program / st || SContinue / st
  | E_While_True : forall st st' st'' b c program,
      beval st b = true ->
      c ; program / st || SContinue / st' ->
      CWhile b c ; program / st' || SContinue / st'' ->
      CWhile b c ; program / st || SContinue / st''
  | E_Call : forall st st' st'' entry_st status f program body params args X rexp,
      program f = (body, params, rexp) ->
      list_unique_items params ->
      list_unique_items args ->
      length params = length args ->
      ls_disjoint params (assigned_vars body []) ->
      entry_st = zip_state st empty_state params args -> 
      body ; program / entry_st || status / st'' ->
      st' = update st X (aeval st'' rexp) ->
      CCall f X args ; program / st || SContinue / st'
     
  (* | E_Call : forall st st' st'' entry_st status f program body params args X rexp,
      program f = (body, params, rexp) ->
      entry_st = update empty_state params (aeval st args) -> 
      body ; program / entry_st || status / st'' ->
      st' = update st X (aeval st'' rexp) ->
      CCall f X args ; program / st || SContinue / st' *)
      
  (*| E_Call : forall st st' status f program body params args X rexp,
      program f = (body, params, rexp) ->
      body ; program / st || status / st' ->
      CCall f X args ; program / st || SContinue / st' *)
      
  (*| E_Call : forall st st' st'' ident status p program c rexp params args entry_st x,
      program p = (c, params, rexp) ->
      length params = length args ->
      entry_st = update st params args ->
      c / entry_st || status / st ->
      x = aeval st rexp ->
      st'' = update st' ident x ->
      CCall ident p args / st' || SContinue / st'' *)

  where "c1 ';' program '/' st '||' s '/' st'" := (ceval c1 program st s st').
  
(*Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1  ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros.
  generalize dependent s2.
  generalize dependent st2.
  induction H0; intros.
  Case "E_Skip". inversion H1; subst; split; reflexivity.
  Case "E_Break". inversion H1; subst; split; reflexivity.
  Case "E_Ass". inversion H2; subst; split; reflexivity.
  Case "E_If_True".
    inversion H2; subst.
    apply IHceval', H10.
    rewrite H0 in H9; inversion H9.
  Case "E_If_False".
    inversion H2; subst.
    rewrite H0 in H9; inversion H9.
    apply IHceval'; apply H10.
  Case "E_Seq".
    inversion H1; subst.
    specialize (IHceval'1 _ _ H3).
    destruct IHceval'1; subst.    
    apply IHceval'2, H7.
    specialize (IHceval'1 _ _ H6).
    destruct IHceval'1.
    congruence.
  Case "E_Seq_Break".
    inversion H1; subst.
    specialize (IHceval' _ _ H4); subst.
    destruct IHceval'.
    congruence.
    apply IHceval'.
    assumption.
  Case "E_While_Break".
    inversion H2; subst.
    specialize (IHceval' _ _ H9).
    destruct IHceval'.
    split; [ assumption | reflexivity ].
    congruence.
    specialize (IHceval' _ _ H6).
    destruct IHceval'.
    congruence.
  Case "E_While_False".
    inversion H1; subst.
    congruence.
    split; reflexivity.
    congruence.
  Case "E_While_True".
    inversion H1; subst.
    specialize (IHceval'1 _ _ H8).
    destruct IHceval'1.
    congruence.
    congruence.
    specialize (IHceval'1 _ _ H5); destruct IHceval'1; subst.
    specialize (IHceval'2 _ _ H9); assumption. 
  Case "E_Call".
    inversion H6; subst.
    specialize (IHceval' _ _ H3).
    subst.
Qed.*)