Require Export imp_state.
Require Export imp.

Definition Assertion := program -> state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall program st, P program st -> Q program st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
  
Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall program s st st',
       c / st || s / st'  ->
       P program st  ->
       Q program st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.