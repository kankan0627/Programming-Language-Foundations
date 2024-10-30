Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
Set Default Goal Selector "!".
Hint Constructors multi : core.

Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                                       (in custom tm at level 90, c custom tm at level 80,
                                        t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.


Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.


Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.


Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.


Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.
Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  unfold stuck.
  unfold step_normal_form.
  exists (prd tru).
  split.
  - intros contra. 
    destruct contra as [t H].
    inversion H. inversion H1. 
  - intros contra. inversion contra.
    + inversion H.
    + inversion H.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
 intros. induction H. 
 - induction H. 
   + unfold step_normal_form. intros contra.
     destruct contra as [t' H']. inversion H'.
   + unfold step_normal_form. intros contra.
     destruct contra as [t' H']. inversion H'.
 - induction H.  
   + unfold step_normal_form. intros contra.
     destruct contra as [t' H']. inversion H'.
   + unfold step_normal_form. intros contra.
     destruct contra as [t' H'].  unfold step_normal_form in IHnvalue.
     apply IHnvalue. inversion H'. exists t1'. apply H1.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
 unfold deterministic.
 intros x y1 y2 Hy1 Hy2.
 generalize dependent y2.
 induction Hy1.
 - intros. inversion Hy2.
   + reflexivity.
   + subst. inversion H3.
 - intros. inversion Hy2.
   + reflexivity.
   + subst. inversion H3.
 - intros. inversion Hy2.
   + subst. inversion Hy1.
   + subst. inversion Hy1.
   + subst. apply IHHy1 in H3. rewrite H3. reflexivity.
 - intros. inversion Hy2. subst. apply IHHy1 in H0.
   rewrite H0. reflexivity.
 - intros. inversion Hy2. 
   + reflexivity.
   + inversion H0.
 - intros. inversion Hy2. 
   + reflexivity.
   + subst. inversion H1. subst. 
     assert (value v).
    * right. apply H.
    * apply value_is_nf in H0.
      unfold step_normal_form in H0.
      assert (exists t' : tm, v --> t').
      -- exists t1'0. apply H2.
      -- apply H0 in H3. inversion H3.
 - intros. inversion Hy2. 
   + subst. inversion Hy1. 
   + subst. 
     assert (value y2).
     * right. apply H0.
     * apply value_is_nf in H.
      unfold step_normal_form in H.
      inversion Hy1. subst.
      assert (exists t' : tm, y2 --> t').
      -- exists t1'0. apply H2.
      -- apply H in H1. inversion H1.
   + subst. apply IHHy1 in H0. rewrite H0. reflexivity.
 - intros. inversion Hy2. 
   + reflexivity.
   + inversion H0.
 - intros. inversion Hy2. 
   + subst. reflexivity.
   + inversion H1. subst.
     assert (value v).
     * right. apply H.
     * apply value_is_nf in H0.
       unfold step_normal_form in H0.
       assert (exists t' : tm, v --> t').
       -- exists t1'0. apply H4.
       -- apply H0 in H2. inversion H2.
 - intros. inversion Hy2.
   + subst. inversion Hy1.
   + subst. inversion Hy1. subst. assert (value v).
    * right. apply H0.
    * apply value_is_nf in H.
      unfold step_normal_form in H.
      assert (exists t' : tm, v --> t').
      -- exists t1'0. apply H1.
      -- apply H in H2. inversion H2.
   + subst. apply IHHy1 in H0. rewrite H0. reflexivity.
Qed.

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |-- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
 apply T_If.
 - apply T_False.
 - apply T_0.
 - apply T_Succ.
   + apply T_0.
Qed.

Example has_type_not :
  ~ ( |-- <{ if false then 0 else true}> \in Bool ).
Proof.
  intros contra.
  inversion contra.
  inversion H4.
Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat ->
  |-- t \in Nat.
Proof.
  induction t.
  - intros. inversion H. inversion H1.
  - intros. inversion H. inversion H1.
  - intros. inversion H. inversion H1. apply T_If.
    + apply H5.
    + apply H7.
    + apply H8.
  - intros. apply T_0.
  - intros. inversion H. apply H1.
  - intros. inversion H. apply H1.
  - intros. inversion H. apply H1.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  induction t.
  - intros. apply bv_true.
  - intros. apply bv_false.
  - intros. destruct H0.
    + apply H0.
    + inversion H0.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. destruct H0.
    + apply H0.
    + inversion H0.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  induction t.
  - intros. inversion H.
  - intros. inversion H.
  - intros. destruct H0.
   + inversion H0.
    + apply H0.
  - intros. destruct H0.
   + inversion H0.
    + apply H0.
  - intros. destruct H0.
   + inversion H0.
    + apply H0.
  - intros. destruct H0.
   + inversion H0.
    + apply H0.
  - intros. destruct H0.
    + inversion H0.
    + apply H0.
Qed.

Theorem progress : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros. induction H.
  - left. left. apply bv_true.
  - left. left. apply bv_false.
  - destruct IHhas_type1. 
    + inversion H2. 
      * induction H3.
        -- right. exists t2. apply ST_IfTrue.
        -- right. exists t3. apply ST_IfFalse.
      * inversion H3. 
        -- subst. inversion H.
        -- subst. inversion H.
    + right. destruct H2 as [t5 H2]. exists <{ if t5 then t2 else t3 }>.
      apply ST_If. apply H2.
  - left. right. apply nv_0.
  - destruct IHhas_type.
    + inversion H0. 
      * inversion H1.
        -- subst. inversion H.
        -- subst. inversion H.
      * inversion H1.
        -- subst. left. right. apply nv_succ. apply H1.
        -- subst. left. right. apply nv_succ. apply nv_succ. apply H2.
    + right. destruct H0 as [t2 H0]. exists <{ succ t2 }>. apply ST_Succ. 
      apply H0.  
  - right. destruct IHhas_type. 
    + inversion H0. 
      * inversion H1. 
        -- subst. inversion H.
        -- subst. inversion H.
      * inversion H1. 
        -- subst. exists <{ 0 }>. apply ST_Pred0.
        -- exists t. apply ST_PredSucc. apply H2.
      + destruct H0 as [t2 H0]. exists <{ pred t2 }>.
        apply ST_Pred. apply H0.
   - right. destruct IHhas_type. 
     + inversion H0. 
       * inversion H1. 
         -- subst. inversion H.
         -- subst. inversion H.
       * inversion H1. 
         -- subst. exists <{ true }>. apply ST_Iszero0. 
         -- subst. exists <{ false }>. apply ST_IszeroSucc. apply H2.
      + destruct H0 as [t2 H0]. exists <{ iszero t2 }>.
        apply ST_Iszero. apply H0.
Qed.

Theorem preservation : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
intros. 
generalize dependent t'.
induction H.
- intros. inversion H0.
- intros. inversion H0. 
- intros.  inversion H2.
  + subst. apply H0.
  + subst. apply H1.
  + subst. apply T_If.
    * apply IHhas_type1. apply H7.
    * apply H0.
    * apply H1.
-  intros. inversion H0.
- intros. inversion H0. subst. apply T_Succ. apply IHhas_type. apply H2.
- intros. inversion H0.
  + subst. apply  T_0.
  + subst. inversion H. apply H3.
  + subst. apply T_Pred. apply IHhas_type. apply H2.
- intros. inversion H0. 
  + subst. apply T_True.
  + subst. apply T_False.
  + subst. apply T_Iszero. apply IHhas_type. apply H2.
Qed.

Theorem preservation' : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof with eauto.
  intros. generalize dependent T.
  induction H0.
  - intros. inversion H. subst. apply H5.
  - intros.  inversion H. subst. apply H6.  
  - intros. inversion H. subst. apply T_If.
    + apply IHstep in H4. apply H4.
    + apply H6.
    + apply H7.
  - intros. inversion H. apply T_Succ.
    apply IHstep. apply H2.
  - intros. inversion H. apply H1.
  - intros. inversion H0. inversion H2. apply H5.
  - intros. inversion H. apply T_Pred.  apply IHstep. apply H2.
  - intros. inversion H. apply T_True.
  - intros. inversion H0. apply T_False.
  - intros. inversion H. apply T_Iszero. apply IHstep. apply H2.
Qed.


Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros. generalize dependent T.
 induction H0.
 - intros.  inversion H. 
   + intros contra. unfold stuck in contra. destruct contra. apply H3.
     left. apply bv_true.
  + intros contra. unfold stuck in contra. destruct contra. apply H3.
     left. apply bv_false.
  + subst. intros contra.  unfold stuck in contra. destruct contra.
    apply progress in H. destruct H.
    * apply H4 in H. inversion H.
    * apply H3. apply H.
  + intros contra. unfold stuck in contra. destruct contra.
    apply H3. right. apply nv_0.
  + subst. intros contra. unfold stuck in contra. destruct contra.
    apply progress in H. destruct H.
    * apply H2. apply H. 
    * apply H1. apply H.
  + subst. intros contra. unfold stuck in contra. destruct contra.
    apply progress in H. destruct H.
    * apply H2. apply H. 
    * apply H1. apply H.
+ subst. intros contra. unfold stuck in contra. destruct contra.
    apply progress in H. destruct H.
    * apply H2. apply H. 
    * apply H1. apply H.
  - intros. subst. specialize IHmulti with T. apply IHmulti.
    apply preservation with (t':=y) in H1.
    + apply H1.
    + apply H.
Qed.

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T)
  \/
  ~ (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T).
Proof.
  right. unfold not. intros.
  assert (|-- <{ if false then 0 else true }> \in Bool).
  - eapply H. auto.
  - apply has_type_not in H0. inversion H0.
 Qed.
  
End TM.






