Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.
Set Default Goal Selector "!".
Definition FILL_IN_HERE := <{True}>.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1.
  apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
   apply ST_Plus2.
   apply ST_Plus2.
   apply ST_PlusConstConst.
Qed.

End SimpleArith1.

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2; subst.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_Plus2 *)
      inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
  inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
 induction Hy1; intros y2 Hy2;
  inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    inversion H1. subst. inversion Hy1.
   - inversion H. subst. inversion H3.
   - apply IHHy1 in H4. rewrite H4. reflexivity.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. apply  v_const.
  - right.
    destruct IHt1.
    + inversion H. destruct IHt2.
       * inversion H1. 
        exists (C (n + n0)).
        apply ST_PlusConstConst. 
      * destruct H1 as [t2' H12].
        exists (P (C n) t2').
        apply ST_Plus2.
        ** rewrite H0. apply H.
        ** apply H12.
    + destruct H as [t1' H11]. 
       exists (P t1' t2). apply ST_Plus1.
       apply H11.
Qed.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.  
  intros.
  unfold normal_form.
  intros contra.
  destruct contra as [v' Hcon].
  inversion H. subst.
  inversion Hcon.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  induction t.
  - intros.  apply v_const.
  - intros. specialize strong_progress with (P t1 t2).
    intros. destruct H0.
    + apply H0.
    + unfold normal_form in H. apply H in H0. inversion H0.
 Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
 split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.


Module Temp1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n,
                value (P t1 (C n)). (* <--- *)


Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  where " t '-->' t' " := (step t t').


Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  assert (forall n1 n2, value (P (C n1) (C n2)) /\ ~ normal_form step (P (C n1) (C n2))).
  - intros.  split.
    + apply v_funny.
    + intros contra. unfold normal_form in contra. 
      apply contra. exists (C (n1 + n2)). apply ST_PlusConstConst.
   - specialize H with 1 2.
     exists (P (C 1) (C 2)).
    apply H. 
Qed.


End Temp1.


Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n). (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
 assert (value (C 1) /\ ~ normal_form step (C 1)).
  - intros.  split.
    + apply v_const.
    + unfold not. intros contra. unfold normal_form in contra. 
      apply contra. exists (P (C 1) (C 0)). apply ST_Funny.
  - exists (C 1).
    apply H.
Qed. 

End Temp2.


Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
where " t '-->' t' " := (step t t').


Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
 exists (P (C 0) (P (C 0) (C 1))).
  split. 
  - unfold not. intros. inversion H.
  - unfold normal_form; unfold not; intros.
  destruct H. inversion H. subst.
  inversion H3.
Qed.

End Temp3.

Module Temp4.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.


Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').


Lemma bool_step_prop3 :
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.
Proof.
  apply ST_If.
  apply ST_IfTrue.
Qed.

Theorem strong_progress_bool : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. apply v_tru.
  - left. apply v_fls.
  - right. destruct IHt1.
    + inversion H.
      * exists t2.
        apply ST_IfTrue.
      * exists t3.
        apply ST_IfFalse.
    + destruct H as [t1' Ht1].
      exists (test t1' t2 t3).
      apply ST_If.
      apply Ht1.
Qed.

Theorem step_deterministic : deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2. 
  generalize dependent y2.
 induction Hy1; intros y2 Hy2;
  inversion Hy2; subst; try solve_by_invert.
  - reflexivity.
  - reflexivity.
  - specialize IHHy1 with t1'0.
    apply IHHy1 in H3.
    rewrite H3.
    reflexivity.
Qed.

Module Temp5.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  | ST_ShortCircuit : forall t1 t,  
      test t1 t t --> t
  where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
         fls.


Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  apply ST_ShortCircuit.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof. 
  induction t.
  - left. apply v_tru.
  - left. apply v_fls.
  - right. destruct IHt1.
    + inversion H.
      * exists t2.
        apply ST_IfTrue.
      * exists t3.
        apply ST_IfFalse.
    + destruct H as [t1' Ht1].
      exists (test t1' t2 t3).
      apply ST_If.
      apply Ht1.
Qed.
End Temp5.
End Temp4.


Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
 intros.
 eapply multi_step.
 - apply H.
 - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros.
   induction H.
  - apply H0.
  - eapply multi_step.
    + apply H.
    + apply IHmulti. apply H0.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step.
  - eapply ST_Plus1.
    eapply ST_PlusConstConst.
  - eapply multi_step.
    + eapply ST_Plus2.  
      * simpl. apply v_const.
      * apply ST_PlusConstConst.
    + eapply multi_step. 
      * simpl. apply ST_PlusConstConst.
      * simpl. apply multi_refl.   
Qed. 

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  apply multi_refl.
Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
   apply multi_refl.
Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
eapply multi_step.
- eapply ST_Plus2.
  + apply v_const.
  + eapply ST_Plus2.
    * apply v_const.
    * apply ST_PlusConstConst.
-  eapply multi_step.
    + eapply ST_Plus2.  
      * apply v_const.
      * simpl.  apply ST_PlusConstConst.
    + simpl.  apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').


Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic.  unfold normal_form_of. 
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11; intros; unfold step_normal_form in *;
  unfold normal_form in *.
  - inversion P21.
    + reflexivity.
    + subst. exfalso. apply P12. exists y; assumption.
  - induction P21.
    + exfalso. apply P22. exists y; assumption.
    + assert (y0 = y).
      * eapply step_deterministic. 
        ** apply H0. 
        ** apply H. 
      * apply IHP11.
        ** apply P12.
        ** subst. apply P21.
        ** apply P22.
Qed.
 
Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'. 

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros.
 generalize dependent t2.
  induction H. 
  - intros. apply multi_refl.
  - intros. eapply multi_step.
    + eapply ST_Plus1.
      apply H.
    +  apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
 intros.
 generalize dependent v1.
 induction H0. 
  - intros. apply multi_refl.
  - intros. eapply multi_step.
    + eapply ST_Plus2.
      * apply H1.
      * apply H.
    + apply IHmulti.
      apply H1.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - exists (C n).
    split.
    + apply multi_refl.
    + apply nf_same_as_value.
      apply v_const.
  - destruct IHt1 as [t1' IHt1].
      destruct IHt1 as [IH11 IH12].
      destruct IHt2 as [t2' IHt2].
      destruct IHt2 as [IH21 IH22].
apply nf_same_as_value in IH12. inversion IH12.
apply nf_same_as_value in IH22. inversion IH22.
subst. exists (C (n + n0)).
   split.
  + eapply multi_trans.
    * apply multistep_congr_1.
      apply IH11.
    * eapply multi_trans.
      ** apply multistep_congr_2.
         *** apply IH12.
         *** apply IH21.
      ** apply multi_R.
         apply ST_PlusConstConst.
   + apply nf_same_as_value.
     apply v_const.
Qed.

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
Proof.
  intros. induction H.
  - apply multi_refl.
  - eapply multi_trans.
    + apply multistep_congr_1.
      apply IHeval1.
    + eapply multi_trans.
      * apply multistep_congr_2.
         ** apply v_const.
         ** apply IHeval2.
    * apply multi_R.
         apply ST_PlusConstConst.
Qed.
 
Locate eval.

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs.
  - intros. inversion H.
    + apply E_Plus.
      * apply E_Const.
 * apply E_Const.
   - intros. inversion H. subst. apply E_Plus.
     + apply IHHs. apply H2.
     + apply H4.
   - intros. inversion H0. subst. apply E_Plus.
     + apply H3.
     + apply IHHs. apply H5.
Qed.
 
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  intros.
  unfold normal_form_of in H.
  destruct H as [H1 H2].
  unfold step_normal_form in H2.
  apply nf_same_as_value in H2.
 inversion H2. exists n. split.
   - reflexivity.
   - induction H1. 
      + subst. apply E_Const.
      + subst. apply step__eval with (t':=y).
        * apply H0.
        * apply IHmulti.
           ** apply H2.
         ** reflexivity.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  
   induction t.
  - intros. split.
    + intros. simpl in H. rewrite H. apply E_Const.
    + intros. inversion H. simpl. reflexivity.
  - intros. split.
    + intros. simpl in H. rewrite <- H.
      apply E_Plus.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + intros. inversion H. subst. simpl.
      apply IHt1 in H2.  apply IHt2 in H4.
      rewrite H2.  rewrite H4. reflexivity.
Qed.
  

Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

Theorem combined_step_deterministic: (deterministic step) \/ ~ (deterministic step).
Proof.
  left.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
  inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    inversion H1. 
    + subst. inversion Hy1.
    + subst. inversion Hy1.
    + subst. inversion Hy1.
  - inversion H.
    + subst. inversion H3.
    + subst. inversion H3.
    + subst. inversion H3.
  - apply IHHy1 in H4. rewrite H4. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHHy1 in H3. rewrite H3. reflexivity.
Qed.

Theorem combined_strong_progress :
  (forall t, value t \/ (exists t', t --> t'))
  \/ ~ (forall t, value t \/ (exists t', t --> t')).
Proof.
  right.
  intros contra.
  assert (~ (value (P (C 1) tru) \/ (exists t' : tm, (P (C 1) tru) --> t'))).
  - intros Hcon.
    destruct Hcon.
    + inversion H.
    + destruct H as [s H].
      inversion H.
      * inversion H3.
      * subst. inversion H4.
   - apply H. apply contra.
Qed.

End Combined.


Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).


Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW: c1||c2 *)

Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).


Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.


Example par_loop_example_0:
  exists st',
      par_loop / empty_st  -->* <{skip}> / st'  /\  st' X = 0.
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step.  
    + apply CS_Par1. apply CS_Asgn.
    + eapply multi_step.
      * apply CS_Par2. apply CS_While.
      * eapply multi_step.
        ** apply CS_Par2. apply CS_IfStep.
           apply BS_Eq1. apply AS_Id.
        ** eapply multi_step.
           *** apply CS_Par2. apply CS_IfStep.
              apply BS_Eq.
           *** simpl. eapply multi_step.
               **** apply CS_Par2. apply CS_IfFalse.
               **** eapply multi_step.
                    ***** apply CS_ParDone.
                    ***** eapply multi_refl.
  - reflexivity.
Qed.

  
Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st' /\ st' X = 2.
Proof.
  unfold par_loop.
  eexists. split.
  - eapply multi_step. 
    + apply CS_Par2. apply CS_While.
    + eapply multi_step.
      * apply CS_Par2. apply CS_IfStep.
        apply BS_Eq1. apply AS_Id.
      * eapply multi_step.
        -- apply CS_Par2. apply CS_IfStep.
           apply BS_Eq.
        -- simpl. eapply multi_step.
           ++ apply CS_Par2. apply CS_IfTrue.
           ++ eapply multi_step.
              ** apply CS_Par2. apply CS_SeqStep.
                 apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
              ** eapply multi_step.
                 --- apply CS_Par2. apply CS_SeqStep.
                     apply CS_AsgnStep. apply AS_Plus.
                 --- eapply multi_step.
                     +++ apply CS_Par2. apply CS_SeqStep.
                         apply CS_Asgn.
                     +++ eapply multi_step.
                         *** apply CS_Par2. apply CS_SeqFinish.
                         *** eapply multi_step.
                             ---- apply CS_Par2. apply CS_While.
                             ---- eapply multi_step.
                                  ++++ apply CS_Par2. apply CS_IfStep.
                                       apply BS_Eq1. apply AS_Id.
                                  ++++ eapply multi_step.
                                       **** apply CS_Par2. apply CS_IfStep.
                                            apply BS_Eq.
                                       **** simpl.
                                            eapply multi_step.
                                            ----- apply CS_Par2. apply CS_IfTrue.
                                            ----- eapply multi_step.
                                                  +++++ apply CS_Par2. apply CS_SeqStep.
                                                        apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
                                                  +++++ eapply multi_step.
                                                        ***** apply CS_Par2. apply CS_SeqStep.
                                                              apply CS_AsgnStep. apply AS_Plus.
                                                        ***** eapply multi_step.
                                                              ------ apply CS_Par2. apply CS_SeqStep.
                                                                     apply CS_Asgn.
                                                              ------ eapply multi_step.
                                                                     ++++++ apply CS_Par1. apply CS_Asgn.
                                                                     ++++++ eapply multi_step.
                                                                            ****** apply CS_Par2. apply CS_SeqFinish.
                                                                            ****** eapply multi_step.
                                                                                   ------- apply CS_Par2. apply CS_While.
                                                                                   ------- eapply multi_step.
                                                                                           +++++++ apply CS_Par2. apply CS_IfStep.
                                                                                                   apply BS_Eq1. apply AS_Id.
                                                                                           +++++++ eapply multi_step.
                                                                                                   ******* apply CS_Par2. apply CS_IfStep.
                                                                                                           apply BS_Eq.
                                                                                                   ******* simpl. eapply multi_step.
                                                                                                           -------- apply CS_Par2. apply CS_IfFalse.
                                                                                                           -------- eapply multi_step.
                                                                                                                    ++++++++ apply CS_ParDone.
                                                                                                                    ++++++++ eapply multi_refl.
  - reflexivity. Qed.

Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  intros. destruct H.
  eapply multi_step. 
  - apply CS_Par2. apply CS_While.
  - eapply multi_step.
    + apply CS_Par2. apply CS_IfStep.
      apply BS_Eq1. apply AS_Id.
    + eapply multi_step.
      * apply CS_Par2. apply CS_IfStep. apply BS_Eq. 
      * rewrite H0. simpl.
        -- eapply multi_step.
           ++ apply CS_Par2. apply CS_IfTrue.
           ++ eapply multi_step.
               ** apply CS_Par2. apply CS_SeqStep.
                  apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
               ** eapply multi_step.
                  --- apply CS_Par2. apply CS_SeqStep.
                      rewrite H. apply CS_AsgnStep. apply AS_Plus.
                  --- eapply multi_step.
                      +++ apply CS_Par2. apply CS_SeqStep. apply CS_Asgn.
                      +++ eapply multi_step.
                          *** apply CS_Par2. apply CS_SeqFinish.
                          *** assert (n + 1 = S n) by lia. rewrite H1. apply multi_refl.
Qed.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st', par_loop / st -->* par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros n. induction n; intros.
  - exists st. split.
    + constructor.
    + assumption.
  - apply IHn in H. destruct H. destruct H. exists (X !-> S n ; x). split. 
    + eapply multi_trans.
      * apply H.
      * apply par_body_n__Sn.
        -- assumption.
    + split.
      * rewrite t_update_eq. reflexivity.
      * rewrite t_update_neq.
        -- destruct H0. assumption.
        -- unfold not. intros. inversion H1.
Qed.
                

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->* <{skip}> / st' 
    /\ st' X = n.
Proof.
intros n.
destruct (par_body_n n empty_st).
- split. 
  + reflexivity.
  + reflexivity.
- rename x into st.
  inversion H as [H' [HX HY]]. clear H.
  exists (Y !-> 1; st).  split.
  + eapply multi_trans with (par_loop,st). 
    * apply H'.
    * eapply multi_step.
      -- apply CS_Par1. apply CS_Asgn.
      -- eapply multi_step.
         ++ apply CS_Par2. apply CS_While.
         ++ eapply multi_step.
            ** apply CS_Par2. apply CS_IfStep.
               apply BS_Eq1. apply AS_Id.
            ** rewrite t_update_eq. eapply multi_step.
               --- apply CS_Par2. apply CS_IfStep. apply BS_Eq.
               --- simpl. eapply multi_step.
                   +++ apply CS_Par2. apply CS_IfFalse.
                   +++ eapply multi_step.
                       *** apply CS_ParDone.
                       *** apply multi_refl.
  + rewrite t_update_neq.
    * assumption.
    * intro X; inversion X.                                 
Qed.
    
End CImp.    
     
Definition stack := list nat.
Definition prog := list sinstr.

Inductive stack_step (st : state) : prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load : forall stk i p,
    stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_Plus : forall stk n m p,
    stack_step st (SPlus :: p, n::m::stk) (p, (m+n)::stk)
  | SS_Minus : forall stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : forall stk n m p,
    stack_step st (SMult :: p, n::m::stk) (p, (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros; inversion H0; reflexivity.
Qed.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 6; fail) | simpl]);
  apply multi_refl.

Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  eexists. split.
  - eapply multi_step.
   + apply ST_Plus2. 
     * apply v_const.
     * apply ST_PlusConstConst.
    + simpl. apply multi_R. apply ST_PlusConstConst.
   - simpl.  apply v_const.
Qed.
  
Theorem normalize_ex' :  exists e',
  (P (C 3) (P (C 2) (C 1)))
  -->* e' /\ value e'.
Proof.
  eexists. split.
  - apply multi_step with (P (C 3) (C 3)).
    + apply ST_Plus2. 
      * apply v_const.
      * apply ST_PlusConstConst.
    + apply multi_step with (C 6).
      * apply ST_PlusConstConst.
      * apply multi_refl. 
   - apply v_const. 
Qed.









