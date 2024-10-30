Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
Set Default Goal Selector "!".

Module STLC.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.


Notation idB :=
  <{\x:Bool, x}>.

Notation idBB :=
  <{\x:Bool -> Bool, x}>.

Notation idBBBB :=
  <{\x:((Bool -> Bool) -> (Bool -> Bool)), x}>.

Notation k := <{\x:Bool, \y:Bool, x}>.

Notation notB := <{\x:Bool, if x then false else true}>.


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.


Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Inductive substi (s:tm) (x:string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 : forall y,
        x <> y ->
        substi s x (tm_var y) (tm_var y)
  | s_abs1 : forall m T,
        substi s x (tm_abs x T m) (tm_abs x T m)
  | s_abs2 : forall m m' T y,
        x <> y ->
        substi s x m m' ->
        substi s x (tm_abs y T m) (tm_abs y T m')
  | s_app : forall t1 t2 t1' t2',
        substi s x t1 t1' ->
        substi s x t2 t2' ->
        substi s x (tm_app t1 t2) (tm_app t1' t2')
  | s_true :
      substi s x tm_true tm_true
  | s_false :
      substi s x tm_false tm_false
  | s_if : forall t1 t2 t3 t1' t2' t3',
        substi s x t1 t1' ->
        substi s x t2 t2' ->
        substi s x t3 t3' ->
        substi s x (tm_if t1 t2 t3) (tm_if t1' t2' t3').

Hint Constructors substi : core.

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  intros.
  generalize dependent t'.
  induction t.
  - intros. split.
    + intros. simpl in H.
      destruct ((x0 =? s0)%string) eqn:Heq.
      * subst. apply  eqb_eq in Heq.
        subst. apply s_var1.
      * apply eqb_neq in Heq. subst.
        apply s_var2. apply Heq.
    + intros. inversion H.
      * subst. simpl. 
        assert ((s0 =? s0)%string = true).
        -- apply eqb_eq. reflexivity.
        -- rewrite H0. reflexivity.
      * subst. simpl. 
        assert ((x0 =? s0)%string = false).
        -- apply eqb_neq. apply H1.
        -- rewrite H0. reflexivity.
  - split.
    + intros. induction H.  simpl.
      apply s_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + intros. inversion H. subst.
      simpl. apply IHt1 in H2. apply IHt2 in H4.
      rewrite H2. rewrite H4. reflexivity.
  - intros. split.
    + intros. simpl in H.
      destruct ((x0 =? s0)%string) eqn:Heq.
      * rewrite H. apply eqb_eq in Heq. 
        subst.  simpl. apply s_abs1.
      * apply eqb_neq in Heq. subst. apply s_abs2.
        -- apply Heq.
        -- apply IHt. reflexivity.
    + intros. inversion H.
      * subst. simpl.
        assert ((s0 =? s0)%string = true).
        -- apply eqb_eq. reflexivity.
        -- rewrite H0. reflexivity.
      * subst. simpl.
        assert ((x0 =? s0)%string = false).
        -- apply eqb_neq. apply H4.
        -- rewrite H0. apply IHt in H5. rewrite H5.
           reflexivity.
  - intros. split.
    + intros. inversion H. simpl. apply s_true.
    + intros. inversion H. simpl. reflexivity.
  - intros. split.
    + intros. inversion H. simpl. apply s_false.
    + intros. inversion H. simpl. reflexivity.
  - intros. split.
    + intros. inversion H. simpl. apply s_if.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
      * apply IHt3. reflexivity.
    + intros. inversion H. subst. simpl. apply IHt1 in H3.
      apply IHt2 in H5. apply IHt3 in H6. subst. reflexivity.
Qed.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{[x:=v2]t1}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
  - apply ST_AppAbs.
    apply v_abs.
  - simpl. apply multi_refl.
Qed.

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  apply multi_trans with <{idBB idB}>.
  - eapply multi_step.
    + apply ST_App2.
      * apply v_abs.
      * apply ST_AppAbs.
        -- apply v_abs.
    + simpl. apply multi_refl.
  - apply step_example1.
Qed.

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
   eapply multi_trans. 
   - eapply multi_step.
     + apply ST_App1.
       apply ST_AppAbs. apply v_abs.
     + simpl. apply multi_R.  apply ST_AppAbs.
       apply v_true.
   - simpl. apply multi_R. apply ST_IfTrue.  
Qed.

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_step.
  - apply ST_App2.
    + apply v_abs.
    + apply ST_AppAbs. apply v_true.
  - simpl. eapply multi_step.
    + apply ST_App2.
      * apply v_abs.
      * apply ST_IfTrue.
    + eapply multi_step.
      * apply ST_AppAbs. apply v_false.
      * simpl. apply multi_refl.
Qed.

Lemma step_example5 :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  eapply multi_trans. 
   - eapply multi_step.
     + apply ST_App1. apply ST_AppAbs. apply v_abs.
     + simpl. apply step_example1.
   - apply multi_refl.
Qed.
       
Lemma step_example5_with_normalize :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  normalize.
Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma, 
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Example typing_example_1 :
  empty |-- \x:Bool, x \in (Bool -> Bool).
Proof. apply T_Abs.  
      apply T_Var. apply update_eq. Qed.

Example typing_example_2_full :
  empty |--
    \x:Bool,
       \y:Bool -> Bool,
          (y (y x)) \in
    (Bool -> (Bool -> Bool) -> Bool).
Proof.
  apply T_Abs. apply T_Abs. eapply T_App.
  - apply T_Var. 
    + apply update_eq .
  - eapply T_App.
    + apply T_Var. 
      apply update_eq .
    + apply T_Var. 
      assert (y <> x).
      * intros contra. inversion contra.
      * eapply  update_neq  in H . rewrite H.
        apply update_eq. Qed.


Example typing_example_3 :
  exists T,
    empty |--
      \x:Bool -> Bool,
         \y:Bool -> Bool,
            \z:Bool,
               (y (x z)) \in T.
Proof.
  eexists.
 apply T_Abs. apply T_Abs. apply T_Abs.
  eapply T_App.
 - apply T_Var.
   + assert (z <> y).
     * intros contra. inversion contra.
     * eapply update_neq in H. rewrite H.
       rewrite update_eq. reflexivity.
 - eapply T_App.
   + apply T_Var. assert (z <> x).
      * intros contra. inversion contra.
      * eapply update_neq in H. rewrite H.
        assert (y <> x).
        -- intros contra. inversion contra.
        -- eapply update_neq in H0. rewrite H0.
           apply update_eq.
   + apply T_Var. apply update_eq.
Qed.


Example typing_nonexample_1 :
  ~ exists T,
      empty |--
        \x:Bool,
            \y:Bool,
               (x y) \in T.
Proof.
  intros Hc. destruct Hc as [T Hc].
  (* The clear tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.

Example typing_nonexample_3 :
  ~ (exists S T, empty |-- \x:S, x x \in T).
Proof.
  intros contra.
  inversion contra.
  inversion H.
  inversion H0; subst.
  inversion H6; subst.
  inversion H4; subst.
  inversion H7; subst.
  inversion H5; subst.
  rewrite update_eq in H3. inversion H3.
  assert (forall T0 T3, T0 <> Ty_Arrow T0 T3).
  - intros. induction T0.
    + intros cons. inversion cons.
    + intros cons. inversion cons.
      eapply IHT0_1. subst. apply H8.
  - eapply H1. eauto.
Qed.

End STLC.













