Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps. 
From PLF Require Import Types.
From PLF Require Import STLC.
From PLF Require Import SmallStep.
From Coq Require Import Lia.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |-- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros. inversion H. 
  - subst. inversion H1.
  - subst. inversion H0.  
  - left. reflexivity.
  - subst. right. reflexivity.
  - subst. inversion H0.
Qed. 

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros.
  destruct H0.
  - inversion H. exists x0.
    exists t1. reflexivity.
 - inversion H.
 - inversion H.
Qed.

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht. 
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.         
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    discriminate H.
  - (* T_App *) 
    (* t = t1 t2.  Proceed by cases on whether t1 is a
       value or steps... *)
    right.  destruct IHHt1.  
    + reflexivity.
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1;  [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...
  - (* T_If *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
Qed.
    

Theorem progress' : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  - inversion Ht. subst. discriminate H1.
  -  right. inversion Ht; subst. remember H2. clear Heqh.
  apply IHt1 in H2.
  apply IHt2 in H4.
  destruct H2; destruct H4.
 + apply canonical_forms_fun in h.
   *  destruct h as [x [t0 H1]]. rewrite H1.
     exists <{[x:=t2]t0}>. apply ST_AppAbs. apply H0.
   * apply H.
+ destruct H0. eexists. apply ST_App2.
  * apply H.
  * apply H0.
+ destruct H. eexists. apply ST_App1. apply H.
+ destruct H. eexists.  apply ST_App1. apply H.
  - inversion Ht. subst. right.   remember H3. clear Heqh.
    apply IHt1 in H3. destruct H3.
    + apply canonical_forms_bool in h. 
      *  destruct h.
        -- rewrite H0. exists t2. apply ST_IfTrue.
      --  rewrite H0. exists t3. apply ST_IfFalse.
   * apply H.
  + destruct H. eexists. apply ST_If. apply H.
Qed. 

 Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof.
 intros. 
 generalize dependent Gamma'.
 induction H0.
 - intros. apply T_Var. apply H0. apply H.
 - intros. apply T_Abs. unfold includedin in IHhas_type.
   apply includedin_update with (x:=x0) (vx:=T2) in H.
   unfold includedin in H. apply IHhas_type.
   intros. apply H. apply H1.
 - intros. apply T_App with (T2:=T2).
   + apply IHhas_type1. apply H.
   + apply IHhas_type2. apply H.
 - intros. apply T_True.
 - intros. apply T_False.
 - intros. apply T_If.
   + apply IHhas_type1. apply H.
   + apply IHhas_type2. apply H.
   + apply IHhas_type3. apply H.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T ->
     Gamma |-- t \in T.
Proof.
  intros.
  apply weakening with empty.
  - unfold includedin. intros. inversion H0.
  - apply H.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
intros. 
generalize dependent T.
generalize dependent Gamma.
induction t.
 - intros. simpl. destruct ((x0 =? s)%string) eqn:Hxs. 
   + apply weakening_empty with (Gamma:=Gamma) in H0.
     apply eqb_eq in Hxs. subst. 
     inversion H.  
     subst. rewrite update_eq in H3. 
     injection H3.
     intros. subst. apply H0.
   + inversion H. subst.  
     apply eqb_neq in Hxs. 
     apply update_neq with (A:=ty) (m:=Gamma) (v:=U) in Hxs.
     rewrite Hxs in H3.
     apply T_Var in H3. apply H3.
 - intros. simpl. inversion H. subst. apply T_App with T2.
   + apply IHt1. apply H4.
   + apply IHt2. apply H6.
 - intros. simpl. destruct ((x0 =? s)%string) eqn:Hxs. 
   + apply eqb_eq in Hxs.  subst. inversion H. subst.
     apply T_Abs. rewrite  update_shadow in H6. apply H6. 
   + apply eqb_neq in Hxs. inversion H. subst. apply T_Abs.
     apply IHt. eapply update_permute in Hxs. rewrite <- Hxs.
     apply H6.
 - intros. simpl. inversion H. subst. apply T_True.
 - intros. simpl. inversion H. subst. apply T_False.
 - intros. simpl. inversion H. subst. apply T_If.
   + apply IHt1. apply H5.
   + apply IHt2. apply H7.
   + apply IHt3. apply H8.
Qed.

Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct ((x =? x0)%string) eqn:Hx.
    + apply eqb_eq in Hx.  subst. 
      rewrite update_eq in H. 
      injection H. intros. subst. 
      apply weakening_empty. apply Hv.
    + apply eqb_neq in Hx. rewrite G in H.
      apply update_neq with (A:=ty) (m:=Gamma') (v:=U) in Hx.
      rewrite Hx in H.
      apply T_Var in H. apply H.
  - destruct ((x =? x0)%string) eqn:Hx.
    + apply eqb_eq in Hx. subst. apply T_Abs.
      rewrite update_shadow in Ht. apply Ht.
    + apply eqb_neq in Hx. apply T_Abs.
      eapply substitution_preserves_typing with U.
      * rewrite G in Ht. 
        eapply update_permute in Hx.
        rewrite <- Hx. apply Ht.
      * apply Hv.
Qed.

Theorem preservation : forall t t' T,
  empty |-- t \in T ->
  t --> t' ->
  empty |-- t' \in T.
Proof.
  remember (@empty ty) as Gamma.
  intros.
  generalize dependent t'.
  induction H.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H1.
    + subst. apply substitution_preserves_typing with T2.
    * inversion H. subst. apply H4.
    * apply H0.
  + subst. eauto.
  + subst. eauto.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H2.
    + subst. apply H0.
    + subst. apply H1.
    + subst. eauto.        
Qed.  


Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ (empty |-- t' \in T) /\ ~ (empty |-- t \in T).
Proof.
  exists <{ if false then <{\x:Bool, x}> else true }>.
  exists <{true}>.
exists Ty_Bool.
split.
- apply ST_IfFalse.
- split.
  + apply T_True.
  + intros contra. inversion contra.
    inversion H5.
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.


Corollary type_soundness : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck. 
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - apply progress in Hhas_type. destruct Hhas_type.
    + apply Hnot_val in H. inversion H.
    + apply Hnf in H. inversion H.
  - apply IHHmulti.
    + apply preservation with (t:=x0).
      * apply Hhas_type.
      * apply H.
    + apply Hnf.
    + apply Hnot_val.
Qed.


Theorem unique_types : forall Gamma e T T',
  Gamma |-- e \in T ->
  Gamma |-- e \in T' ->
  T = T'.
Proof.
  intros.
 generalize dependent T'.
  induction H.
  -  intros. inversion H0. subst.
    rewrite H3 in H. injection H. auto.
  - intros. apply T_Abs in H. inversion H0. subst.
apply IHhas_type in H6. rewrite H6. reflexivity.
  - intros. inversion H1. subst.
    apply IHhas_type2 in H7. subst.
    apply IHhas_type1 in H5. injection H5. auto.
  -  intros. inversion H0. reflexivity.
 -  intros. inversion H0. reflexivity.
-  intros. inversion H2. subst. apply IHhas_type2 in H9. assumption.
Qed.

Inductive appears_free_in (x : string) : tm -> Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : forall t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{t1 t2}>
  | afi_app2 : forall t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{t1 t2}>
  | afi_abs : forall y T1 t1,
      y <> x ->
      appears_free_in x t1 ->
      appears_free_in x <{\y:T1, t1}>
  | afi_if1 : forall t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if2 : forall t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x <{if t1 then t2 else t3}>
  | afi_if3 : forall t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x <{if t1 then t2 else t3}>.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
 intros.
 generalize dependent Gamma.
generalize dependent T.
 induction H. 
 - intros. inversion H0. subst. exists T. apply H2.
 - intros. inversion H0. subst. eapply IHappears_free_in. apply H4. 
 - intros. inversion H0. subst. eapply IHappears_free_in. apply H6.
 - intros. inversion H1. subst. apply IHappears_free_in in H7.
   apply update_neq with (A:=ty) (m:=Gamma) (v:=T1) in H.
destruct H7 as [T' H7]. rewrite H in H7. exists T'. apply H7.
 - intros. inversion H0. subst. apply IHappears_free_in in H5.
   apply H5.
 - intros. inversion H0. subst. apply IHappears_free_in in H7.
apply H7.
 - intros. inversion H0. subst. apply IHappears_free_in in H8.
apply H8.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |-- t \in T ->
    closed t.
Proof.
intros. unfold closed.
intros. intros contra.
apply free_in_context with (T:=T) (Gamma:=empty) in contra.
- destruct contra as [t' Hcon]. inversion Hcon.
- apply H.
Qed.

Locate f_equal.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |-- t \in T ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |-- t \in T.
Proof.
 intros.
generalize dependent Gamma'.
 induction H.
 - intros. apply T_Var. rewrite <- H. symmetry. apply H0.
   apply afi_var.
 - intros. apply T_Abs. apply IHhas_type. intros.
   destruct ((x0 =? x1)%string) eqn:Hx.
   + apply eqb_eq in Hx. subst. rewrite  update_eq. rewrite  update_eq. reflexivity.
   + apply eqb_neq in Hx. remember Hx.  clear Heqn. remember n. clear Heqn0. eapply update_neq in Hx. 
     rewrite Hx. eapply update_neq in n.  rewrite n. apply H0. apply afi_abs.
     * apply n0. 
     *  apply H1.
 - intros. apply T_App with T2.
   + apply IHhas_type1. intros. apply H1. apply afi_app1. apply H2.
   + apply IHhas_type2. intros. apply H1. apply afi_app2. apply H2.
  -  intros. apply T_True.
  - intros. apply T_False.
  - intros. apply T_If. 
    + apply IHhas_type1.  intros. apply H2. apply afi_if1. apply H3.
 + apply IHhas_type2.  intros. apply H2. apply afi_if2. apply H3.
 + apply IHhas_type3.  intros. apply H2. apply afi_if3. apply H3.
Qed.



End STLCProp.

Module STLCArith.
Import STLC.

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

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

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm := 
   match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | tm_abs y T t1 =>
      tm_abs y T (if String.eqb x y then t1 else <{[x:=s] t1}>)
  | tm_app t1 t2 =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | tm_const n => tm_const n
  | tm_succ t =>  <{ succ ([x:=s] t) }>
  | tm_pred t => <{ pred ([x:=s] t) }>
  | tm_mult t1 t2 => <{ ([x:=s] t1) * ([x:=s] t2)}>
  | tm_if0 t1 t2 t3 =>
      <{if0 ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

 where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n,
      value (tm_const n).


Hint Constructors value : core.

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
  | ST_Succ : forall t t',
         t --> t' ->
         tm_succ t --> tm_succ t'
  | ST_SuccV : forall t n,
         t = tm_const n ->
         tm_succ t --> tm_const (S n)
  | ST_Pred : forall t t',
         t --> t' ->
         tm_pred t --> tm_pred t'
  | ST_PredV : forall t n,
         t = tm_const n ->
         tm_pred t --> tm_const (pred n)
  | ST_Mult1 : forall t1 t1' t2,
       t1 --> t1' ->
       tm_mult t1 t2 --> tm_mult t1' t2 
  | ST_Mult2 : forall t1 t2 t2',
       value t1 ->
       t2 --> t2' ->
       tm_mult t1 t2 --> tm_mult t1 t2'
  | ST_MultConst : forall (n1 n2 : nat),
      <{ n1 * n2 }> --> tm_const (n1 * n2)
  | ST_IfTrue : forall t1 t2 t3 n,
         t1 = tm_const (S n) ->
         tm_if0 t1 t2 t3 --> t2
  | ST_IfFalse : forall t1 t2 t3,
         t1 = tm_const 0 ->
         tm_if0 t1 t2 t3 --> t3
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
where "t '-->' t'" := (step t t').


Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors step : core.

Example Nat_step_example : exists t,
<{(\x: Nat, \y: Nat, x * y ) 3 2 }> -->* t.
Proof.
exists (tm_const 6).
  eapply multi_step.
    { apply ST_App1. apply ST_AppAbs. apply v_nat. }
  simpl.
  eapply multi_step.
    { apply ST_AppAbs. apply v_nat. }
  simpl.
  apply multi_R. apply ST_MultConst.
Qed.

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Cons : forall Gamma (x : nat),
      Gamma |-- x \in Nat
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
 | T_Succ : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
       Gamma |-- t1 \in Nat ->
       Gamma |-- t2 \in Nat ->
       Gamma |--  t1 * t2 \in Nat
  | T_If : forall t1 t2 t3 T1 Gamma, 
       Gamma |-- t1 \in Nat ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if0 t1 then t2 else t3 \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Example Nat_typing_example :
   empty |-- ( \x: Nat, \y: Nat, x * y ) 3 2 \in Nat.
Proof.
  apply T_App with Ty_Nat.
  -  apply T_App with Ty_Nat.
    + apply T_Abs. apply T_Abs. apply T_Mult.
       * apply T_Var. simpl.
          assert ((y |-> <{ Nat }>; x |-> <{ Nat }>) x = (x |-> <{ Nat }>) x ).
          -- apply  update_neq . intros contra. inversion contra.
          -- rewrite H. rewrite update_eq. reflexivity.
       * apply T_Var.  rewrite update_eq. reflexivity.
    + apply T_Cons.
  - apply T_Cons.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof. 
intros. 
 generalize dependent Gamma'.
 induction H0.
- intros. apply T_Var. apply H0. apply H.
- intros. apply T_Cons.
 - intros. apply T_Abs. unfold includedin in IHhas_type.
   apply includedin_update with (x:=x0) (vx:=T2) in H.
   unfold includedin in H. apply IHhas_type.
   intros. apply H. apply H1.
 - intros. apply T_App with (T2:=T2).
   + apply IHhas_type1. apply H.
   + apply IHhas_type2. apply H.
 - intros. apply T_Succ. apply IHhas_type. apply H. 
 - intros. apply T_Pred. apply IHhas_type. apply H. 
 - intros. apply T_Mult.
   + apply IHhas_type1. apply H. 
   + apply IHhas_type2. apply H.
 - intros. apply T_If.
   + apply IHhas_type1. apply H.
   + apply IHhas_type2. apply H.
   + apply IHhas_type3. apply H.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T ->
     Gamma |-- t \in T.
Proof.
  intros.
  apply weakening with empty.
  - unfold includedin. intros. inversion H0.
  - apply H.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
intros. 
generalize dependent T.
generalize dependent Gamma.
induction t.
 - intros. simpl. destruct ((x0 =? s)%string) eqn:Hxs. 
   + apply weakening_empty with (Gamma:=Gamma) in H0.
     apply eqb_eq in Hxs. subst. 
     inversion H.  
     * subst. rewrite update_eq in H3. injection H3.
       intros. subst. apply H0.
    + apply eqb_neq in Hxs. 
     apply update_neq with (A:=ty) (m:=Gamma) (v:=U) in Hxs. inversion H.
     * rewrite Hxs in H3. 
       apply T_Var in H3. apply H3.
  
 - intros. simpl. inversion H.
   + subst. apply T_App with T2.  
     * apply IHt1. apply H4.
     * apply IHt2. apply H6.
 - intros. simpl. destruct ((x0 =? s)%string) eqn:Hxs.
   + apply eqb_eq in Hxs. subst. inversion H.
     * subst. apply T_Abs. rewrite update_shadow in H6. apply H6.
   + apply eqb_neq in Hxs. remember Hxs. clear Heqn.
     apply update_neq with (A:=ty) (m:=Gamma) (v:=U) in Hxs. inversion H.
     * subst. apply T_Abs. apply IHt.
       assert ((x0 |-> U; s |-> t; Gamma)=(s |-> t; x0 |-> U; Gamma)).
       -- apply  update_permute. auto.
       -- rewrite H1. apply H6.
  - intros. simpl. inversion H. subst. apply T_Cons.
  - intros. simpl. inversion H.
    + subst. apply T_Succ. apply IHt. apply H3.
 - intros. simpl. inversion H. subst. apply T_Pred. apply IHt. apply H3.
  - intros. simpl. inversion H. subst.
   apply T_Mult.
      + apply IHt1. apply H4.
      + apply IHt2. apply H6.
  - intros. simpl. inversion H. subst.  apply T_If. 
    + apply IHt1. apply H5.
    + apply IHt2. apply H7.
    + apply IHt3. apply H8.
Qed.

Theorem preservation : forall t t' T,
  empty |-- t \in T ->
  t --> t' ->
  empty |-- t' \in T.
Proof with eauto. 
  remember (@empty ty) as Gamma.
  intros.
  generalize dependent t'.
  induction H.
  - intros. subst. inversion H.
  - intros. subst. inversion H0.
  - intros. inversion H0.
  - intros. inversion H1.    
    + subst. inversion H. subst. 
 apply substitution_preserves_typing with T2.
    -- apply H4.
   -- apply H0.
  + subst. apply T_App with T2.
    -- apply IHhas_type1.
       ++ auto.
       ++ auto.
  -- apply H0.
  +  subst. apply T_App with T2.
     -- apply H.
     -- apply IHhas_type2. 
        ++ auto.
        ++ auto.
  - intros; subst; inversion H0; auto. 
  - intros; subst; inversion H0; auto. 
- intros; inversion H1; auto. 
- intros; inversion H2; subst; auto. 
       
Qed.  


Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof. 
  intros.
  destruct H0.
  - inversion H. exists x0.
    exists t1. reflexivity.
 - inversion H.
Qed.

Lemma canonical_forms_nat : forall t,
  empty |-- t \in Nat ->
  value t ->
  exists n, t = tm_const n.
Proof.
  intros.
  destruct H0.
  - inversion H.
  - exists n. auto.
Qed. 


Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht. 
  remember empty as Gamma.
  induction Ht.
  - subst. discriminate H.
  - left. apply v_nat.
  - left. apply v_abs.
  - right. destruct IHHt1.  
    + subst. reflexivity.
    + (* t1 is a value *)
      destruct IHHt2...
      * subst. 
        eapply canonical_forms_fun in Ht1;  [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * destruct H0 as [t2' H0].
        exists <{ t1 t2' }> .
        apply ST_App2.
        -- apply H.
        -- apply H0.
    + destruct H as [t1' H].
      exists <{ t1' t2 }> .
      apply ST_App1.
      apply H.
  - destruct IHHt.
    + subst. auto.
    + subst. destruct H.
      * inversion Ht.
      * right.  exists (tm_const (S n)).
        apply ST_SuccV.
        reflexivity.
    + destruct H as [t' H].
      right. exists (tm_succ t').
      apply ST_Succ.
      apply H.
  - destruct IHHt.
    + subst. reflexivity.
    + subst. destruct H.
      * inversion Ht.
      * right.  exists (tm_const (pred n)).
        apply ST_PredV.
        reflexivity.
    + destruct H as [t' H].
      right. exists (tm_pred t').
      apply ST_Pred.
      apply H.
  - right. subst. destruct IHHt1.
    + auto.
    + destruct IHHt2.
      * reflexivity.
      * destruct H.
        -- inversion Ht1.
        -- destruct H0.
           ++ inversion Ht2.
           ++ exists (tm_const (n * n0)).
              apply ST_MultConst.
      * destruct H0 as [t2' H0].
        exists (tm_mult t1 t2').
        apply ST_Mult2.
        -- apply H.
        -- apply H0.
    + destruct H as [t1' H].
      exists (tm_mult t1' t2).
      apply  ST_Mult1. apply H.
  - right. destruct IHHt1 as [Hv1 | [t1' H1]].
    + subst. reflexivity.
    + subst. destruct (canonical_forms_nat t1 Ht1 Hv1) as [n1 Et1].
      subst t1. destruct n1.
      * exists t3. apply ST_IfFalse. auto.
      * exists t2. apply ST_IfTrue with n1. auto.
    + exists <{ if0 t1' then t2 else t3 }>. apply ST_If. assumption.
 Qed.        

End STLCArith.


