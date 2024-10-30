Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import SmallStep.
Set Default Goal Selector "!".

Module STLCSub.

Inductive ty : Type :=
  | Ty_Top   : ty
  | Ty_Bool  : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit  : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.

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
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).

Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

Notation "{ x }" := x (in custom stlc at level 1, x constr).



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
  | <{unit}> =>
      <{unit}>
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).



Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.
  


Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
       <{(t1 , t2)}> --> <{(t1' , t2)}>
  | ST_Pair2 : forall v1 t2' t2,
      value v1 ->
      t2 --> t2' ->
      <{(v1 , t2)}> --> <{(v1 , t2')}>
  | ST_Fst1 : forall t t',
      t --> t' ->
      <{ t.fst }> --> <{ t'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> v1
  | ST_Snd1 : forall t t',
      t --> t' ->
      <{ t.snd }> --> <{ t'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> v2

where "t '-->' t'" := (step t t').

Hint Constructors step : core.


Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
 | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
where "T '<:' U" := (subtype T U).


Hint Constructors subtype : core.
Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.

Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.

Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof. 
apply S_Arrow.
- apply S_Refl.
- apply S_Top.
 Qed.


Definition Person : ty := (Ty_Prod String Ty_Top).
Definition Student : ty := (Ty_Prod String Float).
Definition Employee : ty := (Ty_Prod String Integer).

Example sub_student_person :
  Student <: Person.
Proof.

apply S_Prod.
- apply S_Refl.
- apply S_Top.
Qed.

Example sub_employee_person :
  Employee <: Person.
Proof.
apply S_Prod.
- apply S_Refl.
- apply S_Top.
Qed.
 

Example subtyping_example_1 :
  <{Top -> Student}> <: <{(C -> C) -> Person}>.
Proof with eauto.
 apply S_Arrow.
 -  apply S_Top.
 - apply sub_student_person.
Qed.


Example subtyping_example_2 :
  <{Top -> Person}> <: <{Person -> Top}>.
Proof with eauto.
   apply S_Arrow.
 -  apply S_Top.
 - apply S_Top.
Qed.

End Examples.

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
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
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1 , t2) \in (T1*T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.


Import Examples.

Lemma typing_example_0 : forall z A B,
 empty |-- ((\z:A,z), (\z:B,z)) \in ((A->A) * (B->B)).
Proof.
  intros.
  eapply T_Sub.
  - apply T_Pair.
    + apply T_Abs.  apply T_Var. 
      rewrite update_eq. reflexivity.
    + apply T_Abs.  apply T_Var. 
      rewrite update_eq. reflexivity.
  - apply S_Refl.
Qed.

Lemma typing_example_1 : forall x A B,
empty |-- (\x:(Top * (B->B)), x.snd) ((\z:A,z), (\z:B,z)) \in (B->B).
Proof.
  intros.
  eapply T_App.
  - apply T_Abs.
    eapply T_Snd.
apply T_Var. 
rewrite update_eq. reflexivity.
  - apply T_Pair.
    + eapply T_Sub.
      * apply T_Abs.
        apply T_Var.
         rewrite update_eq. reflexivity.
  * apply S_Top.
  + apply T_Abs.
    apply T_Var.
         rewrite update_eq. reflexivity.
Qed.

Lemma typing_example_2 : forall x A B,
empty |-- (\z:(C->C)->(Top * (B->B)), (z (\x:C,x)).snd)
              (\z:(C->C), ((\z:A,z), (\z:B,z)))
         \in (B->B).
Proof.
  intros.
  eapply T_App.
  - apply T_Abs.
    eapply T_Snd.
eapply T_App.
     +   apply T_Var. rewrite update_eq. reflexivity.
     + apply T_Abs.  apply T_Var. rewrite update_eq. reflexivity.
  - apply T_Abs.
     apply T_Pair.
    + eapply T_Sub.
     * apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
     * apply S_Top.
    + apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
Qed.



Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs.
  - reflexivity.
  - subst. assert(<{ Bool }> = <{ Bool }>).
    + reflexivity.
    + apply IHHs2 in H. subst. apply IHHs1. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1 -> V2}> ->
     exists U1 U2,
     U = <{U1 -> U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V. 
  generalize dependent V2. generalize dependent V1.
  induction Hs.
  - intros. exists V1. exists V2. split.
    + apply HeqV.
    + split.
      * apply S_Refl.
      * apply S_Refl.
  - intros. apply IHHs2 in HeqV.
    destruct HeqV as [R1 [R2 H]].
    destruct H. apply IHHs1 in H.
    destruct H as [K1 [K2 H]].
    destruct H. exists K1. exists K2. split.
    + apply H.
    + destruct H0. destruct H1. split. 
      * eapply S_Trans.
        -- apply H0.
        -- apply H1.
      * eapply S_Trans.
        -- apply H3. 
        -- apply H2.
  - intros.  inversion HeqV.
  - intros. inversion HeqV. subst. exists S1. exists S2. split.
    + reflexivity.
    + split.
      * apply Hs1.
      * apply Hs2.
  - intros. inversion HeqV.
Qed.

Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof.
  intros U Hs.
  remember <{ Unit }> as V.
  induction Hs.
  - reflexivity.
  - subst. assert(<{ Unit }> = <{ Unit }>).
    + reflexivity.
    + apply IHHs2 in H. subst. apply IHHs1. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.


Lemma sub_inversion_Base : forall U s,
     U <: <{Base s}> ->
     U = <{Base s}>.
Proof.
 intros U s Hs.
  remember <{Base s}>  as V.
  induction Hs.
  - reflexivity.
  - subst. assert(<{ Base s }> = <{ Base s }>).
    + reflexivity.
    + apply IHHs2 in H. subst. apply IHHs1. reflexivity.
  - inversion HeqV.
  - inversion HeqV.
  - inversion HeqV.
Qed.


Lemma sub_inversion_Top : forall U,
     <{ Top }> <: U ->
     U = <{ Top }>.
Proof.
 intros U Hs.
  remember <{Top}>  as V.
  induction Hs.
  - reflexivity.
  - subst. assert(<{ Top }> = <{ Top }>).
    + reflexivity.
    + apply IHHs1 in H. subst. apply IHHs2. reflexivity.
  - auto.
  - inversion HeqV.
  - inversion HeqV.
Qed.

Locate solve_by_invert.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 -> T2) ->
  value s ->
  exists x S1 s2, s = <{\x:S1,s2}>.
Proof.
  intros. remember <{T1->T2}> as T. 
  generalize dependent T1. generalize dependent T2.
  induction H.
  - intros. inversion H0.
  - intros. 
    exists x. exists T2. exists t1. reflexivity.
  - intros. inversion H0.
  - intros. inversion HeqT.
  - intros. inversion HeqT.
  - inversion H0.
  - intros. inversion HeqT.
  - intros. subst. apply sub_inversion_arrow in H1.
    destruct H1 as [U1 [U2 H1]]. destruct H1.
    eapply IHhas_type in H0.
    + apply H0.
    + apply H1.
  - intros. inversion HeqT.
  - intros. inversion H0. 
  - intros. inversion H0.
Qed. 
 

Lemma sub_inversion_Prod : forall U V1 V2,
  U <: <{ V1 * V2 }> ->
      exists U1 U2, U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs.
  - intros. exists V1. exists V2. split.
    + apply HeqV.
    + split.
      * apply S_Refl.
      * apply S_Refl.
  - intros.  apply IHHs2 in HeqV.
    destruct HeqV as [R1 [R2 H]].
    destruct H. apply IHHs1 in H.
    destruct H as [K1 [K2 H]].
    destruct H. exists K1. exists K2. split.
    + apply H.
    + destruct H0. destruct H1. split. 
      * eapply S_Trans.
        -- apply H1.
        -- apply H0.
      * eapply S_Trans.
        -- apply H3. 
        -- apply H2.
  - intros.  inversion HeqV.
  - intros. inversion HeqV. 
   
  - intros. 

subst. exists S1. exists S2. split.
 + reflexivity.
    + injection HeqV. intros. subst. split.
      * apply Hs1.
      * apply Hs2.
Qed.


Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
 intros. remember <{T1 * T2 }> as T. 
  generalize dependent T1. generalize dependent T2.
  induction H. 
  - intros. inversion H0.
  - intros. inversion HeqT.
  - intros. inversion H0.
  - intros.  inversion HeqT.
 - intros.  inversion HeqT.
 - intros.  inversion H0.
 - intros.  inversion HeqT.
 - intros.  subst. apply sub_inversion_Prod in H1.
    destruct H1 as [U1 [U2 H1]]. destruct H1.
    eapply IHhas_type. 
    + apply H0.
   +  apply H1.
 - intros. exists t1. exists t2. reflexivity.
 -  intros. inversion H0.
 -  intros. inversion H0.
Qed.


Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
   - inversion H.
   - assert ((@empty ty) = (@empty ty)).
     + reflexivity.
     + remember H. clear Heqe. apply IHHt1 in H. 
       destruct H.
      * apply IHHt2 in e. destruct e.
        -- apply canonical_forms_of_arrow_types in Ht1.
            ++  destruct Ht1 as [x [S1 [s2 Ht1]]].
                right. subst. exists <{ [x:=t2]s2 }>.
                apply ST_AppAbs.
                **  apply H0.
            ++ apply H.
      -- right. destruct H0 as [t2' H0].
         exists <{t1  t2'}>.
         apply ST_App2.
         ++ apply H.
         ++ apply H0.
  * right. destruct H as [t1' H].
     exists <{t1'  t2}>.
apply ST_App1.  apply H.
    - destruct IHHt1.
      + reflexivity.
       + apply canonical_forms_of_Bool in Ht1.
      * destruct Ht1.
        -- subst. right. 
                exists t2. apply ST_IfTrue.
         -- subst. right. 
                exists t3. apply ST_IfFalse.
        * apply H. 
       + destruct H as [t1' H].
             right. exists <{if t1' then t2 else t3}>.
            apply ST_If. apply H.
- destruct IHHt1.
      + reflexivity.
 + destruct IHHt2.
    * reflexivity.
* left.  apply v_pair.
   -- apply H.
   -- apply H0.
* destruct H0 as [t2' H0].
  right.  exists <{(t1 , t2')}>.
  apply ST_Pair2.
  -- apply H.
   -- apply H0.
+ destruct H as [t1' H].
  right. exists <{(t1' , t2)}>.
  apply ST_Pair1. apply H.
- destruct IHHt. 
  + reflexivity. 
  + apply canonical_forms_of_Pair in Ht.
    * destruct Ht as [v1 [v2 Ht]].
      subst. right. exists v1.
      apply ST_FstPair.
      -- inversion H. subst. apply H2.
      -- inversion H. subst. apply H3.
    *  apply H.
   + destruct H as [t0' H].
     right.  exists <{ t0'.fst }>.
     apply ST_Fst1. apply H.
- destruct IHHt. 
  + reflexivity. 
  + apply canonical_forms_of_Pair in Ht.
    * destruct Ht as [v1 [v2 Ht]].
      subst. right. exists v2.
      apply ST_SndPair.
      -- inversion H. subst. apply H2.
      -- inversion H. subst. apply H3.
    *  apply H.
   + destruct H as [t0' H].
     right.  exists <{ t0'.snd }>.
     apply ST_Snd1. apply H.
Qed.
   
Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1 -> S2}> <: T
       /\ (x |-> S1; Gamma) |-- t2 \in S2.
Proof.
  intros.  remember <{ \ x : S1, t2 }> as Hx.
  induction H.
  - inversion HeqHx.
  - injection HeqHx. intros. subst.
    exists T1. auto.
  - inversion HeqHx.
 - inversion HeqHx.
 - inversion HeqHx.
 - inversion HeqHx.
 - inversion HeqHx.
 - apply IHhas_type in HeqHx.
   destruct HeqHx as [S2 Hs].
destruct Hs. exists S2.
  split.
  + eapply S_Trans.
    * apply H1.
    * apply H0.
  + apply H2.
   
 - inversion HeqHx.
 - inversion HeqHx.
 - inversion HeqHx.
Qed.

Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof.
  intros.
  remember (tm_var x) as G.
  induction H.
- exists T1. subst. split.
   + inversion HeqG. subst.
apply H. 
   + apply S_Refl.
- inversion HeqG.
 - inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. subst. apply  IHhas_type in H1.
  destruct H1 as [T0 H1]. destruct H1. exists T0.
  split.
  + apply H1.
  +  eapply S_Trans.
    * apply H2.
    * apply H0.
- inversion HeqG. 
- inversion HeqG.
 - inversion HeqG.
Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1 -> T2) /\
    Gamma |-- t2 \in T1.
Proof.
 intros.
 remember (tm_app t1 t2) as G.
 induction H.
 - inversion HeqG.
 - inversion HeqG. 
- inversion HeqG. subst. exists T2.
  split.
  + apply H.
  + apply H0.
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
- apply IHhas_type in HeqG.  
 destruct HeqG as [T0 H1]. destruct H1. exists T0.
split.
 + assert( <{T0 -> T1}> <: <{T0 -> T2}>).
   * apply S_Arrow.
     -- apply S_Refl.
     -- apply H0.
   * eapply T_Sub.
     -- apply H1.
     -- apply H3.
  + apply H2.
- inversion HeqG. 
- inversion HeqG. 
- inversion HeqG. 
Qed. 

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |-- unit \in T ->
    <{Unit}> <: T.
Proof.
intros.
remember <{ unit }> as G.
 induction H.
 - inversion HeqG.
 - inversion HeqG. 
 - inversion HeqG.
 - inversion HeqG. 
 - inversion HeqG.
 - inversion HeqG. 
 - apply S_Refl.
 - eapply S_Trans.
   + apply  IHhas_type.
     apply HeqG.
   + apply H0.
  - inversion HeqG.
 - inversion HeqG. 
 - inversion HeqG.
Qed. 

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1 -> T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq. subst...  Qed.

Locate includedin.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof. 
intros.
generalize dependent Gamma'. 
induction H0; intros; eauto.
apply T_Abs.   
apply IHhas_type.
apply includedin_update.
apply H.
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T ->
     Gamma |-- t \in T.
Proof.
 intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-- t \in T ->
  empty |-- v \in U ->
  Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - destruct (x =? x0 ) eqn:Hxs.
    + apply weakening_empty. apply eqb_eq in Hxs. subst.
      rewrite update_eq in H. injection H. intros. subst. apply Hv.
    + apply eqb_neq in Hxs. 
      rewrite G in H. subst. apply update_neq with (A:=ty) (m:=Gamma') (v:=U) in Hxs.
      rewrite Hxs in H.  apply T_Var in H. apply H.
  - destruct (x =? x0 ) eqn:Hxs.
    + apply eqb_eq in Hxs. subst. apply T_Abs. rewrite update_shadow in Ht.
      apply Ht.
    + apply T_Abs. apply eqb_neq in Hxs. 
      apply IHHt. 
      assert((x |-> U; x0 |-> T2; Gamma')=(x0 |-> T2; x |-> U; Gamma')).
      * apply update_permute. auto.
      * rewrite H.
        rewrite G. reflexivity.
Qed.

Lemma typing_inversion_prod : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists S1 S2,
    Gamma |-- t1 \in S1 /\
    Gamma |-- t2 \in S2 /\
    <{S1 * S2}> <: T.
Proof.
  intros.
  remember <{(t1, t2) }> as pt.
generalize dependent t1. generalize dependent t2.
 
induction H.
 - intros. inversion Heqpt.
- intros. inversion Heqpt.
- intros. inversion Heqpt.
- intros. inversion Heqpt.
- intros. inversion Heqpt.
 - intros. inversion Heqpt.
- intros. inversion Heqpt.
- intros. apply IHhas_type in Heqpt.
  destruct Heqpt as [S1 [S2 Heq]].
  destruct Heq.
  exists S1. exists S2.
  split.
  + apply H1.
  + destruct H2.
    split. 
    * apply H2.
    * eapply S_Trans. 
      -- apply H3.
       --  apply H0.
- intros. injection Heqpt. intros. subst.
  exists T1. exists T2.
  split. 
  + apply H.
  + split. 
    * apply H0.
    * apply S_Refl.
- intros. inversion Heqpt.
- intros. inversion Heqpt.
Qed.


Lemma pair_prod : forall t1 t2 T1 T2,
  empty |-- (t1, t2) \in (T1 * T2) ->
    empty |-- t1 \in T1 /\ empty |-- t2 \in T2.
Proof.
 intros.
remember <{(T1*T2) }> as T.
apply typing_inversion_prod in H.
destruct H as [S1 [S2 H]].
destruct H.
destruct H0.
subst.
apply sub_inversion_Prod in H1.
destruct H1 as [U1 [U2 H1]].
destruct H1.
injection H1. intros. subst.
split.
- destruct H2. eapply T_Sub.
  + apply H.
  + apply H2.
- destruct H2. eapply T_Sub.
  + apply H0.
  + apply H3.
Qed.


Theorem preservation : forall t t' T,
     empty |-- t \in T ->
     t --> t' ->
     empty |-- t' \in T.
Proof with eauto.
intros.
 remember empty as Gamma.
generalize dependent t'.
induction H.
- intros. inversion H0.
- intros. inversion H0.
- intros. inversion H1.
   + subst. apply abs_arrow in H.
    apply substitution_preserves_typing with T0.
    * destruct H. apply H2.
    * eapply T_Sub.
      -- apply H0.
      -- destruct H. apply H.
    + subst. eapply T_App.
      * apply IHhas_type1.
        -- reflexivity.
        -- apply H5.
      * apply H0.
    + subst. eapply T_App.
      * apply H.
      * apply IHhas_type2.
         -- reflexivity.
        -- apply H6.
   - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H2.
    + subst. apply H0.
  + subst. apply H1.
   + apply T_If.
     * subst. apply IHhas_type1.
       -- reflexivity.
       -- apply H7.
     * apply H0.
 * apply H1.
  - intros. inversion H0.
  - intros. eapply T_Sub. 
    + apply IHhas_type. 
      * apply HeqGamma.
      * apply H1.
    + apply H0.
  - intros. inversion H1.
    + apply T_Pair.
      * subst.  apply IHhas_type1.
        -- reflexivity.
        -- apply H5.
      * subst. apply H0.
    + subst. apply T_Pair.
      * apply H.
      * apply IHhas_type2.
         -- reflexivity.
        -- apply H6.
  - intros. inversion H0.
    + eapply T_Fst. apply IHhas_type.
      * apply HeqGamma.
      * apply H2.
    + subst. apply pair_prod in H.
      destruct H. apply H.
  - intros.  inversion H0.
      + eapply T_Snd. apply IHhas_type.
      * apply HeqGamma.
      * apply H2.
    + subst. apply pair_prod in H.
      destruct H. apply H1.
Qed.

Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".
Definition TF P := P \/ ~P.

Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T -> S}> <: <{T -> S}>).
Proof.
  unfold TF.
  left.
  intros.
  apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{Top -> U}> <: <{S -> Top}>).
Proof.
  unfold TF.
left.
  intros.
apply S_Arrow.
  - apply S_Top.
- apply S_Top.
Qed.

Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(C -> C) -> (A*B)}> <: <{(C -> C) -> (Top*B)}>).
Proof.
  unfold TF.
left.
  intros.
apply S_Arrow.
 -  apply S_Refl.
 - apply S_Prod.
   + apply S_Top.
   + apply S_Refl.
Qed.

Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T -> (T -> U)}> <: <{S -> (S -> V)}>).
Proof.
  unfold TF.
left.
  intros.
apply S_Arrow.
- apply H.
- apply S_Arrow.
  + apply H.
  + apply H0.
Qed.

Lemma sub_inversion_arrow2 : 
 forall S1 S2 T1 T2,
      <{S1->S2}> <: <{T1->T2}> ->
       T1 <: S1 /\ S2 <: T2.
Proof.
  intros.
  apply sub_inversion_arrow in H.
  destruct H as [U1 [U2 H]].
  destruct H. injection H.
  intros. subst.
  apply H0.
Qed.

Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(T -> T) -> U}> <: <{(S -> S) -> V}>).
Proof.
  unfold TF.
  right.
  intros H.
  specialize (H Ty_Unit Ty_Top Ty_Unit Ty_Unit (S_Top _) (S_Refl _)).
  apply sub_inversion_arrow2 in H. destruct H as [HsU1 _].
  apply sub_inversion_arrow2 in HsU1. destruct HsU1 as [HsU1 _].
  remember <{Top}> as U.
  apply sub_inversion_Unit in HsU1.
  rewrite HeqU in HsU1. inversion HsU1.
Qed.

Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{((T -> S) -> T) -> U}> <: <{((S -> T) -> S) -> V}>).
Proof.
  unfold TF.
  left.
  intros.
apply S_Arrow.
 - apply S_Arrow.
   + apply S_Arrow.
     * apply H.
     * apply H.
   + apply H.
- apply H0.
Qed.


Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{S*V}> <: <{T*U}>).
Proof.
    unfold TF.
  right.
  intros H.
   specialize (H Ty_Unit Ty_Top Ty_Unit Ty_Top).
  assert(<{ Unit }> <: <{ Top }>).
  + apply S_Top.
  + apply H in H0.
    * apply sub_inversion_Prod in H0.
       destruct H0 as [U1 [U2 H0]].
      destruct H0.
      injection H0.  intros. subst.
      destruct H1. 
remember <{Top}> as U.
  apply sub_inversion_Unit in H2.
  rewrite HeqU in H2.
 inversion H2.
  * apply H0.
Qed.

Theorem formal_subtype_instances_tf_2a:
  TF (forall S T,
         S <: T ->
         <{S -> S}> <: <{T -> T}>).
Proof.
  unfold TF.
  right.
  intros H.
  specialize (H Ty_Unit Ty_Top).
   assert(<{ Unit }> <: <{ Top }>).
  - apply S_Top.
  - apply H in H0.
    apply sub_inversion_arrow2 in H0.
   destruct H0.
  remember <{Top}> as U.  apply sub_inversion_Unit in H0.
   rewrite HeqU in H0. inversion H0.
Qed.

Theorem formal_subtype_instances_tf_2b:
  TF (forall S,
         S <: <{A -> A}> ->
         exists T,
           S = <{T -> T}> /\ T <: A).
Proof.
 unfold TF.
  right.
  intros H.
   specialize (H <{ Top -> A}>).
  assert(<{ Top -> A }> <: <{ A -> A }>).
  - apply S_Arrow.
   + apply S_Top.
   + apply S_Refl.
  - apply H in H0. destruct H0 as [T' H0].
   destruct H0. injection H0.
     intros. subst. inversion H3.
Qed.
 
Theorem formal_subtype_instances_tf_2d:
  TF (exists S, S <: <{S -> S}>).
Proof.
right. 
  assert (H : forall S T, ~ S <: <{T->S}>). 
    { induction S; intros T H;
        destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [E [_ HsU2]]]]; 
        try discriminate E.
      - injection E as _ E. subst U2.
        apply (IHS2 _ HsU2). } 
  intros [S Hs]. apply (H S S Hs).
Qed.

Theorem formal_subtype_instances_tf_2e:
  TF (exists S, <{S -> S}> <: S).
Proof.
 left.
 exists Ty_Top.
apply S_Top.
Qed.


Theorem formal_subtype_concepts_tfa:
  TF (exists T, forall S, S <: T).
Proof.
 left.
 exists Ty_Top.
apply S_Top.
Qed.

Theorem formal_subtype_concepts_tfb:
  TF (exists T, forall S, T <: S).
Proof.
right.
intros [T H]. destruct T;
    try (specialize (H Ty_Unit); apply sub_inversion_Unit in H;  discriminate H).
  - specialize (H Ty_Bool). apply sub_inversion_Bool in H.
    discriminate H.
Qed.

Theorem formal_subtype_concepts_tfc:
  TF (exists T1 T2, forall S1 S2, <{S1 * S2}> <: <{T1 * T2}>).
Proof.
left. exists Ty_Top. exists Ty_Top.
intros. apply S_Prod.
- apply S_Top.
- apply S_Top.
Qed.

Theorem no_min_sub : ~ exists T, forall S, T <: S.
Proof.
intros contra.
destruct contra as [T H].
destruct T.
- specialize (H Ty_Unit). apply sub_inversion_Unit in H. discriminate H.
- specialize (H Ty_Unit). apply sub_inversion_Unit in H. discriminate H.
- specialize (H Ty_Unit). apply sub_inversion_Unit in H. discriminate H.
- specialize (H Ty_Unit). apply sub_inversion_Unit in H. discriminate H.
- specialize (H Ty_Bool). apply sub_inversion_Bool in H. discriminate H.
- specialize (H Ty_Unit). apply sub_inversion_Unit in H. discriminate H.
Qed.


Lemma sub_inversion_Prod2 : forall T1 T2 U1 U2,
  <{ T1 * T2 }> <: <{ U1 * U2 }> ->
  T1 <: U1 /\ T2 <: U2.
Proof.
intros. remember <{ T1 * T2 }> as T.
apply sub_inversion_Prod in H.
destruct H as [U3 [U4 H]].
destruct H.
subst. injection H.
intros. subst. apply H0.
Qed.


Theorem formal_subtype_concepts_tfd:
  TF (exists T1 T2, forall S1 S2, <{T1*T2}> <: <{S1*S2}>).
Proof.
right. intros [T1 [T2 H]].
  apply no_min_sub.
  exists T2. intros S. specialize (H T1 S).
  apply sub_inversion_Prod2 in H.  intuition.
Qed.


Theorem formal_subtype_concepts_tfe:
  TF (exists T1 T2, forall S1 S2, <{S1 -> S2}> <: <{T1 -> T2}>).
Proof.
  right. 
intros contra.
destruct contra as [T1 [T2 H]].
 apply no_min_sub. exists T1. intros. specialize (H S T1).
apply sub_inversion_arrow2 in H.
destruct H.
apply H.
Qed.

Fixpoint ty_fun1 i :=
  match i with
  | 0 => Ty_Top
  | S n => Ty_Prod Ty_Top (ty_fun1 n)
  end.

Lemma ty_fun1_inj : forall i j, i <> j -> ty_fun1 i <> ty_fun1 j.
Proof.
induction i.
- intros. intros contra. simpl in contra.
  induction j.
  + apply H. reflexivity.
  + simpl in contra. inversion contra.
- intros.
  simpl. intros contra. induction j.
  + simpl in contra. inversion contra.
  + simpl in contra. injection contra. 
    intros. specialize (IHi j). apply IHi.
    * intros Q. apply H. rewrite Q. reflexivity.
    * apply H0.
Qed.


Lemma ty_fun1_sub : forall i : nat, ty_fun1 (S i) <: ty_fun1 i.
Proof.
simpl.
induction i.
- simpl. apply S_Top.
- simpl. apply S_Prod.
  + apply S_Top.
  + apply IHi.
Qed.

Theorem formal_subtype_concepts_tfg:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f (S i) <: f i)).
Proof.
 left. exists ty_fun1.
  split.
  - apply ty_fun1_inj.
  - apply ty_fun1_sub.
Qed.

Theorem formal_subtype_concepts_tfh:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f i <: f (S i))).
Proof.
left. exists (fun i => Ty_Arrow (ty_fun1 i) Ty_Top).
  split.
  - intros i j Hne H. apply ty_fun1_inj in Hne.
    injection H as H. exact (Hne H).
  - intros i. apply S_Arrow.
    + apply ty_fun1_sub.
    + apply S_Refl.
Qed.

Theorem formal_proper_subtypes:
  TF (forall T,
         ~(T = <{Bool}> \/ (exists n, T = <{Base n}>) \/ T = <{Unit}>) ->
         exists S,
           S <: T /\ S <> T).
Proof.
  right. intros H.
  specialize (H (Ty_Arrow Ty_Top Ty_Unit)).
  destruct H as [S [Hs Hne]].
  - intros [contra | [[n contra] | contra]].
    + discriminate contra.
    + discriminate contra.
    + discriminate contra.
  - apply sub_inversion_arrow in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
    subst S.
    apply sub_inversion_Top in HsU1. subst U1.
    apply sub_inversion_Unit in HsU2. subst U2.
    apply Hne. reflexivity.
Qed.

Definition smallest_largest HT :=
  (* There exists a smallest and a largest. *)
  (exists TS TL, forall T, TS <: T /\ T <: TL <-> HT T)
  \/
  (* There exists a smallest, but no largest. *)
  ((exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists a largest, but not smallest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   (exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists neither a smallest nor a largest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T)).


Lemma typing_inversion_fst : forall Gamma t T,
  Gamma |-- t.fst \in T ->
  exists S1 S2,
    Gamma |-- t \in (S1 * S2) /\
    S1 <: T.
Proof.
 intros Gamma t1 T H.
  remember <{t1.fst}> as t.
  induction H.
 - inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- subst. destruct IHhas_type.
  + reflexivity.
  + destruct H1 as [S2 H1].
   exists x. exists S2.
   split.
   * destruct H1. apply H1.
   * destruct H1.
     eapply S_Trans.
     -- apply H2.
     -- apply H0.
     
- inversion Heqt.
- injection Heqt. intros. subst. exists T1. exists T2.
  split.
  + apply H.
  + apply S_Refl.
- inversion Heqt.
Qed.

Lemma typing_inversion_snd : forall Gamma t T,
  Gamma |-- t.snd \in T ->
  exists S1 S2,
    Gamma |-- t \in (S1 * S2) /\
    S2 <: T.
Proof.
intros Gamma t1 T H.
  remember <{t1.snd}> as t.
  induction H.
 - inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- inversion Heqt.
- subst. destruct IHhas_type.
  + reflexivity.
  + destruct H1 as [S2 H1].
   exists x. exists S2.
   split.
   * destruct H1. apply H1.
   * destruct H1.
     eapply S_Trans.
     -- apply H2.
     -- apply H0.
     
- inversion Heqt.
- inversion Heqt.
- injection Heqt. intros. subst. exists T1. exists T2.
  split.
  + apply H.
  + apply S_Refl.

Qed.



Lemma typing_inv_var : forall Gamma (x:string) T U,
  Gamma x = Some U ->
  Gamma |-- x \in T ->
  U <: T.
Proof.
  intros. apply typing_inversion_var in H0.
  destruct H0 as [S [E Hs]].
  rewrite E in H. injection H as Eu. subst S. apply Hs.
Qed.

Theorem formal_small_large_1:
  smallest_largest
  (fun T =>
   empty |-- <{(\p: T * Top, p.fst) ((\z:A, z), unit)}> \in <{A -> A}>).
Proof.
left. exists <{A->A}>. exists <{A->A}>. intros T. split. 
  - intros [Haa Ht].
    apply sub_inversion_arrow in Ht. destruct Ht as [U1 [U2 [E [_ HsU2]]]].
    subst T.
    apply sub_inversion_Base in HsU2. subst U2.
    apply sub_inversion_arrow2 in Haa. destruct Haa as [HsU1 _].
    apply sub_inversion_Base in HsU1. subst U1.
    eapply T_App.
    + apply T_Abs. eapply T_Fst.
      apply T_Var. rewrite update_eq. reflexivity.
   + apply T_Pair.
     * apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
     * eapply T_Sub.
       -- apply T_Unit.
       -- apply S_Top.
   -  intros H. apply and_comm.
    apply typing_inversion_app in H. destruct H as [T1 [Hl Hr]].
    apply abs_arrow in Hl. destruct Hl as [HsT1 Hp].
    apply typing_inversion_fst in Hp. destruct Hp as [S1 [S3 [Hp HsS12]]].
     apply typing_inv_var with (U:=<{ T * Top }>) in Hp.
    + apply sub_inversion_Prod2 in Hp. destruct Hp as [HsTS1 _]. clear S3.

    assert (HsT : T <: <{ A->A }>).
      { apply S_Trans with S1.
        - apply HsTS1.
        - apply HsS12. }
    clear HsTS1 S1 HsS12.

    apply typing_inversion_prod in Hr. destruct Hr as [S1 [S2 [Ha [_ HsP]]]].
    apply typing_inversion_abs in Ha. destruct Ha as [S3 [HsArr Hz]].
    assert (HsS12 : <{ S1 * S2 }> <: <{ T * Top }>).
      { eapply S_Trans with T1; assumption. }
    clear T1 HsT1 HsP.
    apply sub_inversion_Prod2 in HsS12. destruct HsS12 as [HsS1 _]. clear S2.
    assert (HsAS3 : <{ A -> S3 }> <: T).
      { eapply S_Trans with S1; assumption. }
    clear S1 HsS1 HsArr.

    apply sub_inversion_arrow in HsT. destruct HsT as [U1 [U2 [E [HsU1 HsU2]]]].
    subst T.
    apply sub_inversion_arrow2 in HsAS3. destruct HsAS3 as [Ha _].
    apply sub_inversion_Base in HsU2. subst U2.
    split.
    * apply S_Arrow; auto.
    * apply S_Arrow; auto.
   + rewrite update_eq. reflexivity.
Qed.

Theorem formal_small_large_2:
  smallest_largest
  (fun T =>
   empty |-- <{(\p:(A->A) * (B->B), p) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
left. exists <{ (A -> A) * (B -> B) }>. exists Ty_Top. intros T. split.
- intros. destruct H. eapply T_App.
  + apply T_Abs. apply T_Sub with (T1:= <{ (A -> A) * (B -> B) }> ).
    * apply T_Var. rewrite update_eq. reflexivity.
    * apply H.
  + apply T_Pair. 
    * apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
    * apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
- intros. apply typing_inversion_app in H. destruct H as [T1 H].
   destruct H. apply typing_inversion_abs in H.
   destruct H as [S2 H]. destruct H.
     eapply typing_inv_var in H1; [|reflexivity]. apply sub_inversion_arrow2 in H.
    destruct H.
assert (HsT : <{ (A -> A) * (B -> B) }>  <: T).
      { apply S_Trans with S2.
        - apply H1.
        - apply H2. }
    clear H2 S2 H1. split.
    + apply HsT.
    + apply S_Top.
Qed.


Theorem formal_small_large_3:
  smallest_largest
  (fun T =>
   (a |-> A) |-- <{(\p : A*T, (p.snd) (p.fst)) (a, \z:A, z)}> \in A).
Proof.
left. exists <{ A -> A }>. exists <{ A -> A }>.
intros T. split.
- intros. eapply T_App.
  + apply T_Abs. apply T_App with A.
    * apply T_Snd with A. apply T_Sub with <{ A * T }>.
      -- apply T_Var. rewrite update_eq. reflexivity.
      -- apply S_Prod.
         ++ apply S_Refl.
         ++ destruct H. apply H0.
     * apply T_Fst with T. apply T_Var.
       rewrite update_eq. reflexivity.
   + apply T_Pair.
     * apply T_Var. rewrite update_eq. reflexivity.
     * eapply T_Sub with <{ A -> A }>.
       -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
      -- destruct H. apply H.
   - intros. apply typing_inversion_app in H.
     destruct H as [T1 H]. destruct H. apply typing_inversion_abs in H.
      destruct H as [S2 H].  destruct H. apply sub_inversion_arrow2 in H.
     apply typing_inversion_app in H1.  destruct H1 as [T2 H1]. destruct H1. 
apply typing_inversion_fst in H2. destruct H2 as [S3 [S4 H2]].
    destruct H2. apply typing_inversion_var in H2. destruct H2 as [S0 H2].
    destruct H2. rewrite update_eq in H2. injection H2. intros. subst.
    apply typing_inversion_prod in H0. destruct H0 as [S5 [S6 H0]].
destruct H0. destruct H5. apply typing_inversion_abs in H5.
destruct H5 as [S8 H5]. destruct H5. destruct H.
assert(<{ S5 * S6 }> <: <{ A * T }>).
+ apply S_Trans with T1.
  * apply H6.
  * apply H.
+ clear H H6. apply sub_inversion_Prod2 in H9. destruct H9.
  assert(<{ A -> S8 }>  <: T).
* apply S_Trans with S6.
 -- apply H5.
 -- apply H6.
* clear H5 H6.  eapply typing_inv_var in H7; [|reflexivity].
  assert(<{ A -> A }> <: <{ A -> S8 }>  ).
  -- apply S_Arrow.
     ++ apply S_Refl.
     ++ apply H7.
  -- assert(<{ A -> A }> <: T ).
     ++ apply S_Trans with <{ A -> S8 }>.
 ** apply H5.
 ** apply H9.
++  apply sub_inversion_Prod2 in H4. apply typing_inversion_snd in H1. 
   destruct H1 as [K1 [K2 H1]]. destruct H1.
    eapply typing_inv_var in H1; [|reflexivity]. 
 apply sub_inversion_Prod2 in H1. destruct H1.
 assert(T <: <{ T2 -> S2 }> ).
{
apply S_Trans with K2.
        - apply H11.
        - apply H10.

}
clear H10 H11. destruct H4.
 assert(A <: T2).
{
apply S_Trans with S3.
        - apply H4.
        - apply H3.

}
clear H2 H3 H4.
assert(<{ T2 -> S2 }> <: <{ A -> A }>).
{
apply S_Arrow.
        - apply H11.
        - apply H8.

}
assert(T <: <{ A -> A }>).
{
apply S_Trans with <{ T2 -> S2 }>.
        - apply H12.
        - apply H2.

}
split.
** apply H6.
** apply H3.
Qed.

Theorem formal_small_large_4:
  smallest_largest
  (fun T =>
  exists S,
     empty |-- <{\p:A*T, (p.snd) (p.fst)}> \in S).
Proof.
assert (H: forall T,
    (exists S, empty |-- <{\p:A*T, (p.snd) (p.fst)}> \in S) <->
    (exists U, T <: <{A->U}>)).
  {
  intros T. split.
  - intros. destruct H as [S H]. apply typing_inversion_abs in H.
    destruct H as [S2 H]. destruct H. apply typing_inversion_app in H0.
    destruct H0 as [T1 H0]. destruct H0. apply typing_inversion_snd in H0.
    destruct H0 as [S1 [S3 H0]]. destruct H0. 
 eapply typing_inv_var in H0; [|reflexivity].  
apply typing_inversion_fst in H1. destruct H1 as [p1 [p2 H1]].
destruct H1.  eapply typing_inv_var in H1; [|reflexivity].
apply sub_inversion_Prod2 in H0. destruct H0.
apply sub_inversion_Prod2 in H1.
destruct H1. assert(T <: <{ T1 -> S2 }>).
{
apply S_Trans with S3.
        - apply H4.
        - apply H2.

}

assert(A <: T1).
{
apply S_Trans with p1.
        - apply H1.
        - apply H3.
}

assert(<{ T1 -> S2 }> <: <{ A -> S2 }>).
{
apply S_Arrow.
        - apply H7.
        - apply S_Refl.
}

assert(T <: <{ A -> S2 }>).
{
apply S_Trans with <{ T1 -> S2 }>.
        - apply H6.
        - apply H8.
}

exists S2.
apply H9.
- intros.
  destruct H as [U H].
  exists <{ A*T -> U }>.
apply T_Abs. apply T_App with A.
+ apply T_Snd with A. eapply T_Sub.
   * apply T_Var. rewrite update_eq. reflexivity.
   *  apply S_Prod. 
    -- apply S_Refl.
    -- apply H.
  + eapply T_Fst. apply T_Var. rewrite update_eq. reflexivity.

}
 right. right. left.
  setoid_rewrite H.  clear H. split.
  - intros [Ts Ht].
    assert (exists U, <{ Top }> <: <{ A->U }>).
      { apply Ht. apply S_Top. }
    destruct H. apply sub_inversion_Top in H. discriminate H.
  - exists <{A->Top}>. intros T. split.
    + intros H. apply sub_inversion_arrow in H. destruct H as [U1 [U2 [E [HsA HsU2]]]].
      subst T. exists U2. apply S_Arrow.
      * apply HsA.
      * apply S_Refl.
    + intros [U Hs]. eapply S_Trans.
      * apply Hs.
      * apply S_Arrow; auto.
Qed.

Definition smallest P :=
  TF (exists TS, forall T, TS <: T <-> P T).

Theorem formal_smallest_1:
  smallest
  (fun T =>
   exists S t,
     empty |-- <{ (\x:T, x x) t }> \in S).
Proof.
 right. intros H. destruct H as [TS H].
 specialize (H Ty_Top).
 assert (TS <: <{ Top }>). { apply S_Top. }
 apply H in H0. destruct H0 as [S [t G]].
apply typing_inversion_app in G.
destruct G as [T1 G]. destruct G.
apply typing_inversion_abs in H0.
destruct H0 as [S2 H0].
destruct H0. apply typing_inversion_app in H2.
destruct H2 as [T2 H2].
destruct H2. eapply typing_inv_var in H3; [|reflexivity]. 
eapply typing_inv_var in H2; [|reflexivity]. 
apply sub_inversion_Top in H2. inversion H2.
Qed.

Theorem formal_smallest_2:
  smallest
  (fun T =>
   empty |-- <{(\x:Top, x) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
  left. exists Ty_Top.
  intros.
  split.
  - intros. eapply T_App.
    +  apply sub_inversion_Top in H.
   apply T_Abs. apply T_Var. rewrite update_eq. 
rewrite H. reflexivity.
    + assert (<{ (A->A)*(B->B)}> <: Ty_Top).
      { apply S_Top. } 
      apply T_Sub with <{ (A->A)*(B->B)}>.
      * apply T_Pair.
         -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
         -- apply T_Abs. apply T_Var. rewrite update_eq. reflexivity.
      * apply S_Top.
   - intros. apply typing_inversion_app in H.
     destruct H as [T1 H]. destruct H. apply typing_inversion_abs in H.
     destruct H as [S2 H]. destruct H. apply sub_inversion_arrow2 in H.
     destruct H.  eapply typing_inv_var in H1; [|reflexivity].
      eapply S_Trans.
     + apply H1.
     + apply H2.
Qed.

End FormalThoughtExercises.
End STLCSub.

(* 2024-08-27 17:05 *)
