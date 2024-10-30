
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
From PLF Require Import STLC.

Module STLCExtendedRecords.

Module FirstTry.

Definition alist (X : Type) := list (string * X).

Inductive ty : Type :=
  | Base     : string -> ty
  | Arrow    : ty -> ty -> ty
  | TRcd     : (alist ty) -> ty.

End FirstTry.

Inductive ty : Type :=
  | Ty_Base : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.


Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* records *)
  | tm_rproj : tm -> string -> tm
  | tm_rnil :  tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0).

Notation "  l ':' t1  '::' t2" := (Ty_RCons l t1 t2) (in custom stlc_ty at level 3, right associativity).
Notation " l := e1 '::' e2" := (tm_rcons l e1 e2) (in custom stlc at level 3, right associativity).
Notation "'nil'" := (Ty_RNil) (in custom stlc_ty).
Notation "'nil'" := (tm_rnil) (in custom stlc).
Notation "o --> l" := (tm_rproj o l) (in custom stlc at level 0).

(** Some examples... *)
Open Scope string_scope.

Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".

Check (Ty_RCons i1 A Ty_RNil).


Definition weird_type := <{{  a : A  :: B }}>.

Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.


Inductive well_formed_ty : ty -> Prop :=
  | wfBase : forall (i : string),
        well_formed_ty <{{ Base i }}>
  | wfArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty <{{ T1 -> T2 }}>
  | wfRNil :
        well_formed_ty <{{ nil }}>
  | wfRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty <{{ i : T1 :: T2 }}>.

Hint Constructors record_ty well_formed_ty : core.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Hint Constructors record_tm : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{ t1 --> i }> =>
      <{ ( [x := s] t1) --> i }>
  | <{ nil }> =>
      <{ nil }>
  | <{ i := t1 :: tr }> =>
     <{ i := [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.

Hint Constructors value : core.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr'}> => if String.eqb i i' then Some t else tlookup i tr'
  | _ => None
  end.

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
         <{v1 t2}> --> <{v1 t2'}>
  | ST_Proj1 : forall t1 t1' i,
        t1 --> t1' ->
        <{ t1 --> i }> --> <{ t1' --> i }>
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        <{ tr --> i }> --> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 --> t1' ->
        <{ i := t1 :: tr2 }> --> <{ i := t1' :: tr2 }>
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 --> tr2' ->
        <{ i := v1 :: tr2 }> --> <{ i := v1 :: tr2' }>

where "t '-->' t'" := (step t t').
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors step : core.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.


Definition context := partial_map ty.


Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc_ty at level 0).

Inductive has_type (Gamma : context) :tm -> ty -> Prop :=
  | T_Var : forall x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |-- x \in T
  | T_Abs : forall x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |-- t12 \in T12 ->
      Gamma |-- \x : T11, t12 \in (T11 -> T12)
  | T_App : forall T1 T2 t1 t2,
      Gamma |-- t1 \in (T1 -> T2) ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- (t1 t2) \in T2
  (* records: *)
  | T_Proj : forall i t Ti Tr,
      Gamma |-- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |-- (t --> i) \in Ti
 | T_RNil :
      Gamma |-- nil \in nil
  | T_RCons : forall i t T tr Tr,
      Gamma |-- t \in T ->
      Gamma |-- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |-- (i := t :: tr) \in (i : T :: Tr)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Lemma typing_example_2 :
  empty |-- (\a : (i1 : (A -> A) :: i2 : (B -> B) :: nil), a --> i2)
            (i1 := (\a : A, a) :: i2 := (\a : B, a) :: nil ) \in (B -> B).
Proof.
  eapply T_App.
  - apply T_Abs.
    + apply wfRCons.
      * apply wfArrow.
        -- apply wfBase.
-- apply wfBase.
   * apply wfRCons.
     -- apply wfArrow.
    ++ apply wfBase.
    ++ apply wfBase.
   -- apply wfRNil.
-- apply RTnil.
* apply RTcons.
 + eapply T_Proj.
   * apply T_Var.
     -- rewrite update_eq. reflexivity.
     -- apply wfRCons.
   ++ apply wfArrow.
  ** apply wfBase. 
** apply wfBase. 
  ++ apply wfRCons.
  ** apply wfArrow.
     ---  apply wfBase. 
---  apply wfBase. 
  ** apply wfRNil.
  **  apply RTnil.
  ++  apply RTcons.
  * simpl. reflexivity.
 - apply T_RCons.
   + apply T_Abs.
      * apply wfBase. 
      * apply T_Var.
    -- rewrite update_eq. reflexivity.
    -- apply wfBase. 
    + apply T_RCons.
      *  apply T_Abs.
       -- apply wfBase. 
       -- apply T_Var.
      ++ rewrite update_eq. reflexivity.
      ++ apply wfBase. 
      * apply T_RNil.
      * apply RTnil.
      * apply rtnil.
    + apply RTcons.
    + apply rtcons.
Qed.

Example typing_nonexample :
  ~ exists T,
     (a |-> <{{ i2 : (A -> A) :: nil }}>) |--
       ( i1 := (\a : B, a) :: a ) \in T.
Proof.
 intros H.
 destruct H as [T H].
 inversion H.
 subst. inversion H7.
Qed.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (y |-> A) |--
     (\a : ( i1 : A :: nil ), a --> i1 )
      ( i1 := y :: i2 := y :: nil ) \in T.
Proof.
   intros y H. destruct H as [T H].
   inversion H. subst. inversion H2. subst. inversion H3.
   subst. inversion H4. subst. inversion H13.
Qed.

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof.
  intros.
  generalize dependent i.
  induction H.
  - intros. simpl in H0. inversion H0.
  - intros. simpl in H1. inversion H1.
 - intros. simpl in H0. inversion H0.
 - intros. simpl in H2. 
    destruct (i0 =? i) eqn:Hi.
   + injection H2. intros. subst.
     apply H.
   + apply IHwell_formed_ty2 in H2.
     apply H2.
Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof. 
  intros.
  generalize dependent tr'.
  induction H.
  - intros. inversion H0.
  - intros. inversion H0.
     + apply rtcons.
     + apply rtcons.
 Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |-- t \in T -> well_formed_ty T.
Proof.
intros. 
generalize dependent T.
generalize dependent Gamma.
induction t.
   - intros. inversion H. subst. apply H2.
   - intros. inversion H. subst. apply IHt1 in H2.
     inversion H2. apply H5.
   - intros. inversion H. subst. apply wfArrow.
     + apply H4. 
     + apply IHt in H5. apply H5.
   - intros. inversion H. subst. apply wf_rcd_lookup in H4.
     + apply H4.
     + apply IHt in H2. apply H2.
   - intros. inversion H. apply wfRNil.
 - intros. inversion H. subst.  apply wfRCons.
   +  apply IHt1 in H3. 
 * apply H3.
   + apply IHt2 in H4. apply H4.
   + apply H6.
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |-- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |-- ti \in Ti.
Proof.
intros. 
remember empty as Gamma.
induction H0.
- subst. inversion H0.
- simpl in H1. inversion H1.
- inversion H.
- inversion H.
- simpl in H1. inversion H1.
- simpl in H1. destruct (i =? i0) eqn:Hi. inversion H.
   + subst. simpl. rewrite Hi. injection H1. intros. subst.
     exists t. split.  
     * reflexivity. 
     *  apply H0_.
  + simpl. rewrite Hi. inversion H. subst.
    apply IHhas_type2.
    * apply H7.
    * reflexivity.
    * apply H1.
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
intros.
remember empty as Gamma.
induction H.
- subst. inversion H.
- left. apply v_abs.
- right. assert (Gamma = empty). apply HeqGamma. apply IHhas_type1 in HeqGamma. destruct HeqGamma.
  + assert (Gamma = empty). apply H1. apply IHhas_type2 in H1. destruct H1.
     * inversion H.
       -- subst. inversion H4.
       -- subst. exists <{ [x:=t2]t12 }>.
          apply ST_AppAbs. apply H1.
       -- subst. inversion H2.
       -- subst. inversion H2.
     * destruct H1 as [t2' H1]. 
       exists <{t1 t2'}>. apply ST_App2.
       -- apply H2.
       -- apply H1.
  + destruct H2 as [t1' H2]. exists <{t1' t2}>. apply ST_App1. apply H2.
- assert (Gamma = empty). apply HeqGamma. apply  IHhas_type in HeqGamma. destruct HeqGamma.
  + eapply lookup_field_in_value in H2.
    * right. destruct H2 as [ti H2].  destruct H2. 
      apply IHhas_type in H1.  destruct H1. 
      -- exists ti.  apply ST_ProjRcd.
         ++ apply H1.
         ++ apply H2.
      -- destruct H1 as [t1 H1]. exists <{ t1 --> i }>.
         apply ST_Proj1. apply H1.
    * subst. apply H.
    * apply H0.
  + right. destruct H2 as [t' H2].  exists <{ t' --> i }>.
    apply ST_Proj1. apply H2.
- left. apply v_rnil.
- assert (Gamma = empty). apply HeqGamma. apply IHhas_type1 in HeqGamma. destruct HeqGamma. 
  + apply IHhas_type2 in H3. destruct H3.
    * left. apply v_rcons.
      -- apply H4.
      -- apply H3.
    * destruct H3 as [tr' H3]. 
      right. exists <{ i := t :: tr' }>.
      apply ST_Rcd_Tail. 
      -- apply H4.
      -- apply H3.
  + destruct H4 as [t' H4]. right.
    exists <{ i := t' :: tr }>.
    apply ST_Rcd_Head. apply H4.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.


Lemma weakening_empty : forall Gamma t T,
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
intros. 
generalize dependent T.
generalize dependent Gamma.
induction t.
- intros. simpl. destruct (x =? s) eqn:Hxs. 
   + apply weakening_empty with (Gamma:=Gamma) in H0.
     apply eqb_eq in Hxs. subst. 
     inversion H.  
     subst. rewrite update_eq in H2. 
     injection H2.
     intros. subst. apply H0.
   + inversion H. subst.  
     apply eqb_neq in Hxs. 
     apply update_neq with (A:=ty) (m:=Gamma) (v:=U) in Hxs.
     rewrite Hxs in H2.
     apply T_Var in H2. apply H2. apply H3.
 - intros. simpl. inversion H. subst. apply T_App with T1.
   + apply IHt1. apply H3.
   + apply IHt2. apply H5.
 - intros. simpl. destruct (x =? s) eqn:Hxs. 
   + apply eqb_eq in Hxs.  subst. inversion H. subst.
     apply T_Abs. 
     * apply H5.
     * rewrite  update_shadow in H6.  apply H6.
   + apply eqb_neq in Hxs. inversion H. subst. apply T_Abs.
     * apply H5.
     * apply IHt. eapply update_permute in Hxs. rewrite <- Hxs.
     apply H6.
 - intros. simpl. inversion H. subst. eapply T_Proj.
   + apply IHt. apply H3.
   + apply H5.
 - intros. simpl. inversion H. apply T_RNil.
 - intros. simpl. inversion H. subst. apply T_RCons.
   + apply IHt1. apply H4.
   + apply IHt2. apply H5.
   + apply H7.
   + inversion H8. 
     * simpl. apply rtnil. 
     * simpl. apply rtcons.
Qed.

Theorem preservation : forall t t' T,
  empty |-- t \in T ->
  t --> t' ->
  empty |-- t' \in T.
Proof with eauto.
  remember empty as Gamma.
  intros.
  generalize dependent t'.
  induction H.
  - intros. subst. inversion H.
  - intros. inversion H1.
  - intros. inversion H1.
    + subst. apply substitution_preserves_typing with T1.
      * inversion H. subst. apply H9.
      * apply H0.
    + subst. eauto.
    + subst. eauto.
  - intros. subst. inversion H1.
    + subst. eapply T_Proj.  
      * apply IHhas_type. 
        -- reflexivity.
        -- apply H5.
      * apply H0.
    + subst. apply lookup_field_in_value with (T:=Tr) (i:=i) (Ti:=Ti)  in H4.
      * destruct H4 as [t0 H4]. destruct H4. rewrite H2 in H6. injection H6.
        intros. subst. apply H3.
      * apply H.
      * apply H0.
  - intros. inversion H0.
  - intros. inversion H3.
    + subst. apply T_RCons.
      * apply IHhas_type1.
        -- reflexivity.
        -- apply H8.
      * apply H0.
      * apply H1.
      * apply H2.
    + subst. apply T_RCons.
      * apply H.
      * apply IHhas_type2.
        -- reflexivity.
        -- apply H9.
      * apply H1.
      * eapply step_preserves_record_tm.
        -- apply H2.
        -- apply H9.       
Qed.  

End STLCExtendedRecords.
(* 2024-09-08 13:03 *)




