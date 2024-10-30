Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
Module RecordSub.

Inductive ty : Type :=
  (* proper types *)
  | Ty_Top   : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  (* record types *)
  | Ty_RNil : ty
  | Ty_RCons : string -> ty -> ty -> ty.

Inductive tm : Type :=
  (* proper terms *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_rproj : tm -> string -> tm
  (* record terms *)
  | tm_rnil :  tm
  | tm_rcons : string -> tm -> tm -> tm.

Declare Custom Entry stlc.
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

Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0).


Inductive record_ty : ty -> Prop :=
  | RTnil :
        record_ty <{{ nil }}>
  | RTcons : forall i T1 T2,
        record_ty <{{ i : T1 :: T2 }}>.

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm <{ nil }>
  | rtcons : forall i t1 t2,
        record_tm <{ i := t1 :: t2 }>.

Inductive well_formed_ty : ty -> Prop :=
  | wfTop :
        well_formed_ty <{{ Top }}>
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

Hint Constructors record_ty record_tm well_formed_ty : core.

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
     <{ i :=  [x := s] t1 :: ( [x := s] tr) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value  <{ \ x : T2, t1 }>
  | v_rnil : value <{ nil }>
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value <{ i := v1 :: vr }>.

Hint Constructors value : core.

Fixpoint Tlookup (i:string) (Tr:ty) : option ty :=
  match Tr with
  | <{{ i' : T :: Tr' }}> =>
      if String.eqb i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:string) (tr:tm) : option tm :=
  match tr with
  | <{ i' := t :: tr' }> =>
      if String.eqb i i' then Some t else tlookup i tr'
  | _ => None
  end.

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

Hint Constructors step : core.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  (* Subtyping between proper types *)
  | S_Refl : forall T,
    well_formed_ty T ->
    T <: T
  | S_Trans : forall S U T,
    S <: U ->
    U <: T ->
    S <: T
  | S_Top : forall S,
    well_formed_ty S ->
    S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
    T1 <: S1 ->
    S2 <: T2 ->
    <{{ S1 -> S2 }}> <: <{{ T1 -> T2 }}>
  (* Subtyping between record types *)
  | S_RcdWidth : forall i T1 T2,
    well_formed_ty <{{ i : T1 :: T2 }}> ->
    <{{ i : T1 :: T2 }}> <: <{{ nil }}>
  | S_RcdDepth : forall i S1 T1 Sr2 Tr2,
    S1 <: T1 ->
    Sr2 <: Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    <{{ i : S1 :: Sr2 }}> <: <{{ i : T1 :: Tr2 }}>
  | S_RcdPerm : forall i1 i2 T1 T2 Tr3,
    well_formed_ty <{{ i1 : T1 :: i2 : T2 :: Tr3 }}> ->
    i1 <> i2 ->
       <{{ i1 : T1 :: i2 : T2 :: Tr3 }}>
    <: <{{ i2 : T2 :: i1 : T1 :: Tr3 }}>

where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Module Examples.
Open Scope string_scope.

Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation j := "j".
Notation k := "k".
Notation i := "i".
Notation A := <{{ Base "A" }}>.
Notation B := <{{ Base "B" }}>.
Notation C := <{{ Base "C" }}>.

Definition TRcd_j  :=
  <{{ j  : (B -> B) :: nil }}>.     (* {j:B->B} *)
Definition TRcd_kj :=
  <{{ k : (A -> A) :: TRcd_j }}>.      (* {k:C->C,j:B->B} *)

Example subtyping_example_0 :
  <{{ C -> TRcd_kj }}> <: <{{ C -> nil }}>.
Proof.
 apply S_Arrow.
 - apply S_Refl. apply wfBase.
 - unfold TRcd_kj. eapply S_Trans.
   + unfold TRcd_j. apply S_RcdPerm.
     * apply wfRCons.
       -- apply wfArrow.
          ++ apply wfBase.
          ++ apply wfBase.
       -- apply wfRCons.
          ++ apply wfArrow.
             ** apply wfBase.
             ** apply wfBase.
          ++ apply wfRNil.
          ++ apply RTnil.
      -- apply RTcons.
      * intros contra. inversion contra.
   + apply S_RcdWidth.
     *  apply wfRCons.
      -- apply wfArrow.
         ++ apply wfBase.
          ++ apply wfBase.
      -- apply wfRCons.
         ++ apply wfArrow.
             **  apply wfBase.
             ** apply wfBase.
         ++ apply wfRNil.
         ++ apply RTnil.
     -- apply RTcons.
Qed.

Example subtyping_example_1 :
  TRcd_kj <: TRcd_j.
Proof with eauto.
  unfold TRcd_kj. unfold TRcd_j.  
  eapply S_Trans.  
  - apply S_RcdPerm.
    + apply wfRCons.
      * apply wfArrow. apply wfBase.
        apply wfBase.
    * apply wfRCons.
     -- apply wfArrow.
           ++ apply wfBase.
          ++ apply wfBase.
    -- apply wfRNil.
    -- apply RTnil.
   * apply RTcons.
    + intros contra. inversion contra.
  - apply S_RcdDepth.
    + apply S_Arrow. 
      * apply S_Refl.
        -- apply wfBase.
   * apply S_Refl.
-- apply wfBase.
    + apply S_RcdWidth. apply wfRCons.
      * apply wfArrow.
        -- apply wfBase.
        -- apply wfBase.
      * apply wfRNil.
      * apply RTnil.
     + apply RTcons.
     + apply RTnil.
Qed.       

Example subtyping_example_2 :
  <{{ Top -> TRcd_kj }}> <:
          <{{ (C -> C) -> TRcd_j }}>.
Proof with eauto.
  apply S_Arrow.
  - apply S_Top. apply wfArrow.
    + apply wfBase.
    + apply wfBase.
  - apply subtyping_example_1.
Qed.

Example subtyping_example_3 :
  <{{ nil -> (j : A :: nil) }}> <:
          <{{ (k : B :: nil) -> nil }}>.
(* {}->{j:A} <: {k:B}->{} *)
Proof with eauto.
  apply S_Arrow.
  - apply S_RcdWidth.
    apply wfRCons.
    + apply wfBase.
    + apply wfRNil.
    + apply RTnil.
  - apply S_RcdWidth.
   apply wfRCons.
   + apply wfBase.
   + apply wfRNil.
   + apply RTnil.
Qed. 

Example subtyping_example_4 :
  <{{ x : A :: y : B :: z : C :: nil }}> <:
  <{{ z : C :: y : B :: x : A :: nil }}>.
Proof with eauto. 
 apply S_Trans with <{{  "x" : A :: "z" : C :: "y" : B :: nil }}>.
 - apply S_RcdDepth. 
   + apply S_Refl.
     apply wfBase.
 + apply S_RcdPerm.
   * apply wfRCons.
     apply wfBase.
     -- apply wfRCons.
        ++ apply wfBase.
        ++ apply wfRNil.
        ++ apply RTnil.
      --  apply RTcons.
    * intros contra.
      inversion contra.
 + apply RTcons.
 + apply RTcons.
  - apply S_Trans with <{{  "z" : C :: "x" : A :: "y" : B :: nil }}>.
    + apply S_RcdPerm.
      * apply wfRCons.
        -- apply wfBase.
        -- apply wfRCons.
           apply wfBase.
           apply wfRCons.
           apply wfBase.
           apply wfRNil.
   apply RTnil.
apply RTcons.
    -- apply RTcons.
   * intros contra. inversion contra.
  + apply S_RcdDepth.
    * apply S_Refl.
      -- apply wfBase.
    * apply S_RcdPerm.
     -- apply wfRCons.
        ++  apply wfBase.
        ++ apply wfRCons.
           ** apply wfBase.
           **  apply wfRNil.
           ** apply RTnil.
        ++ apply RTcons.
      -- intros contra.  inversion contra.
    * apply RTcons.
    * apply RTcons.
Qed.

End Examples.


Lemma subtype__wf : forall S T,
  subtype S T ->
  well_formed_ty T /\ well_formed_ty S.
Proof.
 intros.
 induction H; auto.
 - destruct IHsubtype1.  destruct IHsubtype2.
   auto.
 - destruct IHsubtype1.  destruct IHsubtype2.
   auto.
 - destruct IHsubtype1.  destruct IHsubtype2.
   auto.
 - split. 
   + inversion H. apply wfRCons.
     * inversion H5. apply H10.
     * apply wfRCons.
       -- apply H4.
       -- inversion H5. apply H11.
       -- inversion H5. apply H12.
     *  apply RTcons.
  + apply H.
Qed.
      
Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof.
  intros. 
  induction H.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H0.
  - simpl in H0. inversion H0.
    - simpl in H0. destruct ((i =? i0)%string) eqn:Hn.
      + injection H0. intros. subst. apply H.
      + apply IHwell_formed_ty2.  apply H0.
Qed.

Lemma rcd_types_match : forall S T i Ti,
  subtype S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ subtype Si Ti.
Proof.
 intros. 
 generalize dependent Ti.
 induction H. 
 - intros. exists Ti. split. 
   + apply H0. 
   + apply S_Refl.  apply wf_rcd_lookup in H0. 
     * apply H0.
     * apply H.
  - intros.  apply IHsubtype2 in H1.
    destruct H1 as [Q H1]. destruct H1.
   apply IHsubtype1 in H1.  destruct H1 as [M H1]. 
    destruct H1. exists M. split. 
    + apply H1.
    + eapply S_Trans.
      * apply H3.
      * apply H2.
  - intros. simpl in H0. inversion H0.
  - intros. simpl in H1.  inversion H1. 
  - intros. simpl in H0. inversion H0.
  - intros. simpl in H3. destruct ((i =? i0)%string) eqn:Hn.
    + simpl. rewrite Hn. exists S1. split. 
      * reflexivity. 
      * injection H3. intros. subst. apply H.
    + simpl. rewrite Hn. 
     apply IHsubtype2 in H3. destruct H3 as [Sn H3].
     exists Sn. apply H3. 
 - intros. simpl.  destruct ((i =? i1)%string) eqn:Hn.
   + simpl in H1. rewrite Hn in H1.  destruct ((i =? i2)%string) eqn:Hnn.
     * apply eqb_eq in Hnn. apply eqb_eq  in Hn. rewrite <- Hnn in H0. 
     rewrite <- Hn in H0. unfold not in H0. assert(i=i).
     -- reflexivity.
     -- apply H0 in H2. inversion H2. 
   * injection H1.  intros. subst.  exists Ti.
     split. 
     -- reflexivity. 
     -- inversion H. apply S_Refl. apply H5.
   + destruct ((i =? i2)%string) eqn:Hnn.
     * simpl in H1. rewrite Hn in H1.  rewrite Hnn in H1.
       injection H1. intros. subst Ti. exists T2. inversion H.
    split. 
     -- reflexivity. 
     -- apply S_Refl. inversion H6. apply H11.
     * simpl in H1. rewrite Hn in H1.  rewrite Hnn in H1.
       exists Ti. split. 
       -- apply H1. 
       -- apply wf_rcd_lookup in H1. 
          ++ apply S_Refl. apply H1.
          ++  inversion H.  inversion H6. apply H12.
Qed.  


Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1 -> V2 }}> ->
     exists U1 U2,
       (U = <{{ U1 -> U2 }}> ) /\ (V1 <: U1) /\ (U2 <: V2).
Proof. 
  intros.
  remember <{{ V1 -> V2 }}> as V.
  generalize dependent V1.
  generalize dependent V2.
  induction H.   
  - intros. exists V1, V2. split. 
    + auto.
    + split. 
      * apply S_Refl. subst.  inversion H.  apply H2.
      * apply S_Refl. subst. inversion H.  apply H3.
  - intros. subst.  
    assert(<{{ V1 -> V2 }}> = <{{ V1 -> V2 }}>).
    + reflexivity.
    + apply IHsubtype2 in H1. destruct H1 as [U1 [U2 H1]].
      destruct H1 as [H2 [H3 H4]]. apply IHsubtype1 in H2.
      destruct H2 as [U3 [U4 H2]].   destruct H2 as [H5 [H6 H7]].
      exists U3, U4. split. 
      * apply H5.
      * split.
        -- eapply S_Trans. 
           ++ apply H3.
           ++ apply H6.
        -- eapply S_Trans. 
           ++ apply H7.
           ++ apply H4.
  - intros. inversion HeqV.
  - intros. injection HeqV. intros. subst. exists S1, S2. split.
    + reflexivity. 
    + split. 
      * apply H.
      * apply H0.
  - intros. inversion HeqV.
  - intros. inversion HeqV.
  - intros. inversion HeqV.
Qed. 

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc at level 99, T custom stlc_ty at level 0).


Inductive has_type : context -> tm -> ty -> Prop :=

  | T_Var : forall Gamma (x : string) T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |-- x \in T

  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (x |-> T11; Gamma) |-- t12 \in T12 ->
      Gamma |-- (\ x : T11, t12) \in (T11 -> T12)

  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T1 -> T2) ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t1 t2 \in T2

  | T_Proj : forall Gamma i t T Ti,
      Gamma |-- t \in T ->
      Tlookup i T = Some Ti ->
      Gamma |-- t --> i \in Ti

  (* Subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |-- t \in S ->
      subtype S T ->
      Gamma |-- t \in T

  (* Rules for record terms *)
  | T_RNil : forall Gamma,
      Gamma |-- nil \in nil

  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |-- t \in T ->
      Gamma |-- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |-- i := t :: tr \in (i : T :: Tr)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Module Examples2.
Import Examples.



Definition trcd_kj :=
  <{ k := (\z : A, z) :: j := (\z : B, z) :: nil }>.

Example typing_example_0 :
  empty |-- trcd_kj \in TRcd_kj.
(* empty |-- {k=(\z:A.z), j=(\z:B.z)} : {k:A->A,j:B->B} *)
Proof.
   unfold TRcd_kj. unfold TRcd_j. unfold trcd_kj.
   apply T_RCons.
   - apply T_Abs.
     + apply wfBase.
     + apply T_Var.
       * apply update_eq.
       * apply wfBase.
   - apply T_RCons. 
     + apply T_Abs.
       * apply wfBase.
       * apply T_Var.
         -- apply update_eq.
         -- apply wfBase.
     + apply T_RNil.
     + apply RTnil.
     + apply rtnil.
  - apply RTcons.
  - apply rtcons.
Qed.
       


Example typing_example_1 :
  empty |-- (\x : TRcd_j, x --> j) trcd_kj \in (B -> B).
Proof.
  eapply T_App.
  - apply T_Abs.
    + unfold TRcd_j. apply wfRCons.
      * apply wfArrow.
        -- apply wfBase.
        -- apply wfBase.
      * apply wfRNil.
      * apply RTnil.
    + eapply T_Proj.
      * apply T_Var.
        -- apply update_eq.
         -- unfold TRcd_j. apply wfRCons.
            ++ apply wfArrow.
               ** apply wfBase.
               ** apply wfBase.
            ++  apply wfRNil.
      ++ apply RTnil.
      * simpl. reflexivity. 
   - apply T_Sub with TRcd_kj. 
     + apply typing_example_0.
     + apply subtyping_example_1.
Qed.
     

Example typing_example_2 :
  empty |-- (\ z : (C -> C) -> TRcd_j, (z (\ x : C, x) ) --> j )
            ( \z : (C -> C), trcd_kj ) \in (B -> B).
(* empty |-- (\z:(C->C)->{j:B->B}, (z (\x:C,x)).j)
              (\z:C->C, {k=(\z:A,z), j=(\z:B,z)})
           : B->B *)
Proof.
  eapply T_App.
  - apply T_Abs.
    + apply wfArrow.
      * apply wfArrow.
        -- apply wfBase.
        -- apply wfBase.
      * unfold TRcd_j.
        -- apply wfRCons.
           ++ apply wfArrow.
              ** apply wfBase.
              ** apply wfBase.
           ++  apply wfRNil.
           ++ apply RTnil.
     + eapply T_Proj.
       * eapply T_App.
         -- apply T_Var.
            ++ apply update_eq.
            ++ apply wfArrow.
               ** apply wfArrow.
                  --- apply wfBase.
                  --- apply wfBase.
               ** unfold TRcd_j.
                  --- apply wfRCons.
                      +++ apply wfArrow.
                          *** apply wfBase.
                          *** apply wfBase.
                      +++  apply wfRNil.
                      +++ apply RTnil.
          -- apply T_Abs.
             ++ apply wfBase.
             ++ apply T_Var. 
                ** apply update_eq.
                ** apply wfBase.
        * simpl. reflexivity.
    - apply T_Abs.
      + apply wfArrow.
        * apply wfBase.
        * apply wfBase.
      + apply T_Sub with TRcd_kj.
        *  apply T_RCons.
          -- apply T_Abs.
             ++ apply wfBase.
             ++ apply T_Var. 
                ** apply update_eq.
                ** apply wfBase.
          -- apply T_RCons.
             ++ apply T_Abs.
                ** apply wfBase.
                ** apply T_Var. 
                --- apply update_eq.
                --- apply wfBase.
             ++ apply T_RNil.
             ++ apply RTnil.
             ++ apply rtnil.
          -- apply RTcons.
          -- apply rtcons.
      * apply subtyping_example_1.
Qed.


End Examples2.


Lemma has_type__wf : forall Gamma t T,
  has_type Gamma t T -> well_formed_ty T.
Proof.
  intros. 
  induction H.
  - apply H0.
  - apply wfArrow.
    + apply H.
    + apply IHhas_type.
  - inversion IHhas_type1. apply H4.
  - apply wf_rcd_lookup in H0.
    + apply H0.
    + apply IHhas_type.
  - apply subtype__wf in H0. destruct H0.
   apply H0.
  - apply wfRNil.
  - apply wfRCons.
    + apply IHhas_type1.
    + apply IHhas_type2.
    + apply H1.
Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr --> tr' ->
  record_tm tr'.
Proof.
 intros.
 induction H.
 - inversion H0.
 - inversion H0.
   + apply rtcons.
   + apply rtcons.
Qed.


Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |-- v \in T ->
  Tlookup i T = Some Ti ->
  exists vi, tlookup i v = Some vi /\ empty |-- vi \in Ti.
Proof.
 intros. generalize dependent Ti. 
 induction H0.
 - intros. inversion H.
- intros. simpl in H2. inversion H2.  
- inversion H.
- inversion H.
- intros.  apply rcd_types_match with (S:=S) in H2.   
  + destruct H2 as [S' H2].
    apply IHhas_type with (Ti:=S') in H. 
    * destruct H as [v' H]. destruct H.
      exists v'. split.
      -- apply H.
      -- eapply T_Sub.
         ++ apply H3.
         ++ destruct H2. apply H4. 
     * destruct H2. apply H2.
   + apply H1.
- intros. simpl in H1. inversion H1. 
- intros. simpl in H2. simpl. destruct ((i =? i0)%string).
  + exists t. split. 
    * auto.
    * injection H2. intros. subst.  apply H0_.
  + apply IHhas_type2.
    * inversion H. apply H7.
    * apply H2. 
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
     Gamma |-- s \in (T1 -> T2) ->
     value s ->
     exists x S1 s2,
        s = <{ \ x : S1, s2 }>.
Proof. 
  intros. remember (Ty_Arrow T1 T2) as T.
  generalize dependent T1.  generalize dependent T2. 
  induction H. 
  - intros. inversion H0.
  - intros. exists x, T11, t12. auto.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. subst. apply sub_inversion_arrow in H1.
    destruct H1 as [U1 [U2 H1]]. destruct H1. 
   apply IHhas_type with (T1:=U1) (T2:=U2).
    + apply H0.
    + apply H1.
  - intros. inversion HeqT.
  - intros. inversion HeqT.
Qed.    


Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros. remember empty as Gamma.  
  induction H.
  - subst. inversion H. 
  - left. apply v_abs.
  - subst. destruct IHhas_type1.
    + reflexivity.
    + destruct IHhas_type2.
      * reflexivity.
      * apply canonical_forms_of_arrow_types in H. 
        destruct H as [x [S1 [y H]]]. 
        -- subst. 
        right. exists <{ [x:=t2]y }>.
       apply ST_AppAbs. apply H2.
        -- apply H1.
     * destruct H2 as [t2' H2].
       right. exists <{ t1 t2' }>. apply ST_App2.
       -- apply H1.
       -- apply H2.
    + destruct H1 as [t1' H1].
      right. exists <{ t1' t2 }>. apply ST_App1.
      apply H1.
   - right. subst. destruct IHhas_type.
     + reflexivity. 
     + assert(value t).
       * apply H1.
       * apply lookup_field_in_value with (T:=T) (i:=i) (Ti:=Ti) in H1.
       -- destruct H1 as [vi H1].
          destruct H1. exists vi.
          apply ST_ProjRcd.
          ++ apply H2.
          ++ apply H1.
       -- apply H.
       -- apply H0.
      + destruct H1 as [t' H1].
        exists (tm_rproj t' i). apply ST_Proj1. apply H1.
    - subst.  apply IHhas_type. auto.
    - left. apply v_rnil.
    - subst. destruct IHhas_type1. 
      + auto.
      + destruct IHhas_type2.
        * auto.
        * left. apply v_rcons.
          -- apply H3.
          -- apply H4.
      * right. destruct H4 as [tr' H4].
        exists <{ i := t :: tr' }>. apply ST_Rcd_Tail.
        -- apply H3.
        -- apply H4.
      + destruct H3 as [t' H3]. right.
        exists <{ i := t' :: tr }>. apply ST_Rcd_Head. apply H3.
Qed.


Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \ x : S1, t2 \in T ->
     (exists S2, <{{ S1 -> S2 }}> <: T
              /\ (x |-> S1; Gamma) |-- t2 \in S2).
Proof.
  intros.  remember  <{ \ x : S1, t2  }> as t.
 induction H.  
  - inversion Heqt.
  - injection Heqt. intros. subst. exists T12. 
    split. 
    + apply  S_Refl. apply wfArrow.
      * apply H.
      * apply has_type__wf in H0. apply H0.
    + apply H0.
  - inversion Heqt.
  - inversion Heqt.
 - apply IHhas_type in Heqt. destruct Heqt as [S2 Hn].
    destruct Hn. exists S2. split. 
    + eapply S_Trans.
      * apply H1. 
      * apply H0.
    + apply H2.
  - inversion Heqt.
  - inversion Heqt.
Qed.    


Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x : S1, s2 \in (T1 -> T2) ->
     T1 <: S1
  /\ (x |-> S1) |-- s2 \in T2.
Proof.
  intros. 
 remember  <{ \ x : S1, s2  }> as t.
 remember empty as Gamma.
 remember (Ty_Arrow T1 T2) as T. 
 generalize dependent T1.  generalize dependent T2. 
 induction H. 
 - intros. subst. inversion H.
 - intros. injection Heqt. intros. subst.
   injection HeqT. intros. subst.
   split.
   + apply S_Refl. apply H.
   + apply H0.
 - inversion Heqt.
- inversion Heqt.
 - intros. subst.    apply sub_inversion_arrow in H0. 
   destruct H0 as [U1 [U2 H0]]. destruct H0.  
  destruct IHhas_type with (T2:=U2) (T1:=U1). 
  + reflexivity. 
  + reflexivity. 
  + apply H0.
  + split.
    * destruct H1.  eapply S_Trans.
      -- apply H1.
     -- apply H2.
     * destruct H1. eapply T_Sub.
       -- apply H3.
       -- apply H4.
 - intros.  inversion HeqT. 
 - intros.  inversion HeqT. 
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
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma. 
  induction Ht.
  - intros Gamma' G. simpl.  rename x0 into y.
    destruct (eqb_spec x y) as [Hxy|Hxy]; subst.
    + (* x = y *)
      rewrite update_eq in H.
      injection H as H. subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var; [|assumption].
      rewrite update_neq in H; assumption.
  - (* T_Abs *)
    intros Gamma' G. simpl. rename x0 into y. subst.
    destruct (eqb_spec x y) as [Hxy|Hxy]; apply T_Abs; try assumption.
    + (* x=y *)
      subst. rewrite update_shadow in Ht. assumption.
    + (* x <> y *)
      subst. apply IHHt.
      rewrite update_permute; auto.
  - intros. simpl. eapply T_App.
    + apply IHHt1. apply HeqGamma'.
    + apply IHHt2. apply HeqGamma'.
  - intros. simpl. eapply T_Proj.
    + apply IHHt. apply HeqGamma'.
    + apply H.
  - intros. eapply T_Sub.
    + apply IHHt. apply HeqGamma'.
    + apply H.
  - intros. simpl. apply T_RNil.
  - (* rcons *) (* <=== only new case compared to pure STLC *)
    intros. simpl.  apply T_RCons.
    + apply IHHt1. apply HeqGamma'.
    + apply IHHt2. apply HeqGamma'.
    + apply H.
    + inversion H0.
      * simpl. apply rtnil. 
      * simpl. apply rtcons. 
Qed.


Theorem preservation : forall t t' T,
     empty |-- t \in T ->
     t --> t' ->
     empty |-- t' \in T.
Proof.
  intros. remember empty as Gamma.
  generalize dependent t'. 
  induction H.
  - intros. subst. inversion H.
  - intros. inversion H1. 
  - intros. inversion H1. 
    + subst. apply abs_arrow in H. destruct H.
      eapply substitution_preserves_typing.
        * apply H2.
        * eapply T_Sub.
          -- apply H0.
          -- apply H.
    + subst.  eapply T_App.
      * apply IHhas_type1.
        -- auto.
        -- apply H5.
      * apply H0. 
    + subst.  eapply T_App.
      * apply H.
      * apply IHhas_type2.
        -- auto.
        -- apply H6. 
  - intros.  inversion H1.
    + subst. eapply T_Proj.
      * apply IHhas_type.
        -- reflexivity. 
        -- apply H5.
      * apply H0.
    + subst. apply lookup_field_in_value with (T:=T) (i:=i) (Ti:=Ti) in H4.
      destruct H4 as [s H4].
      destruct H4. rewrite H2 in H6. injection H6. intros. subst.
      apply H3.
    * apply H.
    * apply H0.
  - intros. eapply T_Sub.
    + apply IHhas_type. 
      * apply HeqGamma.
      * apply H1.
    +  apply H0.
  - intros.  inversion H0.
 - intros. inversion H3.
   + subst. apply T_RCons.
     * apply IHhas_type1.
       -- reflexivity.
       -- apply H8.
     * apply H0.
     * apply H1.
     * apply H2.
   + subst.  apply T_RCons.
    * apply H.
     * apply IHhas_type2.
       -- reflexivity.
       -- apply H9.
     * apply H1.
     * eapply step_preserves_record_tm in H2. 
       -- apply H2.
       -- apply H9.
Qed.
End RecordSub.

(* 2024-09-25 10:00 *)




