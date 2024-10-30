Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-deprecated-syntactic-definition".
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
From Coq Require Import Lists.List. Import Datatypes.
Check length.
Import Nat.

(* mutable references*)

Module STLCRef.

Inductive ty : Type :=
  | Ty_Nat : ty
  | Ty_Unit : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref : ty -> ty.


Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tm_var    : string -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ    : tm -> tm
  | tm_pred    : tm -> tm
  | tm_mult    : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.

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

Notation "{ x }" := x (in custom stlc at level 0, x constr).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

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

Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2) t1 }>.
Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc at level 3).

Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st <{ unit }>.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof.
  intros. 
generalize dependent n.
 induction l.
  - intros. rewrite replace_nil. reflexivity.
  - induction n. 
    + simpl. reflexivity.
  + simpl. specialize IHl with n. rewrite IHl. reflexivity.
Qed. 

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st =  *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l.
    + simpl. auto.
    + simpl. apply IHst'. simpl in Hlen. lia.
Qed.



Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof.
  intros.
unfold store_lookup.
 generalize dependent l1.
 generalize dependent l2.
induction st.
 - intros. destruct l1.
   + destruct l2.
     * unfold not in H. 
       assert(0=0).
       -- reflexivity.
       -- apply H in H0. inversion H0.
     * simpl. reflexivity.
   + destruct l2.
     * simpl. reflexivity.
     * simpl.  reflexivity.
 - intros. destruct l1.
   + destruct l2.
     * unfold not in H. 
       assert(0=0).
       -- reflexivity.
       -- apply H in H0. inversion H0.
     * simpl. reflexivity.
   + destruct l2.
     * simpl. reflexivity.
     * simpl. apply IHst.  lia.
Qed.

Reserved Notation "t '/' st '-->' t' '/' st'"
  (at level 40, st at level 39, t' at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st -->  tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc { length st } }> / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> /  st --> <{ ref t1' }> /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         <{ !(loc l) }> / st --> <{ { store_lookup l st } }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'

where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).


Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).

Definition context := partial_map ty.

Theorem cyclic_store:
  exists t,
    t / nil -->*
    <{ unit }> / (<{ \x:Nat, (!(loc 1)) x }> :: <{ \x:Nat, (!(loc 0)) x }> :: nil).
Proof.
      exists <{ 
      (\y:Ref (Nat->Nat), 
        (\z: Ref (Nat->Nat), y := (\x:Nat, (! z) x))
        (ref (\x:Nat, (! y) x)))
        (ref (\x:Nat,0)) }>.
    eapply multi_step. 
    { apply ST_App2.
      - apply v_abs.
      - apply ST_RefValue. apply v_abs. }
  eapply multi_step.
    { apply ST_AppAbs. apply v_loc. }
  simpl.
  eapply multi_step.
    { apply ST_App2.
      - apply v_abs.
      - apply ST_RefValue. apply v_abs. }
  eapply multi_step.
    { apply ST_AppAbs. apply v_loc. }
  simpl.
  apply multi_R.
  apply ST_Assign.
  - apply v_abs.
  - simpl. lia.
Qed.

Definition store_ty := list ty.


Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST <{ Unit }>.

Reserved Notation "Gamma ';' ST '|--' t '\in' T"
                  (at level 40, t custom stlc, T custom stlc at level 0).

Inductive has_type (ST : store_ty) : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma ; ST |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      update Gamma x T2 ; ST |-- t1 \in T1 ->
      Gamma ; ST |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma ; ST |-- t1 \in (T2 -> T1) ->
      Gamma ; ST |-- t2 \in T2 ->
      Gamma ; ST |-- t1 t2 \in T1
  | T_Nat : forall Gamma (n : nat),
      Gamma ; ST |-- n \in Nat
  | T_Succ : forall Gamma t1,
      Gamma ; ST |-- t1 \in Nat ->
      Gamma ; ST |-- succ t1 \in Nat
  | T_Pred : forall Gamma t1,
      Gamma ; ST |-- t1 \in Nat ->
      Gamma ; ST |-- pred t1 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma ; ST |-- t1 \in Nat ->
      Gamma ; ST |-- t2 \in Nat ->
      Gamma ; ST |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma ; ST |-- t1 \in Nat ->
      Gamma ; ST |-- t2 \in T0 ->
      Gamma ; ST |-- t3 \in T0 ->
      Gamma ; ST |-- if0 t1 then t2 else t3 \in T0
  | T_Unit : forall Gamma,
      Gamma ; ST |-- unit \in Unit
  | T_Loc : forall Gamma l,
      l < length ST ->
      Gamma ; ST |-- (loc l) \in (Ref {store_Tlookup l ST })
  | T_Ref : forall Gamma t1 T1,
      Gamma ; ST |-- t1 \in T1 ->
      Gamma ; ST |-- (ref t1) \in (Ref T1)
  | T_Deref : forall Gamma t1 T1,
      Gamma ; ST |-- t1 \in (Ref T1) ->
      Gamma ; ST |-- (! t1) \in T1
  | T_Assign : forall Gamma t1 t2 T2,
      Gamma ; ST |-- t1 \in (Ref T2) ->
      Gamma ; ST |-- t2 \in T2 ->
      Gamma ; ST |-- (t1 := t2) \in Unit
 

where "Gamma ';' ST '|--' t '\in' T" := (has_type ST Gamma t T).

Hint Constructors has_type : core.

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     empty; ST |-- { store_lookup l st } \in {store_Tlookup l ST }).

Locate length. 

Locate nth.

Theorem store_not_unique:
  exists st, exists ST1, exists ST2,
    store_well_typed ST1 st /\
    store_well_typed ST2 st /\
    ST1 <> ST2.
Proof.
remember (<{\x:Nat, (!(loc 1)) x}> :: <{\x:Nat, (!(loc 0)) x}> :: nil) as st.
  assert (Ht : forall T,
    store_well_typed (Ty_Arrow Ty_Nat T :: Ty_Arrow Ty_Nat T :: nil) st).
    { intros T. subst st. split.
      - reflexivity.
      - simpl. intros l H. destruct l; [| destruct l].
        + unfold store_lookup. simpl. unfold store_Tlookup. simpl. 
         apply T_Abs. apply T_App with Ty_Nat.
          * apply T_Deref. apply T_Loc. simpl. lia.
          * apply T_Var. reflexivity.
        + apply T_Abs. apply T_App with Ty_Nat.
          * apply T_Deref. apply T_Loc. simpl. lia.
          * apply T_Var. reflexivity.
        + lia. }
  exists st. eexists. eexists. split; [| split].
  - apply (Ht Ty_Nat).
  - apply (Ht Ty_Unit).
  - discriminate.
Qed.

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).
Hint Constructors extends : core.

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof.
 intros. unfold store_Tlookup.
generalize dependent l.
induction H0. 
 - intros. simpl in H. inversion H.
 - intros. simpl. destruct l.
   + reflexivity.
   + apply IHextends. simpl in H. lia.
Qed.

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof.
intros. 
generalize dependent l. 
induction H0. 
 - intros. simpl in H. inversion H.
 - intros. simpl. destruct l.
   + lia. 
   + simpl in H. 
     assert(l < length ST).
     * lia.
     * apply IHextends in H1. lia.
Qed.

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST. 
Proof.
intros. induction ST.
- simpl. apply extends_nil.
- simpl. apply extends_cons. apply IHST.
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
induction ST. 
- apply extends_nil.
- apply extends_cons. apply IHST.
Qed.

Lemma weakening : forall Gamma Gamma' ST t T,
     includedin Gamma Gamma' ->
     Gamma ; ST |-- t \in T ->
     Gamma' ; ST |-- t \in T.
Proof.
  intros Gamma Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.


Lemma weakening_empty : forall Gamma ST t T,
     empty ; ST |-- t \in T ->
     Gamma ; ST |-- t \in T.
Proof.
  intros Gamma ST t T.
  eapply weakening. 
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x U t v T,
  (update Gamma x U); ST |-- t \in T ->
  empty ; ST |-- v \in U ->
  Gamma ; ST |-- [x:=v]t \in T.
Proof.
  intros Gamma ST x U t v T Ht Hv. 
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *) 
    rename s into y. destruct (String.eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption. 
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y.
    destruct (String.eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty ; ST |-- t \in {store_Tlookup l ST} ->
  store_well_typed ST (replace l t st).
Proof.
intros. 
remember empty as Gamma.
generalize dependent l. 
 induction st.
- intros. simpl in H. inversion H.
- intros. simpl.  unfold store_well_typed. split.
  + rewrite length_replace.
  unfold store_well_typed in H0. 
destruct H0.  apply H0.
  + intros. destruct(l0 =? l) eqn:Heq.
    * apply eqb_eq in Heq. subst.   apply lookup_replace_eq with (t:=t0) in H.
      rewrite H. apply H1.
    * apply eqb_neq in Heq.  apply lookup_replace_neq with (t:=t0) (st:= (a :: st)) in Heq.
      rewrite Heq. destruct l0.
      -- unfold store_lookup. simpl. destruct H0.
           specialize H3 with (l:=0). simpl in H3.
            assert (0 < S (length st)).
            ++ lia.
            ++ apply H3 in H4.
               unfold store_lookup in H4. simpl in H4. apply H4.
       --  unfold store_well_typed in H0. destruct H0. apply H3.
             rewrite length_replace in H2. apply H2. 
Qed.   

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma ; ST |-- t \in T ->
  Gamma ; ST' |-- t \in T.
Proof. 
intros Gamma ST ST' t T H G. 
generalize dependent ST'.
induction G.
- intros. apply T_Var with (ST:=ST') in H. apply H.
- intros. apply T_Abs. apply IHG. apply H.
- intros. apply T_App with T2.
  + apply IHG1. apply H.
 + apply IHG2. apply H.
- intros. apply T_Nat.
-  intros. apply T_Succ. apply IHG. apply H.
- intros. apply T_Pred. apply IHG. apply H.
- intros. apply T_Mult. 
  + apply IHG1. apply H.
  + apply IHG2. apply H.
- intros. apply T_If0. 
   + apply IHG1. apply H.
  + apply IHG2. apply H.
+ apply IHG3. apply H.
- intros. apply T_Unit. 
- intros. assert(l < length ST). 
  + apply H.
  + apply extends_lookup with (ST':=ST') in H.
    * rewrite <- H. apply T_Loc. apply length_extends with (l:=l) in H0.
      --  apply H0.
       --  apply H1.
     * apply H0.
- intros. apply T_Ref. apply IHG. apply H.
- intros. apply T_Deref. apply IHG. apply H.
- intros.  apply T_Assign with T2. 
   + apply IHG1. apply H.
   + apply IHG2. apply H.
Qed.

Locate sub_diag.

Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  empty ; ST |-- t1 \in T1 ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).

Proof with auto.
  intros.
  unfold store_well_typed in *.
  destruct H as [Hlen Hmatch].
  rewrite app_length, add_comm. simpl.
  rewrite app_length, add_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      apply <- Nat.succ_lt_mono in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST.
        -- apply extends_app.
        -- apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- Hlen.
      rewrite sub_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. } 
      rewrite app_nth2; [|lia].
      rewrite sub_diag. simpl. assumption.
Qed.


Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
intros. 
rewrite app_nth2.
- rewrite sub_diag. simpl. reflexivity.
- lia.
Qed.

Locate app_nth2.

Theorem preservation : forall ST t t' T st st',
  empty ; ST |-- t \in T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     empty ; ST' |-- t' \in T /\
     store_well_typed ST' st'.
Proof.
intros.
remember empty as Gamma. 
generalize dependent t'.
generalize dependent st'.
induction H.
- intros. subst. inversion H.
- intros. inversion H1.
- intros. inversion H2.
  + subst. exists ST. split. 
    * apply extends_refl.
    * split. 
      --  inversion H.  subst. eapply substitution_preserves_typing. 
         ++ apply H6. 
         ++  apply H1. 
     -- apply H0.
+ subst. destruct IHhas_type1 with (st':=st') (t':=t1'). 
  * reflexivity.  
  * apply H4. 
  * exists x0. destruct H3. split. 
    -- apply H3. 
    -- split. 
       ++ apply T_App with T2. 
          ** destruct H5. apply H5. 
          ** apply store_weakening with (Gamma:=empty) (t:=t2) (T:=T2) in H3.
             --- apply H3. 
             --- apply H1. 
        ++ destruct H5. apply H6.
+ subst. destruct IHhas_type2 with (st':=st') (t':=t2').
  * reflexivity.  
  * apply H9. 
  * exists x0. destruct H3. split.   
          -- apply H3. 
    -- split. 
++ apply T_App with T2. 
          ** apply store_weakening with (Gamma:=empty) (t:=t1) (T:=(Ty_Arrow T2 T1)) in H3.
             --- apply H3. 
             --- apply H. 
        ** destruct H4. apply H4.
       ++ destruct H4. apply H6.
- intros. inversion H1. 
- intros. inversion H1.
  + subst. exists ST. split. 
    * apply extends_refl. 
    * split. 
      -- apply T_Nat.
      --  apply H0.
+ intros. subst.  
  destruct IHhas_type with (st':=st') (t':=t1'). 
   * reflexivity. 
   * apply H3. 
   * exists x0. 
     destruct H2 as [H5 [H6 H7]].
     split. 
     -- apply H5. 
     -- split. 
        ++ apply T_Succ. apply H6. 
        ++ apply H7. 
- intros. inversion H1. 
  + subst. exists ST. 
    split.
    * apply extends_refl.
* split.
  -- apply T_Nat.
  -- apply H0. 
+ subst. destruct IHhas_type with (st':=st') (t':=t1'). 
  * reflexivity.
  * apply H3.
  * exists x0. destruct H2 as [H5 [H6 H7]].
     split. 
    -- apply H5. 
    -- split. 
       ++ apply T_Pred. apply H6.
       ++ apply H7.
- intros. inversion H2. 
  + subst. exists ST.
    split.
    * apply extends_refl.
    * split. 
      -- apply T_Nat.
      -- apply H0. 
+  subst. destruct IHhas_type1 with (st':=st') (t':=t1').
  * reflexivity. 
  * apply H4. 
  * exists x0.  destruct H3 as [H5 [H6 H7]].
    split. 
    -- apply H5. 
    -- split. 
       ++ apply T_Mult.
          ** apply H6.
          ** apply store_weakening with (Gamma:=empty) (t:=t2) (T:= Ty_Nat) in H5.
             --- apply H5.
             --- apply H1.
      ++ apply H7.
+ subst. destruct IHhas_type2 with (st':=st') (t':=t2').
    * reflexivity. 
  * apply H9. 
  * exists x0.  destruct H3 as [HA [HB HC]].
    split. 
    -- apply HA. 
    -- split.
       ++ apply T_Mult.
          **  apply store_weakening with (Gamma:=empty) (t:=t1) (T:= Ty_Nat) in HA.
             --- apply HA.
             --- apply H.
          ** apply HB.
      ++ apply HC.
- intros. inversion H3.
  + subst.  destruct IHhas_type1 with (st':=st') (t':=t1').
    * reflexivity.
    * apply H5.
    * exists x0. destruct H4 as [HA [HB HC]].
      split. 
      -- apply HA.
      -- split. 
         ++ apply T_If0.
            ** apply HB.
            ** apply store_weakening with (Gamma:=empty) (t:=t2) (T:= T0) in HA. 
               --- apply HA.
               --- apply H1.
            ** apply store_weakening with (Gamma:=empty) (t:=t3) (T:= T0) in HA.
               --- apply HA.
               --- apply H2.
          ++ apply HC.
   + subst. exists ST.
     split. 
     * apply extends_refl.
     * split.
       -- apply H1. 
       -- apply H0.
   + subst. exists ST. 
    split. 
     * apply extends_refl.
     * split.
       -- apply H2. 
       -- apply H0.
- intros. inversion H1. 
- intros. inversion H1. 
- intros. inversion H1. 
  + subst. exists (ST ++ T1::nil). split. 
    * apply extends_app. 
    * split. 
      -- assert (store_Tlookup (length ST) (ST ++ T1 :: nil) = T1).
         ++ unfold store_Tlookup. rewrite nth_eq_last. reflexivity.
         ++ remember (ST ++ T1 :: nil) as STA. rewrite <- H2. unfold store_well_typed in H0.
            destruct H0. rewrite H0. apply T_Loc. rewrite HeqSTA. rewrite app_length.
            simpl. rewrite H0. lia.
      -- apply store_well_typed_app.
         ++ apply H0.
         ++ apply H.
+ subst. destruct IHhas_type with (st':=st') (t':=t1').
  * reflexivity. 
  * apply H3.
  * exists x0.  destruct H2 as [HA [HB HC]]. split. 
    -- apply HA.
    -- split. 
       ++ apply T_Ref. apply HB.
       ++ apply HC.
- intros. inversion H1. 
  + subst. inversion H. subst. exists ST. split. 
    * apply extends_refl.
     * split.
       -- unfold store_well_typed in H0.
         destruct H0. specialize H2 with (l:=l).
         apply H2 in H3. apply H3.
       -- apply H0.
  + subst. destruct IHhas_type with (st':=st') (t':=t1').
    * reflexivity. 
  * apply H3.
  * exists x0.  destruct H2 as [HA [HB HC]]. split. 
    -- apply HA.
    -- split.   
 ++ apply T_Deref. apply HB.
       ++ apply HC.
- intros. inversion H2.
  + subst. exists ST. split.
    * apply extends_refl.
     * split.
    -- apply T_Unit. 
    -- apply assign_pres_store_typing. 
       ++ apply H9. 
       ++ apply H0. 
       ++ inversion H.  subst. apply H1. 
  + subst. destruct IHhas_type1 with (st':=st') (t':=t1').
     * reflexivity. 
  * apply H4.
  * exists x0.  destruct H3 as [HA [HB HC]]. split. 
    -- apply HA.
    -- split. 
       ++ eapply T_Assign.
          ** apply HB.
         ** apply store_weakening with (Gamma:=empty) (t:=t2) (T:=T2) in HA.
            --- apply HA.
            --- apply H1.
       ++ apply HC.
  + subst. destruct IHhas_type2 with (st':=st') (t':=t2').
     * reflexivity. 
  * apply H9.
 * exists x0.  destruct H3 as [HA [HB HC]]. split. 
    -- apply HA.
    -- split. 
       ++ eapply T_Assign.
      
         ** apply store_weakening with (Gamma:=empty) (t:=t1) (T:=(Ty_Ref T2)) in HA.
            --- apply HA.
            --- apply H.
       ** apply HB.
       ++ apply HC.
Qed.

Locate empty. 

Theorem progress : forall ST t T st,
  empty ; ST |-- t \in T ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
Proof. 
  intros ST t T st H. 
  remember empty as Gamma.
  induction H. 
  - intros. subst. inversion H.
  - intros. left. apply v_abs.
  - intros. destruct IHhas_type1.
    + subst. reflexivity.
    + apply H1. 
    + right. destruct IHhas_type2.
      * subst. reflexivity.
      * apply H1. 
      * inversion H. subst. 
        -- inversion H4. 
        -- subst. exists <{ [x0 := t2] t0 }>.
           exists st. apply ST_AppAbs. 
           apply H3.
       -- subst. inversion H2.
       -- subst. inversion H2. 
       -- subst. inversion H2.
      * destruct H3 as [t2' [st' H3]].
        exists <{ {t1} {t2'} }>, st'.
   apply ST_App2. 
         -- apply H2.
         -- apply H3.
    + right. destruct H2 as [t1' [st' H2]].
        exists <{ {t1'} {t2} }>, st'.
        apply ST_App1. apply H2.
   - intros. left. apply v_nat. 
   - intros. destruct IHhas_type. 
     + apply HeqGamma.
     + apply H0.
     + inversion H. 
       * subst. inversion H2.
       * subst. inversion H1.
       * subst. right. exists (tm_const (S n)), st.
         apply ST_SuccNat.
       * subst. inversion H1.
       * subst. inversion H1.
       * subst. inversion H1. 
       *  subst.  inversion H1. 
      *  subst.  inversion H1. 
  + right. destruct H1 as [t1' [st' H2]]. exists <{ succ t1' }>, st'. 
    apply ST_Succ. apply H2.
- intros. subst. destruct IHhas_type.
  + reflexivity. 
  + apply H0.
  + inversion H. 
 * subst. inversion H2.
       * subst. inversion H1.
       * subst. right. exists (tm_const (n - 1)), st.
         apply ST_PredNat.
       * subst. inversion H1.
       * subst. inversion H1.
       * subst. inversion H1. 
       *  subst.  inversion H1. 
      *  subst.  inversion H1. 
  + right. destruct H1 as [t1' [st' H2]]. exists <{ pred t1' }>, st'. 
    apply ST_Pred. apply H2.
- intros. subst. destruct IHhas_type1.
    + reflexivity.
    + apply H1. 
    + right. destruct IHhas_type2.
      * reflexivity.
      * apply H1.
      * inversion H.
        -- subst. inversion H4.
 -- subst. inversion H2.
 -- subst. inversion H0.
    ++ subst. inversion H4.
 ++ subst. inversion H3.
 ++ subst. exists (tm_const (n * n0)), st.
    apply ST_MultNats.
    ++ subst. inversion H3.
++ subst. inversion H3.
++ subst. inversion H3.
 ++ subst. inversion H3.
++ subst. inversion H3.
-- subst. inversion H2.
-- subst. inversion H2.
-- subst. inversion H2.
-- subst. inversion H2.
-- subst. inversion H2.
* destruct H3 as [t2' [st' H3]].
  -- exists <{ {t1} * {t2'} }>, st'. apply ST_Mult2.
     ++ apply H2.
     ++ apply H3.
+ destruct H2 as [t1' [st' H2]].
  * right. exists <{ {t1'} * {t2} }>, st'.
    apply ST_Mult1. apply H2. 
- intros. right. destruct IHhas_type1. 
  + apply HeqGamma.
  + apply H2.
  + inversion H.
    * subst. inversion H4.
 * subst. inversion H3.
 * subst.  destruct n.
   -- exists t2, st. apply ST_If0_Zero.
   -- exists t3, st.  apply ST_If0_Nonzero.
 * subst. inversion H3.
 * subst. inversion H3.
 * subst. inversion H3.
 * subst.  inversion H3.
 * subst. inversion H3.
+ subst. destruct H3 as [t1' [st' H3]].
  exists  <{ if0 t1' then t2 else t3 }> , st'.
  apply ST_If0. apply H3.
- intros. left. apply v_unit.
- intros. left. apply v_loc.
- intros. destruct IHhas_type.
  + apply HeqGamma.
  + apply H0.
  + right. exists <{ loc { length st } }>, (st ++ t1::nil).
    apply ST_RefValue. apply H1.
  + destruct H1 as [t1' [st' H1]].
    right. exists <{ ref t1' }>, st'.
    apply ST_Ref. apply H1.
- intros. destruct IHhas_type.
  + apply HeqGamma.
  + apply H0.
  + right. inversion H.
    * subst. inversion H2.
    * subst. inversion H1.
* subst. inversion H1.
* subst. exists <{ { store_lookup l st } }>, st.
  apply ST_DerefLoc. unfold store_well_typed in H0. destruct H0.
  rewrite H0 in H5. apply H5.
* subst. inversion H1.
* subst. inversion H1.
+ destruct H1 as [t1' [st' H1]].
  right. exists <{ ! t1' }> , st'.
  apply ST_Deref. apply H1. 
- intros. destruct IHhas_type1. 
  + apply HeqGamma.
  + apply H1.
  + right. destruct IHhas_type2.
    * apply  HeqGamma. 
    * apply H1. 
    * inversion H.
      -- subst. inversion H4.
      -- subst. inversion H2.
      -- subst. inversion H2. 
      -- subst. exists <{ unit }> , (replace l t2 st).
         apply ST_Assign.
         ++ apply H3.
         ++ unfold store_well_typed in H1. destruct H1. 
            rewrite H1 in H7.  apply H7.
      -- subst. inversion H2. 
      -- subst. inversion H2. 
    * destruct H3 as [t2' [st' H3]].
      exists <{ t1 := t2' }>, st'.
      apply ST_Assign2. 
      -- apply H2.
      -- apply H3. 
   + destruct H2 as [t1' [st' H2]].
     right. exists <{ t1' := t2 }> , st'. 
    apply ST_Assign1. apply H2. 
Qed.

Module ExampleVariables.
Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".
End ExampleVariables.
Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  <{ \x : Unit, (!r) unit }>.

Definition loop :=
  <{ (\r : Ref (Unit -> Unit), (( r := loop_fun ); ( (! r) unit ) )) (ref (\x : Unit, unit)) }> .

Lemma loop_typeable : exists T, empty; nil |-- loop \in T.
Proof.
 
  eexists. unfold loop. unfold loop_fun.
  eapply T_App.
  - eapply  T_Abs.
    eapply T_App.
    + eapply T_Abs. eapply T_App.
      * eapply T_Deref. eapply T_Var.
    rewrite update_neq; [|intros; discriminate].
    rewrite update_eq. reflexivity.
     * auto.
    + eapply T_Assign.
      * eapply T_Var. rewrite update_eq. reflexivity.
      * eapply T_Abs.
        eapply T_App.
        -- eapply T_Deref. eapply T_Var. reflexivity.
        -- apply T_Unit. 
   - apply T_Ref. apply  T_Abs. apply T_Unit. 
Qed.

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.

Definition multistep1 := (step_closure step).

Notation "t1 '/' st '-->+' t2 '/' st'" :=
        (multistep1 (t1,st) (t2,st'))
        (at level 40, st at level 39, t2 at level 39).

Ltac print_goal := match goal with |- ?x => idtac x end.

Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | compute];
            try solve [apply multi_refl]).

Lemma loop_steps_to_loop_fun :
  loop / nil -->*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.

Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil -->+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.

  Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one.
  unfold store_lookup. simpl. 
  apply ST_AppAbs...
Qed.

End RefsAndNontermination.
End STLCRef.



