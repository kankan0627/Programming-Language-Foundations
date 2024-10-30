Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import SmallStep.

Hint Constructors multi : core.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod  : ty -> ty -> ty.

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
    (* pairs *)
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

Notation "{ x }" := x (in custom stlc at level 1, x constr).

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

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ \ y : T, t1 }> =>
      if String.eqb x y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{(t1, t2)}> =>
      <{( ([x:=s] t1), ([x:=s] t2) )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end

  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
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
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> -->  <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
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
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

 Theorem preservation : forall t t' T,
   empty |-- t \in T  ->
   t --> t'  ->
   empty |-- t' \in T.
Proof with eauto.
intros t t' T HT. generalize dependent t'.
remember empty as Gamma.
induction HT;
  intros t' HE; subst; inversion HE; subst...
- (* T_App *)
  inversion HE; subst...
  + (* ST_AppAbs *)
    apply substitution_preserves_typing with T2...
    inversion HT1...
- (* T_Fst *)
  inversion HT...
- (* T_Snd *)
  inversion HT...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Context Invariance *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>
.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.


Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |-- t \in S ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |-- t \in S.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H.
  - intros. apply T_Var. rewrite <- H. symmetry. apply H0. apply afi_var.
  - intros. apply T_Abs. apply IHhas_type. intros. 
     destruct ((x =? x0)%string) eqn:Hn.
    + apply eqb_eq in Hn. subst. rewrite update_eq. rewrite update_eq. reflexivity.
    + apply eqb_neq in Hn. assert (x <> x0).
      * apply Hn. 
      * eapply update_neq in Hn. rewrite Hn. 
        assert (x <> x0). 
        -- apply H2. 
        -- eapply update_neq in H2. rewrite H2. apply H0.
        apply afi_abs.
        ++ apply H3.
        ++ apply H1. 
  - intros. eapply T_App.
    + apply  IHhas_type1. intros. apply H1. apply afi_app1.  apply H2. 
    + apply  IHhas_type2. intros. apply H1. apply afi_app2.  apply H2.
  - intros.  apply T_True. 
  - intros. apply T_False.
  - intros. apply T_If. 
    + apply IHhas_type1. intros. apply H2. apply afi_test0.  apply H3. 
    + apply IHhas_type2. intros. apply H2. apply afi_test1.  apply H3. 
    + apply IHhas_type3. intros. apply H2. apply afi_test2.  apply H3. 
  - intros. apply T_Pair. 
    + apply IHhas_type1. intros. apply H1.  apply afi_pair1. apply H2. 
    + apply IHhas_type2. intros. apply H1.  apply afi_pair2. apply H2. 
  - intros.  eapply T_Fst.
   apply IHhas_type. intros. apply H0.  apply afi_fst. apply H1. 
    - intros.  eapply T_Snd.
   apply IHhas_type. intros. apply H0.  apply afi_snd. apply H1. 
Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof.
 intros. apply eqb_neq in H. apply H. Qed. 

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T', Gamma x = Some T'. 
Proof.
  intros. 
  generalize dependent x. 
  induction H0. 
  - intros. inversion H0. subst. exists T1. apply H.
- intros. inversion H. subst. apply IHhas_type in H6.
  destruct H6 as [T' H6]. eapply update_neq in H4. rewrite H6 in H4.
   exists T'. symmetry. apply H4.
- intros. inversion H.
  + subst. apply IHhas_type1. apply H2.
 + subst. apply IHhas_type2. apply H2.
- intros. inversion H.
- intros.  inversion H.
- intros.  inversion H.
  + subst. apply IHhas_type1. apply H2.
 + subst. apply IHhas_type2. apply H2.
 + subst. apply IHhas_type3. apply H2.
- intros. inversion H.
  + subst. apply IHhas_type1. apply H2.
 + subst. apply IHhas_type2. apply H2.
- intros. inversion H. subst.  apply IHhas_type. apply H3.
- intros. inversion H. subst.  apply IHhas_type. apply H3.
Qed.

Corollary typable_empty__closed : forall t T,
    empty |-- t \in T ->
    closed t.
Proof. 
 intros.
 remember empty as Gamma.
unfold closed.
intros. intros contra. 
 induction H.
 - subst. inversion H. 
 - inversion contra. subst. apply free_in_context with (T:=T1) (Gamma:=(x0 |-> T2))in H5.
   + destruct H5 as [T' H5]. eapply update_neq  in H3. rewrite H5 in H3. inversion H3.
   + apply H.
 - inversion contra. 
   + subst. apply IHhas_type1. 
     * reflexivity. 
     * apply H3. 
   + subst. apply IHhas_type2. 
     * reflexivity. 
     * apply H3. 
  - inversion contra.
  - inversion contra.
  - inversion contra.
    + subst. apply IHhas_type1.
      * reflexivity. 
      * apply H4. 
+ subst. apply IHhas_type2.
      * reflexivity. 
      * apply H4. 
+ subst. apply IHhas_type3.
      * reflexivity. 
      * apply H4. 
  - inversion contra.
     + subst. apply IHhas_type1.
      * reflexivity. 
      * apply H3. 
 + subst. apply IHhas_type2.
      * reflexivity. 
      * apply H3. 
  - inversion contra. subst.  apply IHhas_type.
 + reflexivity. 
     + apply H2. 
  - inversion contra. subst.  apply IHhas_type.
 + reflexivity. 
     + apply H2. 
Qed.

Ltac solve_by_value_nf :=
  match goal with | H : value ?v, H' : ?v --> ?v' |- _ =>
  exfalso; apply value__normal in H; eauto
  end.

Lemma step_deterministic :
   deterministic step.
Proof.
unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2. 
 - inversion Hy2.
   + subst. auto. 
+ subst. inversion H3.
 + subst. solve_by_value_nf.
 - inversion Hy2.
   + subst. inversion Hy1.
   + subst. apply IHHy1 in H2. subst. reflexivity. 
   + subst. solve_by_value_nf.
   - inversion Hy2.
+ subst. solve_by_value_nf.
   + subst. solve_by_value_nf.
   + subst. apply IHHy1 in H4. subst. reflexivity. 
- inversion Hy2.
  + reflexivity. 
  + subst.  inversion H3. 
- inversion Hy2.
  + reflexivity. 
  + subst.  inversion H3. 
- inversion Hy2.
  + subst. inversion Hy1.
  + subst. inversion Hy1.
  + subst. apply IHHy1 in H3. subst. reflexivity. 
- inversion Hy2.
  + subst. apply IHHy1 in H2. subst. reflexivity. 
 + subst. solve_by_value_nf.
- inversion Hy2.
  + subst. solve_by_value_nf.
+ subst. apply IHHy1 in H4. subst. reflexivity.
- inversion Hy2.  
  + subst. apply IHHy1 in H0. subst. reflexivity.
  + subst. inversion Hy1.
    * subst. solve_by_value_nf.
    * subst. solve_by_value_nf. 
- inversion Hy2.
  + subst. inversion H2.
    * subst. solve_by_value_nf.
    * subst. solve_by_value_nf.
  + auto.
- inversion Hy2.
  + subst. apply IHHy1 in H0. subst. reflexivity.
  + subst. inversion Hy1. 
    * subst. solve_by_value_nf. 
     * subst. solve_by_value_nf. 
- inversion Hy2.
  + subst. inversion H2.
    * subst. solve_by_value_nf.
    * subst. solve_by_value_nf.
  + auto.
Qed.

Definition halts (t:tm) : Prop := exists t', t -->* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros. unfold halts.
  exists v. split.
  - apply multi_refl.
  - apply H.
Qed.


Fixpoint R (T:ty) (t:tm) : Prop :=
  empty |-- t \in T /\ halts t /\
  (match T with
   | <{ Bool }> => True
   | <{ T1 -> T2 }> => (forall s, R T1 s -> R T2 <{t s}> )

   (* ... edit the next line when dealing with products *)
   | <{ T1 * T2 }> => R T1 <{ t.fst }> /\ R T2 <{ t.snd }>
   end).

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros. 
  induction T;  destruct H;  destruct H0;  apply H0.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> empty |-- t \in T.
Proof.
  intros. 
  induction T.
  - simpl in H. destruct H. apply H.
   - simpl in H. destruct H. apply H.
 - simpl in H. destruct H. apply H.
Qed.

Lemma step_preserves_halting :
  forall t t', (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST. unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]]. 
  destruct STM.  
   + exfalso; apply value__normal in V; eauto.
   + rewrite (step_deterministic _ _ _ ST H). exists z. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.

Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof.
  induction T.
  - intros. simpl in H0. destruct H0. destruct H1. 
    simpl. split.    
    + eapply preservation.
      * apply H0. 
      * apply H.
   + split.  
     * apply step_preserves_halting in H. apply H.  apply H1. 
     * auto.
 - intros.   simpl in H0. destruct H0. destruct H1. 
   simpl.  split. 
   + eapply preservation.
      * apply H0. 
      * apply H.
   +  split.  
     * apply step_preserves_halting in H. apply H.  apply H1. 
     * intros.   eapply IHT2. 
        -- apply ST_App1. apply H. 
        -- apply H2. apply H3. 
- intros. simpl in H0. destruct H0. destruct H1. destruct H2.
   simpl.  split. 
   + eapply preservation.
     * apply H0. 
      * apply H.
   + split. 
* apply step_preserves_halting in H. apply H.  apply H1. 
     * split.  
       -- eapply IHT1.
          ++ eapply ST_Fst1. apply H. 
          ++ apply H2.
       -- eapply IHT2.
          ++ apply ST_Snd1. apply H. 
          ++ apply H3.
Qed. 

Lemma multistep_preserves_R : forall T t t',
  (t -->* t') -> R T t -> R T t'.
Proof. 
 intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.


Lemma step_preserves_R' : forall T t t',
  empty |-- t \in T -> (t --> t') -> R T t' -> R T t.
Proof.
  induction T.  
  - intros.
    + simpl. split. 
      * apply H. 
      * split. 
        -- apply step_preserves_halting in H0. 
           apply H0. eapply R_halts. apply H1. 
       -- auto. 
   - intros. simpl. split. 
     + apply H.
     + split. 
       * apply step_preserves_halting in H0.
         apply H0. eapply R_halts. apply H1.  
       * intros. simpl in H1. destruct H1.  destruct H3. eapply IHT2.
         -- apply T_App with T1.
            ++ apply H.
            ++ apply R_typable_empty in H2. apply H2.
          -- apply ST_App1. apply H0.
          -- apply H4. apply H2.
  - intros. simpl.  split.  
    + apply H. 
    + split. 
      * apply step_preserves_halting in H0.
         apply H0. eapply R_halts. apply H1. 
      * simpl in H1. destruct H1.  destruct H2. destruct H3. split. 
       -- eapply IHT1.
          ++ eapply T_Fst. apply H.
          ++ apply ST_Fst1. apply H0.
       ++ apply H3.
       -- eapply IHT2.
          ++ eapply T_Snd. apply H.
          ++ apply ST_Snd1. apply H0.
       ++ apply H4.
Qed.

Lemma multistep_preserves_R' : forall T t t',
  empty |-- t \in T -> (t -->* t') -> R T t' -> R T t.
Proof. 
 intros. 
 induction H0.
 - apply H1.
 - eapply step_preserves_R'.
   + apply H.
   + apply H0.
   + apply IHmulti. 
     * eapply preservation.
       -- apply H. 
       -- apply H0.
     * apply H1.
Qed.


Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
end.

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.


Fixpoint lookup {X:Set} (k : string) (l : list (string * X)) : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if String.eqb j k then Some x else lookup k l'
  end.


Fixpoint drop {X:Set} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.


Inductive instantiation : tass -> env -> Prop :=
| V_nil :
    instantiation nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation c e ->
    instantiation ((x,T)::c) ((x,v)::e).


Lemma vacuous_substitution : forall t x,
     ~ appears_free_in x t ->
     forall t', <{ [x:=t']t }> = t.
Proof. 
induction t.
  - intros. simpl. destruct ((x =? s)%string) eqn:Hx.
    + apply eqb_eq in Hx. subst. exfalso. apply H. apply afi_var.
    + reflexivity. 
  - intros. assert ((appears_free_in x t1) \/ (~ appears_free_in x t1)).
    + auto.
    + assert ((appears_free_in x t2) \/ (~ appears_free_in x t2)).
      * auto.
      * destruct H0.
        -- destruct H1.
           ++ exfalso. apply H. apply afi_app1. apply H0.
           ++ exfalso. apply H. apply afi_app1. apply H0.
        -- destruct H1. 
           ++ exfalso. apply H. apply afi_app2. apply H1.
           ++ simpl. apply IHt1 with (t':=t') in H0.
               apply IHt2 with (t':=t') in H1.
               rewrite H0. rewrite H1. reflexivity. 
   - intros. simpl. destruct ((x =? s)%string) eqn:Hx.
     +  reflexivity. 
     + apply eqb_neq in Hx. assert ((appears_free_in x t0) \/ (~ appears_free_in x t0)).
       * auto.
       * destruct H0. 
         -- exfalso.  apply H. eapply afi_abs.
            ++ intros contra. unfold not in Hx. symmetry in contra.
         apply Hx in contra. inversion contra.
       ++  apply  H0.
         -- eapply IHt in H0. rewrite H0.  reflexivity. 
    - intros. simpl. reflexivity. 
    - intros. simpl. reflexivity. 
    - intros. simpl. assert ((appears_free_in x t1) \/ (~ appears_free_in x t1)).
    + auto.
    + assert ((appears_free_in x t2) \/ (~ appears_free_in x t2)).
      * auto. 
      * assert ((appears_free_in x t3) \/ (~ appears_free_in x t3)).
        -- auto. 
        -- destruct H0. 
           ++ exfalso. apply H. apply afi_test0. apply H0.
           ++ eapply IHt1 in H0. rewrite H0. destruct H1.
              ** exfalso. apply H. apply afi_test1. apply H1.
              ** eapply IHt2 in H1. rewrite H1. destruct H2.
                 --- exfalso. apply H. apply afi_test2. apply H2.
                 --- eapply IHt3 in H2. rewrite H2. reflexivity.
     - intros. simpl. assert ((appears_free_in x t1) \/ (~ appears_free_in x t1)).
    + auto.
    + assert ((appears_free_in x t2) \/ (~ appears_free_in x t2)).
      * auto. 
      * destruct H0. 
        -- exfalso. apply H. apply afi_pair1. apply H0.
        -- eapply IHt1 in H0. rewrite H0. destruct H1. 
           ++ exfalso. apply H. apply afi_pair2. apply H1.
           ++ eapply IHt2 in H1. rewrite H1. reflexivity. 
    - intros. simpl. assert ((appears_free_in x t) \/ (~ appears_free_in x t)).
      + auto. 
      + destruct H0. 
        * exfalso. apply H.  apply afi_fst. apply H0. 
        * eapply IHt in H0. rewrite H0. reflexivity. 
    - intros. simpl. assert ((appears_free_in x t) \/ (~ appears_free_in x t)).
      + auto. 
      + destruct H0. 
        * exfalso. apply H.  apply afi_snd. apply H0. 
        * eapply IHt in H0. rewrite H0. reflexivity. 
Qed.

Lemma subst_closed: forall t,
     closed t ->
     forall x t', <{ [x:=t']t }> = t.
Proof. 
  intros t H. 
  unfold closed in H. 
  intros. apply vacuous_substitution with (x:=x) (t':=t') in H. apply H.
Qed.

Lemma subst_not_afi : forall t x v,
    closed v -> ~ appears_free_in x <{ [x:=v]t }>.
Proof.
  induction t.
  - intros. simpl.  destruct ((x =? s)%string) eqn:Hx.
    + apply eqb_eq in Hx.  subst. 
     unfold closed in H. apply H. 
    + unfold closed in H. intros contra. inversion contra. apply eqb_neq in Hx. apply Hx in H2.
      inversion H2. 
  - intros. simpl. 
  intros contra. inversion contra.
  + apply IHt1 with (x:=x) in H.  apply H.  apply H2. 
 + apply IHt2 with (x:=x) in H.  apply H.  apply H2.
 - intros. simpl.  destruct ((x =? s)%string) eqn:Hx.
   + apply eqb_eq in Hx.  subst.  intros contra. 
     inversion contra. apply H3. reflexivity. 
   +  apply eqb_neq in Hx. intros contra.  inversion contra. subst. 
  apply IHt  with (x:=x) in H. apply H. apply H5. 
  - intros. simpl. intros contra.  inversion contra. 
  -  intros. simpl. intros contra.  inversion contra. 
  - intros. simpl.  intros contra. inversion contra.
    + apply IHt1  with (x:=x) in H. apply H. apply H2.  
+ apply IHt2  with (x:=x) in H. apply H. apply H2. 
+ apply IHt3  with (x:=x) in H. apply H. apply H2.
  - intros. simpl. intros contra. inversion contra. 
    + apply IHt1  with (x:=x) in H. apply H. apply H2.  
+ apply IHt2  with (x:=x) in H. apply H. apply H2.
  -  intros. simpl. intros contra. inversion contra. 
apply IHt  with (x:=x) in H. apply H. apply H2.
  -   intros. simpl. intros contra. inversion contra. 
apply IHt  with (x:=x) in H. apply H. apply H2.  

Qed.

Axiom classic : forall P:Prop, P \/ ~ P.

Lemma duplicate_subst : forall t' x t v,
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
 intros.  apply subst_not_afi with (t:=t') (x:=x) in H. 
 induction t'.
 - simpl. simpl in H.  destruct ((x =? s)%string) eqn:Hx.
   + eapply vacuous_substitution in H. apply H.
   + simpl. rewrite Hx. reflexivity. 
 - simpl. simpl in H.  assert ((appears_free_in x <{ [x := v] t'1 }>) \/ (~ appears_free_in x <{ [x := v] t'1 }>)).
    + auto.
    + assert ((appears_free_in x <{ [x := v] t'2 }> ) \/ (~ appears_free_in x <{ [x := v] t'2 }> )).
      * auto.
      * destruct H0. 
        -- exfalso. apply H. apply afi_app1. apply H0.
        -- apply IHt'1 in H0. rewrite H0. 
           destruct H1. 
           ++ exfalso. apply H. apply afi_app2. apply H1.
           ++ apply IHt'2 in H1. rewrite H1.  reflexivity. 
  -  assert ((appears_free_in x <{[x := v] t'}> ) \/ (~ appears_free_in x <{ [x := v] t'}>)). 
     + apply classic.
     + destruct ((x =? s)%string) eqn:Hx.
       * simpl. rewrite Hx. simpl. rewrite Hx.  reflexivity. 
       * simpl. rewrite Hx. simpl. rewrite Hx. destruct H0.  
         -- exfalso. apply H. simpl.  rewrite Hx. apply afi_abs. apply eqb_neq in Hx. 
            ++ intros contra. symmetry in contra.  apply Hx in contra. 
            inversion contra. 
            ++ apply H0. 
         -- apply IHt' in H0. rewrite H0. reflexivity. 
  - simpl. reflexivity. 
- simpl. reflexivity.
 - assert ((appears_free_in x <{ [x := v] t'1 }> ) \/ (~ appears_free_in x <{ [x := v] t'1 }> )).
      * apply classic.
      * destruct H0. 
        -- exfalso.  apply H. simpl. apply afi_test0.  apply H0. 
        -- apply IHt'1 in H0. simpl.  rewrite H0. 
      assert ((appears_free_in x <{ [x := v] t'2 }> ) \/ (~ appears_free_in x <{ [x := v] t'2 }> )).
           ++ apply classic.
          ++ destruct H1. 
       ** exfalso.  apply H. simpl. apply afi_test1.  apply H1. 
        ** apply IHt'2 in H1. rewrite H1.  
 assert ((appears_free_in x <{ [x := v] t'3 }> ) \/ (~ appears_free_in x <{ [x := v] t'3 }> )).
            --- apply classic.
            --- destruct H2. 
                +++ exfalso.  apply H. simpl. apply afi_test2.  apply H2. 
              +++ apply IHt'3 in H2. rewrite H2. reflexivity. 
   - simpl. assert ((appears_free_in x <{ [x := v] t'1 }> ) \/ (~ appears_free_in x <{ [x := v] t'1 }> )).
      * apply classic.
      * destruct H0.  
        -- exfalso.  apply H. simpl. apply afi_pair1.  apply H0. 
        -- apply IHt'1 in H0. simpl.  rewrite H0. 
      assert ((appears_free_in x <{ [x := v] t'2 }> ) \/ (~ appears_free_in x <{ [x := v] t'2 }> )).
           ++ apply classic.
          ++ destruct H1. 
 ** exfalso.  apply H. simpl. apply afi_pair2.  apply H1. 
        ** apply IHt'2 in H1. rewrite H1. reflexivity.
  - simpl.  assert ((appears_free_in x <{ [x := v] t' }> ) \/ (~ appears_free_in x <{ [x := v] t'}> )).
    + apply classic.
    + destruct H0.
      * exfalso.  apply H. simpl. apply afi_fst.  apply H0.
      * apply IHt' in H0. rewrite H0. reflexivity.
 - simpl.  assert ((appears_free_in x <{ [x := v] t' }> ) \/ (~ appears_free_in x <{ [x := v] t'}> )).
    + apply classic.
    + destruct H0.
      * exfalso.  apply H. simpl. apply afi_snd.  apply H0.
      * apply IHt' in H0. rewrite H0. reflexivity.
Qed.

Lemma swap_subst : forall t x x1 v v1,
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof. 
  intros. 
  induction t. 
  - simpl. destruct ((x =? s)%string) eqn:Hx.
   + destruct ((x1 =? s)%string) eqn:Hx1.
     * apply eqb_eq in Hx. apply eqb_eq in Hx1. rewrite <- Hx1 in Hx. apply H in Hx. inversion Hx.  
      * apply eqb_eq in Hx. subst. simpl. rewrite eqb_refl. apply subst_closed with (x:=x1) (t':=v1)in H0. 
        rewrite H0. reflexivity.
  + destruct ((x1 =? s)%string) eqn:Hx1.
    * apply eqb_eq in Hx1. subst. simpl. rewrite eqb_refl.  
       apply subst_closed with (x:=x) (t':=v)in H1. rewrite H1. reflexivity.
    * simpl. rewrite Hx. rewrite Hx1. reflexivity.
 - simpl. rewrite IHt1. rewrite IHt2. reflexivity. 
 - simpl. destruct ((x =? s)%string) eqn:Hx.
   + destruct ((x1 =? s)%string) eqn:Hx1.
     * apply eqb_eq in Hx. apply eqb_eq in Hx1. subst. simpl.  rewrite eqb_refl. reflexivity.
     * apply eqb_eq in Hx. subst. simpl. rewrite Hx1. rewrite eqb_refl. simpl. reflexivity.
   + destruct ((x1 =? s)%string) eqn:Hx1.
     * apply eqb_eq in Hx1. subst. simpl.  rewrite eqb_refl.  rewrite Hx. simpl. reflexivity.
     * simpl. rewrite Hx. rewrite Hx1. rewrite IHt. reflexivity.
 - simpl.  reflexivity.
- simpl.  reflexivity.
- simpl. rewrite IHt1, IHt2, IHt3. reflexivity.
- simpl.  rewrite IHt1, IHt2. reflexivity.
- simpl. rewrite IHt. reflexivity.
- simpl. rewrite IHt. reflexivity.
Qed.


Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof. 
 intros. 
 induction ss. 
 - intros. simpl. reflexivity. 
 - simpl. destruct a. eapply subst_closed in H. rewrite H. apply IHss.
Qed.

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
    msubst env <{ [x:=v]t }> = <{ [x:=v] { msubst (drop x env) t } }> .
Proof.
   intros. 
   generalize dependent t. 
   induction env0.
   - intros. simpl.  reflexivity. 
   - intros. simpl. destruct a.  destruct ((s =? x)%string) eqn:Hx.
     + apply eqb_eq in Hx. subst. simpl in H0. destruct H0.  apply IHenv0 with t in H1.
       rewrite <- H1. apply duplicate_subst with (t':=t) (x:=x) (t:=t0) in H.
       rewrite H. reflexivity.
     + simpl. simpl in H0. destruct H0.  apply eqb_neq in Hx. 
       eapply swap_subst in Hx. 
       * rewrite <- Hx.  apply IHenv0 with (<{ [s := t0] t }>) in H1. apply H1. 
       * apply H0. 
       * apply H. 
Qed. 
 
Lemma msubst_var: forall ss x, closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None => tm_var x
  end.
Proof. 
  intros. 
  induction ss. 
  - simpl. reflexivity.
  - simpl. destruct a. destruct ((s =? x)%string ) eqn:Hx.
    + simpl in H. destruct H. eapply msubst_closed in H.
      apply H.
    + apply IHss.  simpl in H. destruct H. apply H0.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (drop x ss) t} }>.
Proof.
  intros. 
  generalize dependent t.
  induction ss. 
  - intros. simpl. reflexivity. 
  - intros. simpl. destruct a.  destruct ((s =? x)%string ) eqn:Hx.
    + rewrite IHss. reflexivity. 
    + simpl. apply IHss.  
Qed.

Lemma msubst_app : forall ss t1 t2,
    msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
Proof.
  induction ss. 
  - simpl. reflexivity.
  - intros. simpl. destruct a. apply IHss.
Qed.

Lemma mupdate_lookup : forall (c : tass) (x:string),
    lookup x c = (mupdate empty c) x.
Proof.
  induction c.
  - simpl. intros. reflexivity.
  - intros. simpl. destruct a. destruct ((s =? x)%string ) eqn:Hx.
    + apply eqb_eq in Hx.  subst. rewrite update_eq.  reflexivity. 
    + apply eqb_neq in Hx. eapply update_neq in Hx.
      rewrite Hx. rewrite IHc. reflexivity.
Qed.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
      mupdate Gamma (drop x c) x'
       = if String.eqb x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c.
  - simpl. intros. destruct ((x =? x')%string ) eqn:Hx.
    + reflexivity.
    + reflexivity.
  - intros. destruct ((x =? x')%string ) eqn:Hxx.
    + simpl. destruct a. destruct ((s =? x)%string ) eqn:Hsx.
      * specialize IHc with (Gamma:=Gamma) (x:=x) (x':=x').
        rewrite Hxx in IHc. apply IHc.
      * simpl. apply eqb_neq in Hsx.  
        specialize IHc with (Gamma:=Gamma) (x:=x) (x':=x').
        rewrite Hxx in IHc.
        apply eqb_eq in Hxx. subst. eapply update_neq in Hsx. 
        rewrite Hsx. apply IHc.
     + simpl. destruct a. destruct ((s =? x)%string ) eqn:Hsx.
       * apply eqb_eq in Hsx. subst. 
         specialize IHc with (Gamma:=Gamma) (x:=x) (x':=x').
         rewrite Hxx in IHc. apply eqb_neq in Hxx.
         eapply update_neq in Hxx.  rewrite Hxx. apply IHc. 
       * simpl.  specialize IHc with (Gamma:=Gamma) (x:=x) (x':=x').
         rewrite Hxx in IHc. destruct ((s =? x')%string ) eqn:Hsx'.
         -- apply eqb_eq in Hsx'. subst. rewrite update_eq. rewrite update_eq.
            reflexivity.
         -- apply eqb_neq in Hsx'. assert (s<>x').
            ++ apply Hsx'.
            ++ eapply update_neq in Hsx'. 
            rewrite Hsx'. eapply update_neq in H. rewrite H. rewrite IHc.
            reflexivity.
Qed.  

Lemma instantiation_domains_match: forall {c} {e},
    instantiation c e ->
    forall {x} {T}, lookup x c = Some T -> exists t, lookup x e = Some t.
Proof. 
  induction c. 
  - intros. simpl in H0. inversion H0.
  - intros.  simpl in H0. destruct a. destruct ((s =? x)%string ) eqn:Hsx.
    + injection H0. intros. subst. inversion H. subst.  
      simpl.  rewrite Hsx. exists v.  reflexivity. 
    + inversion H.  subst. 
      simpl. rewrite Hsx. apply IHc with T.
      * apply H7.
      * apply H0.
Qed.

Lemma instantiation_env_closed : forall c e,
  instantiation c e -> closed_env e.
Proof. 
  induction c. 
  - induction e. 
     + intros. simpl. reflexivity.
     + intros. inversion H. 
  - induction e. 
    + intros. simpl. reflexivity.
    + intros. inversion H. 
    subst. simpl. split.
     * apply R_typable_empty in H5. apply typable_empty__closed in H5. apply H5. 
     * apply IHc. apply H6.
Qed.

Lemma instantiation_R : forall c e,
    instantiation c e ->
    forall x t T,
      lookup x c = Some T ->
      lookup x e = Some t -> R T t.
Proof.
   induction c. 
  - induction e. 
    + intros. simpl in H0. inversion H0.
    + intros. simpl in H0. inversion H0.
  - induction e. 
    + intros. simpl in H1. inversion H1.
    + intros. simpl in H1. inversion H. subst. simpl in H0.
      destruct ((x0 =? x)%string ) eqn:Hxx. 
      * injection H0. injection H1. intros. subst. apply H7.
      * eapply IHc in H8.
        -- apply H8.
        -- apply H0.
        -- apply H1.
Qed.

Lemma instantiation_drop : forall c env,
    instantiation c env ->
    forall x, instantiation (drop x c) (drop x env).
Proof.
   induction c. 
   - induction env0.
     + intros. simpl. apply H. 
     + intros. inversion H. 
  - induction env0.
     + intros. inversion H. 
     + intros. inversion H. subst.  simpl.  
       destruct ((x0 =? x)%string ) eqn:Hxx.  
       * apply IHc. apply H6. 
       * apply V_cons.
         -- apply H4. 
         -- apply H5. 
         -- apply IHc. apply H6. 
Qed.

Lemma multistep_App2 : forall v t t',
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
  intros.
  induction H0.
  - intros. apply multi_refl.
  - apply multi_step with <{ v y }>.
    + apply ST_App2. 
      * apply H. 
      * apply H0.
   + apply IHmulti.
Qed.

Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, (mupdate Gamma c) |-- t \in S ->
     Gamma |-- { (msubst e t) } \in S.
Proof. 
   induction c. 
   - induction e.
     + intros. simpl in H0. simpl. apply H0.
     + intros. inversion H. 
   - induction e.
     + intros. inversion H.
     + intros. inversion H. subst. 
       simpl. apply IHc. 
       * apply H7.
       * eapply substitution_preserves_typing. simpl in H0. 
         -- apply H0.
         -- apply R_typable_empty in H6.  apply H6.
Qed.


Lemma multistep_preserves_typing : forall t t' T,
  empty |-- t \in T ->
  t -->* t' ->
  empty |-- t' \in T.
Proof.
  intros t t' T Ht He. induction He.
  - apply Ht.
  - apply IHHe. apply preservation with x; assumption.
Qed.

Lemma multistep_If : forall t1 t1' t2 t3,
  (t1 -->* t1') ->
  <{ if t1 then t2 else t3 }> -->* <{ if t1' then t2 else t3 }>.
Proof.
  intros t1 t1' t2 t3 He. induction He.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_If. apply H.
    + apply IHHe.
Qed.

Lemma multistep_Pair1 : forall t1 t1' t2,
  t1 -->* t1' ->
  <{ (t1, t2) }> -->* <{ (t1', t2) }>.
Proof.
  intros t1 t1' t2 He. induction He.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Pair1. apply H.
    + apply IHHe.
Qed.

Lemma multistep_Pair2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  <{ (v1, t2) }> -->* <{ (v1, t2') }>.
Proof.
  intros v1 t2 t2' Hv He. induction He.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Pair2.
      * apply Hv.
      * apply H.
    + apply IHHe.
Qed.

Lemma multistep_Fst : forall t t',
  t -->* t' ->
  <{ t.fst }> -->* <{ t'.fst }>.
Proof.
  intros t t' He. induction He.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Fst1. apply H.
    + apply IHHe.
Qed.

Lemma multistep_Snd : forall t t',
  t -->* t' ->
  <{ t.snd }> -->* <{ t'.snd }>.
Proof.
  intros t t' He. induction He.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Snd1. apply H.
    + apply IHHe.
Qed.

Lemma msubst_if : forall ss t0 t1 t2,
  msubst ss <{ if t0 then t1 else t2 }> = tm_if (msubst ss t0) (msubst ss t1) (msubst ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - simpl. destruct a. apply IHss.
Qed.

Lemma msubst_pair : forall ss t1 t2,
  msubst ss <{ (t1, t2) }> = tm_pair (msubst ss t1) (msubst ss t2).
Proof.
  induction ss; intros.
  - reflexivity.
  - simpl. destruct a. apply IHss.
Qed.

Lemma msubst_fst : forall ss t, msubst ss <{ t.fst }> = tm_fst (msubst ss t).
Proof.
  induction ss; intros.
  - reflexivity.
  - simpl. destruct a. apply IHss.
Qed.

Lemma msubst_snd : forall ss t, msubst ss <{ t.snd }> = tm_snd (msubst ss t).
Proof.
  induction ss; intros.
  - reflexivity.
  - simpl. destruct a. apply IHss.
Qed.

Lemma msubst_R : forall c env t T,
    (mupdate empty c) |-- t \in T ->
    instantiation c env ->
    R T (msubst env t).
Proof.

  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  induction HT; intros.
  - (* T_Var *)
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var. rewrite P. auto. eapply instantiation_env_closed; eauto.
  - (* T_Abs *)
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT : empty |-- \x : T2, {msubst (drop x env0) t1 } \in (T2 -> T1) ).
    { eapply T_Abs. eapply msubst_preserves_typing.
      { eapply instantiation_drop; eauto. }
      eapply context_invariance.
      { apply HT. }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_spec x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a. unfold update, t_update.
        destruct (String.eqb s x0); auto. }
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]]. 
     pose proof (multistep_preserves_R _ _ _ P H0).
     apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply multi_trans. eapply multistep_App2; eauto.
       eapply multi_R.
       simpl. rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T2)::c)).
          intros. unfold update, t_update, lookup. destruct (String.eqb x x0); auto.
       constructor; auto.
  - (* T_App *)
    rewrite msubst_app. 
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2. fold R in P1. auto.
 
  - unfold R. split. 
    + eapply msubst_preserves_typing.
      * apply V.
      * apply T_True.
    + split.
      * assert (closed <{ true }>). 
        -- unfold closed. intros. intros contra. inversion contra.
        --  eapply msubst_closed in H0. rewrite H0. unfold halts. exists <{ true }>.
            auto.
      * reflexivity. 
   - unfold R. split. 
    + eapply msubst_preserves_typing.
      * apply V.
      * apply T_False.
    + split.
      * assert (closed <{ false }>). 
        -- unfold closed. intros. intros contra. inversion contra.
        --  eapply msubst_closed in H0. rewrite H0. unfold halts. exists <{ false }>.
            auto.
      * reflexivity.
   -   assert (Ht : empty |-- {msubst env0 <{if t1 then t2 else t3}>} \in T1).
      { apply (msubst_preserves_typing _ _ V).
        apply context_invariance with Gamma. { apply T_If; assumption. }
        intros x _. rewrite <- mupdate_lookup. apply H. } 
    destruct (IHHT1 _ H _ V) as [HtSt1 [[v1 [HeV1 HvV1]] _]].
    pose proof (multistep_preserves_typing _ _ _ HtSt1 HeV1) as HtV1. 
    assert (He :
      msubst env0 <{ if t1 then t2 else t3 }> -->*
      tm_if v1 (msubst env0 t2) (msubst env0 t3)).
      { rewrite msubst_if. apply multistep_If. apply HeV1. }
    destruct HvV1; try solve [inversion HtV1]; clear HtV1.
    + eapply multistep_preserves_R'.
      * apply Ht.
      * apply (multi_trans _ _ _ _ _ He).
        apply multi_R. apply ST_IfTrue.
      * apply (IHHT2 _ H _ V).
    + eapply multistep_preserves_R'.
      * apply Ht.
      * apply (multi_trans _ _ _ _ _ He).
        apply multi_R. apply ST_IfFalse.
      * apply (IHHT3 _ H _ V).
  - (* T_Pair *) simpl.
      specialize (IHHT1 _ H _ V). specialize (IHHT2 _ H _ V).
      assert (Ht : empty |-- {msubst env0 <{ (t1, t2) }>} \in (T1 * T2)).
        { apply (msubst_preserves_typing _ _ V).
          apply context_invariance with Gamma. { apply T_Pair; assumption. }
          intros x _. rewrite <- mupdate_lookup. apply H. }
      destruct (R_halts IHHT1) as [v1 [HeV1 HvV1]].
      destruct (R_halts IHHT2) as [v2 [HeV2 HvV2]].
      assert (He : tm_pair (msubst env0 t1) (msubst env0 t2) -->* <{ (v1, v2) }>).
        { eapply multi_trans. { apply multistep_Pair1. apply HeV1. }
          apply multistep_Pair2; assumption. }
      rewrite msubst_pair in *.
      repeat split.
      * apply Ht.  
      * exact (ex_intro _ <{(v1, v2)}> (conj He (v_pair _ _ HvV1 HvV2))). 
      * eapply multistep_preserves_R'.
          { apply T_Fst with T2. apply Ht. }
          { eapply multi_trans. { exact (multistep_Fst _ _ He). }
            apply multi_R. apply ST_FstPair; assumption. }
          { exact (multistep_preserves_R _ _ _ HeV1 IHHT1). }
      * eapply multistep_preserves_R'.
          { apply T_Snd with T1. apply Ht. }
          { eapply multi_trans. { exact (multistep_Snd _ _ He). }
            apply multi_R. apply ST_SndPair; assumption. } 
          { exact (multistep_preserves_R _ _ _ HeV2 IHHT2). }
  - (* T_Fst *) destruct (IHHT _ H _ V) as [_ [_ [HR _]]].
    fold R in HR. rewrite msubst_fst. apply HR.
  - (* T_Snd *) destruct (IHHT _ H _ V) as [_ [_ [_ HR]]].
    fold R in HR. rewrite msubst_snd. apply HR.
Qed.

Theorem normalization : forall t T, empty |-- t \in T -> halts t.
Proof.
 intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.

Locate ex_intro.

Check ex_intro.

(* 2024.10.01 9:51 *)
