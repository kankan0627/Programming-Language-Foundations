Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.


Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof. unfold aequiv. intros. simpl. lia. Qed.


Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof. unfold bequiv. intros. simpl. 
       assert (Q: st X - st X = 0).
       -  lia.
       - rewrite Q. simpl. reflexivity. Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').


Theorem skip_left : forall c,
  cequiv  <{ skip; c }>  c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H5. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st'.
    + apply H.
    + apply E_Skip.
Qed.

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.  
  intros c1 c2 st st'. 
  split; intros H.
  - (* -> *)
    inversion H. 
    + apply H6.
    + inversion H5.
  - (* <- *)
    apply E_IfTrue.
    + reflexivity.
    +  apply H.
Qed. 

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof. intros b c1 c2.
       intros H st st'. 
       split.
       - intros H1. remember <{ if b then c1 else c2 end }> as ifdef eqn:Heqifdef.
         induction H1.
         + inversion Heqifdef.
         + inversion Heqifdef.
         + inversion Heqifdef.
         + inversion Heqifdef. subst. assumption.
         + injection Heqifdef. intros. subst. unfold bequiv in H. simpl in H. specialize H with (st:= st).
           rewrite H in H0. inversion H0.
         + inversion Heqifdef.
         + inversion Heqifdef.
       - intros Q. unfold bequiv in H. simpl in H.  specialize H with (st:= st). apply E_IfTrue.
         + assumption.
         + assumption.
Qed.

Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2.
  intros H st st'. 
 split.
 - intros H1. remember <{ if b then c1 else c2 end }> as ifdef eqn:Heqifdef.
   induction H1.
   + inversion Heqifdef.
   + inversion Heqifdef.
   + inversion Heqifdef.
   + inversion Heqifdef. subst. unfold bequiv in H. specialize H with (st:= st). 
     simpl in H. rewrite H in H0. inversion H0. 
   + injection Heqifdef. intros. subst. apply H1.
   + inversion Heqifdef.
   + inversion Heqifdef.
 - intros Q. unfold bequiv in H. simpl in H.  specialize H with (st:= st). apply E_IfFalse.
   + assumption.
   + assumption.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros b c1 c2.
  unfold cequiv. 
  split.
  - intros H1. remember <{ if b then c1 else c2 end }> as ifdef eqn:Heqifdef.
    induction H1. 
    + inversion Heqifdef.
    + inversion Heqifdef.
    + inversion Heqifdef.
    + injection Heqifdef. intros. subst.
      apply E_IfFalse.
      * simpl. rewrite H. simpl. reflexivity.
      * apply H1.
    + injection Heqifdef. intros. subst.  apply E_IfTrue. 
      * simpl. rewrite H. simpl. reflexivity.
      * apply H1.
    + inversion Heqifdef.
    + inversion Heqifdef.
  - intros. remember <{ if ~ b then c2 else c1 end }> as ifdef eqn:Heqifdef.
    induction H.
    + inversion Heqifdef.
    + inversion Heqifdef.
    + inversion Heqifdef.
    + injection Heqifdef. intros. subst. simpl in H. apply  negb_true_iff in H.
      apply E_IfFalse.
      * apply H. 
      * apply H0.
    + injection Heqifdef. intros. subst.  simpl in H. apply  negb_false_iff in H.
      apply E_IfTrue. 
      * apply H.
      * apply H0.
    + inversion Heqifdef.
    + inversion Heqifdef.
Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
 intros.
 unfold cequiv.  split. 
 - intros. remember <{ while b do c end }> as whileDef eqn:HwhileDef.
   induction H0.
   + apply E_Skip.
   + inversion HwhileDef.
   + inversion HwhileDef.
   + inversion HwhileDef.
   + inversion HwhileDef.
   + apply E_Skip.
   + injection HwhileDef. intros. subst. unfold bequiv in H. simpl in H.
     specialize H with (st:= st). rewrite H in H0. inversion H0.
 - intro. inversion H0.
   apply E_WhileFalse. unfold bequiv in H. 
   specialize H with (st:= st'). simpl in H.
   apply H. 
Qed.


Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  intros. unfold not. intros.
  remember <{ while b do c end }> as whileDef eqn:HwhileDef.
  induction H0. 
  - inversion HwhileDef.
  - inversion HwhileDef.
  - inversion HwhileDef.
  - inversion HwhileDef.
  - inversion HwhileDef.
  - injection HwhileDef. intros. subst.
    unfold bequiv in H. simpl in H. 
    specialize H with (st:= st). rewrite H in H0. inversion H0.
  - injection HwhileDef. intros. subst. apply IHceval2. reflexivity.
Qed.

Theorem while_true : forall b c,
  bequiv b <{true}> ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros. unfold cequiv.
  intros. split.
  - intros. apply while_true_nonterm with (st:= st) (st':= st') (c:= c) in H.
    apply H in H0. inversion H0.
  - intros. remember <{ while true do skip end }> as whileDef eqn:HwhileDef. 
    induction H0. 
    + inversion HwhileDef.
    + inversion HwhileDef.
    + inversion HwhileDef.
    + inversion HwhileDef.
    + inversion HwhileDef.
    + injection HwhileDef. intros. subst. 
      simpl in H0. inversion H0.
    + injection HwhileDef. intros. subst. inversion H0_ . subst.
      apply IHceval2. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
intros. unfold cequiv.
intros. split.
- intros.  remember <{ while b do c end }> as whileDef eqn:HwhileDef. 
induction H.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ injection HwhileDef. intros. subst.
  apply E_IfFalse. 
  * apply H.
  * apply E_Skip.
+ injection HwhileDef. intros. subst. 
  apply E_IfTrue.
  * apply H.
  * apply E_Seq with (st' := st').
    ** apply H0.
    ** apply H1.
- intros. inversion H. 
  + subst. inversion H6. subst. apply E_WhileTrue with (st' := st'0).
    * apply H5.
    * apply H2.
    * apply H7.
  + inversion H6. apply E_WhileFalse. subst. apply H5.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
intros. unfold cequiv.
intros. split.
- intros. 
remember <{ (c1; c2); c3 }> as ccDef eqn:HccDef. 
induction H.
+  inversion HccDef.
+  inversion HccDef.
+  injection HccDef. intros. subst. inversion H. subst. 
   apply E_Seq with (st' := st'0). 
   * apply H3.
   * apply E_Seq with (st' := st'). 
     ** apply H6.
     ** apply H0.
+  inversion HccDef.
+  inversion HccDef.
+  inversion HccDef.
+  inversion HccDef. 
- intros. inversion H. inversion H5. subst. 
  apply E_Seq with (st' := st'1). 
  + apply E_Seq with (st' := st'0).
    * apply H2.
    * apply H8.
  + apply H11.
Qed.

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
intros. split.
- intros. unfold aequiv in H. simpl in H. 
 assert (Hx : (X !-> st' X ; st') = st').
 + apply t_update_same.
+ rewrite <- Hx. inversion H0. subst. apply E_Asgn. auto.
- intros. inversion H0. subst. unfold aequiv in H. simpl in H.  
specialize H with (st:= st).
rewrite <- H. rewrite t_update_same. apply E_Skip.
Qed.

Definition prog_a : com :=
  <{ while X > 0 do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>. 

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while X <> X do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while X <> Y do
       X := Y + 1
     end }>.

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity. Qed.
 
Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H st.
  unfold aequiv in H.
  rewrite H. reflexivity. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  intros a1 a2 a3 H1 H2 st.
  unfold aequiv in H1.
 unfold aequiv in H2.
  rewrite H1. rewrite H2. reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  intros b1 b2 H st.
  unfold bequiv in H.
  rewrite H.
  reflexivity.
  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  intros b1 b2 b3 H1 H2 st.
 unfold bequiv in H1.
 unfold bequiv in H2.
  rewrite H1. rewrite H2. reflexivity. Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  intros c st st'.
  split.
  +  intros H. apply H.
  +  intros H.  apply H.
Qed.


Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  intros c1 c2 H st st'.
  split.
  +  intros H1. unfold cequiv in H. apply H. apply H1. 
  +  intros H1. unfold cequiv in H. apply H. apply H1.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros c1 c2 c3 H1 H2 st st'.
  split.
  + intros H. unfold cequiv in H1. unfold cequiv in H2. 
    apply H2. apply H1. apply H.
  + intros H.  unfold cequiv in H1. unfold cequiv in H2. 
    apply H1. apply H2. apply H.
  Qed.

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' -> cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' H st st'.
  split.
  + intros G.  inversion G. subst. apply E_Asgn. auto.
  + intros G.  inversion G. subst. apply E_Asgn. auto.
Qed.

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  intros b b' c c' H G st st'.
  split.
  - intros.  remember <{ while b do c end }> as whileDef eqn:HwhileDef. induction H0. 
    + inversion HwhileDef.
    + inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ injection HwhileDef. intros. subst. apply E_WhileFalse. unfold bequiv in H. rewrite <- H. apply H0.
+ injection HwhileDef. intros. subst. apply E_WhileTrue with (st' := st'). 
  * unfold bequiv in H. rewrite <- H. apply H0.
  * unfold cequiv in G. apply G. apply H0_.
  * apply IHceval2. reflexivity. 
- intros. remember <{ while b' do c' end }> as whileDef eqn:HwhileDef. induction H0. 
    + inversion HwhileDef.
    + inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ inversion HwhileDef.
+ injection HwhileDef. intros. subst. apply E_WhileFalse. unfold bequiv in H. rewrite -> H. apply H0.
+ injection HwhileDef. intros. subst. apply E_WhileTrue with (st' := st'). 
  * unfold bequiv in H. rewrite -> H. apply H0.
  * unfold cequiv in G. apply G. apply H0_.
  * apply IHceval2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' H G st st'.
  split.
  - intros. unfold cequiv in H. unfold cequiv in G. inversion H0. subst. apply E_Seq with (st' := st'0).
    + specialize H with (st := st) (st' := st'0). apply H. apply H3. 
    + specialize G with (st := st'0) (st' := st'). apply G. apply H6.
  - intros. unfold cequiv in H. unfold cequiv in G. inversion H0. subst. apply E_Seq with (st' := st'0).
    + specialize H with (st := st) (st' := st'0). apply H. apply H3. 
    + specialize G with (st := st'0) (st' := st'). apply G. apply H6.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  intros b b' c1 c1' c2 c2' H G Q st st'.
  split. 
  - intros. remember <{ if b then c1 else c2 end }> as ifDef eqn:HifDef. induction H0. 
    + inversion HifDef.
    + inversion HifDef.
    + inversion HifDef.
    + injection HifDef. intros. subst. apply E_IfTrue. 
      * unfold bequiv in H. rewrite <- H. apply H0.
      * unfold cequiv in G. apply G. apply H1.
    + injection HifDef. intros. subst. apply E_IfFalse. 
      * unfold bequiv in H. rewrite <- H. apply H0.
      * unfold cequiv in Q. rewrite <- Q. apply H1.
    + inversion HifDef.
    + inversion HifDef.
  - intros. remember <{ if b' then c1' else c2' end }> as ifDef eqn:HifDef. induction H0. 
    + inversion HifDef.
    + inversion HifDef.
    + inversion HifDef.
    + injection HifDef. intros. subst. apply E_IfTrue. 
      * unfold bequiv in H. rewrite -> H. apply H0.
      * unfold cequiv in G. apply G. apply H1.
    + injection HifDef. intros. subst. apply E_IfFalse. 
      * unfold bequiv in H. rewrite -> H. apply H0.
      * unfold cequiv in Q. rewrite -> Q. apply H1.
    + inversion HifDef.
    + inversion HifDef.
Qed.


Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if X = 0 then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if X = 0 then Y := X - X (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + unfold cequiv. 
      split. 
      * intros. inversion H. subst.  apply E_Asgn. simpl. lia.
      * intros. inversion H. subst.  apply E_Asgn. simpl. lia.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),  aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com), cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ a1 + a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }> = <{ 3 * X }>.
Proof.
  simpl. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof.
  reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof.
  simpl. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof.
  simpl. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}> => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if (X - Y) = (2 + 4) then skip
       else Y := 0 end;
       if 0 <= (4 - (2 + 1)) then Y := 0
       else skip end;
       while Y = 0 do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if (X - Y) = 6 then skip
       else Y := 0 end;
       Y := 0;
       while Y = 0 do
         X := X + 1
       end }>.
Proof. 
  simpl. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
 atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. 
  unfold aequiv. intros st. 
  induction a; simpl; try reflexivity;
  destruct (fold_constants_aexp a1);
  destruct (fold_constants_aexp a2);
  rewrite IHa1; rewrite IHa2; simpl; reflexivity.
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    assert (Q: aeval st a1 = aeval st a1').
    + subst a1'. rewrite <- fold_constants_aexp_sound. reflexivity.
    + assert (H: aeval st a2 = aeval st a2').
      * subst a2'. rewrite <- fold_constants_aexp_sound. reflexivity.
      * rewrite -> Q. rewrite -> H. destruct a1'. 
        ** destruct a2'. 
           *** simpl. destruct (n <=? n0). 
               **** simpl. reflexivity.
               **** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
  - (* BGt *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    assert (Q: aeval st a1 = aeval st a1').
    + subst a1'. rewrite <- fold_constants_aexp_sound. reflexivity.
    + assert (H: aeval st a2 = aeval st a2').
      * subst a2'. rewrite <- fold_constants_aexp_sound. reflexivity.
      * rewrite -> Q. rewrite -> H. destruct a1'.
        ** destruct a2'. 
           *** simpl. destruct (n <=? n0). 
               **** simpl. reflexivity.
               **** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
           *** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
        ** simpl. reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.


Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. 
  induction c; simpl.  
  - apply refl_cequiv. 
  - unfold cequiv.  intros. split. 
    + intros. inversion H. subst. apply E_Asgn. rewrite <- fold_constants_aexp_sound. reflexivity.
    + intros. inversion H. apply E_Asgn. subst. rewrite <- fold_constants_aexp_sound. reflexivity.
  - unfold cequiv. split.
    + intros. unfold cequiv in IHc1. unfold cequiv in IHc2. inversion H.
      apply E_Seq with (st':=st'0).
      * specialize IHc1 with (st:=st) (st':=st'0).
        apply IHc1.  apply H2.
      * specialize IHc2 with (st:=st'0) (st':=st').
        apply IHc2.  apply H5.
    + intros. unfold cequiv in IHc1. unfold cequiv in IHc2. inversion H.
      apply E_Seq with (st':=st'0).
      * specialize IHc1 with (st:=st) (st':=st'0).
        apply IHc1.  apply H2.
      * specialize IHc2 with (st:=st'0) (st':=st').
        apply IHc2.  apply H5.
  - assert (bequiv b (fold_constants_bexp b)). 
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
    try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - assert (bequiv b (fold_constants_bexp b)). 
    { apply fold_constants_bexp_sound. } 
    destruct (fold_constants_bexp b) eqn:Heqb.
    + apply while_true. apply H.
    + apply while_false. apply H.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
Qed.

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | AId X => AId X
    | APlus (ANum 0) a2 => optimize_0plus_aexp a2
    | APlus a1 a2 => APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | AMinus a1 a2 => AMinus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | AMult a1 a2 => AMult (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
    | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BNot b1 => BNot (optimize_0plus_bexp b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
    | _ => b
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
   match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> =>
      <{ optimize_0plus_com c1 ; optimize_0plus_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match optimize_0plus_bexp b with
      | <{true}> => optimize_0plus_com c1
      | <{false}> => optimize_0plus_com c2
      | b' => <{ if b' then optimize_0plus_com c1
                       else optimize_0plus_com c2 end}>
      end
  | <{ while b do c end }> =>
      match optimize_0plus_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (optimize_0plus_com c) end }>
      end
  end.

Example test_optimize_0plus:
    optimize_0plus_com
       <{ while X <> 0 do X := 0 + X - 1 end }>
  = <{ while X <> 0 do X := X - 1 end }>.
Proof.
 simpl. reflexivity. Qed.

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. unfold aequiv. 
  intros. induction a.
  - simpl. reflexivity. 
  - simpl. reflexivity. 
  - simpl.  destruct a1.
    + simpl. destruct n.
      * simpl. rewrite IHa2. reflexivity.
      * simpl.  rewrite IHa2. reflexivity.
    + simpl.  rewrite IHa2. reflexivity.
   + rewrite IHa1. simpl. rewrite IHa2. reflexivity.
   + rewrite IHa1. simpl. rewrite IHa2. reflexivity.
   + rewrite IHa1. simpl. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. 
  intros. induction b.
  - simpl. reflexivity. 
  - simpl. reflexivity. 
  - simpl. rewrite optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- IHb. reflexivity. 
  - simpl. rewrite <- IHb1. rewrite <- IHb2. reflexivity. 
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. 
  induction c; simpl.  
  - apply refl_cequiv. 
  - unfold cequiv.  intros. split. 
 + intros. inversion H. subst. apply E_Asgn. rewrite <- optimize_0plus_aexp_sound. reflexivity.
    + intros. inversion H. apply E_Asgn. subst. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - unfold cequiv. split.
    + intros. unfold cequiv in IHc1. unfold cequiv in IHc2. inversion H.
      apply E_Seq with (st':=st'0).
      * specialize IHc1 with (st:=st) (st':=st'0).
        apply IHc1.  apply H2.
      * specialize IHc2 with (st:=st'0) (st':=st').
        apply IHc2.  apply H5.
    + intros. unfold cequiv in IHc1. unfold cequiv in IHc2. inversion H.
      apply E_Seq with (st':=st'0).
      * specialize IHc1 with (st:=st) (st':=st'0).
        apply IHc1.  apply H2.
      * specialize IHc2 with (st:=st'0) (st':=st').
        apply IHc2.  apply H5.
  - assert (bequiv b (optimize_0plus_bexp b)). 
    { apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
    try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - assert (bequiv b (optimize_0plus_bexp b)). 
    { apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb.
    + apply while_true. apply H.
    + apply while_false. apply H.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
    + apply CWhile_congruence. 
      * apply H.
      * apply IHc.
Qed.

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).


Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. unfold optimizer.
  intros. 
  assert (H: cequiv (fold_constants_com c) (optimize_0plus_com (fold_constants_com c))).
  - remember (fold_constants_com c) as c' eqn:Heqc'. apply optimize_0plus_com_sound.
  - apply sym_cequiv. apply trans_cequiv with (c2:=(fold_constants_com c)).
    + apply sym_cequiv. apply H.
    + apply sym_cequiv. apply fold_constants_com_sound.
Qed.

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId x' =>
      if String.eqb x x' then u else AId x'
  | <{ a1 + a2 }> =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }> =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}> = <{ Y + (42 + 53)}>.
Proof. 
  simpl. reflexivity. Qed.

Definition subst_equiv_property : Prop := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  (* Here is the counterexample: assuming that subst_equiv_property
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1; Y := X }> as c1.
  remember <{ X := X + 1; Y := X + 1 }> as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.
  (* ... allows us to show that the command c2 can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1; X !-> 1) as st1.
  remember (Y !-> 2; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1).
    + subst. apply E_Seq with (st' := (X !-> 1)).
      * apply E_Asgn. reflexivity.
      * apply E_Asgn. reflexivity.
    + assert (H2 : empty_st =[ c2 ]=> st2).
      * subst. apply E_Seq with (st' := (X !-> 1)).
       ** apply E_Asgn. reflexivity.
       ** apply E_Asgn. reflexivity.
  * clear Heqc1 Heqc2.
    apply H in H1.
    clear H.
    (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
    assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
    clear H1 H2.
    assert (Hcontra' : st1 Y = st2 Y)

    by (rewrite Hcontra; reflexivity).
    subst. discriminate. Qed.
  
Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros.
  induction a; simpl; inversion H; subst;
    try reflexivity;
    try (
        apply IHa1 in H2; apply IHa2 in H3;
        rewrite H2, H3;
        reflexivity
      ).
  - apply t_update_neq with (A:=nat) (m:=st) (v:=ni) in H1.
    apply H1.
Qed.

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  unfold not; intros.
  apply loop_never_stops with empty_st empty_st.
  unfold loop.
  apply H.
  apply E_Skip.
Qed.


Module Himp.


Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com. (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
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



Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)
 where "st =[ c ]=> st'" := (ceval c st st').


Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
  apply E_Seq with empty_st.
  - apply E_Skip.
  - apply E_Havoc.
Qed.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

Definition pXY := <{ havoc X ; havoc Y }>.

Definition pYX := <{ havoc Y; havoc X }>.


Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~ cequiv pXY pYX.
Proof.
  left.
  intros. split.
  - intros H. inversion H. subst.
    inversion H2. inversion H5. subst.
    apply E_Seq with (Y !-> n0; st).
    + apply E_Havoc.
    + assert (Q: (Y !-> n0; X !-> n; st) = (X !-> n; Y !-> n0; st)).
      * apply t_update_permute.
        intros conxy.
        discriminate.
      * rewrite Q. apply E_Havoc.
  - intros H. inversion H. subst.
    inversion H2. inversion H5. subst.
    apply E_Seq with (X !-> n0; st).
    + apply E_Havoc.
    + assert (Q: (X !-> n0; Y !-> n; st) = (Y !-> n; X !-> n0; st)).
      * apply t_update_permute.
        intros conxy.
        discriminate.
      * rewrite Q. apply E_Havoc.
Qed.

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~ cequiv ptwice pcopy.
Proof.
   right. unfold not, cequiv. intros.
  remember (X !-> 1; Y !-> 2) as st.
  assert (empty_st =[ ptwice ]=> st).
  - apply E_Seq with (X !-> 1).
    + apply E_Havoc.
    + assert (Q: (X !-> 1; Y !-> 2) = (Y !-> 2; X !-> 1)).
      * apply t_update_permute.
        intros conxy.
        discriminate.
      * rewrite Heqst. rewrite Q. apply E_Havoc.
  - assert (Hcontra: st X = st Y).
    + apply H in H0. inversion H0. inversion H6. subst. simpl. rewrite t_update_eq.
    apply t_update_neq. unfold not. intros. inversion H1.
    + subst. inversion Hcontra.  
 Qed.
 
Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.   

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
  unfold not, p1; intros.
  remember <{ while ~ (X = 0) do havoc Y; X := X + 1 end }> as p1.
  induction H0; inversion Heqp1.
  - subst. 
    apply H.
    simpl in H0.
    apply negb_false_iff in H0.
    apply beq_nat_true in H0.
    assumption.
  - apply IHceval2.
    + rewrite H3 in H0_.
      inversion H0_; subst.
      inversion H8; subst.
      rewrite t_update_eq.
      simpl.
      rewrite <- plus_n_Sm.
      intros.
      inversion H1.
    + assumption.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
 ~ st =[ p2 ]=> st'.
Proof.
   unfold not, p2; intros.
remember <{ while ~ (X = 0) do skip end }> as p2.
  induction H0; inversion Heqp2.
  - subst. 
    apply H.
    simpl in H0.
    apply negb_false_iff in H0.
    apply eqb_eq in H0.
    assumption.
  - apply IHceval2.
    + rewrite H3 in H0_.
      inversion H0_; subst.
      apply H.
    + apply Heqp2.
Qed.


Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  unfold cequiv.
  intros. split.
  - intros. inversion H.
    + apply E_WhileFalse.
      apply H4.
    + simpl in H2. apply negb_true_iff in H2. apply eqb_neq in H2.
      apply p1_may_diverge with (st':= st') in H2. apply H2 in H. inversion H.
  - intros. inversion H.
   + apply E_WhileFalse.
     apply H4.
   + simpl in H2. apply negb_true_iff in H2. apply eqb_neq in H2.
     apply p2_may_diverge with (st':= st') in H2. apply H2 in H. inversion H.
Qed.

Definition p3 : com :=
  <{ Z := 1;
     while X <> 0 do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0; Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. 
  unfold not. intros.
  remember (X !-> 1; empty_st) as st.
  remember (Z !-> 1; st)  as st1.
  remember (X !-> 0; st1) as st2.
  remember (Z !-> 2; st2) as st3.
  remember (Z !-> 1; X !-> 0; st) as st4.
  assert (st =[p3]=> st3).
  - apply E_Seq with st1.
    + subst st1. apply E_Asgn. reflexivity.
    + apply E_WhileTrue with st3.
      * subst. reflexivity.
      * apply E_Seq with st2.
        ** subst. apply E_Havoc.
        ** subst. apply E_Havoc.
      * apply E_WhileFalse. subst. simpl. reflexivity.
  - assert (Hcontra: st4 = st3).
    + apply H in H0. inversion H0. inversion H3. inversion H6.
      subst. reflexivity.
    + assert (Hcontra': st4 Z = st3 Z).
      * rewrite Hcontra. reflexivity.
      * subst. inversion Hcontra'.  
Qed.


Definition p5 : com :=
  <{ while X <> 1 do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.   
 split; intros.
 - unfold p5 in H.
   remember <{ while X <> 1 do havoc X end }> as p5.
   induction H; inversion Heqp5; clear Heqp5.
   + rewrite H1 in H. simpl in H. 
     assert (st = (X!->1; st)).
     * apply negb_false_iff in H. apply beq_nat_true in H. 
       rewrite <- H. symmetry. apply t_update_same.
     * rewrite -> H0 at 2. apply E_Asgn. reflexivity.
   + subst.  inversion H0; subst. 
     assert ((X !-> n; st) =[ p6 ]=> st''). 
     * apply IHceval2. reflexivity.
     * inversion H2; subst. simpl.
       assert ((X !-> 1; X !-> n; st) = (X !-> 1; st)).
       ** rewrite t_update_shadow. reflexivity.
       ** rewrite H3. apply E_Asgn. reflexivity.
 - inversion H. subst. simpl. simpl in H. 
   destruct (negb (eqb (st X) 1)) eqn:eqnat.
   + apply E_WhileTrue with (X !-> 1; st).
     * simpl. assumption.
     * apply E_Havoc.
     * apply E_WhileFalse. reflexivity.
   + assert ((X!->1; st) = st).
     * apply negb_false_iff in eqnat. apply beq_nat_true in eqnat.
       rewrite <- eqnat. apply t_update_same.
     * rewrite H0. apply E_WhileFalse. simpl. assumption.
Qed.

End Himp.

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
 intros.
 split. 
 - intros. inversion H2. inversion H5. inversion H8. subst. 
   apply aeval_weakening with (ni := aeval st a1) (st:=st) in H0.
   rewrite -> H0. 
   apply aeval_weakening with (ni := aeval st a2) (st:=st) in H1.
   apply E_Seq with (l2 !-> aeval st a2; st).
   + apply E_Asgn. reflexivity.
   + assert ((l2 !-> aeval st a2; l1 !-> aeval st a1; st) = (l1 !-> aeval st a1; l2 !-> aeval st a2; st)).
     * apply t_update_permute. apply H.
     * rewrite H3. apply E_Asgn. apply H1.
 - intros. inversion H2. inversion H5. inversion H8. subst. 
   apply aeval_weakening with (ni := aeval st a2) (st:=st) in H1.
   rewrite -> H1.
   apply aeval_weakening with (ni := aeval st a1) (st:=st) in H0.
   apply E_Seq with (l1 !-> aeval st a1; st).
   + apply E_Asgn. reflexivity.
   + assert ((l2 !-> aeval st a2; l1 !-> aeval st a1; st) = (l1 !-> aeval st a1; l2 !-> aeval st a2; st)).
     * apply t_update_permute. apply H.
     * rewrite <- H3. apply E_Asgn. apply H0.
Qed.








