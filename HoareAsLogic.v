Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Hoare.
Hint Constructors ceval : core.

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable (Q [V |-> a]) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassertion b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassertion b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassertion b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassertion b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof.
  intros.
  apply H_Consequence with P' Q.
  - apply X. 
  - apply H.
  - auto.
Qed.

Lemma H_Consequence_post : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
Proof.
  intros.
  apply H_Consequence with P Q';
  try apply X; auto.
Qed.

Example sample_proof :
  derivable
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    <{ X := X + 1; X := X + 2}>
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

Theorem provable_true_post : forall c P,
    derivable P c True.
Proof.
  induction c.
  - intros. eapply H_Consequence. apply H_Skip.
    + intros. apply H.
    + intros. reflexivity.
  - intros. eapply H_Consequence. 
    + assert (derivable (True [x |-> a]) <{x := a}> True).
      apply H_Asgn.
      apply X.
    + intros. unfold assertion_sub.  simpl. reflexivity.
    + reflexivity.
  - intros. eapply H_Seq.
    + apply IHc2.
    + apply IHc1.
  - intros. eapply H_If.
      + apply IHc1.
      + apply IHc2.
  - intros. eapply H_Consequence.
    + eapply H_While. apply IHc.
    + intros. reflexivity.
    + intros. reflexivity.
Qed.

Theorem provable_false_pre : forall c Q,
    derivable False c Q.
Proof.
   induction c.
  - intros. eapply H_Consequence. apply H_Skip.
    + intros. simpl in H. inversion H.
    + intros. apply H. 
  - intros. eapply H_Consequence.  
     + assert (derivable (False [x |-> a]) <{x := a}> False).
      apply H_Asgn.
      apply X.
    + intros. simpl in H. inversion H.
    + intros. simpl in H. inversion H.
 - intros. eapply H_Seq.
    + apply IHc2.
    + apply IHc1.
  - intros. eapply H_If.
      + eapply H_Consequence.
        * apply IHc1.
        * intros. simpl in H. destruct H. inversion H.
        * intros. apply H.
      +  eapply H_Consequence.
        * apply IHc2.
        * intros. simpl in H. destruct H. inversion H.
        * intros. apply H.
  - intros. eapply H_Consequence.   
    eapply H_While.
    +  apply H_Consequence_pre with (assert_of_Prop False).
       * apply IHc. 
       * intros. destruct H. apply H.
     
    + intros. inversion H.
    + intros.  simpl in H. destruct H. inversion H.
  Qed.

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Theorem hoare_sound : forall P c Q,
  derivable P c Q -> valid P c Q.
Proof.
   intros. induction X.
   - unfold valid. intros. inversion H. subst. apply H0.
   - unfold valid. intros. inversion H. subst. 
     unfold assertion_sub in H0. apply H0.
   - unfold valid.  intros. unfold valid in IHX1. unfold valid in IHX2. inversion H.
     apply IHX1 in H6. subst.
     + apply H6.
     + subst. apply IHX2 in H3.
       * apply H3.
       * apply H0.
  -  unfold valid. intros. unfold valid in IHX1. unfold valid in IHX2. inversion H.
     subst.
     + apply IHX1 with st.
       * apply H7.
       * split. 
         ** apply H0.
         ** apply H6.
      + subst.  apply IHX2 with st.
        * apply H7.
        * split. 
          ** apply H0.
          ** apply bexp_eval_false. apply H6.
   - unfold valid.  intros. 
     remember <{ while b do c end }> as Hwh. 
     induction H. 
     + inversion HeqHwh.
     + inversion HeqHwh.
     + inversion HeqHwh.
     + inversion HeqHwh.
     + inversion HeqHwh.
     + injection HeqHwh. intros. subst. split.
       * apply H0.
       * apply bexp_eval_false. apply H.
     + injection HeqHwh. intros. subst. apply IHceval2 in HeqHwh.
       * apply HeqHwh.
       * unfold valid in IHX. apply IHX with st.
         ** apply H1.
         ** split. 
            *** apply H0.
            *** apply bexp_eval_true. apply H.
   - unfold valid. intros. unfold valid in IHX. apply IHX in H.
     + apply q. apply H.
     + apply p. apply H0.
Qed.

Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

Hint Unfold wp : core.

Theorem wp_is_precondition : forall c Q,
  {{ wp c Q }} c {{ Q }}.
Proof. auto. Qed.

Theorem wp_is_weakest : forall c Q P',
    {{P'}} c {{Q}} ->
    P' ->> (wp c Q).
Proof. eauto. Qed.

Lemma wp_seq : forall P Q c1 c2,
    derivable P c1 (wp c2 Q) -> derivable (wp c2 Q) c2 Q -> derivable P <{c1; c2}> Q.
Proof.
   intros. apply H_Seq with (wp c2 Q).
   - apply X0.
   - apply X.
Qed.

Lemma wp_invariant : forall b c Q,
    valid (wp <{while b do c end}> Q /\ b) c (wp <{while b do c end}> Q).
Proof.
  intros.
  unfold valid.
  intros.
   destruct H0.
   unfold wp. intros.
     unfold wp in H0. apply H0. apply E_WhileTrue with st'.   
     + apply H1.
     + apply H.
     + apply H2.
Qed.

Theorem hoare_complete: forall P c Q,
  valid P c Q -> derivable P c Q.
Proof.
  unfold valid. intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - eapply H_Consequence. apply H_Skip.
    + intros. apply H.
    + intros. apply HT with st.
      * apply E_Skip.
      * apply H.
  - eapply H_Consequence.
    + apply H_Asgn.
    + intros.  apply HT with st.
      * apply E_Asgn. reflexivity.
      * apply H.
    + intros. apply H.
  - apply wp_seq.
    + apply IHc1. intros.
      unfold wp. intros. apply HT with st.
      * apply E_Seq with st'.
        ** apply H.
        ** apply H1.
      * apply H0.
    +  apply IHc2. intros. unfold wp in H0. apply H0.
       apply H.
  - apply H_If.
    + apply IHc1. intros. apply HT with st.
      * apply E_IfTrue.
        ** destruct H0. apply H1.
        ** apply H.
        *  destruct H0. apply H0.
    + apply IHc2. intros. apply HT with st.
      * apply E_IfFalse.
        ** destruct H0. destruct (beval st b) eqn:Hb.
           *** unfold not in H1. apply H1 in Hb. inversion Hb.
           *** reflexivity.
        ** apply H.
        * destruct H0. apply H0.
   - eapply H_Consequence.
     + apply H_While. apply IHc. 
       specialize wp_invariant with b c Q.
       intros H. unfold valid in H. intros. apply H in H0.
       * apply H0.
       * apply H1.
       + intros.  unfold wp. intros. apply HT with st.
         * apply H0.
         * apply H.
     + intros. destruct H. unfold wp in H. apply H. apply E_WhileFalse.
       simpl in H0. destruct (beval st b) eqn:Hb. unfold not in H0.
      assert (true = true). reflexivity. apply H0 in H1. inversion H1. reflexivity.
 Qed.
      
       












