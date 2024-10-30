Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).

End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.


Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExamplePrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.

Definition assertion1 : Assertion := X <= Y.
Definition assertion2 : Assertion := X = 3 \/ X <= Y.
Definition assertion3 : Assertion := Z = ap2 max X Y.
Definition assertion4 : Assertion := Z * Z <= X
                            /\  ~ (((ap S Z) * (ap S Z)) <= X).
End ExamplePrettyAssertions.

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 90, c custom com at level 99) : hoare_spec_scope.

Check ({{True}} X := 0 {{True}}).

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) -> {{P}} c {{Q}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  apply H in H1.
  inversion H1.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst. assumption.
Qed.
  
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros.
  intros st st' M MP.
  inversion M. subst.
  apply H0 in H3.
  apply H in H6.
  apply H3 in MP.
  apply H6 in MP.
  apply MP.
Qed.

Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) => P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros.
  intros st st' M MP.
  unfold assertion_sub in MP.
  inversion M. rewrite H3 in MP. apply MP.
Qed.

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
 exists ((X <= 10) [X |-> 2 * X]).
 apply hoare_asgn.
Qed.


Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof.
  exists (APlus (AId X) (ANum 1)).
  intros contra.
  unfold valid_hoare_triple in contra.
  remember (X!->1; X!->0) as st1.
  assert (Aexp_of_aexp X st1 = Aexp_of_aexp <{ X + 1 }> st1 -> False).
 - intros.
  rewrite Heqst1 in H.
  simpl in H.
  inversion H.
- apply H.
  apply contra with (X!->0).
  + rewrite Heqst1. apply E_Asgn.
    simpl. reflexivity.
  + reflexivity.
Qed.

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st)
           /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros. split.
  - inversion H. subst.
    destruct H0.
    rewrite -> t_update_shadow.
    rewrite <- H1.
    rewrite -> t_update_same.
    apply H0.
  - inversion H.
    subst.
    rewrite -> t_update_shadow.
    destruct H0.
    rewrite <- H1.
    rewrite -> t_update_same.
    apply t_update_eq.
Qed.


Theorem hoare_asgn_fwd_exists :
  forall a P,
  {{fun st => P st}}
    X := a
  {{fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros. 
  exists (st X). split.
  - inversion H.
    subst.
    rewrite -> t_update_shadow.
    rewrite -> t_update_same.
    apply H0.
  - inversion H.
    subst.
    rewrite -> t_update_shadow.
    rewrite -> t_update_same.
    apply t_update_eq.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
 unfold valid_hoare_triple in H.
apply H with st.
 - apply H1.
 - apply H0. apply H2.
Qed.


Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  unfold valid_hoare_triple in H.
  apply H0.
  apply H with st.
  - apply H1.
  - apply H2.
Qed.

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.

apply hoare_consequence_pre with ((X = 1) [X |-> 1]).
- simpl. apply hoare_asgn.
- unfold assert_implies.
  intros. simpl. reflexivity.
Qed.

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_consequence_pre with (P' := (X < 5) [X |-> X + 1]).
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
unfold valid_hoare_triple.
  intros.
  unfold valid_hoare_triple in H.
  apply H1. apply H with st.
  - apply H2.
  - apply H0. apply H3.
Qed.

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
Abort.

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assertion_sub. unfold t_update.
    intros st. simpl. reflexivity.
Qed.

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

Example assertion_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

Ltac assertion_auto :=
  try auto; (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.
Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example assertion_sub_ex1' :
  {{ X <=5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>".  unfold assertion_sub. unfold t_update. 
     intros. simpl in *. lia.
Qed.

Example assertion_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
   eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros. 
   eapply hoare_seq.
  - apply hoare_skip.
  -  eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

Definition swap_program : com :=  <{ X := 0; Y := 0 }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
   eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold valid_hoare_triple.
  intros H.
  simpl in *.
  specialize H with (a := APlus (AId X) (AId Y)) (n := 4).
  remember (Y!->1) as st1.
  remember (Y!->4; X!->3; Y!->1) as st2.
  assert (H1 : st1 =[ X := 3; Y := X + Y]=> st2).
  - apply E_Seq with (X!->3; Y!->1).
    + rewrite Heqst1. apply E_Asgn. reflexivity.
    + rewrite Heqst2. apply E_Asgn. reflexivity.
  - assert (st2 Y = 4).
    + rewrite Heqst2. unfold t_update. reflexivity.
  +  remember (Y !-> 7; X !-> 3; Y !-> 4) as st3.  
    assert (H2 : (Y !-> 4) =[ X := 3; Y := X + Y]=> st3).
    * apply E_Seq with (X!->3; Y !-> 4).
      ** apply E_Asgn. reflexivity.
      ** rewrite Heqst3. apply E_Asgn. reflexivity.
      * apply H in H2. 
        ** rewrite Heqst3 in H2. unfold t_update in H2. simpl in H2. inversion H2.
        ** simpl. reflexivity.
Qed.

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.
Arguments bassertion /.

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassertion b) st.
Proof.
  intros b st Hbe.
  unfold bassertion. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof.
  intros.
  intros Hcontra.
  induction b.
  - inversion H.
  - simpl in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
  - simpl in Hcontra. inversion H. rewrite H1 in Hcontra. inversion Hcontra.
Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros.
unfold valid_hoare_triple.
intros.
inversion H1.
- subst.
  unfold valid_hoare_triple in H.
  unfold valid_hoare_triple in H0.
  apply H in H9.
  + apply H9.
  + split. 
    * apply H2.
    * congruence.
 - apply H0 in H9. 
   apply H9.
   split.
   + apply H2.
   + congruence.    
Qed.
    
Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto. (* no progress *)
      unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.


Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
  try apply hoare_asgn; try assertion_auto'.
Qed.


Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *; (* for inequalities *)
  auto; try lia.

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
  try apply hoare_asgn; assertion_auto''.
Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" := (CIf1 x y)
                (in custom com at level 0, x custom com at level 99).

Notation "'skip'" := CSkip (in custom com at level 0).

Notation "x := y" := (CAsgn x y)
                     (in custom com at level 0, x constr at level 0,
                      y at level 85, no associativity).

Notation "x ; y" := (CSeq x y)
                    (in custom com at level 90, right associativity).

Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
                             (in custom com at level 89, x at level 99,
                              y at level 99, z at level 99).

Notation "'while' x 'do' y 'end'" := (CWhile x y)
                    (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
  | E_IfTrue1 : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_IfFalse1 : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. 
  eauto.
Qed.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. 
   eauto.
Qed.

Definition valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
       forall st st',
       st =[ c ]=> st' ->
       P st ->
       Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" := (valid_hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

Theorem hoare_if1 : forall P Q (b:bexp) c,
  {{ P /\ b }} c {{Q}} ->
  {{ P /\ ~ b}} skip {{Q}} ->
  {{P}} if1 b then c end {{Q}}.
Proof.
intros.
unfold valid_hoare_triple.
intros.
inversion H1.
- subst.
  unfold valid_hoare_triple in H.
  apply H in H8.
  + apply H8.
  + split. 
    * apply H2.
    * congruence.
- unfold valid_hoare_triple in H0.
  subst. 
  apply H0 with st'.
  * apply E_Skip.
  * split.
    ** apply H2.
    ** congruence.
Qed.

Theorem if1_example :  
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof.
  apply hoare_if1.
  - simpl. 
    unfold valid_hoare_triple.
    intros. 
    inversion H.
    subst. 
    rewrite t_update_eq.
    simpl.
    destruct H0.
    rewrite H0.
    symmetry.
    apply t_update_neq.
    intros contra.
    inversion contra.
  - simpl.
    unfold valid_hoare_triple.
    intros.
    destruct H0.
    inversion H.
    apply not_true_is_false in H1.
    apply negb_false_iff in H1.
    apply eqb_eq in H1.
    rewrite H1 in H0.
    assert (st X = st Z).
    + lia.
    + subst. apply H2.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  apply HQ.
Qed.


End If1.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - split.
    + apply HP.
    + congruence.
  - injection Horig.
    intros. subst. 
    apply IHHeval2.
    + reflexivity.
    + apply Hhoare in Heval1.
      apply Heval1. split.
      * apply HP.
      * apply H.
Qed.

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
Proof.
eapply hoare_consequence_post.
- apply hoare_while.
  simpl.
 eapply hoare_consequence_pre.
+ apply hoare_asgn.
+ assertion_auto'.
  destruct H.
apply leb_le in H0.
lia.
- unfold "->>", assertion_sub, t_update, bassertion.
  intros; simpl in *.
   rewrite -> leb_le in *. (* for inequalities *)
  lia.
Qed.

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
 intros.  
 unfold valid_hoare_triple.
 intros. 
 remember <{while true do skip end}> as original_command eqn:Horig.
 induction H.
 - inversion Horig.
 - inversion Horig.
 - inversion Horig.
 - inversion Horig.
 - inversion Horig.
 - injection Horig. intros. subst. simpl in *. inversion H.
 - injection  Horig. intros. subst. inversion H1. subst.
   apply IHceval2.
   + reflexivity.
   + apply H0.
Qed.

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.


Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).

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


Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
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
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatTrue : forall st st' b c,    
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatFalse : forall st st' st'' b c,    
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

where "st '=[' c ']=>' st'" := (ceval st c st').


Definition valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (valid_hoare_triple P c Q) (at level 90, c custom com at level 99).


Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
constructor.
   - apply E_Seq with (X !-> 1).
     + apply E_Asgn. simpl. reflexivity.
     + apply E_Asgn. simpl. reflexivity.
   - simpl.  constructor; reflexivity.
Qed.

Theorem hoare_repeat : forall (P Q : Assertion) (c : com) (b : bexp),
{{P}} c {{Q}} ->
(fun st => Q st /\ ~ (bassertion b st)) ->> P -> 
{{P}} repeat c until b end {{fun st => Q st /\ bassertion b st}}.
Proof.
intros P Q c b HEnd HRepeat st st' Hc HP.
remember <{ repeat c until b end }> as rcom.
induction Hc.
- inversion Heqrcom.
- inversion Heqrcom.
- inversion Heqrcom.
- inversion Heqrcom.
- inversion Heqrcom.
- inversion Heqrcom.
- inversion Heqrcom.
- split.
  + unfold valid_hoare_triple in HEnd. apply HEnd with st.
    * injection Heqrcom. intros. subst. apply Hc.
    * apply HP.
  + injection Heqrcom.  intros. subst. apply bexp_eval_true. apply H.
- injection Heqrcom.  intros. subst. unfold valid_hoare_triple in HEnd. 
  apply IHHc2 .
  + reflexivity.
  + apply HRepeat. split.
    * apply HEnd with st.
      ** apply Hc1.
      ** apply HP.
    * apply bexp_eval_false. apply H.
Qed.
End RepeatExercise.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
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

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
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
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

Definition valid_hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }}  c  {{ Q }}" := (valid_hoare_triple P c Q)
                                  (at level 90, c custom com at level 99)
                                  : hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop :=
 forall n, Q (X !-> n; st).

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  intros. 
  unfold valid_hoare_triple.
  intros.
inversion H.
unfold havoc_pre in H0. 
apply H0.
Qed.

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ fun st => exists (n:nat), P [X |-> n] st }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc. 
  - unfold "->>". intros. unfold havoc_pre. intros. 
  
    + exists (st X). unfold assertion_sub. simpl. rewrite t_update_shadow. 
      rewrite t_update_same. apply H.
Qed.

End Himp.

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).

Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).

Notation "'skip'" := CSkip 
                     (in custom com at level 0).

Notation "x := y" := (CAsgn x y)
                     (in custom com at level 0, x constr at level 0,
                      y at level 85, no associativity).

Notation "x ; y" := (CSeq x y)
                    (in custom com at level 90, right associativity).

Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
                                             (in custom com at level 89, x at level 99,
                                              y at level 99, z at level 99).

Notation "'while' x 'do' y 'end'" := (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).


Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r -> P st  -> (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (valid_hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}}) /\ ~ ({{P}} assert b {{Q}}).
Proof.
 exists (fun st => True).
 exists (BFalse).
 exists (fun st => False).
split.
 - unfold valid_hoare_triple.
   intros.
   inversion H.
   inversion H2.
- intros contra.
unfold valid_hoare_triple in contra.
assert (empty_st =[ assert false ]=> RError).
+ apply E_AssertFalse.
  simpl. reflexivity.
+ apply contra in H.
  * inversion H. destruct H0. inversion H1.
  * reflexivity.
Qed.

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
unfold valid_hoare_triple in H.
apply H with st.
- inversion H0.
apply E_AssertTrue.
apply H3.
- apply H1. 
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inversion H.
  exists (X !-> n; st).
  split.
  - reflexivity.
  - unfold assertion_sub in H0.
    rewrite <- H5.
    apply H0.
Qed. 

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  assertion_auto''.
  unfold valid_hoare_triple.
  intros.
unfold valid_hoare_triple in H.
  apply H with st.
  - apply H1.
  - apply H0. apply H2.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
 assertion_auto''.
  unfold valid_hoare_triple.
  intros.
unfold valid_hoare_triple in H.

  apply H in H1.
  - destruct H1 as [st' HC].
    exists st'.
    split.
    + destruct HC. apply H1.
    + destruct HC. apply H0. apply H3.
  - apply H2. 
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
assertion_auto''.
unfold valid_hoare_triple.
intros.
unfold valid_hoare_triple in H.
unfold valid_hoare_triple in H0.
inversion H1. 
- subst.  
  apply H0 in H5.
  * destruct H5 as [st'' HH5].
    destruct HH5.
    specialize H with (st:=st'') (r:=r).
    injection H3.
    intros.
    subst.
    apply H.
    ** apply H8.
    ** apply H4.
  * apply H2.
- subst.   
  apply H0 in H7.
  + destruct H7 as [st'' HH7].
    destruct HH7.
    inversion H3.
  + apply H2.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inversion H.
  exists st.
  split.
  - reflexivity.
  - apply H0.
Qed.


Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros.
   unfold valid_hoare_triple.
  intros.
unfold valid_hoare_triple in H.
unfold valid_hoare_triple in H0.
inversion H1.
- apply H with st.
  + apply H9.
  + split.
    * apply H2.
    * apply bexp_eval_true. apply H8.
- apply H0 with st.
 + apply H9.
  + split.
  * apply H2.
    * congruence.
Qed.


Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~ b}}.

Proof.
  intros. 
  unfold valid_hoare_triple.
  intros.
  unfold valid_hoare_triple in H.
  remember <{ while b do c end }> as cwhe.
  induction H0.
  - inversion Heqcwhe.
- inversion Heqcwhe.
- inversion Heqcwhe.
- inversion Heqcwhe.
- inversion Heqcwhe.
- inversion Heqcwhe.
- exists st. split.
  + reflexivity.
  + split.
    * apply H1.
    * injection Heqcwhe. intros. subst. congruence.
- injection Heqcwhe. intros. subst. apply IHceval2.
  + reflexivity.
  + apply H in H0_.
    * destruct H0_ as [st'' HH0].
      destruct HH0. injection H2.
      intros. subst. apply H3.
  * split.
    ** apply H1.  
 ** congruence.
- injection Heqcwhe. intros. subst. apply H in H2.
  + destruct H2 as [st'' HH2]. destruct HH2.
     inversion H2.
  + split.
    * apply H1.
    * congruence.
- inversion Heqcwhe.
- inversion Heqcwhe.
- inversion Heqcwhe.
Qed.

Theorem  hoare_assume : forall P b,
     {{P}} assume b {{P}}.
Proof.
   intros.
   unfold valid_hoare_triple.   
   intros.
   inversion H.
    subst.
   exists st.
   split.
   - reflexivity.
   - apply H0.
Qed.

Theorem  hoare_assert : forall P (b:bexp),
     {{P/\b}} assert b {{P}}.
Proof.
   intros. unfold valid_hoare_triple.   
   intros. inversion H.
   - subst. exists st. split.
     + reflexivity.
     + destruct H0. 
       * apply H0.  
  - subst. destruct H0. 
    apply bexp_eval_false in H2.
    unfold not in H2. apply H2 in H1. inversion H1.
Qed.

Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
unfold valid_hoare_triple.   
intros.
simpl in *.
inversion H.
- subst.
  inversion H6. 
  + subst. inversion H8.
    * subst.
      exists st'0.
      split.
      ** reflexivity. 
      ** reflexivity. 
    * subst. inversion H3. subst. inversion H4. subst. simpl in H2.
      rewrite t_update_eq in H2. simpl in H9. rewrite eqb_eq in H9.
      rewrite H9 in H2. simpl in H2. inversion H2.
  + subst. inversion H7.
- subst. inversion H5.
Qed.
 
End HoareAssertAssume.





