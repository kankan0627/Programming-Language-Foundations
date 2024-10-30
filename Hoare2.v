Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-intuition-auto-with-star".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
Set Default Goal Selector "!".
Definition FILL_IN_HERE := <{True}>.

(*
  {{ True }}
    if X <= Y then
              {{   True /\ X <= Y   }} ->>
              {{ (Y - X) + X = Y  \/  (Y - X) + Y = X     }}
      Z := Y - X
              {{    Z + X = Y  \/  Z + Y = X       }}
    else
              {{   True  /\  ~ (X <= Y)  }} ->>
              {{  (X + Z) - X = Z  \/  (X + Z) - Z = X    }}
      Y := X + Z
              {{   Y - X = Z  \/  Y - Z = X    }}
    end
  {{ Y = X + Z }}
*)


Definition reduce_to_zero : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.


Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves loop invariant *)
      (* Massage precondition so hoare_asgn applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assertion_sub, "->>". simpl. intros.
        exact I.
  - (* Loop invariant and negated guard imply post *)
    intros st [Inv GuardFalse].
    unfold bassertion in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    simpl. 
    apply GuardFalse.
Qed.


Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero. simpl.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assertion.
  - verify_assertion.
Qed.

Module DComFirstTry.
Inductive dcom : Type :=
| DCSkip (P : Assertion)
  (* {{ P }} skip {{ P }} *)
| DCSeq (P : Assertion) (d1 : dcom) (Q : Assertion)
        (d2 : dcom) (R : Assertion)
  (* {{ P }} d1 {{Q}}; d2 {{ R }} *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* etc. *)
| DCIf (P : Assertion) (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
| DCWhile (P : Assertion) (b : bexp)
          (P1 : Assertion) (d : dcom) (P2 : Assertion)
          (Q : Assertion)
| DCPre (P : Assertion) (d : dcom)
| DCPost (d : dcom) (Q : Assertion).
End DComFirstTry.

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.


Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
           (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
           (in custom com at level 0, l constr at level 0,
            a custom com at level 85, P constr, no associativity)
           : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
               Pbody constr, Ppost constr)
           : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr)
           : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
          (in custom com at level 12, right associativity, P constr)
          : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
           (in custom com at level 10, right associativity, P constr)
           : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
           (in custom com at level 90, right associativity)
           : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
           (in custom com at level 91, P constr)
           : dcom_scope.

Local Open Scope dcom_scope.


Example dec_while : decorated :=
  <{ 
    {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\ X = 0}} ->>
  {{ X = 0 }} }>.

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (erase d1) (erase d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _    => CWhile b (erase d)
  | DCPre _ d          => erase d
  | DCPost d _         => erase d
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.

Example erase_while_ex :
    erase_d dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  simpl. reflexivity.
Qed.

Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Example precondition_from_while : precondition_from dec_while = True.
Proof. 
simpl. 
reflexivity. Qed.

Example postcondition_from_while : postcondition_from dec_while = (X = 0)%assertion.
Proof. 
simpl.
reflexivity. Qed.

Definition outer_triple_valid (dec : decorated) :=
  {{precondition_from dec}} erase_d dec {{postcondition_from dec}}.


Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof.
  unfold outer_triple_valid. simpl. reflexivity.
Qed.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Q d R =>
      (* post d is both the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Q)%assertion
      /\ ((post d  /\ ~ b) ->> R)%assertion
      /\ verification_conditions Q d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} erase d {{post d}}.
Proof.

  induction d.
  - intros. simpl in H. simpl. unfold "->>" in H.
    unfold valid_hoare_triple.
    intros. inversion H0. subst. apply H. apply H1.
  - intros. simpl in H. simpl. eapply hoare_seq.
    + apply IHd2. destruct H. apply v0.
    + apply IHd1. destruct H. apply H.
  - intros. simpl.  simpl in H. unfold valid_hoare_triple.
    unfold "->>" in H. intros. inversion H0. subst. apply H. apply H1.
  - intros. simpl. destruct H as [H1 [H2 [H3 [H4 H5]]]].  apply hoare_if.
    + eapply hoare_consequence_post. 
      * unfold valid_hoare_triple. intros. unfold "->>" in H3. apply H3. 
        unfold valid_hoare_triple in IHd1. apply IHd1 with (P:=P1) (st:=st).
        ** destruct H5. apply H5.
        ** apply H.
        **  unfold "->>" in H1. apply H1. apply H0.
      * unfold "->>" . intros. apply H.
    + eapply hoare_consequence_post. 
      * unfold valid_hoare_triple. intros. unfold "->>" in H4. apply H4. 
        unfold valid_hoare_triple in IHd2. apply IHd2 with (P:=P2) (st:=st).
        ** destruct H5. apply H6.
        ** apply H.
        **  unfold "->>" in H2. apply H2. apply H0.
     * unfold "->>" . intros. apply H.
  - intros. simpl. simpl in H. destruct H as [H1 [H2 [H3 H4]]]. 
    eapply hoare_consequence. 
    + apply hoare_while. eapply hoare_consequence_pre.
      * apply IHd. apply H4.
      * apply H2.
    + apply H1.
    + apply H3.
  - intros. simpl. simpl in H. destruct H. unfold "->>" in H. 
    unfold valid_hoare_triple.  intros. 
    unfold valid_hoare_triple in IHd. eapply IHd. 
    + apply H0. 
    + apply H1.
    + apply H in H2. apply H2.
  - intros. simpl. simpl in H.  destruct H. eapply hoare_consequence_post.
    + apply IHd.  apply H.
    + apply H0.
Qed. 
   
Definition verification_conditions_from (dec : decorated) : Prop :=
  match dec with
   | Decorated P d => verification_conditions P d
  end.


Corollary verification_conditions_correct : forall dec,
  verification_conditions_from dec ->
  outer_triple_valid dec.
Proof.
 induction dec.
 intros. 
 unfold outer_triple_valid. simpl. 
 apply verification_correct. simpl in H. apply H.
Qed.

Example vc_dec_while : verification_conditions_from dec_while.
Proof. verify_assertion. Qed.

Ltac verify :=
  intros;
  apply verification_correct;
  verify_assertion.

Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.

Definition swap_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.

Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.

Definition positive_difference_dec :=
  <{
    {{True}}
    if X <= Y then
          {{True /\ X <= Y}} ->>
          {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
      Z := Y - X
          {{Z + X = Y \/ Z + Y = X}}
    else
          {{True /\ ~(X <= Y)}} ->>
          {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
      Z := X - Y
          {{Z + X = Y \/ Z + Y = X}}
    end
    {{Z + X = Y \/ Z + Y = X}}
  }>.

Theorem positive_difference_correct :
  outer_triple_valid positive_difference_dec.
Proof. verify. Qed.

Definition if_minus_plus_dec :=
  <{
  {{True}}
  if (X <= Y) then
              {{ FILL_IN_HERE }} ->>
              {{ FILL_IN_HERE }}
    Z := Y - X
              {{ FILL_IN_HERE }}
  else
              {{ FILL_IN_HERE }} ->>
              {{ FILL_IN_HERE }}
    Y := X + Z
              {{ FILL_IN_HERE }}
  end
  {{ Y = X + Z}} }>.

Theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec.
Proof. 
- unfold outer_triple_valid.
  simpl.
  apply hoare_if.
  + eapply hoare_consequence_pre.
    * apply hoare_asgn.
    * unfold "->>". intros. unfold assertion_sub.
      assert (Z <> X).
      ** unfold not. intros.
         inversion H0. 
      ** eapply t_update_neq in H0.
         rewrite -> H0.
         assert (Z <> Y).
         *** unfold not. intros. inversion H1.
         *** eapply t_update_neq in H1.
             rewrite -> H1. rewrite t_update_eq. simpl.
             destruct H. simpl in H2. apply leb_le in H2. lia.
   + eapply hoare_consequence_pre.
     * apply hoare_asgn.
     * unfold "->>". intros. unfold assertion_sub.
       assert (Y <> X).
       ** unfold not. intros. inversion H0.
       ** eapply t_update_neq in H0. rewrite -> H0. rewrite t_update_eq.
          assert (Y <> Z).
          *** unfold not. intros. inversion H1.
          *** eapply t_update_neq in H1. rewrite -> H1. reflexivity.
Qed.

Definition div_mod_dec (a b : nat) : decorated :=
  <{
  {{ True }} ->>
  {{ FILL_IN_HERE }}
    X := a
             {{ FILL_IN_HERE }};
    Y := 0
             {{ FILL_IN_HERE }};
    while b <= X do
             {{ FILL_IN_HERE }} ->>
             {{ FILL_IN_HERE }}
      X := X - b
             {{ FILL_IN_HERE }};
      Y := Y + 1
             {{ FILL_IN_HERE }}
    end
  {{ FILL_IN_HERE }} ->>
  {{ FILL_IN_HERE }} }>.


Theorem div_mod_outer_triple_valid : forall a b,
  outer_triple_valid (div_mod_dec a b).
Proof.
verify.
Qed.


Example subtract_slowly_dec (m : nat) (n : nat) : decorated :=
  <{
  {{ X = m /\ Y = n }} ->>
  {{ Y - X = n - m }}
    while X <> 0 do
                  {{ Y - X = n - m /\ X <> 0 }} ->>
                  {{ (Y - 1) - (X - 1) = n - m }}
       Y := Y - 1
                  {{ Y - (X - 1) = n - m }} ;
       X := X - 1
                  {{ Y - X = n - m }}
    end
  {{ Y - X = n - m /\ X = 0 }} ->>
  {{ Y = n - m }} }>.


Theorem subtract_slowly_outer_triple_valid : forall m n,
  outer_triple_valid (subtract_slowly_dec m n).
Proof.
  verify. (* this grinds for a bit! *)
Qed.

Example slow_assignment_dec (m : nat) : decorated :=
  <{
   {{ X = m /\ Y = 0 }} ->>
                    {{ X + Y = m }} 
      while X <> 0 do
                    {{ X + Y = m /\ X <> 0  }} ->>
                    {{ (X - 1) + (Y + 1) = m }}
         X := X - 1
                    {{ X + (Y + 1) = m }} ;
         Y := Y + 1
                    {{ X + Y = m }}
      end
    {{ (X + Y = m) /\ X = 0 }} ->>
    {{ Y = m }}
  }>.

Theorem slow_assignment : forall m,
  outer_triple_valid (slow_assignment_dec m).
Proof. verify. Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Definition parity_dec (m:nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ ap parity X = parity m  }}
    while 2 <= X do
                  {{ ap parity X = parity m /\ (2 <= X) }} ->>
                  {{ ap parity (X-2) = parity m }}
      X := X - 2
                  {{ ap parity X = parity m }}
    end
  {{ ap parity X = parity m  /\ ~(2 <= X) }} ->>
  {{ X = parity m }} }>.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct x. 
    + inversion H. inversion H1. 
    + simpl. rewrite sub_0_r. reflexivity.
  Qed.


Lemma parity_lt_2 : forall x,
  ~ 2 <= x -> parity x = x.
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct x.
    + reflexivity.
    + unfold not in H.
      assert (2 <= S (S x)).
      * lia.
    *  apply H in H0.
       inversion H0.
  Qed. 

Theorem parity_outer_triple_valid : forall m,
  outer_triple_valid (parity_dec m).
Proof.
  verify. 
  - destruct (st X) eqn:Hx.
    + inversion H0.
    + destruct n.
      * inversion H0.
      * lia.
  - intros contra. 
    destruct (st X) eqn:Hx.
    + inversion contra.
    + destruct n.
      * inversion contra.
        ** inversion H2.
      * inversion H0.
  - rewrite <- H. apply parity_ge_2. apply H0.
  - rewrite <- H. symmetry. apply parity_lt_2. apply H0.
Qed.

Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X = m }} ->>
    {{ X = m /\ 0 * 0 <= m }}
      Z := 0
                   {{ X = m /\ Z * Z <= m }};
      while (( Z + 1 ) * ( Z + 1 ) <= X) do
                   {{ X = m /\ Z * Z <= m /\ (Z+1)*(Z+1)<=X }} ->>
                   {{  X = m /\ (Z+1)*(Z+1) <= m  }}
        Z := Z + 1
                   {{ X = m /\ Z * Z <= m }}
      end
    {{  X = m /\ Z * Z <= m  /\ ~((Z+1)*(Z+1)<=X) }} ->>
    {{ Z * Z <= m /\ m<(Z+1)*(Z+1) }}
  }>.

Theorem sqrt_correct : forall m,
  outer_triple_valid (sqrt_dec m).
Proof. verify. Qed.

Fixpoint fact (n : nat) : nat :=
      match n with
      | O => 1
      | S n' => n * (fact n')
      end.

Example factorial_dec (m:nat) : decorated := 
<{
    {{ X = m }} ->>
    {{ 1 * ap fact X  = fact m }}
      Y := 1
         {{ Y * ap fact X = fact m }};
      while (X <> 0) do
       {{ Y * ap fact X = fact m /\ X <> 0 }} ->>
       {{ Y * X * ap fact (X - 1) = fact m }}
     Y :=  Y * X
       {{  Y * ap fact (X - 1) = fact m }};
     X :=  X - 1
       {{ Y * ap fact X = fact m }}
   end
     {{ Y * ap fact X = fact m /\ X = 0 }} ->>
     {{ Y = fact m }}
}>.

Theorem factorial_correct: forall m,
  outer_triple_valid (factorial_dec m).
Proof. verify.
   - destruct (st X) eqn:Hst in H.
     + rewrite Hst in H0.
       unfold not in H0.
       assert (0=0).
       * reflexivity.
       * apply H0 in H1.
         inversion H1.
    + simpl in H.
      rewrite Hst.
      simpl. rewrite sub_0_r. 
      lia.
   - simpl in H.
     lia.
  Qed. 

Definition minimum_dec (a b : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 0 + ap2 min a b = ap2 min a b }}
      X := a
             {{ 0 + ap2 min X b = ap2 min a b  }};
      Y := b
             {{ 0 + ap2 min X Y = ap2 min a b  }};
      Z := 0
             {{ Z + ap2 min X Y = ap2 min a b  }};
      while X <> 0 && Y <> 0 do
             {{ Z + ap2 min X Y = ap2 min a b /\ X <> 0 /\ Y <> 0 }} ->>
             {{ Z + 1 + ap2 min (X-1) (Y-1) = ap2 min a b }}
        X := X - 1
             {{Z + 1 + ap2 min X (Y-1) = ap2 min a b}};
        Y := Y - 1
             {{ Z + 1 + ap2 min X Y = ap2 min a b }};
        Z := Z + 1
             {{ Z + ap2 min X Y = ap2 min a b  }}
      end
    {{ ( Z + ap2 min X Y = ap2 min a b ) /\ ( X = 0 \/ Y = 0) }} ->>
    {{ Z = min a b }}
  }>.

Theorem minimum_correct : forall a b,
  outer_triple_valid (minimum_dec a b).
Proof. verify.
   - rewrite <- negb_orb in H0. 
     rewrite negb_true_iff in H0. 
     rewrite orb_false_iff in H0.
     destruct H0.  unfold not. intros.
     apply eqb_eq in H2. rewrite H2 in H0.
     inversion H0.
  - rewrite <- negb_orb in H0. 
     rewrite negb_true_iff in H0. 
     rewrite orb_false_iff in H0.
     destruct H0.  unfold not. intros.
     apply eqb_eq in H2. rewrite H2 in H1.
     inversion H1.
   - rewrite <- negb_orb in H0. 
     rewrite negb_false_iff in H0. 
     rewrite orb_true_iff in H0.
     destruct H0.   
     + apply eqb_eq in H0. left. apply H0.
     + apply eqb_eq in H0. right. apply H0.
 Qed.


Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ c = 0 + 0 + c }}
      X := 0
                   {{ c = X + 0 + c }};
      Y := 0
                   {{ c = X + Y + c }};
      Z := c
                   {{ Z = X + Y + c }};
      while X <> a do
                   {{ Z = X + Y + c /\ X <> a }} ->>
                   {{ Z + 1 = X + 1 + Y + c }}
        X := X + 1
                   {{ Z + 1 = X + Y + c }};
        Z := Z + 1
                   {{ Z = X + Y + c }}
      end
                   {{ Z = X + Y + c /\ X = a }} ->>
                   {{ Z = a + Y + c }};
      while Y <> b do
                   {{ Z = a + Y + c /\ Y <> b }} ->>
                   {{ Z + 1 = a + Y + 1 + c }}
        Y := Y + 1
                   {{ Z + 1 = a + Y + c }};
        Z := Z + 1
                   {{ Z = a + Y + c }}
      end
    {{ Z = a + Y + c /\ Y = b }} ->>
    {{ Z = a + b + c }}
  }>.

Theorem two_loops : forall a b c,
  outer_triple_valid (two_loops_dec a b c).
Proof.
verify.
Qed.

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.


Definition dpow2_dec (n : nat) :=
  <{
    {{ True }} ->>
    {{ 1 = pow2 (0 + 1) - 1 /\ 1 = pow2 0 }}
      X := 0
               {{ 1 = ap pow2 (X + 1) - 1 /\ 1 = ap pow2 X }};
      Y := 1
               {{ Y = ap pow2 (X + 1) - 1 /\ 1 = ap pow2 X }};
      Z := 1
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X }};
      while X <> n do
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X /\ X <> n }} ->>
               {{ Y + 2 * Z = ap pow2 ((X + 1) + 1) - 1 /\ 2 * Z = ap pow2 (X + 1) }}
        Z := 2 * Z
               {{ Y + Z = ap pow2 ((X + 1) + 1) - 1 /\ Z = ap pow2 (X + 1)}};
        Y := Y + Z
               {{ Y = ap pow2 ((X + 1) + 1) - 1 /\ Z = ap pow2 (X + 1) }};
        X := X + 1
               {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X  }}
      end
    {{ Y = ap pow2 (X + 1) - 1 /\ Z = ap pow2 X /\ X = n }} ->>
    {{ Y = pow2 (n + 1) - 1 }}
  }>.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof.
  induction n; simpl.
  - reflexivity.
  - lia.
Qed.


Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof.
  induction n; simpl; [constructor | lia].
Qed.

Theorem dpow2_down_correct : forall n,
  outer_triple_valid (dpow2_dec n).
Proof.
verify.
- rewrite pow2_plus_1. rewrite pow2_plus_1. rewrite pow2_plus_1. lia.
- rewrite pow2_plus_1. lia.
Qed.


Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.
 

Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (1 + n).
Proof.
  intros. 
  induction n. 
  - inversion H.
  - simpl. destruct n.
    + simpl. reflexivity.
    + reflexivity.
Qed.

Definition T : string := "T".

Definition dfib (n : nat) : decorated :=
  <{
    {{ True }} ->>
    {{ 1 + 1 = fib (1 + 1) /\ 1 = fib 1 }}
    X := 1
                {{ 1 + 1 = ap fib (1 + X) /\ 1 = ap fib X }} ;
    Y := 1
                {{ 1 + Y = ap fib (1 + X) /\ 1 = ap fib X }} ;
    Z := 1
                {{ Z + Y = ap fib (1 + X) /\ Z = ap fib X }} ;
    while X <> 1 + n do
                  {{ Z + Y = ap fib (1 + X) /\ Z = ap fib X /\ X <> 1 + n }} ->>
                  {{ Z + Z + Y = ap fib (1 + 1 + X) /\ Z + Y = ap fib (1 + X) }}
      T := Z
                  {{ T + Z + Y = ap fib (1 + 1 + X) /\ Z + Y = ap fib (1 + X) }};
      Z := Z + Y
                  {{ T + Z = ap fib (1 + 1 + X) /\ Z = ap fib (1 + X) }};
      Y := T
                  {{ Y + Z = ap fib (1 + 1 + X) /\ Z = ap fib (1 + X) }};
      X := 1 + X
                  {{ Y + Z = ap fib (1 + X) /\ Z = ap fib X }}
    end
    {{ Y + Z = ap fib (1 + X) /\ Z = ap fib X /\ X = 1 + n }} ->>
    {{ Y = fib n }}
   }>.

Theorem dfib_correct : forall n,
  outer_triple_valid (dfib n).
Proof.
verify.
Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
  unfold is_wp. simpl. split.
  - unfold valid_hoare_triple.
    intros. inversion H. subst. rewrite t_update_eq.
    simpl. lia.
  - intros. unfold "->>". intros.
    unfold valid_hoare_triple in H.
    remember (X !-> aeval st <{ Y + 1 }>; st) as st'.
    assert (st =[ X := Y + 1 ]=> st').
    + rewrite Heqst'. apply E_Asgn. reflexivity.
    + apply H in H1.
      * rewrite Heqst' in H1.  
        rewrite t_update_eq in H1. simpl in H1. lia.
      * apply H0.
Qed.


Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
 intros.
 unfold is_wp.  split.
 - apply hoare_asgn.
 - intros.  unfold "->>". intros.
    unfold valid_hoare_triple in H. unfold assertion_sub.
   apply H with st.
   + apply E_Asgn. reflexivity.
   + apply H0.
Qed.

Module Himp2.
Import Himp.
Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  {{ P }} havoc X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
intros.
unfold "->>". intros. unfold havoc_pre. intros.
unfold valid_hoare_triple in H.
apply H with st.
- apply  E_Havoc.
- apply H0.
Qed.

End Himp2.
