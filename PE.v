From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import SmallStep.
From PLF Require Import Imp.


Definition pe_state := list (string * nat).

Fixpoint pe_lookup (pe_st : pe_state) (V:string) : option nat :=
  match pe_st with
  | [] => None
  | (V',n')::pe_st => if String.eqb V V' then Some n'
                      else pe_lookup pe_st V
  end.

Definition empty_pe_state : pe_state := []. 


Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (String.eqb_spec i j) as [H|H];
  [ subst j | ].


Theorem pe_domain: forall pe_st V n,
  pe_lookup pe_st V = Some n ->
  In V (map (@fst _ _) pe_st).
Proof. 
  intros. 
  induction pe_st. 
 - simpl. simpl in H. inversion H.
 - simpl. simpl in H. destruct a. compare V s.
   + injection H. intros. subst. simpl. left. reflexivity.
   + right. apply IHpe_st. apply H. 
Qed.


Fixpoint inb {A : Type} (eqb : A -> A -> bool) (a : A) (l : list A) :=
  match l with
  | [] => false
  | a'::l' => eqb a a' || inb eqb a l'
  end.



Lemma inbP : forall A : Type, forall eqb : A -> A -> bool,
  (forall a1 a2, reflect (a1 = a2) (eqb a1 a2)) ->
  forall a l, reflect (In a l) (inb eqb a l).
Proof.
  intros. 
  induction l.
  - simpl. apply  ReflectF. intros contra. inversion contra. 
  - simpl. destruct (eqb0 a a0) eqn:Heq. 
    + simpl. apply ReflectT. 
      specialize X with (a1:=a) (a2:=a0).
      rewrite Heq in X. apply reflect_iff in X. destruct X. 
      destruct H0. 
      * reflexivity. 
      * left. reflexivity. 
    + simpl. specialize X with (a1:=a) (a2:=a0). rewrite Heq in X.
      apply reflect_iff in X. apply iff_reflect. split. 
      * intros. destruct H. 
        -- symmetry in H. apply X in H. inversion H. 
        -- apply reflect_iff in IHl. apply IHl in H. apply H.
      * intros.  apply reflect_iff in IHl. apply IHl in H. 
        right. apply H.
Qed.


Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => match pe_lookup pe_st i with (* <----- NEW *)
             | Some n => ANum n
             | None => AId i
             end
  | <{ a1 + a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => <{ a1' + a2' }>
      end
  | <{ a1 - a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => <{ a1' - a2' }>
      end
  | <{ a1 * a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => <{ a1' * a2' }>
      end
  end.

Example test_pe_aexp1:
  pe_aexp [(X,3)] <{X + 1 + Y}> = <{4 + Y}>.
Proof.
  simpl. reflexivity. 
Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] <{X + 1 + Y}> = <{X + 1 + 3}>. 
Proof. 
 simpl. reflexivity. Qed.

Definition pe_consistent (st:state) (pe_st:pe_state) :=
  forall V n, Some n = pe_lookup pe_st V -> st V = n.


Theorem pe_aexp_correct_weak: forall st pe_st, pe_consistent st pe_st ->
  forall a, aeval st a = aeval st (pe_aexp pe_st a).
Proof.
  intros. unfold pe_consistent in H. 
  induction a. 
  - simpl.  reflexivity. 
  - simpl. destruct (pe_lookup pe_st x) eqn:Heq. 
    + simpl. apply H. symmetry. apply Heq. 
    + simpl. reflexivity. 
  - simpl.   destruct (pe_aexp pe_st a1) eqn:Heq1.
    + destruct (pe_aexp pe_st a2) eqn:Heq2.
      * simpl. rewrite IHa1. rewrite IHa2. simpl. reflexivity.
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
* rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
- simpl. destruct (pe_aexp pe_st a1) eqn:Heq1.
    + destruct (pe_aexp pe_st a2) eqn:Heq2.
      * simpl. rewrite IHa1. rewrite IHa2. simpl. reflexivity.
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
* rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
- simpl. destruct (pe_aexp pe_st a1) eqn:Heq1.
    + destruct (pe_aexp pe_st a2) eqn:Heq2.
      * simpl. rewrite IHa1. rewrite IHa2. simpl. reflexivity.
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
* rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  * rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
  + rewrite IHa1. rewrite IHa2. simpl. reflexivity.
+ rewrite IHa1. rewrite IHa2. simpl. reflexivity.
Qed.

Fixpoint pe_update (st:state) (pe_st:pe_state) : state :=
  match pe_st with
  | [] => st
  | (V,n)::pe_st => t_update (pe_update st pe_st) V n
  end.


Example test_pe_update:
  pe_update (Y !-> 1) [(X,3);(Z,2)]
  = (X !-> 3 ; Z !-> 2 ; Y !-> 1).
Proof.
 simpl. reflexivity.  
Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> String.eqb x y = false.
Proof. 
  intros. 
  rewrite String.eqb_neq.
  apply H. 
Qed.

Theorem pe_update_correct: forall st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | Some n => n
  | None => st V0
  end.
Proof. 
 intros. 
 induction pe_st.
 - simpl. reflexivity.
 - simpl. destruct a. compare V0 s. 
   + rewrite t_update_eq. reflexivity. 
   + rewrite <- IHpe_st. assert (s<>V0).
     * intros contra. apply HeqV0s. symmetry. apply contra.
     * eapply t_update_neq in H. rewrite H. reflexivity.  
Qed.

Theorem pe_update_consistent: forall st pe_st,
  pe_consistent (pe_update st pe_st) pe_st.
Proof. 
  intros. unfold pe_consistent. 
  intros. induction pe_st.
  - simpl. simpl in H. inversion H. 
  - simpl. destruct a. simpl in H. compare V s.
    + rewrite t_update_eq. injection H. intros. subst. 
      reflexivity. 
    + assert (s<>V).
     * intros contra. apply HeqVs. symmetry. apply contra.
     * eapply t_update_neq in H0. rewrite H0. apply IHpe_st.
       apply H. 
Qed. 

Theorem pe_consistent_update: forall st pe_st,
  pe_consistent st pe_st -> forall V, st V = pe_update st pe_st V.
Proof.
  intros. rewrite pe_update_correct. 
  unfold pe_consistent in H. 
  destruct (pe_lookup pe_st V) eqn:Hn.  
  - apply H. symmetry. apply Hn.
  - reflexivity. 
Qed.

Theorem pe_aexp_correct: forall (pe_st:pe_state) (a:aexp) (st:state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a).
Proof.
  intros. 
  induction a. 
  - simpl. reflexivity. 
  -  induction pe_st.
    + simpl. reflexivity.
    + simpl. destruct a. compare x s.
      * rewrite t_update_eq. simpl. reflexivity. 
      *  assert (s<>x).
        -- intros contra. apply Heqxs. symmetry. apply contra.
        -- eapply t_update_neq in H. rewrite H. apply IHpe_st.
  - simpl. destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
   + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
- simpl.  destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
   + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
- simpl.  destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      * rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
      *  rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
   + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
 + rewrite IHa1. rewrite IHa2. simpl. reflexivity. 
Qed. 

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ a1 = a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 =? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if negb (n1 =? n2) then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ true }> else <{ false }>
      | (a1', a2') => <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }> =>
      match (pe_aexp pe_st a1, pe_aexp pe_st a2) with
      | (ANum n1, ANum n2) => if n1 <=? n2 then <{ false }> else <{ true }>
      | (a1', a2') => <{ a1' > a2' }>
      end
  | <{ ~ b1 }> =>
      match (pe_bexp pe_st b1) with
      | <{ true }> => <{ false }>
      | <{ false }> => <{ true }>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }> =>
      match (pe_bexp pe_st b1, pe_bexp pe_st b2) with
      | (<{ true }>, <{ true }>) => <{ true }>
      | (<{ true }>, <{ false }>) => <{ false }>
      | (<{ false }>, <{ true }>) => <{ false }>
      | (<{ false }>, <{ false }>) => <{ false }>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.


Example test_pe_bexp1:
  pe_bexp [(X,3)] <{~ (X <= 3)}> = <{ false }>.
Proof.
  simpl. reflexivity. 
Qed.

Example test_pe_bexp2: forall b:bexp,
  b = <{ ~ (X <= (X + 1)) }> -> pe_bexp [] b = b.
Proof.
  intros. 
  rewrite H.  simpl.  reflexivity. 
Qed.

Theorem pe_bexp_correct: forall (pe_st:pe_state) (b:bexp) (st:state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b).
Proof.
 intros. 
  induction b. 
  - simpl. reflexivity. 
  - simpl. reflexivity.
  - simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct. 
    destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
      * destruct (n =? n0) eqn:Hnn. 
        -- assert ((n =? n0) = true). 
           ++ apply Hnn.
           ++ apply eqb_eq in Hnn. subst. simpl. apply H.   
        --  simpl. apply Hnn. 
      * simpl. reflexivity.
      * simpl. reflexivity.  
 * simpl. reflexivity.
      * simpl. reflexivity.  
   + simpl. reflexivity.  
   + simpl. reflexivity.  
  + simpl. reflexivity.  
   + simpl. reflexivity. 
 - simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct. 
    destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
 * destruct (n =? n0) eqn:Hnn. 
        -- assert ((n =? n0) = true). 
           ++ apply Hnn.
           ++ apply eqb_eq in Hnn. subst. simpl. rewrite H. simpl. reflexivity.    
        --  simpl. rewrite Hnn. simpl. reflexivity.    
      * simpl. reflexivity.
      * simpl. reflexivity.  
* simpl. reflexivity.
      * simpl. reflexivity.  
   + simpl. reflexivity.  
   + simpl. reflexivity.  
  + simpl. reflexivity.  
   + simpl. reflexivity. 
 - simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct. 
    destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
* destruct (n <=? n0) eqn:Hnn. 
        -- assert ((n <=? n0) = true). 
           ++ apply Hnn.
           ++ simpl. apply H. 
        --  simpl. apply Hnn.   
      * simpl. reflexivity.
      * simpl. reflexivity.  
* simpl. reflexivity.
      * simpl. reflexivity.  
   + simpl. reflexivity.  
   + simpl. reflexivity.  
  + simpl. reflexivity.  
   + simpl. reflexivity.
- simpl. rewrite pe_aexp_correct. rewrite pe_aexp_correct. 
    destruct (pe_aexp pe_st a1). 
    + destruct (pe_aexp pe_st a2).
* destruct (n <=? n0) eqn:Hnn. 
        -- assert ((n <=? n0) = true). 
 ++ apply Hnn.
           ++ simpl. rewrite H. simpl. reflexivity. 
        --  simpl. rewrite Hnn. simpl. reflexivity.   
      * simpl. reflexivity.
      * simpl. reflexivity.  
* simpl. reflexivity.
      * simpl. reflexivity.  
   + simpl. reflexivity.  
   + simpl. reflexivity.  
  + simpl. reflexivity.  
   + simpl. reflexivity.


- simpl. rewrite IHb.
    destruct (pe_bexp pe_st b). 
    + simpl. reflexivity. 
    + simpl. reflexivity. 
 + simpl. reflexivity. 
    + simpl. reflexivity. 
   + simpl. reflexivity. 
    + simpl. reflexivity. 
 + simpl. reflexivity. 
    + simpl. reflexivity. 

- simpl. rewrite IHb1. rewrite IHb2.
   destruct (pe_bexp pe_st b1);
   destruct (pe_bexp pe_st b2); simpl; reflexivity. 
Qed.


Fixpoint pe_remove (pe_st:pe_state) (V:string) : pe_state :=
  match pe_st with
  | [] => []
  | (V',n')::pe_st => if String.eqb V V' then pe_remove pe_st V
                      else (V',n') :: pe_remove pe_st V
  end.


Theorem pe_remove_correct: forall pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0
  = if String.eqb V V0 then None else pe_lookup pe_st V0.
Proof.
  induction pe_st. 
  - simpl. intros. compare V V0. 
    + reflexivity.
    + reflexivity. 
  - simpl. destruct a . intros. compare V s.
    + specialize IHpe_st with (V:=V) (V0:=V0).  compare V V0. 
      * apply IHpe_st.
      * assert (V0 <> V).
        -- intros contra. apply HeqVV0. symmetry.
           apply contra.
        -- rewrite <- String.eqb_neq in H. rewrite H.
           rewrite IHpe_st. reflexivity. 
   +  specialize IHpe_st with (V:=V) (V0:=V0).  compare V V0. 
     * simpl. rewrite <- String.eqb_neq in HeqVs. rewrite HeqVs. apply IHpe_st.
     * simpl. rewrite IHpe_st. reflexivity. 
Qed.
       
Definition pe_add (pe_st:pe_state) (V:string) (n:nat) : pe_state :=
  (V,n) :: pe_remove pe_st V.

Theorem pe_add_correct: forall pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0
  = if String.eqb V V0 then Some n else pe_lookup pe_st V0.
Proof.
  intros.  compare V V0. 
  - simpl. rewrite String.eqb_refl. reflexivity. 
  - simpl.  assert (V0 <> V).
    + intros contra. apply HeqVV0. symmetry.
           apply contra.
    + rewrite <- String.eqb_neq in H. rewrite H. rewrite pe_remove_correct.
      rewrite <- String.eqb_neq in HeqVV0.  rewrite HeqVV0. reflexivity. 
Qed.
      
Theorem pe_update_update_remove: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update (t_update st V n) (pe_remove pe_st V).
Proof.
  intros.  
  induction pe_st.
  - simpl. reflexivity. 
  - simpl. destruct a. compare V s.
    + rewrite t_update_shadow. apply IHpe_st.
    + simpl. eapply t_update_permute in HeqVs. rewrite <- HeqVs.
      rewrite IHpe_st. reflexivity. 
Qed.


Theorem pe_update_update_add: forall st pe_st V n,
  t_update (pe_update st pe_st) V n =
  pe_update st (pe_add pe_st V n).
Proof.
 intros. 
 induction pe_st. 
 - simpl. reflexivity. 
 - simpl. destruct a. compare V s.
   + rewrite t_update_shadow. rewrite IHpe_st. simpl. reflexivity. 
   + assert (V <> s).
    * intros contra. apply HeqVs. apply contra.
    * simpl. eapply t_update_permute in HeqVs. rewrite <- HeqVs. rewrite IHpe_st. simpl. 
      eapply t_update_permute in H. rewrite <- H. reflexivity.
Qed. 
 
Definition pe_disagree_at (pe_st1 pe_st2 : pe_state) (V:string) : bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | Some x, Some y => negb (x =? y)
  | None, None => false
  | _, _ => true
  end.


Theorem pe_disagree_domain: forall (pe_st1 pe_st2 : pe_state) (V:string),
  true = pe_disagree_at pe_st1 pe_st2 V ->
  In V (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2).
Proof.
  intros. 
  induction pe_st1.
  - induction pe_st2. 
    + unfold pe_disagree_at in H.
      simpl in H. inversion H. 
    + simpl. unfold fst. unfold pe_disagree_at in H. simpl in H.  destruct a. compare V s. 
      * left. reflexivity. 
      * unfold pe_disagree_at in IHpe_st2.  simpl in IHpe_st2. unfold fst in IHpe_st2.
          right. apply IHpe_st2.  destruct (pe_lookup pe_st2 V).
         -- reflexivity. 
         -- inversion H. 
  - induction pe_st2.
    + unfold pe_disagree_at in H. simpl in H. simpl. unfold fst. destruct a.
      compare V s. 
      * left. reflexivity. 
      * unfold pe_disagree_at in IHpe_st1.  simpl in IHpe_st1. 
          right. apply IHpe_st1.  destruct (pe_lookup pe_st1 V).
        -- reflexivity. 
        -- inversion H. 
    +  simpl. simpl in IHpe_st1. unfold fst. unfold pe_disagree_at in H. simpl in H.  destruct a.  
       compare V s.
     * left. reflexivity. 
      * unfold pe_disagree_at in IHpe_st1.  simpl in IHpe_st1. 
          right. apply IHpe_st1. apply H.  
Qed.

Locate in_app_iff.

Locate filter.

Fixpoint pe_unique (l : list string) : list string :=
  match l with
  | [] => []
  | x::l =>
      x :: filter (fun y => if String.eqb x y then false else true) (pe_unique l)
  end.

Theorem pe_unique_correct: forall l x,
  In x l <-> In x (pe_unique l).
Proof. 
intros l x. induction l as [| h t]. reflexivity.
 simpl in *. split.
  - (* -> *)
    intros. destruct H. 
    + left. apply H.
    + destruct ((h =? x)%string) eqn:Hx.
      * left. apply String.eqb_eq in Hx.  apply Hx.
      * right. apply filter_In. split. 
        -- apply IHt.  apply H. 
        -- rewrite Hx. reflexivity. 
  - intros. destruct H. 
    + left. apply H. 
    + right.  rewrite filter_In in H.  destruct H. apply IHt. apply H.
Qed. 

Definition pe_compare (pe_st1 pe_st2 : pe_state) : list string :=
  pe_unique (filter (pe_disagree_at pe_st1 pe_st2)
    (map (@fst _ _) pe_st1 ++ map (@fst _ _) pe_st2)).

Theorem pe_compare_correct: forall pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V <->
  ~ In V (pe_compare pe_st1 pe_st2).
Proof.
  intros. split. 
  - intros. intros contra.
    induction pe_st1.
    +  induction pe_st2.
      * simpl in contra. inversion contra. 
      * simpl in H. destruct a.  compare V s. 
        -- inversion H.
        -- simpl in IHpe_st2. apply IHpe_st2. 
           ++ apply H. 
           ++ simpl. unfold pe_compare. simpl. rewrite <- pe_unique_correct.
              rewrite filter_In. unfold pe_compare in contra. 
               rewrite <- pe_unique_correct in contra.
                   rewrite filter_In in contra. destruct contra. simpl in H0. 
                  destruct H0.
               ** rewrite H0 in HeqVs. exfalso. apply HeqVs. auto.
               ** split. 
                  --- apply H0. 
                  --- unfold pe_disagree_at. simpl. unfold pe_disagree_at in H1. 
                        simpl in H1. rewrite <- String.eqb_neq in HeqVs. rewrite HeqVs in H1.
                       apply H1. 
      + simpl in H. unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
                   rewrite filter_In in contra. destruct contra. simpl in H0. 
                  destruct H0. 
        * unfold fst in H0. destruct a. symmetry in H0. rewrite <- String.eqb_eq in H0.
          rewrite H0 in H. unfold pe_disagree_at in H1. simpl in H1. rewrite H0 in H1. 
         rewrite <- H in H1. destruct (n =? n) eqn:Hnn. 
         -- simpl in H1. inversion H1. 
         -- rewrite eqb_neq in Hnn. apply Hnn. auto. 
        * destruct a. unfold pe_disagree_at in H1. simpl in H1. compare V s. rewrite <- H in H1.
             destruct (n =? n) eqn:Hnn. 
         -- simpl in H1. inversion H1. 
         -- rewrite eqb_neq in Hnn. apply Hnn. auto. 
     -- apply IHpe_st1. 
        ++ apply H. 
        ++ unfold pe_compare. rewrite <- pe_unique_correct.
              rewrite filter_In. split. 
           ** apply H0. 
           ** unfold pe_disagree_at. apply H1. 
    - intros.  induction pe_st1.
    +  induction pe_st2. 
     * auto. 
     * simpl. destruct a. unfold pe_compare in H. rewrite <- pe_unique_correct in H.
              rewrite filter_In in H. simpl in H. unfold pe_disagree_at in H. simpl in H. 
              compare V s.
       -- exfalso. apply H. split. 
          ++ left. auto. 
          ++ auto. 
       -- simpl in IHpe_st2. apply IHpe_st2. intros contra. 
          unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
              rewrite filter_In in contra. simpl in contra. destruct contra. 
          apply H. split. 
          ++ right. apply H0. 
          ++ unfold pe_disagree_at in H1. simpl in H1. apply H1. 
     + induction pe_st2. 
        * simpl. destruct a. unfold pe_compare in H. rewrite <- pe_unique_correct in H.
          rewrite filter_In in H. simpl in H. unfold pe_disagree_at in H. simpl in H.   
          compare V s.
       -- exfalso. apply H. split. 
          ++ left. auto. 
          ++ auto. 
       -- simpl in IHpe_st1. apply IHpe_st1. intros contra. 
          unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
              rewrite filter_In in contra. simpl in contra. destruct contra. 
          apply H. split. 
          ++ right. apply H0. 
          ++ unfold pe_disagree_at in H1. simpl in H1. apply H1. 
    * unfold pe_compare in H .  rewrite <- pe_unique_correct in H.
          rewrite filter_In in H. simpl in H. unfold pe_disagree_at in H. destruct (pe_lookup (a :: pe_st1) V) eqn:Hst1.
      -- destruct (pe_lookup (a0 :: pe_st2) V) eqn:Hst2.
         ++ destruct (n =? n0) eqn:Hnn.
            ** apply eqb_eq in Hnn. subst.  auto. 
            ** simpl in Hst1. destruct a. compare V s.
               --- simpl in H. exfalso.  apply H. split. 
          +++ left. auto. 
          +++ auto.
             --- simpl in H. simpl in Hst2.  destruct a0.  compare V s0. unfold pe_compare in IHpe_st1.
                      rewrite <- pe_unique_correct in IHpe_st1.
                     rewrite filter_In in IHpe_st1. simpl in IHpe_st1. simpl in H.
           +++ rewrite <- Hst1. apply IHpe_st1. intros contra. apply H. 
               split. 
               *** right. destruct contra. apply H0. 
               *** auto. 
           +++ rewrite <- Hst1. apply IHpe_st1. intros contra. apply H. split.   
               *** right. unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
                     rewrite filter_In in contra. destruct contra. simpl in H0. simpl. apply H0. 
               *** auto.
          ++ simpl in Hst1. destruct a. compare V s. 
             ** simpl in H. exfalso.  apply H.  split. 
                --- left. auto. 
                --- auto. 
             ** rewrite <- Hst1. apply IHpe_st1. intros contra. apply H. split. 
                --- right. unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
                     rewrite filter_In in contra. destruct contra. simpl in H0. apply H0.
                --- auto. 
         -- destruct (pe_lookup (a0 :: pe_st2) V) eqn:Hst2.
            ++ simpl in Hst1. destruct a. compare V s. simpl in H. 
               ** exfalso. apply H. split. 
                  --- left.  auto. 
          --- auto.
              ** rewrite <- Hst1. apply IHpe_st1. intros contra. apply H. split.   
--- right. unfold pe_compare in contra. rewrite <- pe_unique_correct in contra.
                     rewrite filter_In in contra. destruct contra. simpl in H0. apply H0.
                --- auto. 
              ++  auto. 
Qed.

Fixpoint pe_removes (pe_st:pe_state) (ids : list string) : pe_state :=
  match ids with
  | [] => pe_st
  | V::ids => pe_remove (pe_removes pe_st ids) V
  end.

Theorem pe_removes_correct: forall pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb String.eqb V ids then None else pe_lookup pe_st V.
Proof. 
 intros.  
generalize dependent pe_st.
induction ids. 
 - intros. simpl. reflexivity. 
 - intros. simpl.  destruct (pe_removes pe_st ids) eqn:Hp. 
   + simpl. compare V a. 
      * simpl. reflexivity.
      * specialize IHids with pe_st.  rewrite Hp in IHids. simpl in IHids.
        simpl. apply IHids.
   + simpl. destruct p eqn:Heq . compare a s.
     * compare V a.
        -- simpl. rewrite pe_remove_correct.  rewrite String.eqb_refl. reflexivity.     
        -- simpl. rewrite pe_remove_correct. assert(a<>V). 
           ++ intros contra.  apply HeqVa.  symmetry.  apply contra. 
           ++ apply String.eqb_neq in H. rewrite H. specialize IHids with pe_st. rewrite Hp in IHids.
               simpl in IHids. apply String.eqb_neq in HeqVa. rewrite HeqVa in IHids. 
               apply IHids.
      * simpl. compare V s. 
        -- compare V a.
           ++ exfalso. apply Heqas. auto.
           ++ simpl. specialize IHids with pe_st. rewrite Hp in IHids. simpl in IHids. 
              rewrite String.eqb_refl in IHids. apply IHids. 
        -- compare V a. 
           ++ simpl. rewrite pe_remove_correct. rewrite String.eqb_refl. auto.
           ++ simpl. rewrite pe_remove_correct. specialize IHids with pe_st. rewrite Hp in IHids. simpl in IHids.
               apply String.eqb_neq in HeqVs. rewrite HeqVs in IHids. assert(a<>V). 
               ** intros contra.  apply HeqVa.  symmetry.  apply contra. 
               ** apply String.eqb_neq in H. rewrite H. apply IHids. 
Qed. 

Theorem pe_compare_removes: forall pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V.
Proof.
  intros. 
  rewrite pe_removes_correct. 
  rewrite pe_removes_correct. 
  destruct (pe_compare pe_st1 pe_st2) eqn:Hc.
  - simpl. assert (~ In V (pe_compare pe_st1 pe_st2)).
    + rewrite Hc. simpl. intros contra. inversion contra. 
    + apply pe_compare_correct in H. apply H. 
  - simpl. compare V s. 
    + simpl. auto. 
    + simpl. destruct (inb String.eqb V l) eqn:Hvl.
      * auto. 
      * Locate reflect. specialize inbP with (A:= string) (eqb:=String.eqb).
        intros H1. assert (forall a1 a2 : string, reflect (a1 = a2) (a1 =? a2)%string).
         -- intros. apply iff_reflect.  split. 
            ++ intros. rewrite String.eqb_eq. apply H. 
            ++ intros.  rewrite String.eqb_eq in H. apply H.
         -- apply H1 with (a:=V) (l:=l) in H.  

assert (~ In V (pe_compare pe_st1 pe_st2)).
++ rewrite Hc. simpl.  intros contra. 
   destruct contra. 
   ** apply HeqVs. symmetry. apply H0. 
   ** rewrite Hvl in H. apply reflect_iff in H. apply H in H0.
      inversion H0. 
++  apply pe_compare_correct in H0. apply H0. 
Qed. 


Theorem pe_compare_update: forall pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)).
Proof. 
  intros. apply functional_extensionality.
  intros. rewrite !pe_update_correct. rewrite pe_compare_removes. reflexivity.
Qed.


Fixpoint assign (pe_st : pe_state) (ids : list string) : com :=
  match ids with
  | [] => <{ skip }>
  | V::ids => match pe_lookup pe_st V with
              | Some n => <{ assign pe_st ids; V := n }>
              | None => assign pe_st ids
              end
  end.

Definition assigned (pe_st:pe_state) (ids : list string) (st:state) : state :=
  fun V => if inb String.eqb V ids then
                match pe_lookup pe_st V with
                | Some n => n
                | None => st V
                end
           else st V.


Theorem assign_removes: forall pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids).
Proof. 
 intros. apply functional_extensionality.
  intros. rewrite !pe_update_correct. rewrite pe_removes_correct. 
 unfold assigned. destruct (inb String.eqb x). 
 - reflexivity. 
 - reflexivity. 
Qed.

Locate functional_extensionality.

Lemma ceval_extensionality: forall c st st1 st2,
  st =[ c ]=> st1 -> (forall V, st1 V = st2 V) -> st =[ c ]=> st2.
Proof. 
intros.
generalize dependent st2.
induction H. 
- intros. apply functional_extensionality in H0.  subst. apply E_Skip. 
- intros. apply functional_extensionality in H0.  subst. apply E_Asgn. auto.
- intros. apply E_Seq with (st':=st').
  + apply H.
  + apply functional_extensionality in H1.  subst. apply H0. 
- intros. apply E_IfTrue. 
  + apply H.
  + apply IHceval. apply H1. 
- intros. apply E_IfFalse. 
+ apply H.
  + apply IHceval. apply H1. 
- intros. apply functional_extensionality in H0. subst. apply E_WhileFalse. apply H. 
- intros. apply E_WhileTrue with (st':=st').
  + apply H.
  + apply H0. 
  + apply functional_extensionality in H2. subst. apply H1.
Qed. 

Theorem eval_assign: forall pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st.
Proof.
 intros. 
induction ids. 
 - simpl. unfold assigned. simpl. apply E_Skip. 
 - simpl. destruct (pe_lookup pe_st a) eqn:Ha. 
   + eapply E_Seq.
     * apply IHids.
     * remember (assigned pe_st ids st) as st0.
       remember (assigned pe_st (a :: ids) st) as st''.
       remember (a!->(aeval st0 n); st0) as st'.
       apply ceval_extensionality with st'. 
       -- subst st'. apply E_Asgn. simpl. auto.
       -- intros. subst. simpl. unfold assigned. simpl. 
          compare V a. simpl.
          ++ rewrite t_update_eq. rewrite Ha. auto.
          ++ simpl. assert(a<>V). 
               ** intros contra.  apply HeqVa.  symmetry.  apply contra. 
               **  eapply t_update_neq  in H.
              rewrite H. auto.
   + eapply ceval_extensionality. 
     * apply IHids. 
     * intros. unfold assigned.
       simpl. compare V a. 
       -- simpl. rewrite Ha. destruct(inb String.eqb V).
          ++ auto. 
          ++ auto. 
       -- simpl.  auto. 
Qed.

Reserved Notation "c1 '/' st '==>' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> Prop :=
  | PE_Skip : forall pe_st,
      <{skip}> / pe_st ==> <{skip}> / pe_st
  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{l := a1}> / pe_st ==> <{skip}> / pe_add pe_st l n1
  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat , a1' <> <{ n }>) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l
  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2',
      c1 / pe_st ==> c1' / pe_st' ->
      c2 / pe_st' ==> c2' / pe_st'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st''
  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st'
  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st'
  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 ->
      c2 / pe_st ==> c2' / pe_st2 ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2)

  where "c1 '/' st '==>' c1' '/' st'" := (pe_com c1 st c1' st').

Local Hint Constructors pe_com : core.
Local Hint Constructors ceval : core.

Example pe_example1:
  <{X := 3 ; Y := Z * (X + X)}> / [] ==> <{skip; Y := Z * 6}> / [(X,3)].
Proof.
  eapply PE_Seq.
  - apply PE_AsgnStatic.
    simpl. auto. 
  - apply PE_AsgnDynamic.
    + simpl. auto. 
    + intros. intros contra. inversion contra. 
Qed. 

Example pe_example2:
  <{X := 3 ; if X <= 4 then X := 4 else skip end}>
  / [] ==> <{skip; skip}> / [(X,4)].
Proof.
  eapply PE_Seq.
  - apply PE_AsgnStatic.
    simpl. auto. 
  - apply PE_IfTrue.
    + simpl. reflexivity.   
    + apply PE_AsgnStatic. simpl.  reflexivity.
Qed.


Example pe_example3:
  <{X := 3;
   if Y <= 4 then
     Y := 4;
     if X = Y then Y := 999 else skip end
   else skip end}> / []
  ==> <{skip;
       if Y <= 4 then
         (skip; skip); (skip; Y := 4)
       else skip; skip end}>
      / [(X,3)].
Proof. 
  erewrite f_equal2 with (f := fun c st =>  _ / _ ==> c / st).
  - eapply PE_Seq.
    + apply PE_AsgnStatic. simpl. auto.
    + apply PE_If.
      * simpl. intros contra. inversion contra. 
      * simpl. intros contra. inversion contra.
      * eapply PE_Seq.
        -- apply PE_AsgnStatic. simpl. auto. 
        -- apply PE_IfFalse. 
           ++ simpl. auto. 
           ++ apply PE_Skip. 
      * apply PE_Skip. 
  -  simpl. auto.
  - simpl. auto. 
Qed.   

Reserved Notation "c' '/' pe_st' '/' st '==>' st''"
  (at level 40, pe_st' at level 39, st at level 39).

Inductive pe_ceval
  (c':com) (pe_st':pe_state) (st:state) (st'':state) : Prop :=
  | pe_ceval_intro : forall st',
    st =[ c' ]=> st' ->
    pe_update st' pe_st' = st'' ->
    c' / pe_st' / st ==> st''
  where "c' '/' pe_st' '/' st '==>' st''" := (pe_ceval c' pe_st' st st'').

Local Hint Constructors pe_ceval : core.

Theorem pe_com_complete:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') ->
  (c' / pe_st' / st ==> st'').
Proof.
  intros c pe_st pe_st' c' H.    
  induction H.   
  - intros. apply pe_ceval_intro with st.
    + apply E_Skip.  
    + inversion H. auto.   
  - intros. inversion H0. subst. 
    eapply pe_ceval_intro.
    + apply E_Skip.  
    + rewrite pe_aexp_correct. rewrite H.   
      rewrite pe_update_update_add. simpl. auto.
  - intros.  
    eapply pe_ceval_intro.
    + apply E_Asgn. auto. 
    + inversion H1. subst. rewrite pe_aexp_correct. rewrite <- pe_aexp_correct.
       rewrite pe_update_update_remove. auto. 
  - intros. inversion H1. subst. apply IHpe_com1 in H4. inversion H4. 
    subst. apply IHpe_com2 in H7. inversion H7. eapply pe_ceval_intro.
     + eapply E_Seq. 
       * apply H2.
       * apply H3.
     + apply H5. 
  - intros. inversion H1. apply IHpe_com in H8.    
    + apply H8.
    + simpl in H7. rewrite pe_bexp_correct in H7. rewrite H in H7. inversion H7.
  - intros. inversion H1. 
   + subst.  rewrite pe_bexp_correct in H7. rewrite H in H7. inversion H7.
   + subst. apply IHpe_com. apply H8. 
 - intros. inversion H3.  
   + subst.  rewrite pe_bexp_correct in H9. apply IHpe_com1 in H10. inversion H10. eapply pe_ceval_intro.  
     * apply E_IfTrue. 
       -- apply H9. 
       -- eapply E_Seq.
          ++ apply H4.
          ++ apply eval_assign. 
     * rewrite <- assign_removes. apply H5. 
  + subst. rewrite pe_bexp_correct in H9. apply IHpe_com2 in H10. inversion H10. eapply pe_ceval_intro.    
  * apply E_IfFalse. 
       -- apply H9. 
       -- eapply E_Seq.
          ++ apply H4.
          ++ apply eval_assign. 
     * rewrite pe_compare_update. rewrite <- assign_removes. apply H5.
Qed. 

Theorem pe_com_sound:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (c' / pe_st' / st ==> st'') ->
  (pe_update st pe_st =[ c ]=> st'').
Proof. 
  intros c pe_st pe_st' c' H. induction H.
  - intros. inversion H. inversion H0. subst.   apply E_Skip.
  - intros. inversion H0. rewrite <- pe_update_update_add in H2. subst. 
    inversion H1. subst. apply E_Asgn. rewrite pe_aexp_correct. rewrite H. simpl. auto.
  - intros. inversion H1. subst. inversion H2. subst. rewrite <- pe_aexp_correct. rewrite <- pe_update_update_remove.
    apply E_Asgn. auto. 
  - intros. inversion H1. subst. inversion H2. subst. eapply E_Seq. 
    + apply IHpe_com1. eapply pe_ceval_intro.
      * apply H5. 
      * auto.
    +  apply IHpe_com2. eapply pe_ceval_intro.
      * apply H8. 
      * auto.
  - intros. inversion H1. subst. apply E_IfTrue. 
    + rewrite pe_bexp_correct. rewrite H. auto. 
    + apply IHpe_com.  apply H1. 
  - intros. inversion H1. subst. apply E_IfFalse. 
    + rewrite pe_bexp_correct. rewrite H. auto. 
    + apply IHpe_com.  apply H1.
  - intros. inversion H3.  subst. inversion H4. subst.  
    + inversion H11.  subst.  
      apply E_IfTrue.
      * rewrite pe_bexp_correct. apply H10.
      * eapply ceval_deterministic in H12; [| apply eval_assign]. subst.  
        rewrite <- assign_removes. apply IHpe_com1.  
        eapply pe_ceval_intro.
        -- apply H7. 
        -- auto.
    + subst. inversion H11. subst. 
       apply E_IfFalse.
      * rewrite pe_bexp_correct. apply H10.
      * eapply ceval_deterministic in H12; [| apply eval_assign]. subst.  
        rewrite pe_compare_update. rewrite <- assign_removes. apply IHpe_com2.  
        eapply pe_ceval_intro.
        -- apply H7. 
        -- auto.
Qed.
  

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (c' / pe_st' / st ==> st'').
Proof.            
  intros. split. 
  - intros. eapply pe_com_complete.
    + apply H.  
    + apply H0. 
  - intros. eapply pe_com_sound.
    + apply H. 
    + apply H0. 
Qed.   
        
Module Loop.

Reserved Notation "c1 '/' st '==>' c1' '/' st' '/' c''"
   (at level 40, st at level 39, c1' at level 39, st' at level 39).

Inductive pe_com : com -> pe_state -> com -> pe_state -> com -> Prop :=
  | PE_Skip : forall pe_st,
      <{ skip }> / pe_st ==> <{ skip }> / pe_st / <{skip}>

  | PE_AsgnStatic : forall pe_st a1 (n1 : nat) l,
      pe_aexp pe_st a1 = <{ n1 }> ->
      <{ l := a1 }> / pe_st ==> <{ skip }> / pe_add pe_st l n1 / <{skip}>

  | PE_AsgnDynamic : forall pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' ->
      (forall n : nat, a1' <> <{ n }> ) ->
      <{l := a1}> / pe_st ==> <{l := a1'}> / pe_remove pe_st l / <{skip}>

  | PE_Seq : forall pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      c2 / pe_st' ==> c2' / pe_st'' / c'' ->
      <{c1 ; c2}> / pe_st ==> <{c1' ; c2'}> / pe_st'' / c''

  | PE_IfTrue : forall pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c1' / pe_st' / c''

  | PE_IfFalse : forall pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = <{ false }> ->
      c2 / pe_st ==> c2' / pe_st' / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st ==> c2' / pe_st' / c''

  | PE_If : forall pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 <> <{ true }> ->
      pe_bexp pe_st b1 <> <{ false }> ->
      c1 / pe_st ==> c1' / pe_st1 / c'' ->
      c2 / pe_st ==> c2' / pe_st2 / c'' ->
      <{if b1 then c1 else c2 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1' ; assign pe_st1 (pe_compare pe_st1 pe_st2)
             else c2' ; assign pe_st2 (pe_compare pe_st1 pe_st2) end}>
            / pe_removes pe_st1 (pe_compare pe_st1 pe_st2) / c''

  | PE_WhileFalse : forall pe_st b1 c1,
      pe_bexp pe_st b1 = <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{skip}>

  | PE_WhileTrue : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      <{while b1 do c1 end}> / pe_st ==> <{c1';c2'}> / pe_st'' / c2''

  | PE_While : forall pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / c2'' ->
      pe_compare pe_st pe_st'' <> [] ->
      (c2'' = <{skip}> \/ c2'' = <{while b1 do c1 end}>) ->
      <{while b1 do c1 end}> / pe_st
        ==> <{if pe_bexp pe_st b1
             then c1'; c2'; assign pe_st'' (pe_compare pe_st pe_st'')
             else assign pe_st (pe_compare pe_st pe_st'') end}>
            / pe_removes pe_st (pe_compare pe_st pe_st'') / c2''

  | PE_WhileFixedEnd : forall pe_st b1 c1,
      pe_bexp pe_st b1 <> <{ false }> ->
      <{while b1 do c1 end}> / pe_st ==> <{skip}> / pe_st / <{while b1 do c1 end}>

  | PE_WhileFixedLoop : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st'
        ==> c2' / pe_st'' / <{while b1 do c1 end}> ->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while true do skip end}> / pe_st / <{skip}>

      (* Because we have an infinite loop, we should actually
         start to throw away the rest of the program:
         (while b1 do c1 end) / pe_st
         ==> skip / pe_st / (while true do skip end) *)

  | PE_WhileFixed : forall pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 <> <{ false }> ->
      pe_bexp pe_st b1 <> <{ true }> ->
      c1 / pe_st ==> c1' / pe_st' / <{skip}> ->
      <{while b1 do c1 end}> / pe_st' ==> c2' / pe_st'' / <{while b1 do c1 end}> ->
      pe_compare pe_st pe_st'' = [] ->
      <{while b1 do c1 end}> / pe_st
        ==> <{while pe_bexp pe_st b1 do c1'; c2' end}> / pe_st / <{skip}>

  where "c1 '/' st '==>' c1' '/' st' '/' c''" := (pe_com c1 st c1' st' c'').
Local Hint Constructors pe_com : core.

 Ltac step i :=
  (eapply i; intuition eauto; try solve_by_invert);
  repeat (try eapply PE_Seq;
          try (eapply PE_AsgnStatic; simpl; reflexivity);
          try (eapply PE_AsgnDynamic;
               [ simpl; reflexivity
               | intuition eauto; solve_by_invert])).

Definition square_loop: com :=
  <{while 1 <= X do
    Y := Y * Y;
    X := X - 1
  end}>.

Example pe_loop_example1:
  square_loop / []
  ==> <{while 1 <= X do
         (Y := Y * Y;
          X := X - 1); skip
       end}> / [] / <{skip}>.        
Proof.
 unfold square_loop. eapply PE_WhileFixed.
 - simpl. intros contra. inversion contra. 
 - simpl.  intros contra. inversion contra. 
 - eapply PE_Seq.
   + apply PE_AsgnDynamic.
     * simpl. auto. 
     * intros. intros contra. inversion contra.
   + apply PE_AsgnDynamic.
     * simpl. auto. 
    * intros. intros contra. inversion contra.
  - apply PE_WhileFixedEnd. simpl. intros contra. inversion contra. 
  - simpl. unfold pe_compare. simpl. auto. 
Qed.
 
Example pe_loop_example2:
  <{X := 3; square_loop}> / []
  ==> <{skip;
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       (Y := Y * Y; skip);
       skip}> / [(X,0)] / <{skip}>.
Proof.
  eapply PE_Seq.
  - apply PE_AsgnStatic.  simpl. auto.
  - unfold square_loop. eapply PE_WhileTrue.
    + simpl. auto. 
    + eapply PE_Seq.
      * apply PE_AsgnDynamic.
        -- simpl. auto. 
        -- intros. intros contra. inversion contra.
      * apply PE_AsgnStatic. simpl. auto. 
    + eapply PE_WhileTrue.
      * simpl. auto.  
      * eapply PE_Seq. 
        -- apply PE_AsgnDynamic.
           ++ simpl. auto. 
           ++ intros. intros contra. inversion contra.
        -- apply PE_AsgnStatic. simpl. auto. 
      * eapply PE_WhileTrue.
        -- simpl. auto.  
        -- eapply PE_Seq. 
           ++ apply PE_AsgnDynamic.
              ** simpl. auto. 
              ** intros. intros contra. inversion contra.
           ++ apply PE_AsgnStatic. simpl. auto.
        -- simpl. apply PE_WhileFalse. simpl. auto. 
        -- simpl. intros contra. inversion contra. 
      * simpl.  intros contra. inversion contra. 
    + simpl.  intros contra. inversion contra.
Qed. 

Example pe_loop_example3:
  <{Z := 3; subtract_slowly}> / []
  ==> <{skip;
       if X <> 0 then
         (skip; X := X - 1);
         if X <> 0 then
           (skip; X := X - 1);
           if X <> 0 then
             (skip; X := X - 1);
             while X <> 0 do
               (skip; X := X - 1); skip
             end;
             skip; Z := 0
           else skip; Z := 1 end; skip
         else skip; Z := 2 end; skip
       else skip; Z := 3 end}> / [] / <{skip}>.
Proof.
  eapply PE_Seq.
  - apply PE_AsgnStatic. simpl. auto.
  - unfold subtract_slowly. unfold subtract_slowly_body.   
   
erewrite f_equal2 with (f := fun c st => _ / _ ==> c / st / <{skip}>).
   +  eapply PE_While.  
     * simpl. intros contra. inversion contra. 
      * simpl. intros contra. inversion contra. 
      * eapply PE_Seq.
        -- apply PE_AsgnStatic. simpl. auto. 
       -- apply PE_AsgnDynamic. 
          ++ simpl. auto.
          ++ intros n. intros contra. inversion contra. 
      * simpl.  eapply PE_While.
        --  simpl. intros contra. inversion contra. 
         --  simpl. intros contra. inversion contra.
         --   eapply PE_Seq.
            ++ apply PE_AsgnStatic. simpl. auto.
            ++ apply PE_AsgnDynamic. 
               ** simpl. auto.
               ** intros n. intros contra. inversion contra.
        -- eapply  PE_While.
           ++  simpl. intros contra. inversion contra. 
++  simpl. intros contra. inversion contra. 
++ eapply PE_Seq.
            ** apply PE_AsgnStatic. simpl. auto.
            ** apply PE_AsgnDynamic. 
               --- simpl. auto.
               --- intros n. intros contra. inversion contra.
      ++ simpl. eapply PE_WhileFixed.
           ** simpl. intros contra. inversion contra. 
** simpl. intros contra. inversion contra.
** eapply  PE_Seq.
 --- apply PE_AsgnStatic. simpl. auto.
           --- apply PE_AsgnDynamic. 
               +++ simpl. auto.
               +++ intros n. intros contra. inversion contra.
    ** apply PE_WhileFixedEnd. simpl. intros contra. inversion contra.
    ** unfold pe_compare. simpl. auto.
   ++ simpl. unfold pe_compare. simpl.  intros contra. inversion contra.
   ++ left. auto.
   -- simpl. unfold pe_compare. simpl.  intros contra. inversion contra.
   -- left. auto.
  *  simpl. unfold pe_compare. simpl.  intros contra. inversion contra.
  *  left. auto.
  + simpl. auto.
  + simpl. auto. 
Qed.

Example pe_loop_example4:
  <{X := 0;
   while X <= 2 do
     X := 1 - X
   end}> / [] ==> <{skip; while true do skip end}> / [(X,0)] / <{skip}>.
Proof.
  eapply PE_Seq.
  - apply PE_AsgnStatic.  simpl. auto.
  - eapply PE_WhileFixedLoop. 
    + simpl. auto. 
    + apply PE_AsgnStatic.  simpl. auto.
    +  eapply PE_WhileTrue.
       *  simpl. auto.
       *  apply PE_AsgnStatic. simpl. auto. 
       * apply PE_WhileFixedEnd.  intros contra. inversion contra.
      *  unfold pe_compare.  simpl. intros contra. inversion contra.
   + unfold pe_compare.  simpl. auto.
Qed. 

Reserved Notation "c1 '/' st '==>' st' '#' n"
  (at level 40, st at level 39, st' at level 39).

Inductive ceval_count : com -> state -> state -> nat -> Prop :=
  | E'Skip : forall st,
      <{skip}> / st ==> st # 0
  | E'Asgn  : forall st a1 n l,
      aeval st a1 = n ->
      <{l := a1}> / st ==> (t_update st l n) # 0
  | E'Seq : forall c1 c2 st st' st'' n1 n2,
      c1 / st  ==> st'  # n1 ->
      c2 / st' ==> st'' # n2 ->
      <{c1 ; c2}> / st ==> st'' # (n1 + n2)
  | E'IfTrue : forall st st' b1 c1 c2 n,
      beval st b1 = true ->
      c1 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'IfFalse : forall st st' b1 c1 c2 n,
      beval st b1 = false ->
      c2 / st ==> st' # n ->
      <{if b1 then c1 else c2 end}> / st ==> st' # n
  | E'WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      <{while b1 do c1 end}> / st ==> st # 0
  | E'WhileTrue : forall st st' st'' b1 c1 n1 n2,
      beval st b1 = true ->
      c1 / st ==> st' # n1 ->
      <{while b1 do c1 end}> / st' ==> st'' # n2 ->
      <{while b1 do c1 end}> / st ==> st'' # S (n1 + n2)

  where "c1 '/' st '==>' st' # n" := (ceval_count c1 st st' n).

Local Hint Constructors ceval_count : core.

Theorem ceval_count_complete: forall c st st',
  st =[ c ]=> st' -> exists n, c / st ==> st' # n.
Proof. 
  intros. induction H. 
  - exists 0. apply E'Skip. 
  - exists 0. apply E'Asgn. apply H.
  - destruct IHceval1 as [n1 H1].
    destruct IHceval2 as [n2 H2].
    exists (n1 + n2). eapply E'Seq.
    + apply H1.  
    + apply H2.
  - destruct IHceval as [n1 H1]. 
    exists n1. apply E'IfTrue.
    + apply H.
    + apply H1. 
  - destruct IHceval as [n1 H1].  
    exists n1. apply E'IfFalse.
    + apply H.
    + apply H1.
  - exists 0. apply E'WhileFalse.  apply H. 
  - destruct IHceval1 as [n1 Heq1].
    destruct IHceval2 as [n2 Heq2].
    exists (S (n1 + n2)). eapply  E'WhileTrue.
    + apply H. 
    + apply Heq1. 
    + apply Heq2. 
Qed. 


Theorem ceval_count_sound: forall c st st' n,
  c / st ==> st' # n -> st =[ c ]=> st'.
Proof.
  intros. induction H.
  - apply E_Skip. 
  - apply E_Asgn. apply H.
  - eapply E_Seq.
    + apply IHceval_count1. 
    + apply IHceval_count2.
  - apply E_IfTrue.  
    + apply H. 
    + apply IHceval_count.
  - apply E_IfFalse. 
    + apply H. 
    + apply IHceval_count. 
  - apply E_WhileFalse. apply H. 
  - eapply E_WhileTrue.
    + apply H. 
    + apply IHceval_count1. 
    + apply IHceval_count2.
Qed.

Theorem pe_compare_nil_lookup: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall V, pe_lookup pe_st1 V = pe_lookup pe_st2 V.
Proof.
  intros. apply pe_compare_correct. 
  intros contra. rewrite H in contra. simpl in contra. inversion contra. 
Qed.

Theorem pe_compare_nil_update: forall pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = [] ->
  forall st, pe_update st pe_st1 = pe_update st pe_st2.
Proof.
 intros. apply functional_extensionality. 
 intros. rewrite pe_update_correct. rewrite pe_update_correct. 
 eapply pe_compare_nil_lookup in H. rewrite H. auto. 
Qed.

Reserved Notation "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n" 
  (at level 40, pe_st' at level 39, c'' at level 39, st at level 39, st'' at level 39).

Inductive pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)
                         (st:state) (st'':state) (n:nat) : Prop :=
  | pe_ceval_count_intro : forall st' n',
    st =[ c' ]=> st' ->
    c'' / pe_update st' pe_st' ==> st'' # n' ->
    n' <= n ->
    c' / pe_st' / c'' / st ==> st'' # n
  where "c' '/' pe_st' '/' c'' '/' st '==>' st'' '#' n" :=
        (pe_ceval_count c' pe_st' c'' st st'' n).


Local Hint Constructors pe_ceval_count : core.

Lemma pe_ceval_count_le: forall c' pe_st' c'' st st'' n n',
  n' <= n ->
  c' / pe_st' / c'' / st ==> st'' # n' ->
  c' / pe_st' / c'' / st ==> st'' # n.
Proof.
  intros. 
  inversion H0. 
  eapply pe_ceval_count_intro.
  - apply H1. 
  - apply H2. 
  - lia.
Qed.
   
Theorem pe_com_complete:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c / pe_update st pe_st ==> st'' # n) ->
  (c' / pe_st' / c'' / st ==> st'' # n).
Proof.
  intros c pe_st pe_st' c' c'' H. 
  induction H. 
  - intros.  eapply pe_ceval_count_intro.
    + apply E_Skip. 
    + apply H. 
    + auto. 
  - intros. inversion H0. subst. eapply pe_ceval_count_intro.
       + apply E_Skip. 
    + rewrite <- pe_update_update_add. rewrite pe_aexp_correct. 
      rewrite H. simpl. apply E'Skip. 
    + auto.
  - intros. inversion H1. subst. eapply pe_ceval_count_intro.
    + apply E_Asgn. auto. 
    + rewrite pe_aexp_correct. rewrite pe_update_update_remove. apply E'Skip. 
    + auto. 
  - auto. intros.  inversion H1.  subst. apply IHpe_com1 in H4.
    inversion H4. subst. inversion H3. subst.
    apply IHpe_com2 in H8. inversion H8. subst. eapply pe_ceval_count_intro.
    + eapply E_Seq.
      * apply H2.
      * apply H6. 
    + apply H7.
    + lia. 
  - intros. inversion H1.  
    + subst.  apply IHpe_com in H9. inversion H9. eapply pe_ceval_count_intro.
      * apply H2.
      * apply H3. 
      * apply H4. 
    + subst. rewrite pe_bexp_correct in H8. rewrite H in H8. simpl in H8. inversion H8.
  - intros. inversion H1. 
    + subst. rewrite pe_bexp_correct in H8. rewrite H in H8. simpl in H8. inversion H8.
    + subst. apply IHpe_com in H9. inversion H9. eapply pe_ceval_count_intro.
      * apply H2.
      * apply H3. 
      * apply H4. 
  - intros. inversion H3. subst. 
    + rewrite pe_bexp_correct in H10. apply IHpe_com1 in H11. inversion H11.
      eapply pe_ceval_count_intro.
      * apply E_IfTrue. 
        -- apply H10. 
        -- eapply E_Seq. 
           ++ apply H4.
           ++ apply eval_assign. 
     * erewrite <- assign_removes. apply H5. 
     * apply H6. 
   + subst. rewrite pe_bexp_correct in H10. apply IHpe_com2 in H11. inversion H11.
       eapply pe_ceval_count_intro.
      * apply E_IfFalse. 
        -- apply H10. 
        -- eapply E_Seq. 
           ++ apply H4.
           ++ apply eval_assign. 
     * rewrite pe_compare_update. erewrite <- assign_removes. apply H5. 
     * apply H6.
  - intros.  inversion H0. 
    + subst. eapply pe_ceval_count_intro.
      * apply E_Skip. 
      * apply E'Skip. 
      * auto. 
    + subst. rewrite pe_bexp_correct in H3. rewrite H in H3. simpl in H3. 
      inversion H3. 
  - intros. inversion H3.  subst.
    + rewrite pe_bexp_correct in H9. rewrite H in H9. simpl in H9.
       inversion H9. 
    + subst. apply IHpe_com1 in H7. inversion H7. inversion H5. subst. apply IHpe_com2 in H11. inversion H11.
      eapply pe_ceval_count_intro.
      * eapply E_Seq. 
        -- apply H4.
        -- 
           apply H9.
     * apply H10. 
     * lia. 
  - intros. inversion H5. destruct H4.
    + subst. eapply pe_ceval_count_intro. 
      * apply E_IfFalse. 
        -- rewrite pe_bexp_correct in H11. apply H11. 
        -- apply eval_assign. 
      *  rewrite <- assign_removes.  apply E'Skip. 
      * auto. 
    + subst. eapply pe_ceval_count_intro. 
      * apply E_IfFalse.
         -- rewrite pe_bexp_correct in H11. apply H11. 
        -- apply eval_assign. 
      *  rewrite <- assign_removes.  apply H5. 
      * auto.
    + subst. apply IHpe_com1 in H9. inversion H9. 
      inversion H7. subst. apply IHpe_com2 in H13. 
      inversion H13. subst. eapply pe_ceval_count_intro. 
      * apply E_IfTrue.
        -- rewrite pe_bexp_correct in H8. apply H8. 
        -- eapply E_Seq.
           ++ apply H6. 
           ++ eapply E_Seq.
              ** apply H11. 
              ** apply eval_assign.
      * rewrite pe_compare_update. rewrite <- assign_removes. apply H12. 
      * lia. 
  - intros. inversion H0.  
    + subst. eapply pe_ceval_count_intro. 
      * apply E_Skip. 
      * apply H0. 
      * auto. 
    + subst. eapply pe_ceval_count_intro. 
      * apply E_Skip. 
      * apply H0. 
      * auto. 
  -  intros. inversion H3.   
    + subst. rewrite pe_bexp_correct in H9. rewrite H in H9. simpl in H9. inversion H9. 
    + subst. exfalso.
    generalize dependent (S (n1 + n2)). intros n.  clear - H H2 IHpe_com1 IHpe_com2.  generalize dependent st. 
      induction n using lt_wf_ind. intros. inversion H3. 
    * rewrite pe_bexp_correct, H in H8. inversion H8.
    * subst. apply IHpe_com1 in H6. inversion H6. inversion H4. subst. apply IHpe_com2 in H10.
      inversion H10. eapply pe_compare_nil_update in H2. 
      assert (n'<S(n1+n2)). 
      -- lia. 
      -- specialize H0 with (m:=n') (st:=st') . rewrite H2 in H0. apply H0 in H12.
         ++ apply H12. 
         ++ apply H9. 
   - intros. generalize dependent st. induction n using lt_wf_ind. intros. inversion H5.
     + subst. eapply pe_ceval_count_intro.  
       * apply E_WhileFalse. rewrite <- pe_bexp_correct. apply H11.
       * apply E'Skip. 
       * auto. 
     + subst.  edestruct IHpe_com1 as [? ? ? Hskip ?].
       * apply H9. 
       * inversion Hskip. subst. edestruct IHpe_com2.
         -- apply H13. 
         -- eapply pe_compare_nil_update in H3. rewrite <- H3 in H11.
            assert (n'<S(n1+n2)). 
            ++ lia.
            ++ specialize H4 with (m:=n') (st:=st') .
               apply H4 in H14. 
               ** inversion H14. eapply pe_ceval_count_intro.  
                  --- eapply E_WhileTrue. 
                      +++ rewrite <- pe_bexp_correct. apply H8. 
                      +++ eapply E_Seq.
                          *** apply H6. 
                          *** apply H10.
                      +++ apply H15. 
                  --- apply H16.
                  --- lia. 
               ** apply H11. 
Qed.   
                   
Theorem pe_com_sound:
  forall c pe_st pe_st' c' c'', c / pe_st ==> c' / pe_st' / c'' ->
  forall st st'' n,
  (c' / pe_st' / c'' / st ==> st'' # n) ->
  (pe_update st pe_st =[ c ]=> st'').
Proof.
  intros c pe_st pe_st' c' c'' H.
  induction H.
  - intros. inversion H. inversion H1. inversion H0. subst. apply E_Skip. 
  - intros. inversion H0. inversion H2. subst. rewrite <- pe_update_update_add.
    inversion H1. subst. apply E_Asgn. rewrite pe_aexp_correct. rewrite H. simpl. auto. 
  - intros. inversion H1. inversion H3. subst. inversion H2. subst. rewrite <- pe_aexp_correct.
    simpl. rewrite <- pe_update_update_remove. apply E_Asgn. auto. 
  - intros. inversion H1. inversion H2. subst. eapply E_Seq.
    + eapply IHpe_com1. eapply pe_ceval_count_intro. 
      * apply H7. 
      * apply E'Skip. 
      * auto.
    + eapply IHpe_com2. eapply pe_ceval_count_intro.
      * apply H10. 
      * apply H3. 
      * auto. 
   - intros. inversion H1. apply E_IfTrue.
      + rewrite pe_bexp_correct. rewrite H. simpl. auto. 
      + eapply IHpe_com. eauto. 
   - intros. inversion H1. apply E_IfFalse.
      + rewrite pe_bexp_correct. rewrite H. simpl. auto. 
      + eapply IHpe_com. eauto.
   - intros. inversion H3. inversion H4. 
     + subst. inversion H13. subst. eapply ceval_deterministic in H14; [| apply eval_assign]. 
       subst. rewrite <- assign_removes in H5. apply E_IfTrue.
       * rewrite pe_bexp_correct. apply H12. 
       * eapply IHpe_com1. eapply pe_ceval_count_intro.
         -- apply H9. 
         -- apply H5.
         -- apply H6. 
     + subst. inversion H13. subst. eapply ceval_deterministic in H14; [| apply eval_assign]. 
       subst. rewrite pe_compare_update in H5. rewrite <- assign_removes in H5. apply E_IfFalse.
       * rewrite pe_bexp_correct. apply H12. 
       * eapply IHpe_com2. eapply pe_ceval_count_intro.
         -- apply H9. 
         -- apply H5.
         -- apply H6.
    - intros. inversion H0. inversion H2. subst. inversion H1. 
      subst.  eapply E_WhileFalse. rewrite pe_bexp_correct. rewrite H. simpl. auto.
    - intros. inversion H3. inversion H4. subst.  eapply E_WhileTrue.
      + rewrite pe_bexp_correct. rewrite H. simpl. auto.
      + eapply IHpe_com1. eauto. 
      + eapply IHpe_com2. eauto. 
   - destruct H4.    
     + subst. intros. inversion H4.  inversion H5.
       * subst. inversion H14. subst. inversion H15. subst.   
        eapply ceval_deterministic in H17; [| apply eval_assign]. 
        subst.  rewrite pe_compare_update in H6.  rewrite <- assign_removes in H6.  
        eapply E_WhileTrue.   
         -- rewrite pe_bexp_correct.  apply H13. 
         -- eapply IHpe_com1.  eapply pe_ceval_count_intro.
            ++ apply H10.
            ++ apply E'Skip.
            ++ auto.
         -- eapply IHpe_com2.  eapply pe_ceval_count_intro.
            ++ apply H11.
            ++ apply H6. 
            ++ apply H7.
       * subst. eapply ceval_deterministic in H14; [| apply eval_assign].
          subst.  rewrite <- assign_removes in H6. inversion H6. subst. eapply E_WhileFalse.
         rewrite pe_bexp_correct.  apply H13. 
     + subst. intros. inversion H4. inversion H5.
       * subst. inversion H14. subst. inversion H15. subst.         
       eapply ceval_deterministic in H17; [| apply eval_assign]. 
        subst.  rewrite pe_compare_update in H6.  rewrite <- assign_removes in H6.  
        eapply E_WhileTrue.
        -- rewrite pe_bexp_correct.  apply H13.
        -- eapply IHpe_com1.  eapply pe_ceval_count_intro.
           ++ apply H10.
           ++ apply E'Skip.
            ++ auto.
         -- eapply IHpe_com2.  eapply pe_ceval_count_intro.
            ++ apply H11.
            ++ apply H6. 
            ++ apply H7.
       * subst. eapply ceval_deterministic in H14; [| apply eval_assign].
         subst. rewrite <- assign_removes in H6. inversion H6.
         -- subst. eapply E_WhileFalse.
            rewrite pe_bexp_correct.  apply H13.
         -- rewrite pe_bexp_correct in H10. rewrite H13 in H10. inversion H10.
     - intros. inversion H0. inversion H1. subst. 
       inversion H2.
       + subst. eapply E_WhileFalse. apply H9. 
       + subst. eapply E_WhileTrue.
         * apply H6. 
         * eapply ceval_count_sound. apply H7.
         * eapply ceval_count_sound. apply H11. 
     - intros. inversion H3. apply loop_never_stops in H4. inversion H4.  
     - intros. clear - H3 IHpe_com1 IHpe_com2 H4. inversion H4.
       remember <{while pe_bexp pe_st b1 do c1'; c2' end}> as c'. 
       induction H.  
       + inversion Heqc'. 
       + inversion Heqc'. 
       + inversion Heqc'. 
       + inversion Heqc'. 
       + inversion Heqc'. 
       + injection Heqc'. intros. subst. 
         inversion H0. subst. eapply E_WhileFalse. rewrite pe_bexp_correct. apply H.
       + injection Heqc'. intros. subst. apply IHceval2 in Heqc'. 
         * apply ceval_count_complete in Heqc'. inversion Heqc'.  
           inversion H2. subst. eapply E_WhileTrue.
            -- rewrite pe_bexp_correct. apply H. 
            -- eapply IHpe_com1. eapply pe_ceval_count_intro.
               ++ apply H9. 
               ++ apply E'Skip.
               ++ auto. 
            -- eapply IHpe_com2. eapply pe_ceval_count_intro.
               ++ apply H12. 
               ++ eapply pe_compare_nil_update in H3. rewrite <- H3. apply H6. 
               ++ auto.
          * eapply pe_ceval_count_intro.
            -- apply H5. 
            -- apply H0.
            -- apply H1. 
          * apply H0. 
Qed.  

Corollary pe_com_correct:
  forall c pe_st pe_st' c', c / pe_st ==> c' / pe_st' / <{skip}> ->
  forall st st'',
  (pe_update st pe_st =[ c ]=> st'') <->
  (exists st', st =[ c' ]=> st' /\ pe_update st' pe_st' = st'').
Proof. 
 intros. split. 
 - intros. apply ceval_count_complete in H0. 
   destruct H0 as [n H0]. apply pe_com_complete with (st:=st) (st'':= st'') (n:=n) in H.
   + inversion H. exists st'. inversion H2. auto.
   + apply H0. 
 - intros. destruct H0 as [st' H0]. destruct H0. apply ceval_count_complete in H0.
   destruct H0 as [n H0]. eapply pe_com_sound in H. 
   + apply H.
   + eapply pe_ceval_count_intro. apply ceval_count_sound in H0. 
     * apply H0. 
     * subst. apply E'Skip.
     * auto.  
Qed.

Inductive block (Label:Type) : Type :=
  | Goto : Label -> block Label
  | If : bexp -> Label -> Label -> block Label
  | Assign : string -> aexp -> block Label -> block Label.

Arguments Goto {Label} _.
Arguments If {Label} _ _ _.
Arguments Assign {Label} _ _ _.

Inductive parity_label : Type :=
  | entry : parity_label
  | loop : parity_label
  | body : parity_label
  | done : parity_label.

Definition parity_body : block parity_label :=
  Assign Y <{Y - 1}>
   (Assign X <{1 - X}>
     (Goto loop)).

Fixpoint keval {L:Type} (st:state) (k : block L) : state * L :=
  match k with
  | Goto l => (st, l)
  | If b l1 l2 => (st, if beval st b then l1 else l2)
  | Assign i a k => keval (t_update st i (aeval st a)) k
  end.

Example keval_example:
  keval empty_st parity_body
  = ((X !-> 1 ; Y !-> 0), loop).
Proof.
  simpl. auto.
Qed.

Definition program (L:Type) : Type := L -> option (block L).

Definition parity : program parity_label := fun l =>
  match l with
  | entry => Some (Assign X 0 (Goto loop))
  | loop => Some (If <{1 <= Y}> body done)
  | body => Some parity_body
  | done => None (* halt *)
  end.

Inductive peval {L:Type} (p : program L) : state -> L -> state -> L -> Prop :=
  | E_None: forall st l,
    p l = None ->
    peval p st l st l
  | E_Some: forall st l k st' l' st'' l'',
    p l = Some k ->
    keval st k = (st', l') ->
    peval p st' l' st'' l'' ->
    peval p st l st'' l''.

Example parity_eval: peval parity empty_st entry empty_st done.
Proof.
  erewrite f_equal with (f := fun st => peval _ _ _ st _).  
  - eapply E_Some.
    + reflexivity.
    + reflexivity.
    + eapply E_Some.
      * reflexivity.
      * reflexivity. 
      * simpl. apply E_None. reflexivity.
  - apply functional_extensionality. intros i. rewrite t_update_same. auto.
Qed.

Fixpoint pe_block {L:Type} (pe_st:pe_state) (k : block L) : block (pe_state * L) :=
  match k with
  | Goto l => Goto (pe_st, l)
  | If b l1 l2 =>
    match pe_bexp pe_st b with
    | BTrue => Goto (pe_st, l1)
    | BFalse => Goto (pe_st, l2)
    | b' => If b' (pe_st, l1) (pe_st, l2)
    end
  | Assign i a k =>
    match pe_aexp pe_st a with
    | ANum n => pe_block (pe_add pe_st i n) k
    | a' => Assign i a' (pe_block (pe_remove pe_st i) k)
    end
  end.


Example pe_block_example:
  pe_block [(X,0)] parity_body
  = Assign Y <{Y - 1}> (Goto ([(X,1)], loop)).
Proof.
  simpl. unfold pe_add. 
  simpl. auto.
Qed.

Theorem pe_block_correct: forall (L:Type) st pe_st k st' pe_st' (l':L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) ->
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l').
Proof.
  intros.
 generalize dependent st. 
 generalize dependent pe_st.
 induction k.
  - intros. simpl. simpl in H. injection H. intros. subst. auto. 
  - intros. simpl. rewrite pe_bexp_correct. destruct (pe_bexp pe_st b) eqn:Hb.
   + simpl. simpl in H. rewrite Hb in H. simpl in H. injection H. intros. subst. auto. 
   + simpl. simpl in H. rewrite Hb in H. simpl in H. injection H. intros. subst. auto. 
   + simpl in H. rewrite Hb in H. simpl in H. simpl. injection H. intros. subst.
     destruct (aeval st' a1 =? aeval st' a2).
     * injection H0. intros. subst. auto.  
      * injection H0. intros. subst. auto.  
   + simpl in H. rewrite Hb in H. simpl in H. simpl. 
     destruct (negb (aeval st a1 =? aeval st a2)).
     * injection H. intros. subst. auto.  
      * injection H. intros. subst. auto.
   + simpl in H. rewrite Hb in H. simpl in H. simpl. 
     destruct (aeval st a1 <=? aeval st a2 ).
     * injection H. intros. subst. auto.  
      * injection H. intros. subst. auto.
   + simpl in H. rewrite Hb in H. simpl in H. simpl. 
     destruct (negb (aeval st a1 <=? aeval st a2 )).
     * injection H. intros. subst. auto.  
      * injection H. intros. subst. auto.
   + simpl in H. rewrite Hb in H. simpl in H. simpl. 
     destruct (negb (beval st b0)).
     * injection H. intros. subst. auto.  
      * injection H. intros. subst. auto.
   + simpl in H. rewrite Hb in H. simpl in H. simpl. 
     destruct (beval st b0_1 && beval st b0_2).
     * injection H. intros. subst. auto.  
      * injection H. intros. subst. auto. 
 - intros.  simpl. simpl in H.   destruct (pe_aexp pe_st a) eqn:Ha.
   + rewrite pe_aexp_correct.  
     apply IHk in H. rewrite <- pe_update_update_add in H.
     rewrite Ha. simpl. apply H. 
   + rewrite pe_aexp_correct. simpl in H. rewrite Ha. 
     apply IHk in H. rewrite <- pe_update_update_remove in H.
     simpl. apply H.
   + rewrite pe_aexp_correct. simpl in H. rewrite Ha.
     apply IHk in H. rewrite <- pe_update_update_remove in H.
     simpl. apply H.
   + rewrite pe_aexp_correct. simpl in H. rewrite Ha.
     apply IHk in H. rewrite <- pe_update_update_remove in H.
     simpl. apply H.
   + rewrite pe_aexp_correct. simpl in H. rewrite Ha.
     apply IHk in H. rewrite <- pe_update_update_remove in H.
     simpl. apply H.
Qed.

Definition pe_program {L:Type} (p : program L) : program (pe_state * L) :=
  fun pe_l => match pe_l with 
              | (pe_st, l) => option_map (pe_block pe_st) (p l)
              end.

Inductive pe_peval {L:Type} (p : program L)
  (st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : Prop :=
  | pe_peval_intro : forall st' pe_st',
    peval (pe_program p) st (pe_st, l) st' (pe_st', l') ->
    pe_update st' pe_st' = st'o ->
    pe_peval p st pe_st l st'o l'.


Theorem pe_program_correct:
  forall (L:Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' <->
  pe_peval p st pe_st l st'o l'.
Proof. intros.
  split.
  - (* -> *) intros Heval.
    remember (pe_update st pe_st) as sto.
    generalize dependent pe_st. generalize dependent st.
    induction Heval as
      [ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];
      intros st pe_st Heqsto; subst sto.
    + (* E_None *) eapply pe_peval_intro. apply E_None.
      simpl. rewrite Hlookup. reflexivity. reflexivity.
    + (* E_Some *)
      remember (keval st (pe_block pe_st k)) as x.
      destruct x as [st' [pe_st' l'_] ].
      symmetry in Heqx. erewrite pe_block_correct in Hkeval by apply Heqx.
      inversion Hkeval. subst st'o l'_. clear Hkeval.
      edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.
      eapply pe_peval_intro; [| reflexivity]. eapply E_Some; eauto.
      simpl. rewrite Hlookup. reflexivity.
  - (* <- *) intros [st' pe_st' Heval Heqst'o].
    remember (pe_st, l) as pe_st_l.
    remember (pe_st', l') as pe_st'_l'.
    generalize dependent pe_st. generalize dependent l.
    induction Heval as
      [ st [pe_st_ l_] Hlookup
      | st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']
        Hlookup Hkeval Heval ];
      intros l pe_st Heqpe_st_l;
      inversion Heqpe_st_l; inversion Heqpe_st'_l'; repeat subst.
    + (* E_None *) apply E_None. simpl in Hlookup.
      destruct (p l'); [ solve [ inversion Hlookup ] | reflexivity ].
    + (* E_Some *)
      simpl in Hlookup. remember (p l) as k.
      destruct k as [k|]; inversion Hlookup; subst.
      eapply E_Some; eauto. apply pe_block_correct. apply Hkeval.
Qed.







