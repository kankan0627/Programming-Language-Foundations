Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Warnings "-non-recursive".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import SmallStep.
From PLF Require Import STLC.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> => true
  | <{ T11 -> T12 }>, <{ T21 -> T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ => false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
induction T.
- simpl. reflexivity.
- simpl. rewrite IHT1. rewrite IHT2.
  simpl. reflexivity.
Qed.




Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
induction T1.
- induction T2. 
  + intros. reflexivity. 
  +  intros. simpl in H. inversion H.
- induction T2.
  + intros. simpl in H. inversion H.
  + intros. simpl in H. rewrite andb_true_iff in H.
    destruct H. apply IHT1_1 in H. apply IHT1_2 in H0.
    rewrite H. rewrite H0.
    reflexivity.
Qed.

End STLCTypes.

Module FirstTry.
Import STLCTypes.
Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2 -> T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11 -> T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.
End FirstTry.

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e "
  := (Some e) (at level 60).
Notation " 'fail' "
  := None.
Module STLCChecker.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{\x:T2, t1}> =>
      T1 <- type_check (x |-> T2 ; Gamma) t1 ;;
      return <{T2->T1}>
  | <{t1 t2}> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{T11->T12}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | <{true}> =>
      return <{ Bool }>
  | <{false}> =>
      return <{ Bool }>
  | <{if guard then t1 else t2}> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | <{ Bool }> =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.



Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof.
intros. 
  generalize dependent Gamma.   generalize dependent T.
 induction t.
  - intros. apply T_Var. simpl in H. destruct (Gamma s).
    + rewrite H. reflexivity.
    +  inversion H.
  - intros. simpl in H. destruct (type_check Gamma t1)  eqn:HT1 in H. 
    + destruct (type_check Gamma t2) eqn:HT2 in H.
      * destruct t eqn:Ht in H. 
        -- inversion H. 
        -- destruct (eqb_ty t3_1 t0) eqn:Hty in H.
              ++ injection H. intros. subst. eapply T_App.
                  **  apply IHt1. apply HT1.
                  ** apply IHt2. apply eqb_ty__eq in Hty.
                     subst. apply HT2.
             ++ inversion H.
     * inversion H.
   +  inversion H.
  - intros. simpl in H.
    destruct (type_check (s |-> t; Gamma) t0) eqn:HG in H.
    + injection H.
      intros. subst.
      apply T_Abs.
      apply IHt. apply HG.
    + inversion H.
  - intros. simpl in H. injection H. intros. subst.
    apply T_True.
  -  intros. simpl in H. injection H. intros. subst.
    apply T_False.
  - intros. simpl in H. 
destruct (type_check Gamma t1) eqn:Ht1 in H.
  + destruct (type_check Gamma t2) eqn:Ht2 in H.
     * destruct (type_check Gamma t3) eqn:Ht3 in H. 
       -- destruct t eqn:Ht in H.
          ++ destruct (eqb_ty t0 t4) eqn:Hty in H.
              ** apply eqb_ty__eq in Hty.
                 apply T_If.
                 --- apply IHt1.
                     rewrite <- Ht. apply Ht1.
                 --- apply IHt2. injection H. intros. subst.
                     apply Ht2.
                 --- apply IHt3. injection H. intros. subst.
                     apply Ht3.
              ** inversion H.
           ++ inversion H.
         -- inversion H.
      * inversion H.
   + inversion H.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
 intros.
 generalize dependent Gamma. generalize dependent T.
induction t.
- intros. simpl. inversion H.  subst. destruct (Gamma s) eqn:Hs.
  + apply H2.
  + inversion H2. 
- intros. simpl. destruct (type_check Gamma t1) eqn:Ht1.
   + destruct (type_check Gamma t2) eqn:Ht2.
     * destruct t eqn:Ht.
       -- inversion H. subst. apply IHt1 in H3. rewrite Ht1 in H3. injection H3. intros. inversion H0.
       -- destruct (eqb_ty t3_1 t0) eqn:Hty.
          ++ apply eqb_ty__eq in Hty. subst. inversion H. subst. 
           apply IHt1 in H3. rewrite Ht1 in H3. injection H3. intros. subst. reflexivity.
         ++ inversion H. subst.  apply IHt2 in H5. rewrite Ht2 in H5. injection H5. intros. subst.
            apply IHt1 in H3. rewrite Ht1 in H3. injection H3. intros. subst. 
             assert (eqb_ty T2 T2 = true).
            { apply eqb_ty_refl. }
            rewrite Hty in H0. inversion H0.
      * inversion H. subst. 
        apply IHt2 in H5. rewrite Ht2 in H5. inversion H5.
    + inversion H. subst.  apply IHt1 in H3. rewrite Ht1 in H3. inversion H3.
 - intros. simpl. destruct (type_check (s |-> t; Gamma) t0) eqn:Htc.
   + inversion H. subst. apply IHt in H5. rewrite Htc in H5.
     injection H5. intros. subst. reflexivity.
   + inversion H. subst. apply IHt in H5. rewrite Htc in H5.
     inversion H5.
- intros. inversion H. subst. auto.
- intros. inversion H. subst. auto.
- intros. inversion H. subst. simpl. destruct (type_check Gamma t1) eqn:Ht1.
  + destruct (type_check Gamma t2) eqn:Ht2.
     * destruct (type_check Gamma t3) eqn:Ht3.
        -- destruct t eqn:Ht.
           ++ destruct (eqb_ty t0 t4) eqn:Hty.
              ** apply eqb_ty__eq in Hty. subst. 
                 apply IHt3 in H7. rewrite H7 in Ht3. injection Ht3. intros. subst.
                 reflexivity.  
             ** apply IHt2 in H6. rewrite H6 in Ht2. injection Ht2. intros. subst.
                apply IHt3 in H7. rewrite H7 in Ht3. injection Ht3. intros. subst.
                rewrite eqb_ty_refl in Hty. inversion Hty.
          ++ apply IHt1 in H4. rewrite H4 in Ht1. injection Ht1. intros. inversion H0.
        -- apply IHt3 in H7. rewrite H7 in Ht3. inversion Ht3.
      * apply IHt2 in H6. rewrite H6 in Ht2. inversion Ht2.
    + apply IHt1 in H4. rewrite H4 in Ht1. inversion Ht1.
Qed.

End STLCChecker.

Module TypecheckerExtensions.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  induction T; simpl; try rewrite IHT1; try rewrite IHT2; auto.
Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
induction T1; intros; simpl in H; destruct T2 eqn:Ht2 in H; inversion H; 
try(apply andb_true_iff in H; destruct H; apply IHT1_1 in H; apply IHT1_2 in H0; subst; reflexivity); 
try(apply IHT1 in H; subst; reflexivity); auto.
Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  (* sums *)
  (* FILL IN HERE *)
  | <{ inl T t }> =>
      T1 <- type_check Gamma t ;;
      return <{{T1 + T}}>
  | <{ inr T t}> =>
      T2 <- type_check Gamma t ;;
      return <{{ T + T2 }}>
  | <{ case t of | inl x1 => t1 | inr x2 => t2 }> =>
      Ts <- type_check Gamma t ;;
      match Ts with
      | <{{ T1 + T2 }}> =>
          Tx1 <- type_check (x1 |-> T1 ; Gamma) t1 ;;
          Tx2 <- type_check (x2 |-> T2 ; Gamma) t2 ;;
          if eqb_ty Tx1 Tx2 then return Tx1 else fail
      | _ => fail
      end
  (* lists (the [tm_lcase] is given for free) *)
  (* FILL IN HERE *)
  | <{ nil T }> => return <{{List T}}>
  | <{ h :: t }> =>
      T1 <- type_check Gamma h ;;
      Tl <- type_check Gamma t;;
      match Tl with
      | <{{List T}}> => if eqb_ty T T1 then return Tl else fail
      | _ => fail
      end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{List T}}> =>
          T1 <- type_check Gamma t1 ;;
          T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  (* unit *)
  (* FILL IN HERE *)
  | <{ unit }> => return <{{Unit}}>
  (* pairs *)
  (* FILL IN HERE *)
  | <{ (t1, t2) }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return <{{ T1 * T2 }}>
  | <{ t.fst }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 * _ }}> => return T1
      | _ => fail
      end
  | <{ t.snd }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ _ * T2 }}> => return T2
      | _ => fail
      end
  (* let *)
  (* FILL IN HERE *)
  | <{ let x = t1 in t2 }> =>
      T1 <- type_check Gamma t1 ;;
      type_check (x |-> T1 ; Gamma) t2
  (* fix *)
  | <{ fix f }> =>
      T <- type_check Gamma f ;;
      match T with
      | <{{ T1 -> T2 }}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.



Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
   intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x.  destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
 - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'. 
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1. 
    fully_invert_typecheck Gamma t1 T1 T11 T12. 
  - (* mlt *)  
    invert_typecheck Gamma t1 T1. 
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *) 
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  (* Complete the following cases. *)
  (* sums *)
  - invert_typecheck Gamma t0 T1.
  - invert_typecheck Gamma t0 T2.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    + fully_invert_typecheck Gamma t1 T1 T11 T12.
       eapply T_Case. 
       * apply IHt1. symmetry.  apply HeqTO.
      * apply IHt2. 
    invert_typecheck (x31 |-> T11; Gamma) t2 T2.
 invert_typecheck (x32 |-> T12; Gamma) t3 T3.
    case_equality T2 T3.
     * apply IHt3.
 invert_typecheck (x31 |-> T11; Gamma) t2 T2.
 invert_typecheck (x32 |-> T12; Gamma) t3 T3.
case_equality T2 T3.
  (* unit *)
 - invert_typecheck Gamma <{ nil t }> T1.
  (* pairs *)
  - invert_typecheck Gamma t1 T1.
invert_typecheck Gamma t2 T2.
 analyze T2 T21 T22.  case_equality T21 T1.
- invert_typecheck Gamma t1 T1.
  analyze T1 T11 T12.
invert_typecheck Gamma t2 T2.
invert_typecheck (s |-> T11; s0 |-> <{{ List T11 }}>; Gamma) t3 T3.
 case_equality T2 T3.
- invert_typecheck Gamma <{ unit }> T1.
- invert_typecheck Gamma t1 T1.
invert_typecheck Gamma t2 T2.
- invert_typecheck Gamma t T1.
analyze T1 T11 T12.  
injection H0. intros. subst. eapply T_Fst. apply IHt. symmetry.
apply HeqTO.
- invert_typecheck Gamma t T1.
analyze T1 T11 T12. 
injection H0. intros. subst. eapply T_Snd. apply IHt. symmetry.
apply HeqTO.
- invert_typecheck Gamma t1 T1.
- invert_typecheck Gamma t T1. analyze T1 T11 T12. 
 case_equality T11 T12.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma _); [assumption| solve_by_invert].
Qed.

End TypecheckerExtensions.

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(** **** Exercise: 2 stars, standard, optional (valuef_defn) *)
(* We must first also redefine [value] as a function. *)
Fixpoint valuef (t : tm) : bool :=
  match t with
  | tm_var _ => false
  | <{ \_:_, _ }> => true
  | <{ _ _ }> => false
  | tm_const _ => true
  | <{ succ _ }> | <{ pred _ }> | <{ _ * _ }> | <{ if0 _ then _ else _ }> => false
  (* Complete the following cases *)
  | <{ inr T t }> => valuef t
  | <{ inl T t }> => valuef t
  | <{ case _ of | inl _ => _ | inr _ => _ }> => false
  | <{ nil _ }> => true
  | <{ h :: t }> => andb (valuef h) (valuef t)
  | <{ case _ of | nil => _ | _ :: _ => _ }> => false
  | <{ unit }> => true
  | <{ (t1, t2) }> => andb (valuef t1) (valuef t2)
  | <{ _ .fst }> => false
  | <{ _ .snd }> => false
  | <{ let _ = _ in _ }> => false
  | <{ fix _ }> => false
  end.


Definition manual_grade_for_valuef_defn : option (nat*string) := None.
(** [] *)

(* A little helper to concisely check some boolean properties
   (in this case, that some term is a value, with [valuef]). *)
Definition assert (b : bool) (a : option tm) : option tm :=
  if b then a else None.

Fixpoint stepf (t : tm) : option tm := 
  match t with
  (* pure STLC *)
  | tm_var x => None (* We only define step for closed terms *)
  | <{ \x1:T1, t2 }> => None (* Abstraction is a value *)
  | <{ t1 t2 }> =>
    match stepf t1, stepf t2, t1 with
    | Some t1', _, _ => Some <{ t1' t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _ => assert (valuef t1) (Some <{ t1 t2' }>)
    (* otherwise [t1], [t2] are normal forms *)
    | None, None, <{ \x:T, t11 }> =>
      assert (valuef t2) (Some <{ [x:=t2]t11 }>)
    | _, _, _ => None
    end
  (* numbers *)
  | tm_const _ => None (* number value *)
  | <{ succ t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ succ t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (S n))
    | None, _ => None
    end
  | <{ pred t1 }> =>
    match stepf t1, t1 with
    | Some t1', _ => Some <{ pred t1' }>
    (* otherwise [t1] is a normal form *)
    | None, tm_const n => Some (tm_const (n - 1))
    | _, _ => None
    end
  | <{ t1 * t2 }>  =>
    match stepf t1, stepf t2, t1, t2 with
    | Some t1', _, _, _ => Some <{ t1' * t2 }>
    (* otherwise [t1] is a normal form *)
    | None, Some t2', _, _ =>
      assert (valuef t1) (Some <{ t1 * t2' }>)
    | None, None, tm_const n1, tm_const n2 => Some (tm_const (mult n1 n2))
    | _, _, _, _ => None
    end
  | <{ if0 guard then t else f }> =>
    match stepf guard, guard with
    | Some guard', _ => Some <{ if0 guard' then t else f }>
    (* otherwise [guard] is a normal form *)
    | None, tm_const 0 => Some t
    | None, tm_const (S _) => Some f
    | _, _ => None
    end
  (* Complete the following cases. *)
   | <{ inl T t }> =>
     match stepf t, t with
     | Some t', _ => Some <{ inl T t' }>
     | _, _ => None
     end
  | <{ inr T t }> =>
     match stepf t, t with
     | Some t', _ => Some <{ inr T t' }>
     | _, _ => None
     end
  (* lists (the [tm_lcase] is given for free) *)

     | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      match stepf t0, t0 with
      | Some t0', _ => Some <{ case t0' of | nil => t1 | x21 :: x22 => t2 }>
      (* otherwise [t0] is a normal form *)
      | None, <{ nil _ }> => Some t1
      | None, <{ vh :: vt }> =>
        assert (valuef vh) (assert (valuef vt)
        (Some <{ [x22:=vt]([x21:=vh]t2) }> ))
      | None, _ => None
      end


     | <{case t0 of | inl x1 => t1 | inr x2 => t2}> =>
       match stepf t0, t0 with
       | Some t0', _ => Some <{case t0' of | inl x1 => t1 | inr x2 => t2}>
       | None, <{inl T v}> => assert (valuef v) (Some <{ [x1:=v] t1 }>)
       | None, <{inr T v}> => assert (valuef v) (Some <{ [x2:=v] t2 }>)
       | _ , _ => None
       end

  (* unit *)
   | <{ unit }> => None

  (* nil *)
   | <{ nil _ }> => None

   (* _.fst *)
   | <{ t1.fst }> =>
     match stepf t1, t1 with
     | Some t1', _ => Some <{ t1'.fst }>
     | None, <{(v1, v2)}> => assert (valuef v1) (assert (valuef v2) (Some v1)) 
     | _, _ => None
     end

 (* _.snd *)
  | <{ t1.snd }> =>
     match stepf t1, t1 with
     | Some t1', _ => Some <{ t1'.snd }>
     | None, <{(v1, v2)}> => assert (valuef v1) (assert (valuef v2) (Some v2)) 
     | _, _ => None
    end

(* _::_ *)
  | <{t1 :: t2}> =>
    match stepf t1, stepf t2, t1 with 
    | Some t1', _, _ => Some <{t1' :: t2}>
    | None, Some t2', _ => assert (valuef t1) (Some <{ t1 :: t2' }>)
    | _, _, _ => None
   end

   (* pairs *)
   | <{ (t1, t2)}> =>
      match stepf t1, stepf t2 with
       | Some t1', _ => Some <{ (t1', t2)}> 
       | None, Some t2' => 
       assert (valuef t1) (Some <{ (t1, t2') }>)
        | _, _ => None
      end
   

  (* let *)
  | <{ let x=t1 in t2 }> =>
    match stepf t1, t1 with
     | Some t1', _ => Some <{ let x=t1' in t2 }>
     | None, _ => 
     assert (valuef t1) (Some <{ [x:=t1]t2 }>)
    end

  (* fix *)
   | <{ fix t1 }> =>
    match stepf t1, t1 with
     | Some t1', _ => Some <{ fix t1' }>
     | None, <{\xf:T1, t1}> => Some <{ [xf:=fix (\xf:T1, t1)] t1 }>
     | _, _ => None
     end
  end.        


Lemma sound_valuef : forall t,
    valuef t = true -> value t.
Proof.
  induction t; 
  intros; simpl in H; try inversion H; eauto.
 - apply v_lcons. 
   + apply andb_true_iff in H. destruct H.
     * apply IHt1. apply H.
   + apply IHt2. apply andb_true_iff in H. destruct H. apply H0.
 - apply v_pair. apply andb_true_iff in H. destruct H.
   + apply IHt1. apply H.
 + apply IHt2. apply andb_true_iff in H. destruct H. apply H0.
Qed.


Lemma complete_valuef : forall t,
    value t -> valuef t = true.
Proof.
  induction t; 
  intros; simpl in H; try inversion H; eauto.
  - simpl. apply andb_true_iff. split.
   +  apply IHt1. apply H2.
   + apply IHt2. apply H3.
 - simpl.  apply andb_true_iff. split.
  +  apply IHt1. apply H2.
   + apply IHt2. apply H3.
Qed.

(* Soundness of [stepf]:

   Theorem sound_stepf : forall t t',
       stepf t = Some t'  ->  t --> t'.

   By induction on [t]. We automate the handling of each case with
   the following tactic [auto_stepf]. *)

Tactic Notation "auto_stepf" ident(H) :=
  (* Step 1: In every case, the left hand side of the hypothesis
     [H : stepf t = Some t'] simplifies to some combination of
     [match u with ... end], [assert u (...)] (for some [u]).
     The tactic [auto_stepf] then destructs [u] as required.
     We repeat this step as long as it is possible. *)
  repeat
    match type of H with
    | (match ?u with _ => _ end = _) =>
      let e := fresh "e" in
      destruct u eqn:e
    | (assert ?u _ = _) =>
      (* In this case, [u] is always of the form [valuef t0]
         for some term [t0]. If [valuef t0 = true], we immediately
         deduce [value t0] via [sound_valuef]. If [valuef t0 = false],
         then that equation simplifies to [None = Some t'], which is
         contradictory and can be eliminated with [discriminate]. *)
      let e := fresh "e" in
      destruct u eqn:e;
      simpl in H; (* [assert true (...)] must be simplified
                     explicitly. *)
      [apply sound_valuef in e | discriminate]
    end;
  (* Step 2: We are now left with either [H : None = Some t'] or
     [Some (...) = Some t'], and the rest of the proof is a
     straightforward combination of the induction hypotheses. *)
  (discriminate + (inversion H; subst; auto)).

(** **** Exercise: 2 stars, standard, optional (sound_stepf) *)
(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof.
  intros t. induction t; simpl; intros t' H;
    auto_stepf H. 
Qed.


Lemma value_stepf_nf : forall t,
    value t -> stepf t = None.
Proof.
  intros t. induction t; simpl; intros H;
    auto_stepf H.
  - destruct (stepf t0). 
    + apply IHt in H1. inversion H1.
    + reflexivity.
  - destruct (stepf t0).
   + apply IHt in H1. inversion H1.
    + reflexivity.
  - destruct (stepf t1).
    + apply IHt1 in H2. inversion H2.
    + destruct (stepf t2).
      * apply IHt2 in H3. inversion H3.
      * reflexivity.
 - destruct (stepf t1).
    + apply IHt1 in H2. inversion H2.
    + destruct (stepf t2).
      * apply IHt2 in H3. inversion H3.
      * reflexivity.
Qed.


Theorem complete_stepf : forall t t',
    t --> t' -> stepf t = Some t'.
Proof.
intros.  
induction H. 
 - simpl. assert (value v2). 
   apply H. apply value_stepf_nf in H. rewrite H.
    + apply complete_valuef in H0.  rewrite H0. 
      simpl. reflexivity.
 - simpl. rewrite IHstep. reflexivity.
 - simpl. rewrite IHstep. assert (value v1).  
   apply H. apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H1. rewrite H1. simpl. reflexivity.
 - simpl. rewrite IHstep. reflexivity.
 - simpl. reflexivity.
 - simpl. rewrite IHstep. reflexivity.
 - simpl.  reflexivity.
 - simpl. reflexivity.
 - simpl. rewrite IHstep. reflexivity.
 - simpl. assert (value v1).  
   apply H. apply value_stepf_nf in H.  rewrite H.  rewrite IHstep. 
    apply complete_valuef in H1. rewrite H1. simpl. reflexivity.
 - simpl. rewrite IHstep. reflexivity. 
- simpl.  reflexivity. 
- simpl.  reflexivity. 
- simpl. rewrite IHstep.  reflexivity. 
- simpl.  rewrite IHstep.  reflexivity.
-  simpl. rewrite IHstep. reflexivity.
- simpl.  assert (value v0).  
   apply H.  apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H0. rewrite H0. simpl. reflexivity. 
- simpl. assert (value v0).  
   apply H.  apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H0. rewrite H0. simpl. reflexivity. 
- simpl. rewrite IHstep.  reflexivity.
- simpl. assert (value v1).  
   apply H.  apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H1. rewrite H1. simpl. rewrite IHstep. reflexivity. 
- simpl. rewrite IHstep. reflexivity. 
- simpl. reflexivity. 
- simpl. assert (value v1).  
   apply H. assert (value vl).  apply H0. apply value_stepf_nf in H. rewrite H. 
   apply value_stepf_nf in H0. rewrite H0. 
   apply complete_valuef in H1. rewrite H1. simpl. 
 apply complete_valuef in H2. rewrite H2. simpl. 
  reflexivity.
- simpl. rewrite IHstep. reflexivity. 
- simpl. assert (value v1).  
   apply H.  apply value_stepf_nf in H. rewrite H. 
  
 apply complete_valuef in H1. rewrite H1. simpl.
rewrite IHstep. reflexivity.
- simpl.  rewrite IHstep. reflexivity.
- simpl.   assert (value v1).  
   apply H. apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H1. rewrite H1. simpl. 
assert (value v2).  
   apply H0. apply value_stepf_nf in H0. rewrite H0. 
apply complete_valuef in H2. rewrite H2. simpl. 
   reflexivity.
-  simpl. rewrite IHstep. reflexivity. 
-  simpl.   assert (value v1).  
   apply H. apply value_stepf_nf in H. rewrite H.
   apply complete_valuef in H1. rewrite H1. simpl. 
assert (value v2).  
   apply H0. apply value_stepf_nf in H0. rewrite H0. 
apply complete_valuef in H2. rewrite H2. simpl. 
   reflexivity.        
 - simpl. rewrite IHstep. reflexivity. 
- simpl. assert (value v1).  
   apply H. apply value_stepf_nf in H. rewrite H. 
   apply complete_valuef in  H0. rewrite H0. simpl.  reflexivity.
- simpl. rewrite IHstep. reflexivity.
- simpl. reflexivity. 
Qed.

End StepFunction.
