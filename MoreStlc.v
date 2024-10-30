
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import SmallStep.
From PLF Require Import STLC.
Set Default Goal Selector "!".

Module STLCExtended.

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.



Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

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

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
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

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).


(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(** **** Exercise: 3 stars, standard (STLCExtended.subst) *)
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
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if String.eqb x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if String.eqb x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>

  (* Complete the following cases. *)

  (* pairs *)
   | <{ (t1, t2)}> =>
      <{(([x:=s] t1), ([x:=s] t2))}>
    | <{ t1.fst}> =>
      <{ ([x:=s] t1).fst}>
   | <{ t1.snd}> =>
      <{ ([x:=s] t1).snd}>
  (* let *)
   | <{ let y=t1 in t2 }> =>
     tm_let y 
      <{ [x:=s] t1 }>
      (if String.eqb x y then t2 else <{ [x:=s] t2 }>)
  (* fix *)
    | <{ fix t1 }> =>
      <{ fix ([x:=s] t1) }> 
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

(** **** Exercise: 3 stars, standard (STLCExtended.step) *)
Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
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
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' -> 
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>

  (* Add rules for the following extensions. *)

  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
      t1 --> t1' ->
       <{(t1 , t2)}> --> <{(t1' , t2)}>
  | ST_Pair2 : forall v1 t2' t2,
      value v1 ->
      t2 --> t2' ->
      <{(v1 , t2)}> --> <{(v1 , t2')}>
  | ST_Fst1 : forall t1 t1', 
      t1 --> t1' ->
      <{ t1.fst }> --> <{ t1'.fst }>
  | ST_FstPair : forall v1 v2, 
      value v1 ->
      value v2 ->
      <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t1 t1', 
      t1 --> t1' ->
      <{ t1.snd }> --> <{ t1'.snd }>
  | ST_SndPair : forall v1 v2, 
      value v1 ->
      value v2 ->
      <{ (v1,v2).snd }> --> v2

  (* let *)
   | ST_Let1 : forall x t1 t1' t2, 
      t1 --> t1' ->
      <{ let x=t1 in t2 }>  --> <{ let x=t1' in t2 }>
   | ST_LetValue : forall x v1 t2,
        value v1 -> 
      <{ let x=v1 in t2 }>  --> <{ [x:=v1]t2 }>

  (* fix *)
  | ST_Fix1 : forall t1 t1', 
      t1 --> t1' ->
      <{ fix t1 }>  --> <{ fix t1' }>
 | ST_FixAbs : forall xf t1 T1, 
      <{ fix (\xf:T1, t1) }> --> <{ [xf:=fix (\xf:T1, t1)] t1 }>

  where "t '-->' t'" := (step t t').


Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

(** **** Exercise: 3 stars, standard (STLCExtended.has_type) *)
Inductive has_type : context -> tm -> ty -> Prop :=
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
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |-- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in T0 ->
      Gamma |-- t3 \in T0 ->
      Gamma |-- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |-- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |-- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |-- t2 \in T3 ->
      Gamma |-- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |-- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (List T1) ->
      Gamma |-- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (List T1) ->
      Gamma |-- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |-- t3 \in T2 ->
      Gamma |-- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit

  (* Add rules for the following extensions. *)

  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1 , t2) \in (T1*T2)
   | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.fst \in T1
 | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1*T2) ->
      Gamma |-- t0.snd \in T2

  (* let *)
 | T_Let : forall Gamma x t1 t2 T1 T2,
     Gamma |-- t1 \in T1  ->   
     (x|->T1; Gamma) |-- t2 \in T2	-> 
     Gamma |-- (let x=t1 in t2) \in T2

  (* fix *)
 | T_Fix : forall Gamma t1 T1,
  Gamma |-- t1 \in (T1 -> T1)	->  
  Gamma |-- (fix t1) \in T1	


where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.
Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

Module Numtest.
Definition tm_test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof.
  unfold tm_test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of auto from the
     default 5 to 10. *)
  auto 10.
Qed.
 
Example reduces :
  tm_test -->* 5.
Proof.
 
  unfold tm_test. normalize.
Qed.

End Numtest.


Module ProdTest.

Definition tm_test :=
  <{((5,6),7).fst.snd}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. 
Qed.


Example reduces :
  tm_test -->* 6.
Proof.
 
  unfold tm_test. normalize.
Qed.

End ProdTest.

Module LetTest.

Definition tm_test :=
  <{let x = (pred 6) in (succ x)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto.
Qed.

Example reduces :
  tm_test -->* 6.
Proof.
 unfold tm_test. normalize.
Qed.

End LetTest.

Module LetTest1.

Definition tm_test :=
  <{let z = pred 6 in
    (succ z)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. 
eapply T_Let.
- apply T_Pred.
  apply T_Nat.
- apply T_Succ.
  apply T_Var.
  simpl. rewrite  update_eq.
  reflexivity.
Qed.

Example reduces :
  tm_test -->* 6.
Proof.
 unfold tm_test. normalize.
Qed.
End LetTest1.

Module Sumtest1.

Definition tm_test :=
  <{case (inl Nat 5) of
    | inl x => x
    | inr y =>  y}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test.
eapply T_Case.
- apply T_Inl. apply T_Nat.
-  apply T_Var. rewrite  update_eq. 
  reflexivity.
-  apply T_Var. rewrite  update_eq. 
  reflexivity.
Qed. 



Example reduces :
  tm_test -->* 5.
Proof.
unfold tm_test. eapply multi_step.
- apply ST_CaseInl. apply v_nat.
- simpl. apply multi_refl. 
Qed.

End Sumtest1.


Module Sumtest2.
(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => tm_test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition tm_test :=
  <{let processSum =
    (\x:Nat + Nat,
      case x of
       | inl n => n
       | inr n => (if0 n then 1 else 0)) in
    (processSum (inl Nat 5), processSum (inr Nat 5))}>.


Example typechecks :
  empty |-- tm_test \in (Nat * Nat).
Proof. unfold tm_test. 
   eapply T_Let.
  - apply T_Abs. eapply T_Case.
    + apply T_Var. rewrite  update_eq.  reflexivity.
    + apply T_Var. rewrite  update_eq.  reflexivity.
    + apply T_If0.
      * apply T_Var. rewrite  update_eq.  reflexivity.
      * apply T_Nat.
      * apply T_Nat.
  - apply T_Pair.
    + eapply T_App.
      * apply T_Var. 
       rewrite  update_eq.  reflexivity.
      * apply T_Inl. apply T_Nat.
    + eapply T_App.
      * apply T_Var. 
       rewrite  update_eq.  reflexivity.
      * apply T_Inr. apply T_Nat.
Qed.


Example reduces :
  tm_test -->* <{(5, 0)}>.
Proof.
  unfold tm_test. eapply multi_step.
  - apply ST_LetValue. 
    + apply v_abs.  
   - eapply multi_step.
     + 
     apply ST_Pair1.
     apply ST_AppAbs. apply v_inl. apply v_nat.
    + simpl. eapply multi_step. 
      * apply ST_Pair1. apply ST_CaseInl.
        apply v_nat.
      * simpl. eapply multi_step. 
        -- apply ST_Pair2.
           ++  apply v_nat.
           ++ apply ST_AppAbs. apply v_inr.
              apply v_nat.
        -- simpl.   eapply multi_step. 
           ++ apply ST_Pair2.
              ** apply v_nat.
              ** apply ST_CaseInr. apply v_nat.
           ++ simpl. eapply multi_step. 
              ** apply ST_Pair2.
                 --- apply v_nat.
                 --- apply ST_If0_Nonzero.
                ** apply multi_refl. 
Qed.
End Sumtest2.

Module ListTest.
(* let l = cons 5 (cons 6 (nil Nat)) in
   case l of
     nil => 0
   | x::y => x*x *)
Definition tm_test :=
  <{let l = (5 :: 6 :: (nil Nat)) in
    case l of
    | nil => 0
    | x :: y => (x * x)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test.
eapply T_Let.
- apply T_Cons.
  + apply T_Nat.
  + apply T_Cons.
    * apply T_Nat.
    * apply T_Nil.
- eapply T_Lcase.
  + apply T_Var.
    rewrite update_eq.
    reflexivity.
  + apply T_Nat.
  + apply T_Mult.
    * apply T_Var. rewrite update_eq. reflexivity.
    * apply T_Var. rewrite update_eq. reflexivity.
Qed.

Example reduces :
  tm_test -->* 25.
Proof.
 
  unfold tm_test. 
eapply multi_step.
  - apply ST_LetValue.  
    + apply v_lcons.
      * apply v_nat.
      * apply v_lcons.
        -- apply v_nat.
        -- apply v_lnil.
   - simpl. eapply multi_step.
     +  apply ST_LcaseCons.
        * apply v_nat.
        * apply  v_lcons.
          -- apply v_nat.
          -- apply v_lnil.
     + simpl. eapply multi_step. 
       * apply ST_Mulconsts.
       * simpl. apply multi_refl. 
Qed.
End ListTest.

Module FixTest1.

End FixTest1.


Module FixTest2.
(*  Definition map :=
  <{ \g:Nat -> Nat,
       fix
         (\f:(List Nat) -> (List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l)))}>.


Example typechecks :
  empty |-- map \in
    ((Nat -> Nat) -> ((List Nat) -> (List Nat))).
Proof. 
unfold map. auto 10.
Qed.


Example reduces :
  <{map (\a:Nat, succ a) (1 :: 2 :: (nil Nat))}>
  -->* <{2 :: 3 :: (nil Nat)}>.
Proof.
 unfold map. normalize.
Qed.  *)

End FixTest2.


Module FixTest3.

(* Definition equal :=
  <{fix
        (\eq: Nat -> Nat -> Nat,
           \m: Nat, \n: Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n))))}>.
Example typechecks :
  empty |-- equal \in (Nat -> Nat -> Nat).
Proof. 
unfold equal. auto 10. 
Qed. 


 Example reduces :
  <{equal 4 4}> -->* 1.
Proof. 
unfold equal. normalize.
Qed.
 

Example reduces2 :
  <{equal 4 5}> -->* 0.
Proof.
unfold equal. normalize.
Qed. *)
 

End FixTest3.


Module FixTest4.


(*  Definition eotest :=
<{let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd = evenodd.snd in
    (even 3, even 4)}>.


Example typechecks :
  empty |-- eotest \in (Nat * Nat).
Proof. unfold eotest. eauto 30. 
Qed.


Example reduces :
  eotest -->* <{(0, 1)}>.
Proof.
unfold eotest. eauto 10. normalize.
Qed.  *)

End FixTest4.
End Examples.


 
Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
intros.
destruct H0.
- inversion H. exists x0.
  exists t1. reflexivity.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
Qed. 



 Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
intros t T Ht. 
remember empty as Gamma.
induction Ht; subst Gamma; eauto.    
     
- (* T_Var *)
  discriminate H.

- (* T_App *) 
  right. destruct IHHt1.  
  + reflexivity.
  + (* t1 is a value *)
    destruct IHHt2...
    * (* t2 is also a value *)
      eapply canonical_forms_fun in Ht1;  [|assumption].
      destruct Ht1 as [x [t0 H1]]. subst.
      exists (<{ [x:=t2]t0 }>)...
    * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...
  + (* t1 steps *)
    destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

(* ST_Succ *)
- right. destruct IHHt.
  + reflexivity.
  + inversion H.
    * subst. inversion Ht.
    * subst. exists <{ {S n} }>.
      apply ST_SuccNat.
    * subst. inversion Ht.
    * subst. inversion Ht.
    * subst. inversion Ht.
    * subst. inversion Ht.
    * subst. inversion Ht.
    * subst. inversion Ht.
  + destruct H as [t' H].
    exists <{ succ t' }>. apply ST_Succ. apply H.

(* ST_Pred *)
- right. destruct IHHt.
    + reflexivity.
    + inversion H.
      * subst. inversion Ht.
      * subst. exists <{ {n - 1} }>.
        apply ST_PredNat.
      * subst. inversion Ht.
      * subst. inversion Ht.
      * subst. inversion Ht.
      * subst. inversion Ht.
      * subst. inversion Ht.
      * subst. inversion Ht.
    + destruct H as [t' H].
      exists <{ pred t' }>. apply ST_Pred. apply H.

(* ST_Mult *)
- right. destruct IHHt1.  
  + reflexivity.
  + (* t1 is a value *)
    destruct IHHt2...
    * destruct H.
      -- inversion Ht1.
      -- inversion H0.
         ++ subst. inversion Ht2.
         ++ exists <{ {n * n0} }>. apply ST_Mulconsts.
         ++ subst. inversion Ht2.
         ++ subst. inversion Ht2.
         ++ subst. inversion Ht2.
         ++ subst. inversion Ht2.
         ++ subst. inversion Ht2.
         ++ subst. inversion Ht2.
      -- subst. inversion Ht1.
      -- subst. inversion Ht1.
      -- subst. inversion Ht1.
      -- subst. inversion Ht1.
      -- subst. inversion Ht1.
      -- subst. inversion Ht1.
    * destruct H0 as [t2' H0].
      exists <{t1 * t2'}>.
      apply ST_Mult2.
      -- apply H.
      -- apply H0.
  + destruct H as [t1' H].
    exists <{t1' * t2}>.
    apply ST_Mult1. apply H.

- (* T_If *)
  right. destruct IHHt1...
  + destruct IHHt2...
    * destruct IHHt3...
      -- destruct H.
         ++ inversion Ht1.
         ++ destruct n.
            ** exists t2. apply ST_If0_Zero.
            ** exists t3. apply ST_If0_Nonzero.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
      -- destruct H.
         ++ inversion Ht1.
         ++ destruct n.
            ** exists t2. apply ST_If0_Zero.
            ** exists t3. apply ST_If0_Nonzero.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
         ++ inversion Ht1.
    * destruct H.
      -- inversion Ht1.
      -- destruct n.
         ++ exists t2. apply ST_If0_Zero.
         ++ exists t3. apply ST_If0_Nonzero.
      -- inversion Ht1.
      -- inversion Ht1.
      -- inversion Ht1.
      -- inversion Ht1.
      -- inversion Ht1.
      -- inversion Ht1.
  + destruct H as [t1' H].
    exists <{if0 t1' then t2 else t3}>.
    apply ST_If0. apply H.

(* ST_Inl *)
- destruct IHHt...
  destruct H as [t1' H]. right.
  exists <{inl T2 t1'}>. apply ST_Inl.
  apply H.

(* ST_Inr *)
- destruct IHHt...
  destruct H as [t2' H]. right.
  exists <{inr T1 t2'}>. apply ST_Inr.
  apply H.

(* ST_Case *)
- right. destruct IHHt1...
  + destruct H.
    * inversion Ht1.
    * inversion Ht1.
    * exists <{ [x1:=v]t1 }>. apply ST_CaseInl. apply H.
    * exists <{ [x2:=v]t2 }>. apply ST_CaseInr. apply H.
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht1.
  + destruct H as [t0' H]. 
    exists <{case t0' of | inl x1 => t1 | inr x2 => t2}>.
    apply ST_Case. apply H.

(* ST_Cons1 *)
- destruct IHHt1...
   + destruct IHHt2...
     right. destruct H0 as [t2' H0].
     exists <{t1 :: t2'}>.
     apply ST_Cons2.
     * apply H.
     * apply H0.
   + destruct H as [t1' H].
     right. exists <{t1' :: t2}>. apply ST_Cons1. apply H.


(* ST_LcaseCons *)
- destruct IHHt1...
  + right. destruct H.
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht1.
    * exists t2. apply ST_LcaseNil.
    * exists <{ [x2 := v2] ([x1 := v1] t3) }>. apply ST_LcaseCons.
      -- apply H.
      -- apply H0.
    * inversion Ht1.
    * inversion Ht1.
  + destruct H as [t1' H]. right.
    exists <{case t1' of | nil => t2 | x1 :: x2 => t3}>. apply ST_Lcase1.
    apply H.

(* ST_Pair *)
- destruct IHHt1...
  + destruct IHHt2... 
    destruct H0 as [t2' H0]. right.
    exists <{(t1 , t2')}>. apply ST_Pair2.
    * apply H.
    * apply H0.
  + destruct H as [t1' H]. right.
    exists <{(t1' , t2)}>. apply ST_Pair1. apply H.
  
(* ST_FstPair *)
-  destruct IHHt...
  + right. destruct H.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * exists v1. apply ST_FstPair. 
      -- apply H.
      -- apply H0.
  + destruct H as [t0' H]. 
    right. exists <{ t0'.fst }>.
    apply ST_Fst1. apply H.

(* ST_SndPair *)
- destruct IHHt...
  + right. destruct H.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * exists v2. apply ST_SndPair.
       -- apply H.
      -- apply H0.
  + destruct H as [t0' H].
    right. exists <{ t0'.snd }>.
    apply ST_Snd1. apply H.
- destruct IHHt1.
  + reflexivity.
  + right. exists <{ [x0:=t1]t2 }>.
    apply ST_LetValue. apply H.
  + right. destruct H as [t1' H].
    exists <{ let x0=t1' in t2 }>.
    apply ST_Let1.
   apply H. 

(* fix *)
-  destruct IHHt... 
  + right. destruct H.
    * exists <{ [x0:=fix (\x0:T2, t1)] t1 }>. apply ST_FixAbs.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
    * inversion Ht.
  + right. destruct H as [t1' H].
    exists <{ fix t1' }>.
    apply ST_Fix1. apply H.
Qed.

 
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma |-- t \in T ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using includedin_update.
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
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
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
  - (* tm_case *)
    rename s into x1, s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (eqb_spec x x1); subst.
      * (* x = x1 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> x1 *)
        apply IHt2.
        rewrite update_permute; auto.
    + (* right arm *)
      destruct (eqb_spec x x2); subst.
      * (* x = x2 *)
        rewrite update_shadow in H9. assumption.
      * (* x <> x2 *)
        apply IHt3.
        rewrite update_permute; auto.
  - (* tm_lcase *)
    rename s into y1, s0 into y2.
    eapply T_Lcase...
    destruct (eqb_spec x y1); subst.
    + (* x=y1 *)
      destruct (eqb_spec y2 y1); subst.
      * (* y2=y1 *)
        repeat rewrite update_shadow in H9.
        rewrite update_shadow.
        assumption.
      * rewrite update_permute in H9; [|assumption].
        rewrite update_shadow in H9.
        rewrite update_permute;  assumption.
    + (* x<>y1 *)
      destruct (eqb_spec x y2); subst.
      * (* x=y2 *)
        rewrite update_shadow in H9.
        assumption.
      * (* x<>y2 *)
        apply IHt3.
        rewrite (update_permute _ _ _ _ _ _ n0) in H9.
        rewrite (update_permute _ _ _ _ _ _ n) in H9.
        assumption.
 - (* tm_let *) apply T_Let with T1. 
    + apply IHt1. assumption.
    +  destruct (String.eqb_spec x s).
      * subst s. rewrite update_shadow in H6.  apply H6.   
      * apply IHt2. rewrite update_permute.
          { assumption. }
          { auto. }
Qed.

 

 
End STLCExtended.







 