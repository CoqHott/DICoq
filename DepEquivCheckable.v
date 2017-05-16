Require Export Unicode.Utf8_core.
Require Import String List. 
Require Export Showable PartialOrder TErrorMonad Equiv HoTT Decidable DepEquiv.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).
Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.

Local Open Scope string_scope.

Set Universe Polymorphism.

(** * Dependent equivalences *) 

(** 

A _simple_ type is an inhabitant of [Type], e.g. [A: Type], [A → B: Type]. 

A _rich_ type is a dependent pair, e.g. [{ a : A | B a}]. 

A _dependent_ type is a type family [A → Type] indexed by some type
[A], e.g. [C: nat → Type], [C (S n) → C n].

  We define the following family of cast operators:
  - [to_rich]: from [A] to [{a: A & P a}]
  - [to_dep]: from [A] to [B a]
  - [to_simp]: from [B a] to [A]

   We don't provide an explicit [rich_to_simpl], since this is just [projT1]
*)


(**

  A dependent equivalence between [B : A -> Type] and [C : Type] is
  witnessed by a (proof-irrelevant) predicate [P : A -> C -> Type]
  such that [B] and [{C & P}] are equivalent while [{C & P}] and [C]
  are partially equivalent. It also a partial index synthesis function
  [c_to_a], which tries to compute an index from a computational
  element [C].

*)

(* =DepEquiv= *)
Class DepAntiCoercion (A:HSet) (B: A -> HSet) (C:HSet) :=
  {  P : A -> C -> HProp;
     total_equiv_C :> forall a, B a ≃ {c:C & P a c}; 
     partial_equiv_C :> forall a, {c:C & P a c} ≲AK C;
     c_to_a_C : C ⇀ A;
     prop_c_to_a : forall a (b:B a), (c_to_a_C °° ((partial_equiv_C a).(ac_fun)))
                                  ((total_equiv_C a).(e_fun) b) = Some a;
  }.
Notation "B ≲AK□ C" := (DepAntiCoercion _ B C)
(* =end= *)
                      (at level 50).


Hint Extern 1 (IsEquiv ?f) => apply (e_isequiv (e := total_equiv_C _)) :
             typeclass_instances.

Hint Extern 1 (IsAntiConnectionK ?f) => apply (ac_isconn (a := partial_equiv_C _)) :
             typeclass_instances.

Definition c_to_b_C {A:HSet} {B: A -> HSet} {C:HSet}
           `{B ≲AK□ C} {a:A}: {c:C & P a c} -> (B a) := 
  e_inv _.

Definition b_to_c_C {A:HSet} {B: A -> HSet} {C}
           `{B ≲AK□ C} {a:A}: B a -> {c:C & P a c} := 
  (total_equiv_C a).(e_fun). 

Definition to_rich_C {A:HSet} {B: A -> HSet} {C}
           `{B ≲AK□ C} {a:A}: C ⇀ {c: C & P a c} :=
  ac_inv _.

Program Definition to_dep_C {A:HSet} {B: A -> HSet} {C}
           `{B ≲AK□ C}
           (a:A) : C ⇀ (B a) := 
  fun c => c' <- ac_inv _ c; clift (e_inv _) c'.

Definition to_simpl_C {A:HSet} {B: A -> HSet} {C:HSet} 
           `{B ≲AK□ C}
           {a:A} : B a ⇀ C := 
  (partial_equiv_C a).(ac_fun) ° ((total_equiv_C a).(e_fun)).

(** ** Properties *)

Definition sub_eq_implies {A B B' : HSet} (x:TError A info_str) {f : A ⇀ B} {y : TError B info_str}
           {g : A ⇀ B'} {y' : TError B' info_str}
  (e : forall a, f a ≼ y -> g a ≼ y') : (a <- x; f a) ≼ y -> (a <- x; g a) ≼ y'.
Proof.
  destruct x. apply e. exact (@id _). 
Defined.

Definition sub_eq_implies_simpl {A B : HSet} (x:TError A info_str) {y : TError A info_str}
           {g : A ⇀ B} {y' : TError B info_str}
  (e : forall a, creturn a ≼ y -> g a ≼ y') : x ≼ y -> (a <- x; g a) ≼ y'.
Proof.
  destruct x. apply e. intros H. exact H.
Defined.

Definition sub_eq_implies_complex  {A B B' C :HSet} (x:TError A info_str) {f : A ⇀ B}
           {y : TError B info_str} {g : A ⇀ B'} {y' : TError C info_str} {g' : B' ⇀ C}
           (e : forall a, f a ≼ y -> (b <- g a ; g' b) ≼ y') :
  (a <- x; f a) ≼ y ->  (b <- (a <- x; g a); g' b)  ≼ y'.
Proof.
  destruct x. apply e. intros X. simpl in *. exact X.
Defined.

Definition sub_eq_implies_op {A B B' : HSet} (x:TError A info_str) {f : A ⇀ B} {y : B}
           {g : A ⇀ B'} {y' : TError B' info_str}
  (e : forall a, creturn y ≼ f a -> y' ≼ g a) : creturn y ≼ (a <- x; f a) -> y' ≼ (a <- x; g a).
Proof.
  destruct x. apply e. intro H; inversion H. 
Defined.

Definition sub_eq_implies_op_simpl {A B :HSet} (x:TError A info_str) {y : A}
           {g : A ⇀ B} {y' : TError B info_str}
  (e : forall a, creturn y ≼ creturn a -> y' ≼ g a) : creturn y ≼ x -> y' ≼ (a <- x; g a).
Proof.
  destruct x. apply e. intros H. inversion H.
Defined.

(* =DepEquiv_PartialEquivK= *)
Program Definition DepCoercion_ConnectionK  (A : HSet) (B : A -> HSet)
         (C : HSet) `{B ≲AK□ C} (a:A) : B a ≲AK C :=
  {| ac_fun := to_simpl_C;
     ac_isconn := {| ac_inv := to_dep_C a|} |}.
(* =end= *)
Next Obligation.
  - rename a0 into b. change ((to_dep_C a °° to_simpl_C) b ≼ creturn b). unfold kleisliComp, compose. 
    unfold to_dep_C, to_rich_C, to_simpl_C, compose in *. 
    assert (f := ac_sect (IsAntiConnectionK := ac_isconn (a := partial_equiv_C a)) _ (b_to_c_C b)).
    unfold kleisliComp in f.
    revert f. unfold b_to_c_C, compose. 
    apply sub_eq_implies. intro c. 
    apply sub_eq_implies_simpl. intro x. 
    intro e. pose (ap (e_inv _) (Some_inj e)). apply (ap (@Some _ _)).
    pose (e_sect (IsEquiv := e_isequiv (e := total_equiv_C a)) _ b). 
    refine (e0 @ e1).
Defined.
Next Obligation.
    rename a0 into c. unfold kleisliComp. 
    unfold to_dep_C, to_rich_C in *.
    unfold to_simpl_C, clift, compose.
    assert (f := ac_retr (IsAntiConnectionK := ac_isconn (a := partial_equiv_C a)) _ c).
    unfold kleisliComp in f.
    revert f. apply sub_eq_implies_complex. intros s e. 
    pose (e_retr (IsEquiv := e_isequiv (e := total_equiv_C a)) _ s).
    unfold compose, id in e0. simpl in *.
    simpl.
    rewrite e0. exact e.
Defined.

(* =IsDepAntiEquiv= *)
Definition IsDepAntiCoercion (A:HSet) (B: A -> HSet) (C:HSet) P (H:forall a c, Checkable (P a c)) 
  (b_to_c : forall a, B a -> {c : C & P a c}) (c_to_b : forall a, {c : C & P a c} -> B a) (c_to_a : C ⇀ A) : 
  (forall a, (c_to_b a) ° (b_to_c a) == id ) -> (forall a, (b_to_c a) ° (c_to_b a) == id) -> 
  (forall a (b:B a), c_to_a (b_to_c a b).1 = Some a) -> B ≲AK□ C
(* =end= *)
  :=
    fun prop_b_to_b prop_c_to_c prop_c_to_a =>
      Build_DepAntiCoercion A B C P
                        (TotalEquiv A B C P b_to_c c_to_b prop_b_to_b prop_c_to_c)
                        (fun a => Decidable_AntiConnectionK C (P a))
                        c_to_a prop_c_to_a.

(** Given a relation [R : TError A -> A -> Type], one can automatically
construct a partial type equivalence between [B: A → Type] and [C:
Type] as long as we can recompute the index from an inhabitant of
[C]. This is the role of the function [c_to_a_rel]. *)


Definition AntiCoercion_rel {A:HSet} {B: A -> HSet} {C:HSet} (R : TError A info_str -> A -> HProp)
   (c_to_a_rel : C ⇀ A)
   (P := fun a c => R (c_to_a_rel c) a)
   (b_to_c_rel : forall a, B a -> {c : C & P a c})
   (c_to_b_rel : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b_rel : forall a, (c_to_b_rel a) ° (b_to_c_rel a) == id) 
   (prop_c_to_c_rel : forall a, (b_to_c_rel a) ° (c_to_b_rel a) == id)
   {DepEquiv_check_rel : forall a a', Checkable (R a a')}
   {HSet_C : IsHSet C}
   (prop_c_to_a_R : forall a (b:B a), c_to_a_rel (b_to_c_rel _ b).1 = Some a) :
  B ≲AK□ C
  :=
  IsDepAntiCoercion A B C P _ b_to_c_rel c_to_b_rel c_to_a_rel prop_b_to_b_rel prop_c_to_c_rel
            (fun _ _ => prop_c_to_a_R _ _).

