Require Export Unicode.Utf8_core.
Require Import String List. 
Require Export Showable PartialOrder TErrorMonad Equiv HoTT Decidable.

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
Class DepCoercion (A:HSet) (B: A -> HSet) (C:HSet) :=
  {  P : A -> C -> HProp;
     total_equiv :> forall a, B a ≃ {c:C & P a c}; 
     partial_equiv :> forall a, {c:C & P a c} ≲K C;
     c_to_a : C ⇀ A;
     prop_c_to_a : forall a (b:B a), (c_to_a °° ((partial_equiv a).(pc_fun)))
                                  ((total_equiv a).(e_fun) b) = Some a;
  }.
Notation "B ≲K□ C" := (DepCoercion _ B C)
(* =end= *)
                      (at level 50).


Hint Extern 1 (IsEquiv ?f) => apply (e_isequiv (e := total_equiv _)) :
             typeclass_instances.

Hint Extern 1 (IsConnectionK ?f) => apply (pc_isconn (c := partial_equiv _)) :
             typeclass_instances.

Definition c_to_b {A:HSet} {B: A -> HSet} {C:HSet}
           `{B ≲K□ C} {a:A}: {c:C & P a c} -> (B a) := 
  e_inv _.

Definition b_to_c {A:HSet} {B: A -> HSet} {C}
           `{B ≲K□ C} {a:A}: B a -> {c:C & P a c} := 
  (total_equiv a).(e_fun). 

Definition to_rich {A:HSet} {B: A -> HSet} {C}
           `{B ≲K□ C} {a:A}: C ⇀ {c: C & P a c} :=
  pc_inv _.

Program Definition to_dep {A:HSet} {B: A -> HSet} {C}
           `{B ≲K□ C}
           (a:A) : C ⇀ (B a) := 
  fun c => c' <- pc_inv _ c; clift (e_inv _) c'.

Definition to_simpl {A:HSet} {B: A -> HSet} {C:HSet} 
           `{B ≲K□ C}
           {a:A} : B a ⇀ C := 
  (partial_equiv a).(pc_fun) ° ((total_equiv a).(e_fun)).

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
         (C : HSet) `{B ≲K□ C} (a:A) : B a ≲K C :=
  {| pc_fun := to_simpl;
     pc_isconn := {| pc_inv := to_dep a|} |}.
(* =end= *)
Next Obligation.
  - rename a0 into b. change (creturn b ≼ (to_dep a °° to_simpl) b). unfold kleisliComp, compose. 
    unfold to_dep, to_rich, to_simpl, compose in *. 
    assert (f := pc_sect (IsConnectionK := pc_isconn (c := partial_equiv a)) _ (b_to_c b)).
    unfold kleisliComp in f.
    revert f. unfold b_to_c, compose. 
    apply sub_eq_implies_op. intro c. 
    apply sub_eq_implies_op_simpl. intro x. 
    intro e. pose (ap (e_inv _) (Some_inj e)). apply (ap (@Some _ _)).
    pose (e_sect (IsEquiv := e_isequiv (e := total_equiv a)) _ b). 
    refine (e1 ^ @ e0).
Defined.
Next Obligation.
    rename a0 into c. unfold kleisliComp. 
    unfold to_dep, to_rich in *.
    unfold to_simpl, clift, compose.
    assert (f := pc_retr (IsConnectionK := pc_isconn (c := partial_equiv a)) _ c).
    unfold kleisliComp in f.
    revert f. apply sub_eq_implies_complex. intros s e. 
    pose (e_retr (IsEquiv := e_isequiv (e := total_equiv a)) _ s).
    unfold compose, id in e0. simpl in *.
    simpl.
    rewrite e0. exact e.
Defined.
(* Next Obligation. *)
(*   apply is_hprop.  *)
(* Defined. *)

(** ** Casts for non-dependent functions *)

(* =to_dep_dom= *)
Definition to_dep_dom {A D:HSet} {B: A -> HSet} {C: HSet}
    `{B ≲K□ C}(f: C ⇀ D) (a:A) : B a ⇀ D := f °° to_simpl. 
(* =end= *)

Definition to_dep_dom2 {A:HSet} {B: A -> HSet} {C} {D E}
           `{B ≲K□ C}
           (f: C -> D ⇀ E) : forall a, B a -> D ⇀ E :=
  fun a b x=> 
    c <- to_simpl b;
    f c x.

(** ** Casts from dependent to simple *)

(* =to_simpl_dom= *)
Definition to_simpl_dom {A D:HSet} {B: A -> HSet} {C : HSet}
    `{DepCoercion A B C}(f : forall a:A, B a ⇀ D) : C ⇀ D :=
  fun c =>
    a  <- c_to_a c;
    b  <- to_dep a c ;
    f a b.
(* =end= *)

Program Definition TotalEquiv (A:HSet) (B: A -> HSet) (C:HSet) (P: A -> C -> HProp)
   {DREquiv_prop : forall a c, IsHProp (P a c)}
   {HSet_C : IsHSet C}
   (b_to_c : forall a, B a -> {c : C & P a c})
   (c_to_b : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b : forall a, (c_to_b a) ° (b_to_c a) == id ) 
   (prop_c_to_c : forall a, (b_to_c a) ° (c_to_b a) == id) a:
  Equiv (B a) {c : C & P a c} :=
    {| e_fun := b_to_c a ;
       e_isequiv :=
         {| e_inv := c_to_b a ;
            e_sect := prop_b_to_b a;
            e_retr := prop_c_to_c a;|} |}.
Next Obligation.
  apply (is_hprop (IsHProp := is_hset (IsHSet := trunc_sigma _ _) _ _)).
Defined. 

(* =IsDepEquiv= *)
Definition IsDepCoercion (A:HSet) (B: A -> HSet) (C:HSet) P `{forall a c, Decidable (P a c)}  
  (b_to_c : forall a, B a -> {c : C & P a c}) (c_to_b : forall a, {c : C & P a c} -> B a) (c_to_a : C ⇀ A) : 
  (forall a, (c_to_b a) ° (b_to_c a) == id ) -> (forall a, (b_to_c a) ° (c_to_b a) == id) -> 
  (forall a (b:B a), c_to_a (b_to_c a b).1 = Some a) -> B ≲K□ C
(* =end= *)
  :=
    fun prop_b_to_b prop_c_to_c prop_c_to_a =>
      Build_DepCoercion A B C P
                        (TotalEquiv A B C P b_to_c c_to_b prop_b_to_b prop_c_to_c)
                        (fun a => Decidable_ConnectionK C (P a))
                        c_to_a prop_c_to_a.

(** Given a relation [R : TError A -> A -> Type], one can automatically
construct a partial type equivalence between [B: A → Type] and [C:
Type] as long as we can recompute the index from an inhabitant of
[C]. This is the role of the function [c_to_a_rel]. *)


Definition Coercion_rel {A:HSet} {B: A -> HSet} {C:HSet} (R : TError A info_str -> A -> HProp)
   (c_to_a_rel : C ⇀ A)
   (P := fun a c => R (c_to_a_rel c) a)
   (b_to_c_rel : forall a, B a -> {c : C & P a c})
   (c_to_b_rel : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b_rel : forall a, (c_to_b_rel a) ° (b_to_c_rel a) == id) 
   (prop_c_to_c_rel : forall a, (b_to_c_rel a) ° (c_to_b_rel a) == id)
   {DepEquiv_check_rel : forall a a', Decidable (R a a')}
   {HSet_C : IsHSet C}
   (prop_c_to_a_R : forall a (b:B a), c_to_a_rel (b_to_c_rel _ b).1 = Some a) :
  B ≲K□ C
  :=
  IsDepCoercion A B C P b_to_c_rel c_to_b_rel c_to_a_rel prop_b_to_b_rel prop_c_to_c_rel
            (fun _ _ => prop_c_to_a_R _ _).

(** A particular case of the above scenario consists in taking
equality (which is likely to decidable, so as to be in hprop) on
[A]. *)

Instance IsHProp_compose A B (f : A -> B) P (H : forall b, IsHProp (P b)) a :
  IsHProp (P (f a)) := H (f a).

Definition DepCoercion_eq {A : HSet} (B: A -> HSet) (C:HSet)
   {DecidablePaths_A : DecidablePaths A}
   (c_to_a_eq : C ⇀ A)
   (P := fun a c => hprop (c_to_a_eq c = Some a))
   (b_to_c_eq : forall a, B a -> {c : C & P a c})
   (c_to_b_eq : forall a, {c : C & P a c} -> B a)
   {prop_b_to_b_eq : forall a, (c_to_b_eq a) ° (b_to_c_eq a) == id}
   {prop_c_to_c_eq : forall a, (b_to_c_eq a) ° (c_to_b_eq a) == id}
   {prop_c_to_a_eq : forall a (b:B a), c_to_a_eq (b_to_c_eq _ b).1 = Some a} : 
  B ≲K□ C :=  
  Coercion_rel (fun c a => hprop (c = Some a))
              c_to_a_eq b_to_c_eq c_to_b_eq prop_b_to_b_eq prop_c_to_c_eq
 (fun a b => prop_c_to_a_eq a b) (DepEquiv_check_rel := fun a c => DecidablePaths_DecidableProp (DecidablePaths_TError _ _) a (Some c)). 
