Require Export Unicode.Utf8_core.
Require Import String List. 
Require Export Showable PreOrder CastMonad Equiv HoTT Decidable.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

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


Class DepEquiv A (B: A -> Type) (C:Type) {HC : IsHSet C}
  :=
    {
      P : A -> C -> Type;
      total_equiv :> forall a, B a ≃ {c:C & P a c}; 
      partial_equiv :> forall a, {c:C & P a c} ≃?K C;
      c_to_a : C ⇀ A;
      prop_c_to_a : forall a (b:B a), (c_to_a °° ((partial_equiv a).(pek_fun )))
                                   ((total_equiv a).(e_fun) b) = Some a;
      showC :> Show C;
    }.

Notation "B ≈ C" := (DepEquiv _ B C) (at level 50).

Hint Extern 1 (IsEquiv ?f) => apply (e_isequiv (e := total_equiv _)) :
             typeclass_instances.

Hint Extern 1 (IsPartialEquivK ?f) => apply (pek_isequiv (p := partial_equiv _)) :
             typeclass_instances.

Definition c_to_b {A} {B: A -> Type} {C} {HC : IsHSet C}
           `{B ≈ C} {a:A}:
  {c:C & P a c} -> (B a) := e_inv.

Definition b_to_c {A} {B: A -> Type} {C} {HC : IsHSet C}
           `{B ≈ C} {a:A}:
  B a -> {c:C & P a c} := (total_equiv a).(e_fun). 

Definition to_rich {A} {B: A -> Type} {C} {HC : IsHSet C}
           `{B ≈ C} {a:A}:
  C ⇀ {c: C & P a c} :=
  pek_inv.

Program Definition to_dep {A} {B: A -> Type} {C} {HC : IsHSet C}
           `{B ≈ C}
           (a:A) : C ⇀ (B a) := fun c =>
    c' <- pek_inv c; clift e_inv c'.
    
Definition to_simpl {A} {B: A -> Type} {C} {HC : IsHSet C}
           `{B ≈ C}
           {a:A} : B a ⇀ C := 
  (partial_equiv a).(pek_fun) ° ((total_equiv a).(e_fun)).

(** ** Properties *)

Definition sub_eq_implies {A B B'} (x:Cast A) {f : A ⇀ B} {y : Cast B}
           {g : A ⇀ B'} {y' : Cast B'}
  (e : forall a, f a ≼ y -> g a ≼ y') : (a <- x; f a) ≼ y -> (a <- x; g a) ≼ y'.
Proof.
  destruct x. apply e. exact (@id _). 
Defined.

Definition sub_eq_implies_simpl {A B} (x:Cast A) {y : Cast A}
           {g : A ⇀ B} {y' : Cast B}
  (e : forall a, creturn a ≼ y -> g a ≼ y') : x ≼ y -> (a <- x; g a) ≼ y'.
Proof.
  destruct x. apply e. intros H. exact H.
Defined.

Definition sub_eq_implies_complex  {A B B' C} (x:Cast A) {f : A ⇀ B}
           {y : Cast B} {g : A ⇀ B'} {y' : Cast C} {g' : B' ⇀ C}
           (e : forall a, f a ≼ y -> (b <- g a ; g' b) ≼ y') :
  (a <- x; f a) ≼ y ->  (b <- (a <- x; g a); g' b)  ≼ y'.
Proof.
  destruct x. apply e. intros X. simpl in *. exact X.
Defined.


Definition DepEquiv_PartialEquivK  (A : Type) (B : A → Type)
         C {HC : IsHSet C} `{B ≈ C} (a:A) : B a ≃?K C.
Proof. 
  simple refine ({| pek_fun := to_simpl;
                    pek_isequiv := {| pek_inv := to_dep a|} |}).
- intro b. unfold kleisli_comp, compose. 
  unfold to_dep, to_rich, to_simpl, compose in *. 
  assert (f := pek_sect (IsPartialEquivK := pek_isequiv (p := partial_equiv a)) (b_to_c b)).
  unfold kleisli_comp in f.
  revert f. unfold b_to_c, compose. 
  apply sub_eq_implies. intro c. 
  apply sub_eq_implies_simpl. intro x. 
  intro e. pose (ap e_inv (Some_inj e)). apply (ap (@Some _ _)).
  pose (e_sect (IsEquiv := e_isequiv (e := total_equiv a)) b). 
  refine (e0 @ e1).
- intro c. unfold kleisli_comp. 
  unfold to_dep, to_rich in *.
  unfold to_simpl, clift, compose.
  assert (f := pek_retr (IsPartialEquivK := pek_isequiv (p := partial_equiv a)) c).
  unfold kleisli_comp in f.
  revert f. apply sub_eq_implies_complex. intros s e. 
  pose (e_retr (IsEquiv := e_isequiv (e := total_equiv a)) s).
  unfold compose, id in e0. simpl in *.
  simpl.
  rewrite e0. exact e.
- intro b. apply is_hprop. 
Defined.

(** ** Casts for non-dependent functions *)

Definition to_dep_dom {A} {B: A -> Type} {C} {HC : IsHSet C} {X}
           `{B ≈ C}
           (f: C ⇀ X) (a:A) : B a ⇀ X :=
  f °° to_simpl. 

Definition to_dep_dom2 {A} {B: A -> Type} {C} {HC : IsHSet C} {X Y}
           `{B ≈ C}
           (f: C -> Y ⇀ X) : forall a, B a -> Y ⇀ X :=
  fun a b x=> 
    c <- to_simpl b;
    f c x.

(** ** Casts from dependent to simple *)

Definition to_simpl_dom {A} {B: A -> Type} {C X}
           `{DepEquiv A B C}
           (f : forall a:A, B a ⇀ X) : C ⇀ X :=
  fun c =>
    a  <- c_to_a c;
    b  <- to_dep a c ;
    f a b.

Program Definition TotalEquiv A (B: A -> Type) C (P: A -> C -> Type)
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
  apply (is_hprop (IsHProp := isHSet (IsHSet := trunc_sigma _ _) _ _)).
Defined. 

Definition IsDepEquiv A (B: A -> Type) C {HC : IsHSet C} (P: A -> C -> Type)
         
   {DepEquiv_check : forall a c, CheckableProp (P a c)}  
   (b_to_c : forall a, B a -> {c : C & P a c})
   (c_to_b : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b : forall a, (c_to_b a) ° (b_to_c a) == id ) 
   (prop_c_to_c : forall a, (b_to_c a) ° (c_to_b a) == id)
   (c_to_a : C ⇀ A)
   (prop_c_to_a : forall a (b:B a), c_to_a (b_to_c _ b).1 = Some a)
   {Show_C : Show C}
  : B ≈ C :=
  Build_DepEquiv A B C HC P
                (TotalEquiv A B C P b_to_c c_to_b prop_b_to_b prop_c_to_c)
                (fun a => Checkable_PartialEquivK C (P a))
                c_to_a prop_c_to_a Show_C.

(** Given a relation [R : Cast A -> A -> Type], one can automatically
construct a partial type equivalence between [B: A → Type] and [C:
Type] as long as we can recompute the index from an inhabitant of
[C]. This is the role of the function [c_to_a_rel]. *)


Definition DepEquiv_rel {A} {B: A -> Type} {C}{HC : IsHSet C} (R : Cast A -> A -> Type)
   (c_to_a_rel : C ⇀ A)
   (P := fun a c => R (c_to_a_rel c) a)
   (b_to_c_rel : forall a, B a -> {c : C & P a c})
   (c_to_b_rel : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b_rel : forall a, (c_to_b_rel a) ° (b_to_c_rel a) == id) 
   (prop_c_to_c_rel : forall a, (b_to_c_rel a) ° (c_to_b_rel a) == id)
   {DepEquiv_check_rel : forall a a', CheckableProp (R a a')}
   {HSet_C : IsHSet C}
   {DepShow : Show C}
   (prop_c_to_a_R : forall a (b:B a), c_to_a_rel (b_to_c_rel _ b).1 = Some a) :
  B ≈ C
  :=
  IsDepEquiv A B C P b_to_c_rel c_to_b_rel prop_b_to_b_rel prop_c_to_c_rel
            c_to_a_rel (fun _ _ => prop_c_to_a_R _ _).

(** A particular case of the above scenario consists in taking
(decidable) equality on [A]. *)

Definition DepEquiv_eq {A} {B: A -> Type} {C} {HC : IsHSet C}
   {DecidablePaths_A : DecidablePaths A}
   {DepShow : Show C}
   (c_to_a_eq : C ⇀ A)
   (P := fun a c => c_to_a_eq c = Some a)
   (b_to_c_eq : forall a, B a -> {c : C & P a c})
   (c_to_b_eq : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b_eq : forall a, (c_to_b_eq a) ° (b_to_c_eq a) == id)
   (prop_c_to_c_eq : forall a, (b_to_c_eq a) ° (c_to_b_eq a) == id)
   (prop_c_to_a_eq : forall a (b:B a), c_to_a_eq (b_to_c_eq _ b).1 = Some a) : 
  B ≈ C :=
  DepEquiv_rel (fun c a => c = Some a)
              c_to_a_eq b_to_c_eq c_to_b_eq prop_b_to_b_eq prop_c_to_c_eq
 (fun a b => prop_c_to_a_eq a b). 
