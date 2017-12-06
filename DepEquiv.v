Require Export Unicode.Utf8_core.
Require Import String List. 
Require Export Showable PartialOrder TErrorMonad Connection HoTT Decidable DepEquivAnti.

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
Class DepConnection (A: HSet) (B: A -> HSet) (C: HSet) := {
    P: A -> C -> HProp;
    total_equiv:> forall a, B a ≃ {c: C & P a c}; 
    partial_equiv:> forall a, {c: C & P a c} ≲K C;
    c_to_a: C ⇀ A;
    prop_c_to_a: forall a (b: B a), c_to_a °° ((partial_equiv a).(pc_fun))
                                  ((total_equiv a).(e_fun) b) = Some a;
}.
Notation "B ≲K□ C" := (DepConnection _ B C)
(* =end= *)
                      (at level 50).


Hint Extern 1 (IsEquiv ?f) => apply (e_isequiv (e := total_equiv _)) :
             typeclass_instances.

Hint Extern 1 (IsConnectionK ?f) => apply (pc_isconn (c := partial_equiv _)) :
                                      typeclass_instances.

 
(* Connection between coercion and anticoercion *)


Instance DepConnection_DepAnticonnection (A: HSet) (B: A -> HSet) (C: HSet)
  (H : B ≲K□ C) : B ≈K□ C.
Proof. 
  unshelve econstructor.
  - exact P.
  - exact total_equiv.
  - intro a. apply Connection_Anticonnection. exact (partial_equiv a). 
  - exact c_to_a. 
  - exact prop_c_to_a.
Defined. 



Instance DepAnticonnection_DepConnection (A: HSet) (B: A -> HSet) (C: HSet)
  (H : B ≈K□ C) (H' : forall a, creturn ≼ (apc_inv (apc_fun (a_partial_equiv a))) °° (apc_fun (a_partial_equiv a))) : B ≲K□ C.
Proof. 
  unshelve econstructor.
  - exact a_P.
  - exact a_total_equiv.
  - intro a. unshelve eapply Anticonnection_Connection. exact (a_partial_equiv a).
    exact (H' a). 
  - exact a_c_to_a. 
  - exact a_prop_c_to_a.
Defined. 

Program
(* =DepEquiv_PartialEquivK= *)
Definition DepConnection_ConnectionK  (A: HSet) (B: A -> HSet)
         (C: HSet) `{B ≲K□ C} (a: A): B a ≲K C :=
  {|  pc_fun := to_simpl;
      pc_isconn := {| pc_inv := to_dep a|} |}.
(* =end= *)
Next Obligation.
  - rename a0 into b. change (creturn b ≼ (to_dep a) °° to_simpl b). unfold kleisliComp, compose. 
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
    unfold compose in e0. simpl in *.
    simpl.
    rewrite e0. exact e.
Defined.

(** ** Casts for non-dependent functions *)

Definition 
(* =IsDepEquiv= *)
DepConnection_hset (A: HSet) (B: A -> HSet) (C: HSet) P 
  `{forall a c, Decidable (P a c)}  
  (b_to_c: forall a, B a -> {c: C & P a c}) (c_to_b: forall a, {c: C & P a c} -> B a) (c_to_a: C ⇀ A): 
  (forall a, (c_to_b a) ° (b_to_c a) == id ) -> (forall a, (b_to_c a) ° (c_to_b a) == id) -> 
  (forall a (b: B a), c_to_a (b_to_c a b).1 = Some a) -> B ≲K□ C.
(* =end= *)
Proof.
  intros prop_b_to_b prop_c_to_c prop_c_to_a.
  unshelve  eapply DepAnticonnection_DepConnection.
  eapply IsDepAnticonnection; eauto. intros;  apply decidable_is_checkable, H.
  intros a c.
  exact (@pc_sect _ _ _ (@pc_isconn _ _ (Decidable_ConnectionK C (P a))) c).
Defined.

(** Given a relation [R : TError A -> A -> Type], one can automatically
construct a partial type equivalence between [B: A → Type] and [C:
Type] as long as we can recompute the index from an inhabitant of
[C]. This is the role of the function [c_to_a_rel]. *)


Definition DepConnection_rel {A:HSet} {B: A -> HSet} {C:HSet} (R : TError A info_str -> A -> HProp)
   (c_to_a_rel : C ⇀ A)
   (P := fun a c => R (c_to_a_rel c) a)
   (b_to_c_rel : forall a, B a -> {c : C & P a c})
   (c_to_b_rel : forall a, {c : C & P a c} -> B a)
   (prop_b_to_b_rel : forall a, (c_to_b_rel a) ° (b_to_c_rel a) == id) 
   (prop_c_to_c_rel : forall a, (b_to_c_rel a) ° (c_to_b_rel a) == id)
   {DepEquiv_check_rel : forall a a', Decidable (R a a')}
   {HSet_C : IsHSet C}
   (prop_c_to_a_R : forall a (b:B a), c_to_a_rel (b_to_c_rel _ b).1 = Some a) :
  B ≲K□ C.
Proof.
  unshelve  eapply DepAnticonnection_DepConnection.
  eapply Anticonnection_rel; eauto. intros;  apply decidable_is_checkable, DepEquiv_check_rel. 
  intros a c. 
  exact (@pc_sect _ _ _ (@pc_isconn _ _ (Decidable_ConnectionK C (P a))) c).
Defined. 

(** A particular case of the above scenario consists in taking
equality (which is likely to decidable, so as to be in hprop) on
[A]. *)


Definition DepConnection_eq {A : HSet} (B: A -> HSet) (C:HSet)
   {DecidablePaths_A : DecidablePaths A}
   (c_to_a_eq : C ⇀ A)
   (P := fun a c => hprop (c_to_a_eq c = Some a))
   (b_to_c_eq : forall a, B a -> {c : C & P a c})
   (c_to_b_eq : forall a, {c : C & P a c} -> B a)
   {prop_b_to_b_eq : forall a, (c_to_b_eq a) ° (b_to_c_eq a) == id}
   {prop_c_to_c_eq : forall a, (b_to_c_eq a) ° (c_to_b_eq a) == id}
   {prop_c_to_a_eq : forall a (b:B a), c_to_a_eq (b_to_c_eq _ b).1 = Some a} : 
  B ≲K□ C :=  
  DepConnection_rel (fun c a => hprop (c = Some a))
              c_to_a_eq b_to_c_eq c_to_b_eq prop_b_to_b_eq prop_c_to_c_eq
 (fun a b => prop_c_to_a_eq a b) (DepEquiv_check_rel := fun a c => DecidablePaths_DecidableProp (DecidablePaths_TError _ _) a (Some c)). 


