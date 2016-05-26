Require Import CastMonad Showable Decidable HoTT PreOrder. 

Set Universe Polymorphism.

(** * Equivalences (first-order) *)

(** ** [Functor] class *)

Definition compose {A B C} : (A -> B) -> (B -> C) -> A -> C := fun f g x => g (f x).

Notation "g ° f" := (compose f g) (at level 1).

Class Functor A B (relA : A -> A -> Type) (relB : B -> B -> Type) (f:A -> B) := 
  { ap :forall x y, relA x y -> relB (f x) (f y)}.

Arguments ap {_ _ _ _} _ {_ _ _} _.

Instance FunctorOnEq A B (f : A -> B) : Functor A B eq eq f :=
  {| ap := fun x y e => HoTT.ap f e |}.


(** ** Type equivalence *)

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv : B -> A ;
  e_sect : e_inv ° f == id;
  e_retr : f ° e_inv == id;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x)
}.

(** A class that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  e_fun : A -> B ;
  e_isequiv : IsEquiv e_fun
}.

Notation "A ≃ B" := (Equiv A B) (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_isequiv {_ _ _}.

(** ** Partial Equivalences *)

Instance FunctorOnPreorder A B `{PreOrder_p A} `{PreOrder_p B} (f : A --> B) :
  Functor A B _ _ f :=
  {| ap := fun x y e => f.(mon) e |}.

Hint Extern 1 (Functor ?X ?Y _ _ ?f) => apply FunctorOnPreorder : typeclass_instances. 

Class IsPartialEquiv {X Y} `{PreOrder_p X} `{PreOrder_p Y} (f:X --> Y)
  := {
      pe_inv :  Y --> X;
      pe_sect : pe_inv ° f ≼ id ;
      pe_retr : f ° pe_inv ≼ id;
      pe_adj : ∀ x, pe_retr (f x) = ap f (pe_sect x);
    }.

Class CanonicalPartialEquiv X Y `{PreOrder_p X} `{PreOrder_p Y} := {
  pe_fun : X --> Y ;
  pe_isequiv : IsPartialEquiv pe_fun
}.

Notation "A ≃? B" := (CanonicalPartialEquiv A B) (at level 20).

(** ** Partial Kleisli Equivalences *)

(**

A monotone function [f: A → B] is a partial equivalence [PartialEquiv] if some
of the [b: B] maps back to the same [a: A] they come from. Think of
[A] as being a refinement of [B] and [f] as dropping the refinement:
not all [B]'s are valid [A]'s but the one which are can easily be
mapped back to [A].

 *)

Definition compV {X Y Z} {f f':X ⇀ Y} {g g' : Y ⇀ Z} : f ≼ f' -> g ≼ g' ->
                                                       g °° f ≼ (g' °° f').  
 Proof. intros e e' x. unfold kleisli_comp. generalize dependent (e x). clear e. 
       cbn. destruct (f x); simpl; eauto. intro e. 
       generalize dependent (e' y). clear e'.
       cbn. destruct (g y); simpl; eauto. intro e'. 
       apply (transport (fun X => _ = b <- X ; _) e). auto. 
Defined.

Notation "f °V g" := (compV f g) (at level 20).

Definition α {X Y Z T} (f:X ⇀ Y) (g:Y ⇀ Z) (h:Z ⇀ T):
    (h °° (g °° f)) ≼ ((h °° g) °° f).
Proof.
  intro x. 
  unfold kleisli_comp.
  destruct (f x); simpl; eauto.
  apply (rel_refl (PreOrder_p := PreOrderCast _)). 
Defined.

Definition idR {X Y} (f:X ⇀ Y):
  (creturn °° f) ≼ f.
Proof.
  intro x. unfold kleisli_comp. destruct (f x); reflexivity.
Defined.

Definition idL {X Y} (f:X ⇀ Y):
  (f °° creturn) ≼ f.
Proof. apply rel_refl. Defined.

Arguments rel_trans {_ _ _ _ _} _ _.

Notation "f °H g" := (rel_trans f g) (at level 60). 

Notation "'idK' f" := (rel_refl f) (at level 60). 

Class IsPartialEquivK {X Y} (f:X ⇀ Y)
  := {
      pek_inv :  Y ⇀ X;
      pek_sect : pek_inv °° f ≼ creturn ;
      pek_retr : f °° pek_inv ≼ creturn;
      pek_adj : forall x,
          ((pek_sect °V (idK f)) °H idL f) x =
          (α _ _ _ °H ((idK f) °V pek_retr) °H idR f) x
    }.

Record PartialEquivK X Y := {
  pek_fun : X ⇀ Y ;
  pek_isequiv : IsPartialEquivK pek_fun
}.

Notation "A ≃?K B" := (PartialEquivK A B) (at level 20).


Arguments pek_fun {_ _} _ _.
Arguments pek_isequiv {_ _ _}.

(**
  Sanity Check: lifting an equivalance yields 
  a partial equivalence in the Kleisli category
*)

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @ p = p
  :=
  match p with eq_refl => eq_refl end.

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ eq_refl = p
  :=
  match p with eq_refl => eq_refl end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ° f) p = ap g (ap f p).
Proof. destruct p. reflexivity.
Defined.

Definition transport_bind A (x y : A) (e:x=y)  B (f : A -> B):
  transport (λ X : Cast A, Some (f x) = b <- X; clift f b)
            (ap creturn e) eq_refl
            = ap creturn (ap f e).
              destruct e. reflexivity.
Defined.

Definition EquivToPartialEquivK A B (f :A -> B) (H :IsEquiv f) : IsPartialEquivK (clift f).
Proof.
  simple refine (Build_IsPartialEquivK _ _ _ (clift e_inv) _ _ _).
  - intro x. exact (HoTT.ap _ (e_sect x)). 
  - intro x. exact (HoTT.ap _ (e_retr x)). 
  - intro x. unfold compV. cbn. 
    pose (e_adj x). rewrite e. clear e. repeat rewrite concat_p1.
    etransitivity. apply transport_bind.
    set (ap (creturn (info := Cast_info)) (ap f (e_sect x))).
    change ( y =
             match
               y in (_ = a)
               return (Some (f (e_inv (f x))) = a)
             with
             | eq_refl => eq_refl
             end). destruct y. reflexivity.
Defined.
    
Notation π1 := (@projT1 _ _). 

(**

we have a subset equivalence between [B] and [{C,P}]
if the type family [B] is isomorphic with a (computationally-relevant)
type [C] and a (computationally-irrelevant) relation [P], ie.

<<
     [B a ≅ { c : C & P a c }]
>>

Remarks: 
 - [C] is non-dependent in [a : A], by definition.

 - Usually, [A] plays the role of the indices, [B] is an inductive
   family indexed over [A]. [C] are the "raw", computational terms
   while [P] is a validity predicate.

*)


Definition to_subset {C P} `{Show C} `{forall c, CheckableProp (P c)}
           : C ⇀ ({c:C & P c}) := fun c => 
   match dec (@checkP _ check) with 
  | inl p => Some (c; convert p)
  | inr _ => Fail _ (Cast_info_wrap (show c))
  end.

Instance HSet_HProp X `{IsHSet X} : forall (a b : X), IsHProp (a = b) :=
  fun a b => is_hprop (IsHProp := isHSet a b).

Program Definition Checkable_PartialEquivK C P `{Show C}
         `{forall c, CheckableProp (P c)} `{IsHSet C}:
  PartialEquivK {c:C & P c} C :=
  {| pek_fun :=  (clift π1 : {c:C & P c} ⇀ C);
     pek_isequiv := {| pek_inv := to_subset |}|}.
Next Obligation.
  rename a into c. unfold kleisli_comp. 
  unfold to_subset in *. simpl. 
  destruct (dec checkP); simpl;
  [ 
  | eauto ].
  simpl. unfold creturn. apply HoTT.ap. refine (path_sigma_uncurried _ _ _ _).
  exists eq_refl. apply is_hprop.
Defined.
Next Obligation.
  rename a into c. unfold kleisli_comp. 
  unfold to_subset in *.
  destruct (dec checkP); simpl;
  [ 
  | eauto ]. 
  reflexivity.
Defined.
Next Obligation.
  apply is_hprop.
    (* cbn. unfold kleisli_comp. cbn. unfold apK, natK, assocK, idR. *)
    (* destruct x. cbn. simpl. apply is_hprop. destruct (to_subset x).  *)
    (* set (to_subset (π1 x)). *)
    (* match goal with | |- ?e = ?e' => set e; set e' end. *)
    (* destruct x. cbn in *. revert y; revert y0. destruct c.   *)
Defined.


(** ** Injective functions (model constructors) *)


Class IsInjective {A B : Type} (f : A -> B) :=
   {
      i_inv : B ⇀ A;
      i_sect : i_inv ° f == creturn ;
      i_retr : clift f °° i_inv ≼ creturn
    }.

Notation "f ^?-1" := (@i_inv _ _ f _) (at level 3, format "f '^?-1'").

Instance Injective_comp {A B C} 
         (f : A -> B) (g : B -> C)
         `{IsInjective A B f} `{IsInjective B C g}:
  IsInjective (g ° f)
  := {| i_inv := (f^?-1 °° g^?-1) |}.
Proof.
  - unfold compose, kleisli_comp. intro a. 
    pose (i_sect (f:=g) (f a)). unfold compose in e.
    rewrite e. 
    exact (i_sect (f:=f) a).
  - intros c. cbn.
    pose (i_retr (f:=g) c).
    unfold compose, kleisli_comp in *.
    cbn in *. 
    generalize dependent r. destruct (g^?-1 c); cbn in *; [| eauto].
    pose (i_retr (f:=f) b).
    unfold compose, kleisli_comp in *.
    generalize dependent r. destruct (f^?-1 b); cbn in *; [| eauto]. 
    unfold clift. intros.
    apply HoTT.ap. 
    inversion r0. inversion r. auto.
Defined.

(** *** Instances of IsInjective *)

(** The identity is an injection : *)  

Definition IsInjective_id {A:Type}: IsInjective (@id A).
Proof.
  simple refine (Build_IsInjective _ _ _ (@Some A _) _ _).
  intro a. reflexivity.
  intros a. reflexivity.
Defined.
  
(** The predecessor over natural numbers is a partial equivalence: *)

Definition S_inv (n: nat) :=
  match n with
    | O => Fail _ (Cast_info_wrap "invalid index")
    | S n' => Some n'
  end.
  
Instance IsInjective_S: IsInjective S :=
  {| i_inv := S_inv : nat -> Cast nat |}.
Proof.
  intro a. reflexivity.
  intros n. destruct n; cbn in *; eauto. 
Defined.