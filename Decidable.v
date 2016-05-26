Require Export Unicode.Utf8_core.
Require Import Bool List Le String Showable HoTT.

Set Universe Polymorphism.

(** * The Decidable Class *)

(** This code is mostly imported from
[https://github.com/HoTT/HoTT]. We are defining it here to be
independent of the Coq/HoTT library.

We can not use the Decidable class of Coq because its definition is in
[Prop] (using [\/]) instead of [Type] (using [+]). All the predicates
defined in this file are proof-relevant.
*)

(** ** Decidability *)


Class Decidable (A : Type) := dec : A + (not A).

Arguments dec A {_}.


(**

A [DecidableProp] [A] is, essentially, isomorphic to [Bool]: it is
either [true] or [false].

 *)

Class DecidableProp (A : Type) := {
    dec_p :> Decidable A;
    is_hprop_p :> IsHProp A }.

Instance DecidableProp_Decidable_HProp (A : Type) {Hdec: Decidable A}
         {Hprop:IsHProp A} : DecidableProp A :=
  {|dec_p := Hdec ; is_hprop_p := Hprop |}.


(** 

The canonical example of a [DecidableProp] is the decidable equality
for a type [A], as per Hedberg theorem. We package it in a dedicated
class.

*)

Class DecidablePaths (A : Type) := { 
  dec_paths : forall a b : A, Decidable (a = b) 
}.

(**

Hedberg theorem is a standard theorem of HoTT: it states that if a
type [A] has decidable equality, then it is a hSet, i.e. its equality
is proof-irrelevant. See the proof at [https://github.com/HoTT] in
[HoTT/theories/Basics/Decidable.v] *)

Instance Hedberg (A : Type) `{DecidablePaths A} : IsHSet A.
Proof. 
econstructor. intros.
assert (lemma: forall p: a = b,  
    match dec_paths a a, dec_paths a b with
    | inl r, inl s => p = r^ @ s
    | _, _ => False
    end).
{
  destruct p.
  destruct (dec_paths a a) as [pr | f].
  apply inverse_left_inverse.
  specialize (f eq_refl).
  inversion f.
}

intros p q.
assert (p_given_by_dec := lemma p).
assert (q_given_by_dec := lemma q).
destruct (dec_paths a a); try contradiction.
destruct (dec_paths a b); try contradiction.
apply (p_given_by_dec @ q_given_by_dec ^).
Defined.

Instance DecidablePaths_DecidableProp A
   (DecidablePaths_A : DecidablePaths A)
  : forall (a b : A), DecidableProp (a = b).
intros. econstructor. exact (@dec_paths _ DecidablePaths_A _ _). eauto with typeclass_instances. 
Defined.

(** ** Checkability *)

Class Checkable (A : Type) :=
  {
    checkP : Type;
    checkP_dec : Decidable checkP ;
    convert : checkP -> A
  }.

Class CheckableProp (A : Type) := {
    check :> Checkable A;
    is_hprop_c :> IsHProp A }.

Instance checkable_decidable (A : Type) {H:Checkable A} : Decidable (@checkP _ H)
  := checkP_dec.

Instance decidable_is_checkable (A : Type) {H:Decidable A} : Checkable A
  := {| checkP := A ; checkP_dec := H ; convert := id |}.

Instance decidablep_is_checkableprop (A : Type) {H:DecidableProp A} : CheckableProp A
  := {| is_hprop_c := _ |}.


(** ** A few instances *)

Set Implicit Arguments.


(** ***  Reflecting a boolean as a decidable property *)

Instance Decidable_bool (t : bool) : Decidable (Is_true t) :=
  match t with
    | true => inl tt
    | false => inr id
  end.

(* Connexion to a boolean version of decidable as in 
   native-coq/theories/Classes/DecidableClass.v 
*)

(*
Class Decidable_relate (P : Type) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.

(* Decidable_relate and Decidable are equivalent *)

Instance Dec_relate_Decidable P (HP: Decidable_relate P) : 
  Decidable P.
destruct HP as [witness spec]. destruct witness.
- left. exact (proj1 spec eq_refl).
- right. intro p. pose (proj2 spec p). inversion e.
Defined.

Definition Decidable_Dec_relate P (HP: Decidable P) :
  Decidable_relate P.
case HP; intro p.
- refine {| Decidable_witness := true |}.  split; auto.
- refine {| Decidable_witness := false |}. split; auto.
  intro e; inversion e.
Defined.
*)

(** ***  Instances for bool *)

Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y).
intros. destruct x, y; try (left ;reflexivity); 
        try (right; intro H; inversion H).
Defined.

Instance DecidablePaths_bool : DecidablePaths bool := 
  { dec_paths := Decidable_eq_bool }.

(** ***  Instances for nat *)

Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.

Instance DecidablePaths_nat : DecidablePaths nat := 
  { dec_paths := Decidable_eq_nat }.

(** *** Instances for list *)

Instance Decidable_eq_list : forall A (HA: DecidablePaths A) 
  (x y: list A), Decidable (eq x y).
intros A HA. induction x.
- destruct y.
  + left; reflexivity.
  + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (dec_paths a a0); intro H. 
    * case (IHx y); intro Hl.
      left. rewrite H. rewrite Hl. reflexivity.
      right. rewrite H. unfold not in *. 
      intro Hc. inversion Hc. exact (Hl H1).
    * right. unfold not in *. 
      intro Hc. inversion Hc. exact (H H1).
Defined.

(** *** Instance for decidable equality on list *)

Instance DecidablePaths_list : 
  forall A (HA: DecidablePaths A), DecidablePaths (list A) := 
    { dec_paths := Decidable_eq_list HA }.

(** *** Instance for less than *)

Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y).
induction x.
- destruct y.
 + left; reflexivity.
 + left. apply le_S, le_0_n. 
- induction y.
  + right. intro e. destruct (le_Sn_0 _ e).
  + case (IHx y). intro H. left. exact (le_n_S _ _ H).
    intro H; right. intro. apply H. exact (le_S_n _ _ H0). 
Defined.

(** *** Instances for option *)

Instance Decidable_eq_option : forall A (HA: DecidablePaths A) 
  (x y: option A), Decidable (eq x y).
intros. destruct x; destruct y.
- case (dec_paths a a0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. reflexivity.
Defined.

Instance DecidablePaths_option :
  forall A (HA: DecidablePaths A), DecidablePaths (option A) := 
    { dec_paths := Decidable_eq_option HA }.

(** *** Instances for logical connectives *)

Instance Decidable_and P Q (HP : Decidable P) 
 (HQ : Decidable Q) : Decidable (P * Q).
destruct HP.
- destruct HQ. 
  + exact (inl (p, q)).
  + apply inr. intro H. exact (n (snd H)).
- apply inr. intro H. exact (n (fst H)).
Defined.

Instance Decidable_or P Q (HP : Decidable P)
        (HQ : Decidable Q) : Decidable (P + Q).
destruct HP.
- exact (inl (inl p)).
- destruct HQ. 
  + exact (inl (inr q)).
  + apply inr. intro H. case H; auto.
Defined.


Instance Decidable_not P (HP : Decidable P) : 
  Decidable (not P).
case HP; intro H.
- exact (inr (fun X => X H)).
- exact (inl H).
Defined.

Instance Decidable_implies P Q (HP : Decidable P) 
  (HQ : Decidable Q) : Decidable (P -> Q).
destruct HQ.
- exact (inl (fun _ => q)).
- destruct HP. 
  + apply inr. intro H. exact (n (H p)).
  + apply inl. intro p. destruct (n0 p).
Defined.


Instance Decidable_True : Decidable True := inl I.

Instance Decidable_False : Decidable False.
right. destruct 1.
Defined. 

Instance DecidablePaths_unit : DecidablePaths unit.
econstructor. intros x y. destruct x, y. exact (inl eq_refl).
Defined.

(** *** Decidability of proven properties *)

Instance Decidable_proven (P : Type) (ev :  P):  Decidable P :=
  inl ev.

Instance DecidablePaths_prod A B `{DecidablePaths A} `{DecidablePaths B}:
  DecidablePaths (A*B).
econstructor. intros (a,b) (a',b').
destruct (dec (a = a')), (dec (b=b'));
  try solve [apply inr; intro H'; inversion H'; auto].
apply inl. subst. reflexivity. 
Defined.

Instance DecidablePaths_fun A B A'
         (H : forall a, DecidablePaths (B a)) (f : A' -> A)
  a' : DecidablePaths (B (f a')) .
Proof.
  auto with typeclass_instances.
Defined.


