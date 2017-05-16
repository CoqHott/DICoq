Require Export Unicode.Utf8_core.
Require Import Bool List Le String Showable HoTT.

Set Implicit Arguments.
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

(* =Decidable= *)
Class Decidable (A : HProp) := dec : A + (not A).
(* =end= *)

Arguments dec A {_}.


(**

A [DecidableProp] [A] is, essentially, isomorphic to [Bool]: it is
either [true] or [false].

 *)

(* Class DecidableProp (A : Type) := { *)
(*     dec_p :> Decidable A; *)
(*     is_hprop_p :> IsHProp A }. *)

(* Instance DecidableProp_Decidable_HProp (A : Type) {Hdec: Decidable A} *)
(*          {Hprop:IsHProp A} : DecidableProp A := *)
(*   {|dec_p := Hdec ; is_hprop_p := Hprop |}. *)


(** 

The canonical example of a [DecidableProp] is the decidable equality
for a type [A], as per Hedberg theorem. We package it in a dedicated
class.

*)

Class DecidablePaths (A : HSet) := { 
  dec_paths : forall a b : A, Decidable (hprop (a = b))
}.

(**

Hedberg theorem is a standard theorem of HoTT: it states that if a
type [A] has decidable equality, then it is a hSet, i.e. its equality
is proof-irrelevant. See the proof at [https://github.com/HoTT] in
[HoTT/theories/Basics/Decidable.v] *)

Instance Hedberg A (dec_paths_ : forall a b : A, ((a = b) + (not (a = b)))%type)
  : IsHSet A.
Proof. 
intros a b.
assert (lemma: forall p: a = b,  
    match dec_paths_ a a, dec_paths_ a b with
    | inl r, inl s => p = r^ @ s
    | _, _ => False
    end).
{
  destruct p.
  destruct (dec_paths_ a a) as [pr | f].
  apply inverse_left_inverse.
  specialize (f eq_refl).
  inversion f.
}

intros p q.
assert (p_given_by_dec := lemma p).
assert (q_given_by_dec := lemma q).
destruct (dec_paths_ a a); try contradiction.
destruct (dec_paths_ a b); try contradiction.
apply (p_given_by_dec @ q_given_by_dec ^).
Defined.

Instance DecidablePaths_DecidableProp A
   (DecidablePaths_A : DecidablePaths A)
  : forall (a b : A), Decidable (hprop (a = b)).
intros. exact (@dec_paths _ DecidablePaths_A _ _). 
Defined.

(** ** Checkability *)

(**

  A [Checkable] type is a type that contains a decidable subset
  [checkP]. Moreover, it is [CheckableProp] if its elements are
  proof-irrelevant.

 *)

(* =Checkable= *)
Class Checkable (A : HProp) :=
  {
    check : HProp;
    check_dec : Decidable check ;
    convert : check -> A
  }.
(* =end= *)

(** A decidable type is checkable (over all its elements). *)

Instance decidable_is_checkable A {H:Decidable A} : Checkable A
  := {| check := A ; check_dec := H ; convert := id |}.

(** We can project the [Decidable] property out of [Checkable]: *)

Instance checkable_decidable A {H:Checkable A} : Decidable (@check _ H)
  := check_dec.


(** ** A few instances *)


(** ***  Reflecting a boolean as a decidable property *)

Instance Decidable_bool (t : bool) : Decidable (hprop (Is_true t)) :=
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

Definition Decidable_eq_bool : forall (x y : bool), (x = y) + not (x = y).
intros. destruct x, y; try (left ;reflexivity); 
        try (right; intro H; inversion H).
Defined.

Instance IsHSet_bool : IsHSet bool := Hedberg Decidable_eq_bool.

Instance DecidablePaths_bool : DecidablePaths (hset bool) := 
  { dec_paths := Decidable_eq_bool }.

(** ***  Instances for nat *)

Definition Decidable_eq_nat : forall (x y : nat),  (x = y) + not (x = y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.

Instance IsHSet_nat : IsHSet nat := Hedberg Decidable_eq_nat.

Instance DecidablePaths_nat : DecidablePaths (hset nat) := 
  { dec_paths := Decidable_eq_nat }.

(** *** Instances for list *)

Definition Decidable_eq_list : forall (A:HSet) (HA: DecidablePaths A) 
  (x y: list A),  (x = y) + not (x = y).
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

Instance IsHSet_list (A:HSet) HA : IsHSet (list A) := Hedberg (@Decidable_eq_list A HA).

Instance DecidablePaths_list : 
  forall A (HA: DecidablePaths A), DecidablePaths (hset (list A)) := 
    { dec_paths := Decidable_eq_list HA }.

(** *** Instance for less than *)

Definition Decidable_le_nat : forall (x y : nat), (x <= y) + not (x <= y).
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

Definition Decidable_eq_option : forall A (HA: DecidablePaths A) 
  (x y: option A), (x = y) + not (x = y).
intros. destruct x as [a|]; destruct y as [a0 |].
- case (dec_paths a a0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. reflexivity.
Defined.

Instance IsHSet_option (A:HSet) HA : IsHSet (option A) := Hedberg (@Decidable_eq_option A HA).

Instance DecidablePaths_option :
  forall A (HA: DecidablePaths A), DecidablePaths (hset (option A)) := 
    { dec_paths := Decidable_eq_option HA }.

(** *** Instances for logical connectives *)

Instance Decidable_and P Q (HP : Decidable P) 
 (HQ : Decidable Q) : Decidable (hprop (P * Q)).
destruct HP as [p | n].
- destruct HQ as [q| n]. 
  + exact (inl (p, q)).
  + apply inr. intro H. exact (n (snd H)).
- apply inr. intro H. exact (n (fst H)).
Defined.

(* Instance Decidable_or P Q (HP : Decidable P) *)
(*         (HQ : Decidable Q) : Decidable (hprop (P + Q) _). *)
(* destruct HP. *)
(* - exact (inl (inl p)). *)
(* - destruct HQ.  *)
(*   + exact (inl (inr q)). *)
(*   + apply inr. intro H. case H; auto. *)
(* Defined. *)


Instance Decidable_not P (HP : Decidable P): 
  Decidable (hprop (not P)).
case HP; intro H.
- exact (inr (fun X => X H)).
- exact (inl H).
Defined.

Instance Decidable_implies P Q (HP : Decidable P) 
  (HQ : Decidable Q) : Decidable (hprop (P -> Q)).
destruct HQ as [q | n].
- exact (inl (fun _ => q)).
- destruct HP as [p | n0]. 
  + apply inr. intro H. exact (n (H p)).
  + apply inl. intro p. destruct (n0 p).
Defined.


Instance Decidable_True : Decidable (hprop True) := inl I.

Instance Decidable_False : Decidable (hprop False).
right. destruct 1.
Defined. 

Instance Hprop_unit : IsHProp unit.
Proof.
  intros x y. destruct x, y; reflexivity.
Defined. 

Instance DecidablePaths_unit : DecidablePaths (hset unit).
econstructor. intros x y. destruct x, y. exact (inl eq_refl).
Defined.

(** *** Decidability of proven properties *)

Instance Decidable_proven (P : HProp) (ev :  P):  Decidable P :=
  inl ev.

(*
Instance DecidablePaths_prod A B `{DecidablePaths A} `{DecidablePaths B}:
  DecidablePaths (hset (A*B) _).
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


*)