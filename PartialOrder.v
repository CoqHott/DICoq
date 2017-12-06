Set Universe Polymorphism.
Require Import HoTT. 

(** * Pointed partial order *)

(**

  A pointed partial order is a type [A] equipped with a partial order [≼]
  (reflexive, transitive relation) and a least element [bot] for that
  relation.

*)

Reserved Notation "x ≼ y" (at level 50).

(* =PartialOrder_pp= *)
Class IsPartialOrder_pp (A: Type) := { 
    rel: A -> A -> HProp where "x ≼ y" := (rel x y);
    bot: A;
    rel_refl: forall x, x ≼ x;
    rel_trans: forall x y z, x ≼ y -> y ≼ z -> x ≼ z;
    rel_antisym: forall x y, x ≼ y -> y ≼ x -> x = y;
    bot_is_least: forall x, bot ≼ x;
}.
(* =end= *)

Arguments rel_trans {_ _ _ _ _} _ _.

Notation "x ≼ y" := (rel x y).

(* =partial_order_forall= *)
Instance IsPartialOrder_pp_fun (A: Type)(B: A -> Type) 
    `{forall a, IsPartialOrder_pp (B a)}: IsPartialOrder_pp (forall a, B a) :=
  {| rel := fun f g => hprop (forall a, f a ≼ g a);
     bot := fun a => bot |}.
(* =end= *)
Proof.
  - simpl; intros. apply rel_refl.
  - simpl; intros f g h H1 H2 a. eapply rel_trans; auto.
  - simpl; intros f g H1 H2. apply funext. intro x. apply rel_antisym; auto. 
  - simpl; intros f a. apply bot_is_least.
Defined.

(** A monotone function between two partial orders respects the partial order
and transports bottom to bottom. *)

(* =monotone_fun= *)
Record monotone_function A B `{IsPartialOrder_pp A} `{IsPartialOrder_pp B} :=
 Build_Mon { 
     f_ord:> A -> B ;
    mon: forall x y, x ≼ y -> f_ord x ≼ f_ord y;
    p_mon: f_ord bot ≼ bot
  }.
Notation "A --> B" := (monotone_function A B)
(* =end= *)
                        (at level 10).

Arguments f_ord {_ _ _ _} _ _. 
Arguments mon {_ _ _ _} _ {_ _} _. 
Arguments Build_Mon {_ _ _ _} _ _ _.
