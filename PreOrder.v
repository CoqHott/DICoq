Set Universe Polymorphism.

(** * Pointed preorder *)

Reserved Notation "x ≼ y" (at level 50).

Class PreOrder_p (A:Type) :=
  { rel : A -> A -> Prop where "x ≼ y" := (rel x y);
    bot : A;
    rel_refl : forall x, x ≼ x ;
    rel_trans : forall x y z, x ≼ y -> y ≼ z -> x ≼ z;
    bot_is_least : forall a, bot ≼ a 
  }.

Notation "x ≼ y" := (rel x y).

Instance PreOrder_forall A (B:A -> Type) `{forall a, PreOrder_p (B a)} :
  PreOrder_p (forall a, B a) :=
  {| rel := fun f g => forall a, f a ≼ g a;
     bot := fun a => bot |}.
Proof.
  - intros. apply rel_refl.
  - intros f g h H1 H2 a. eapply rel_trans; auto.
  - intros f a. apply bot_is_least.
Defined.

Record monotone_function X Y `{PreOrder_p X} `{PreOrder_p Y} :=
  Build_Mon
    { f_ord :> X -> Y ;
      mon :forall x y, x ≼ y -> f_ord x ≼ f_ord y;
      p_mon : f_ord bot ≼ bot
    }.

Arguments f_ord {_ _ _ _} _ _. 
Arguments mon {_ _ _ _} _ {_ _} _. 
Arguments Build_Mon {_ _ _ _} _ _ _. 

Notation "X --> Y" := (monotone_function X Y) (at level 10).
