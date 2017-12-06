Require Import HoTT.

Variable A : Type.

(* =in_masked_list= *)
Inductive In: A -> list A -> Type :=
| here: forall a xs, In a (cons a xs)
| there: forall a b xs, In a xs -> In a (cons b xs).

Inductive mlist: list A -> Type :=
| nil: forall l, mlist l
| cons: forall x l, not (In x l) -> mlist l -> mlist l.
(* =end= *)