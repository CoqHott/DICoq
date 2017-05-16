Set Universe Polymorphism.

Require Import String List.

(** * The [Show] class *)

(** The [Show] class converts values to strings. It is similar to the
 Haskell Show class *)

Class Show (A :Type) := { show : A -> string }.

Local Open Scope string_scope.

(** ** Default Instance: *)

(* Definition not_implemented := "not implemented". *)
(* Axiom show_not_implemented_for: forall (A: Type), string. *)
      
(* Instance show_default A : Show A | 1000 := {| show := fun _ => show_not_implemented_for A |}. *)

(** ** Instance for nat *)
Instance show_nat : Show nat | 0 :=
  {| show := fix _show_nat n :=
       match n with
         | O => "O"
         | S n0 => "S (" ++ _show_nat n0 ++ ")"
       end
  |}.

(** ** Instance for list *)
Fixpoint _show_list {A} `{Show A} (l: list A) :=
  match l with
    | nil => ""
    | a :: l => show a ++ "," ++ _show_list l
  end.

Instance inst_show_list {A} `{Show A} : Show (list A) :=
  {| show l := "(" ++ _show_list l ++ ")" |}.

(** ** Instance for vector *)
Require Vector.
Fixpoint _show_vector {A n} `{Show A} (v: Vector.t A n) :=
  match v with
    | Vector.nil _ => ""
    | Vector.cons _ x _ v' => show x ++ ";" ++ _show_vector v'
  end.

Instance inst_show_vector {A n} `{Show A} : Show (Vector.t A n) :=
  {| show v := "[" ++ _show_vector v ++ "]" |}.