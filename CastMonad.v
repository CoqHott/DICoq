Require Import Ascii String Decidable HoTT PreOrder.
Require Import ExtrOcamlString.

Set Universe Polymorphism.

Set Implicit Arguments.

(** * The [Cast] monad *)

(** ** Datatype *)

Inductive _Cast A info :=
  | Some : A -> _Cast A info
  | Fail : info -> _Cast A info.

Arguments Some {_ _} _.

(** We need to assume that the string message is irrelevant.
    We would not prositional truncation an axiom we were using 
    the simpler version with None *)

Definition Cast_info := Trunc (string * Type).

Definition Cast A := _Cast A Cast_info. 

Unset Implicit Arguments.

Notation "A ⇀ B" := (A -> Cast B) (at level 50). 

(** ** Transport maps *)

Definition transport_Cast (A : Type) (B : A -> Type) {info} a a' (e:a=a') x:
  transport (fun a => _Cast (B a) info) e (Some x) = Some (e # x).
    destruct e. reflexivity.
Defined.

Definition transport_Cast_Fail (A : Type) (B : A -> Type) a a' (e:a=a') {info} i:
  transport (fun a => _Cast (B a) info) e (Fail _ i) = Fail _ i.
    destruct e. reflexivity.
Defined.

Definition path_Cast {A info} {x y : _Cast A info} `{IsHProp info}
           (xy : match x,y with
                   Some x0, Some y0 => x0 = y0
                 | Fail _ _ , Fail _ _ => True
                 | _, _ => False end) : x = y.
Proof. 
  destruct x, y. all: try apply ap, xy.
  all: try elim xy. apply ap. 
  apply is_hprop. 
Defined.

Definition path_Cast_inv {A info} {x y : _Cast A info} :
           x = y -> 
           match x,y with
                   Some x0, Some y0 => x0 = y0
                 | Fail _ _ , Fail _ _ => True
                 | _, _ => False end.
Proof.
  destruct 1, x; reflexivity.
Defined.

Definition Some_inj {A info} {x y : A} : Some x = Some y -> x = y :=
  fun e => path_Cast_inv (info := info) e.

Definition Some_inj_sect {A info} {x y :A} (e:x=y) : Some_inj (ap (@Some _ info) e) = e. 
Proof.
  destruct e; reflexivity.
Defined.

Definition Some_inj_retr {A} {x y : Cast A} (e: x = y) :
  path_Cast (path_Cast_inv e) = e. 
Proof.
  destruct e, x. reflexivity.
  simpl. assert (is_hprop c c = eq_refl).
  simple refine (@contr _ (IsHProp_contr _ c c) eq_refl).
  rewrite H. reflexivity.
Defined.

Definition Some_inj_eq {A} {x y :A} (e:Some x= Some y) : ap (@Some _ _) (Some_inj e) = e := Some_inj_retr e. 

(** ** Monadic operations *)

Definition creturn {A info} : A -> _Cast A info := Some.

Definition clift {A B info} : (A -> B) -> A -> _Cast B info :=
  fun f a => creturn (f a).

Definition cbind {A B info} : (A -> _Cast B info) -> _Cast A info -> _Cast B info := fun f a =>
  match a with 
      Some a => f a
    | Fail _ i => Fail _ i
  end. 

Notation "x >>= f" := (cbind f x) (at level 50).

Notation "x <- e1 ; e2" := (e1 >>= (fun x => e2))
                            (right associativity, at level 60).

Definition kleisli_comp {A B C info}:
  (A -> _Cast B info) -> (B -> _Cast C info) -> (A -> _Cast C info) :=
  fun f g a => b <- f a ; g b.

Notation "g °° f" := (kleisli_comp f g) (at level 50).

Definition cbind_Some {A B info} x (f:A -> _Cast B info) b :
  x >>= f = Some b -> {a:A & ((x = Some a) * (f a = Some b))%type}.
  intro e. destruct x.  
  - exists a. split. reflexivity. exact e. 
  - simpl in e. inversion e.
Defined.

Definition cbind_Some' {A B info} x (f:A -> _Cast B info) b :
   {a:A & ((x = Some a) * (f a = Some b))%type} -> 
  x >>= f = Some b.
  intros [a (Hx, Hfa)]. unfold cbind. destruct x.  
  - inversion Hx. exact Hfa.
  - inversion Hx.
Defined.

Lemma cbind_right_id {A info} (x : _Cast A info):
  (x >>= creturn) = x.
    destruct x; reflexivity.
Defined.

Lemma cbind_assoc {A B C info} x (f: A -> _Cast B info)(g: B -> _Cast C info):
  (x >>= f) >>= g = x >>= (fun x => f x >>= g).
    destruct x; reflexivity.
Defined.

(** ** Extraction *)

Extraction Language Ocaml.

(** Transparent extraction of Cast:
    - if Some t, then extract plain t
    - if Fail, then fail with a runtime cast exception **)
Extract Inductive _Cast
=> ""
     [ ""
       "(let f s = 
          failwith (String.concat """" ([""Cast failure: ""]@ 
                                       (List.map (String.make 1) s))) in 
           f)"
     ]
     "(let new_pattern some none = some in 
         new_pattern)".

(** ** Example *)

Example cast_some {info} : unit -> _Cast bool info := fun _ => Some true.

Definition Cast_info_wrap s A : Cast_info := (tr (s, A)).

Example cast_fail : unit -> Cast bool := fun _ => Fail bool (Cast_info_wrap "H" bool).

Example use_bool (cb: Cast bool)  := cb >>= (fun b => creturn (andb b b)).

Example use_some := fun x => use_bool (cast_some x).
Example use_fail := fun x => use_bool (cast_fail x).

Extraction "test_cast_extr.ml" cast_some cast_fail use_some use_fail.
(* Expected result: it should compile (first..) and then trigger a [failwith] *)


(** ** Decidable instances *)

Instance Decidable_eq_cast : forall A (HA: DecidablePaths A) 
  (x y: Cast A), Decidable (eq x y).
intros. destruct x; destruct y.
- case (dec_paths a a0); intro H.
  + left. rewrite H. reflexivity.
  + right. unfold not in *. intro Hc. inversion Hc. 
    exact (H H1).
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. apply ap. apply is_hprop.
Defined.

Instance DecidablePaths_cast :
  forall A (HA: DecidablePaths A), DecidablePaths (Cast A) := 
  { dec_paths := Decidable_eq_cast A HA }.


(** ** Preorder instance *)

(** We define a notion of preorder between functions on the Cast monad*)

Instance PreOrderCast A : PreOrder_p (Cast A) :=
  {| rel := fun a a' => match a with
                     | Some _ => a = a'
                     | Fail _ _ => True
                     end;
     bot := Fail _ (Cast_info_wrap "cast" A) |}.
Proof.
  - destruct x. reflexivity. exact I.
  - intros x y z. destruct x, y; intros e e'; auto. 
    exact (e @ e'). 
    discriminate.
  - intro; exact I.
Defined.

(** To avoid failure of evaluation of bot in ocaml code *)

Extract Constant PreOrderCast => "0".

Instance PreOrderCast_HProp A `{forall x y : A, IsHProp (x=y)}
         (x y : Cast A) : IsHProp (x ≼ y).
Proof.
  intros e e'. cbn in *. destruct x, y; cbn in *.
  + assert (path_Cast_inv e = path_Cast_inv e') by apply is_hprop.
    apply (ap (@path_Cast A Cast_info (Some a) (Some a0) _)) in H0.
    repeat rewrite Some_inj_retr in H0. assumption. 
  + inversion e.
  + destruct e, e'. reflexivity.
  + destruct e, e'. reflexivity. 
Defined.
