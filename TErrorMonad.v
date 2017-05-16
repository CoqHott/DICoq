Require Import Ascii String Decidable HoTT PartialOrder.
Require Import ExtrOcamlString.

Set Universe Polymorphism.

Set Implicit Arguments.

(** * The [TError] monad *)

(** ** Datatype *)


(* =_Cast= *)
Inductive TError A (info : HProp) :=
  | Some : A -> TError A info
  | Fail : info -> TError A info.
(* =end= *)

Arguments Some {_ _} _.
Arguments Fail {_ _} _.

(** We need to assume that the string message is irrelevant.  We would
    not need prositional truncation as an axiom if we were using the
    simpler version with [None] (and no [info]). *)

(* =Cast= *)
Definition info_str := hprop (Trunc string).
(* =end= *)

Unset Implicit Arguments.

Notation "A ⇀ B" := (A -> TError B info_str) (at level 50). 

(** ** Transport maps *)

Definition transport_TError (A : Type) (B : A -> Type) {info} a a' (e:a=a') x:
  transport (fun a =>  TError (B a) info) e (Some x) = Some (e # x).
    destruct e. reflexivity.
Defined.

Definition transport_TError_Fail (A : Type) (B : A -> Type) a a' (e:a=a') {info} i:
  transport (fun a => TError (B a) info) e (Fail i) = Fail i.
    destruct e. reflexivity.
Defined.

Definition path_TError {A} {info} {x y : TError A info}
           (xy : match x,y with
                   Some x0, Some y0 => x0 = y0
                 | Fail _ , Fail _ => True
                 | _, _ => False end) : x = y.
Proof. 
  destruct x, y. all: try apply ap, xy.
  all: try elim xy. apply ap. 
  apply is_hprop. 
Defined.

Definition path_TError_inv {A} {info} {x y : TError A info} :
           x = y -> 
           match x,y with
                   Some x0, Some y0 => x0 = y0
                 | Fail _ , Fail _ => True
                 | _, _ => False end.
Proof.
  destruct 1, x; reflexivity.
Defined.

Definition Some_inj {A} {info} {x y : A} : @Some _ info x = @Some _ info y -> x = y :=
  fun e => path_TError_inv e.

Definition Some_inj_sect {A} {info} {x y :A} (e:x=y) : Some_inj (ap (@Some _ info) e) = e. 
Proof.
  destruct e; reflexivity.
Defined.

Definition Some_inj_retr {A} info {x y : TError A info} (e: x = y) :
  path_TError (path_TError_inv e) = e. 
Proof.
  destruct e, x as [x|i]. reflexivity.
  simpl. assert (is_hprop i i = eq_refl).
  etransitivity. symmetry. apply contr.  apply contr. 
  refine (transport (fun X => ap _ X =_ ) H^ _). reflexivity.
Defined.

Definition Some_inj_eq {A} {x y :A} info (e:Some x= Some y) : ap (@Some _ _) (Some_inj e) = e := 
  Some_inj_retr info e. 

(** ** Monadic operations *)

Definition creturn {A} : A ⇀ A := Some.

(* =clift= *)
Definition clift A B : (A -> B) -> (A ⇀ B) :=
  fun f a => creturn (f a).
(* =end= *)

Arguments clift {_ _} _ _.

(* =cbind= *)
Definition cbind A B {info} : 
      (A -> TError B info) -> TError A info -> TError B info :=
  fun f a => match a with 
               Some a => f a
             | Fail i => Fail i
             end. 
Notation "x <- e1 ; e2" := (cbind _ _ (fun x => e2) e1)
(* =end= *)
                            (right associativity, at level 60).

Notation "x >>= f" := (cbind _ _ f x) (at level 50).

(* =kleisliComp= *)
Definition kleisliComp {A B C : Type} : (A ⇀ B) -> (B ⇀ C) -> (A ⇀ C) :=
  fun f g a => b <- f a ; g b.
Notation "g °° f" := (kleisliComp f g)
(* =end= *)
 (at level 50).

Definition cbind_Some {A B} x (f:A ⇀ B) b :
  x >>= f = Some b -> {a:A & ((x = Some a) * (f a = Some b))%type}.
  intro e. destruct x.  
  - exists a. split. reflexivity. exact e. 
  - simpl in e. inversion e.
Defined.

Definition cbind_Some' {A B} x (f:A ⇀ B) b :
   {a:A & ((x = Some a) * (f a = Some b))%type} -> 
  x >>= f = Some b.
  intros [a (Hx, Hfa)]. unfold cbind. destruct x.  
  - inversion Hx. exact Hfa.
  - inversion Hx.
Defined.

Lemma cbind_right_id {A} (x : TError A _):
  (x >>= creturn) = x.
    destruct x; reflexivity.
Defined.

Lemma cbind_assoc {A B C} x (f: A ⇀ B) (g: B ⇀ C):
  (x >>= f) >>= g = x >>= (fun x => f x >>= g).
    destruct x; reflexivity.
Defined.

(** ** Extraction *)

Extraction Language Ocaml.

(* =extract_cast= *)
Extract Inductive TError => 
(* Transparent extraction of TError:
   - if Some t, then extract plain t
   - if Fail, then fail with a runtime coercion exception *)
     "" [ "" "(let f s = failwith
                (String.concat """" ([""Coercion failure: ""]@ 
                  (List.map (String.make 1) s))) in f)" ]
     "(let new_pattern some none = some in new_pattern)".
(* =end= *)

(** ** Example *)

Example coercion_some : unit ⇀ bool := fun _ => Some true.

Definition _with (s:string) : info_str := (tr s).

(* =cast_bool= *)
Example err : TError bool info_str := Fail (_with "coercion to bool").
(* =end= *)

Example use_bool (cb: TError bool info_str)  := cb >>= (fun b => creturn (andb b b)).

Example use_some := fun x => use_bool (coercion_some x).
Example use_fail := fun x:unit => use_bool err.

Extraction "test_coercion_extr.ml" use_some use_fail.
(* Expected result: it should compile (first..) and then trigger a [failwith] *)


(** ** Decidable instances *)

Definition Decidable_eq_TError : forall A (HA: DecidablePaths A) 
  (x y: TError A info_str), (x = y) + not (x = y).
intros. destruct x as [a |]; destruct y as [a0 |].
- case (dec_paths a a0); intro H.
  + left. exact (ap _ H). 
  + right. intro Hc. exact (H (Some_inj Hc)). 
- right. unfold not. intro Hc. inversion Hc.
- right. unfold not. intro Hc. inversion Hc.
- left. apply ap. apply is_hprop.
Defined.

Instance IsHSet_TError (A:HSet) HA : IsHSet (TError A info_str) := Hedberg (@Decidable_eq_TError A HA).
                                                              
Instance DecidablePaths_TError :
  forall A (HA: DecidablePaths A), DecidablePaths (hset (TError A info_str)) := 
  { dec_paths := Decidable_eq_TError A HA }.


(** ** Preorder instance *)

(** We define a notion of preorder on [TError A], for any [A]. The least
element is bottom while successful computations are compared by
equality. *)

(* =preordercast= *)
Instance PartialOrderTError (A:HSet) : PartialOrder_pp (TError A info_str) :=
  {| rel := fun a a' => @hprop (match a with
                     | Some _ => a = a'
                     | Fail _ => True
                     end) _;
     bot := Fail (_with "bot") |}.
(* =end= *)
Proof.
  - intros e e'. cbn in *. destruct a as [a|], a' as [a'|]; cbn in *.
    + assert (path_TError_inv e = path_TError_inv e') by apply is_hprop.
      apply (ap (@path_TError A info_str (Some a) (Some a'))) in H.
      repeat rewrite Some_inj_retr in H. assumption. 
    + inversion e.
    + destruct e, e'. reflexivity.
    + destruct e, e'. reflexivity. 
  - destruct x. reflexivity. exact I.
  - intros x y z. destruct x, y; intros e e'; auto. 
    exact (e @ e'). 
    discriminate.
  - intros x y H H'. destruct x, y; eauto.
    apply ap. apply is_hprop. 
  - intro; exact I.
Defined.

(** To avoid failure of evaluation of bot in ocaml code *)

Extract Constant PartialOrderTError => "0".

Instance TError_HSet A `{IsHSet A} : IsHSet (TError A info_str).
intros.
intros a b e e'.
destruct a as [a|]; destruct b as [b|];
  try now inversion e.
+ pose proof (Some_inj_eq info_str e)^.
  pose proof (Some_inj_eq info_str e').
  etransitivity; eauto.
  etransitivity; [| eauto].
  destruct (is_hset a b (Some_inj e) (Some_inj e')).
  reflexivity.
+ pose proof (Some_inj_retr info_str e).
  pose proof (Some_inj_retr info_str e').
  etransitivity; [symmetry; eauto|].
  etransitivity; [|eauto].
  assert (e'': path_TError_inv e = path_TError_inv e') by apply is_hprop.
  destruct e''. reflexivity.
Qed.

Definition TError_HSet_preorder (A:HSet) : forall (x y : TError A info_str) (e e' : x ≼ y), e = e'.
Proof. 
  intros x y e e'; destruct x as [x|], y as [y|]; simpl in *.
  apply TError_HSet; typeclasses eauto. 
  inversion e.
  destruct e, e'; reflexivity.
  destruct e, e'; reflexivity.
Defined. 



Definition transport_bind A (x y : A) (e:y=x)  B (f : A -> B) :
  transport (λ X : TError A info_str, Some (f x) = b <- X; clift f b)
            (ap creturn e)^ eq_refl
  = ap creturn (ap f e^).
    destruct e. reflexivity.
Defined.
