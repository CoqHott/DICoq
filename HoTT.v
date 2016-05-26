Set Universe Polymorphism.

(** This code is mostly imported from
[https://github.com/HoTT/HoTT]. We are defining it here to be
independent of the Coq/HoTT library. 
*)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Definition projT1 {A} {P:A -> Type} (x:sigT P) : A := match x with
                                      | existT _ a _ => a
                                      end.

Definition projT2  {A} {P:A -> Type} (x:sigT P) : P (projT1 x) :=
  match x return P (projT1 x) with
  | existT _ _ h => h
  end.
  
Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Notation "f == g" := (forall x, f x = g x) (at level 3).

Definition apD10 {A} {B:A -> Type} {f g: forall a, B a}:
    f = g -> f == g.
Proof. destruct 1. reflexivity. Defined. 

Definition Funext := forall A (B:A -> Type) (f g: forall a, B a) ,
    (f == g) -> f = g.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with eq_refl => u end.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with eq_refl, eq_refl => eq_refl end.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with eq_refl => eq_refl end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Lemma inverse_left_inverse A (x y : A) (p : x = y) : eq_refl = (p ^ @ p).
Proof.
  destruct p; auto.
Defined.

Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v. 
  destruct u, v. simpl in *.
  destruct p. simpl in q. destruct q. apply eq_refl.
Defined.

Definition transport_cst_sigma {A B : Type} (P : A -> B -> Type) a a' b x
           (e: a = a') : transport (fun a => {b:B & P a b}) e (b;x)
                         = (b; transport (fun a => P a b) e x).
Proof.
  destruct e. reflexivity. 
Defined.

Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  destruct p. reflexivity. 
Defined.

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y.
    destruct p; reflexivity.
Defined.

(* Some definitions à la HoTT *)

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
: u.1 = v.1
  :=  ap (fun x => projT1 x) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2.
  destruct p. reflexivity. 
Defined.

Notation "p ..2" := (pr2_path p) (at level 3).

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & p # u.2 = v.2})
  : u = v.
      destruct u, v. simpl in *. destruct pq.
      destruct x1. simpl in *. destruct e. reflexivity.
Defined.


Definition f_dep_eq {A B X} (f : forall a : A, B a -> X) x y :
  x = y -> f x.1 x.2 = f y.1 y.2.
Proof.
  intros e.  destruct e. reflexivity.
Defined.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
Proof.
  destruct z, z'. simpl in *. destruct pq. destruct e, e0. 
  reflexivity.
Defined.

Definition proj1 {A B : Prop} (H : A /\ B) := match H with
                                 | conj H0 _ => H0
                                 end.

Definition proj2 {A B : Prop} (H : A /\ B) := match H with
                                 | conj _ H0 => H0
                                 end.

Definition path_conj_uncurried {A B : Prop} (z z' : A /\ B)
  (pq : (proj1 z = proj1 z') * (proj2 z = proj2 z'))
  : (z = z').
Proof.
  destruct z, z'. cbn in *. destruct pq. destruct e, e0. reflexivity.
Defined.


Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p)
  :=
    match p with eq_refl => eq_refl end.

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.


Class IsHProp (P : Type) := is_hprop : forall x y:P, x = y.

Arguments is_hprop {P} {_} x y.

Inductive empty : Type := .

Definition not T := T -> empty.

Definition Is_true := fun b : bool => if b then unit else empty.

Instance HProp_bool (t : bool) : IsHProp (Is_true t).
intros x y. destruct t, x, y. reflexivity.
Defined. 


Instance HProp_and P Q (HP : IsHProp P) 
 (HQ : IsHProp Q) : IsHProp (P * Q).
intros (x,x') (y,y'). refine (path_prod_uncurried _ _ _).
split; apply is_hprop.
Defined.


Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => False
                 end)
: z = z'.
  destruct z, z'.
  all:try apply ap, pq.
  all:elim pq.
Defined.

(** Sums don't preserve hprops in general, but they do for disjoint sums. *)

Instance IsHProp_sum A B `{IsHProp A} `{IsHProp B}
: (A -> B -> False) -> IsHProp (A + B).
Proof.
  intros He.
  intros x y. apply path_sum. destruct x, y.
  all : try apply is_hprop. 
  all : apply (He a b). 
Defined.

Instance IsHProp_not (H : Funext) P : IsHProp (not P).
intros x y. apply H. intros. destruct (x x0), (y y0); reflexivity. 
Defined.


(* require functional extensionality *)
Instance IsHProp_implies (H:Funext) P Q (HQ : IsHProp Q) : IsHProp (P -> Q).
intros f g. apply H. intros x. apply is_hprop. 
Defined.

Instance Hprop_True : IsHProp True.
intros x y. destruct x, y; reflexivity.
Defined. 

Instance Hprop_False : IsHProp False.
intros x y. destruct x.
Defined. 

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.


Class IsHSet X := {isHSet :> forall (a b : X), IsHProp (a = b)}.

Hint Extern 1 (IsHProp (?a = ?b)) => apply (is_hprop (IsHProp := isHSet a b)) : typeclass_instances.


Instance HSet_HProp X `{IsHSet X} : forall (a b : X), IsHProp (a = b)  :=
  fun a b => is_hprop (IsHProp := isHSet a b).

(* HoTT machinery *)
Instance trunc_sigma C (P: C -> Type)
   `{forall c, IsHProp (P c)}
   {HSet_C : IsHSet C} : IsHSet {c:C & P c}.
Proof.
  (* this is a consequence of trunc_sigma in 
     https://github.com/HoTT/HoTT/blob/master/theories/Types/Sigma.v*)
  (* it requires quite involve machinery to be proven, so we just *)
  (* admit it*)
Admitted.

Record HSet :=
  {
    _typeS :> Type;
    _HSet_isHSet : IsHSet _typeS
  }.

Record HProp :=
  {
    _typeP :> Type;
    _HProp_isHProp : IsHProp _typeP
  }.


Instance HSet_isHSet (S:HSet) : IsHSet S := S.(_HSet_isHSet).

Instance HProp_isHProp (S:HProp) : IsHProp S := S.(_HProp_isHProp).

Module Export Trunc.
Delimit Scope trunc_scope with trunc.

Private Inductive Trunc (A :Type) : Type :=
  tr : A -> Trunc A.
Bind Scope trunc_scope with Trunc.
Arguments tr {A} a.

Global Instance istrunc_horio (A : Type)
: IsHProp (Trunc A).
Admitted.

Definition Trunc_ind {A}
  (P : Trunc A -> Type) {Pt : forall aa, IsHProp (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).

End Trunc.

Definition IsHProp_contr_ A `{IsHProp A} (x y : A) : forall y0 : x = y, is_hprop x y = y0.
Admitted.

Instance IsHProp_contr A `{IsHProp A} (x y : A) : Contr (x = y) :=
  {| center := is_hprop x y; contr := IsHProp_contr_ _ _ _ |}.
