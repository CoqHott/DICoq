Set Universe Polymorphism.

(** This code is mostly imported from
[https://github.com/HoTT/HoTT]. We are defining it here to be
independent of the Coq/HoTT library. 
*)

(** * Sigma type *)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Definition projT1 {A} {P:A -> Type} (x:sigT P) : A := 
  match x with
  | existT _ a _ => a
  end.

Definition projT2  {A} {P:A -> Type} (x:sigT P) : P (projT1 x) :=
  match x with
  | existT _ _ h => h
  end.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).
Notation π1 := (@projT1 _ _). 

(** * Pi type *)

(* =funeq= *)
Notation "f == g" := (forall x, f x = g x)
(* =end= *)
    (at level 3).

Definition apD10 {A} {B:A -> Type} (f g: forall a, B a) (p: f = g): f == g := 
  match p with eq_refl => fun x => eq_refl end.


Definition compose {A B C} : (A -> B) -> (B -> C) -> A -> C := fun f g x => g (f x).

Notation "g ° f" := (compose f g) (at level 1).

(** * Equality type *)

(** Equality types have a groupoid structure:
    - Identity:            [eq_refl]
    - Partial composition: [p @ q]
    - Inverse:             [p ^]
    st.
    - [eq_refl = p ^ @ p]
*)

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with eq_refl, eq_refl => eq_refl end.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x := 
  match p with eq_refl => eq_refl end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Definition inverse_left_inverse A (x y : A) (p : x = y) : eq_refl = (p ^ @ p) :=
  match p with eq_refl => eq_refl end.

(** Predicates behave functorially wrt. this groupoid structure,
    ie. there is a transport map 
    [[
        _#_ : x = y -> P x -> P y
    ]]

*)

(* =transport= *)
Definition transport {A: Type} (P: A -> Type) {x y: A} 
    (p: x = y) (u: P x): P y :=
  match p with eq_refl => u end.
Notation "p # x" := (transport _ p x)
(* =end= *)
                      (right associativity, at level 65, only parsing).

Definition ap_transport {A} {P Q : A -> Type} {x y : A} 
      (p : x = y) (f : forall x, P x -> Q x) (z : P x) : f y (p # z) = p # (f x z) :=
  match p with eq_refl => eq_refl end.


(** Equality structure over Pi types *)

(* =ap= *)
Definition ap {A B: Type} (f: A -> B) {x y: A} : x = y -> f x = f y.
(* =end= *)
  exact (fun p => match p with eq_refl => eq_refl end).
Defined.

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} 
           (p:x=y): p # (f x) = f y :=
  match p with eq_refl => eq_refl end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} 
           (p : x = y): ap (fun x => g (f x)) p = ap g (ap f p) :=
  match p with eq_refl => eq_refl end.


(** * Equivalences (first-order) *)
     
(** ** Type equivalence *)

(** The typeclass [IsEquiv] includes the data making [f] into an
adjoint equivalence. *)

(** From nlab [https://ncatlab.org/nlab/show/adjoint+equivalence], "an
adjoint equivalence between categories is an adjunction [f ⊣ g] in which
the unit [e_sect] and counit [e_retr] are natural isomorphisms." *)

(** Here, the adjointness states that all the ways to go from [A] to
[B] (and conversely) are strictly the same. *)

(* Pierre: for strict accuracy, the counit [e_retr] should perhaps be
defined in the other direction: [e_retr : id == f ° e_inv] I guess. *)

Notation id := (fun x => x). 

(* =IsEquiv= *)
Class IsEquiv {A B: Type} (f: A -> B) := {
  e_inv: B -> A ;
  e_sect: e_inv ° f == id;
  e_retr: f ° e_inv == id;
  e_adj: forall x: A, e_retr (f x) = ap f (e_sect x)
}.
(* =end= *)

Arguments e_inv {_ _} _ {_}.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.

Definition Funext := forall A (B:A -> Type) (f g: forall a, B a) ,
    IsEquiv (apD10 f g).

Axiom funext : Funext. 

(** A class that includes all the data of an adjoint equivalence. *)
(* =Equiv= *)
Record Equiv (A B: Type) := {
    e_fun: A -> B ;
    e_isequiv: IsEquiv e_fun
}.
Notation "A ≃ B" := (Equiv A B)
(* =end= *)
                      (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_isequiv {_ _ _}.


(** Equality structure over Sigma types *)

Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
  (e0 : u.1 = v.1) (e1 : e0 # u.2 = v.2): u = v.
Proof.
  destruct u, v. simpl in *.
  destruct e0. simpl in e1. destruct e1.
  reflexivity.
Defined.

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 & p # u.2 = v.2}): u = v.
Proof.
  destruct pq; eapply path_sigma; eauto.
Defined.

Definition transport_cst_sigma {A B : Type} (P : A -> B -> Type) a a' b x
           (e: a = a') : transport (fun a => {b:B & P a b}) e (b;x)
                         = (b; transport (fun a => P a b) e x) :=
  match e with eq_refl => eq_refl end.

(* Some definitions à la HoTT *)

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v): u.1 = v.1 :=
  ap (fun x => projT1 x) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v): p..1 # u.2 = v.2 :=
  match p with eq_refl => eq_refl end.

Notation "p ..2" := (pr2_path p) (at level 3).

(** Equality structure over product type *)

Definition path_prod {A B : Type} (z z' : A * B)
  (e0 : fst z = fst z')(e1 : snd z = snd z'): (z = z').
Proof.
  destruct z, z'. simpl in *.
  destruct e0, e1. reflexivity.
Defined.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z')): (z = z').
Proof.
  destruct pq. now apply path_prod.
Defined.

Definition f_dep_eq {A B C} (f : forall a : A, B a -> C) x y
           (e: x = y): f x.1 x.2 = f y.1 y.2 :=
  match e with eq_refl => eq_refl end.

(** Equality structure over conjunction *)

Definition proj1 {A B : Prop} (H : A /\ B) := 
  match H with
  | conj H0 _ => H0
  end.

Definition proj2 {A B : Prop} (H : A /\ B) := 
  match H with
  | conj _ H0 => H0
  end.

Definition path_conj {A B : Prop} (z z' : A /\ B)
  (e : proj1 z = proj1 z')(e0 : proj2 z = proj2 z'): z = z'.
Proof.
  destruct z, z'. cbn in *. destruct e, e0. reflexivity.
Defined.

Definition path_conj_uncurried {A B : Prop} (z z' : A /\ B)
  (pq : (proj1 z = proj1 z') * (proj2 z = proj2 z')): z = z'.
Proof.
  destruct pq. now apply path_conj.
Defined.


(** * Hierarchy of types *)

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

(** ** HProp *)

(* =IsHProp= *)
Class IsHProp (T: Type) := is_hprop: forall x y: T, x = y.
(* =end= *)

Arguments is_hprop {T} {_} x y.

Instance Hprop_True

(*-------------*) :
  IsHProp True.

Proof.
  intros x y. destruct x, y; reflexivity.
Defined. 

Instance Hprop_False

(*--------------*) : 
  IsHProp False.

Proof.
  intros x y. destruct x.
Defined. 

Inductive empty : Type := .
Definition Is_true := fun b : bool => if b then unit else empty.

Instance HProp_bool 
         
  (t : bool)
(*-------------------*) : 
  IsHProp (Is_true t).

Proof.
  intros x y. destruct t, x, y. reflexivity.
Defined. 


Instance HProp_and P Q 

  `{HP : IsHProp P}
  `{HQ : IsHProp Q}
(*----------------*) : 
  IsHProp (P * Q).

Proof.
  intros (x,x') (y,y'). 
  apply path_prod_uncurried.
  split; apply is_hprop.
Defined.


Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => False
                 end)
: z = z'.
Proof.
  destruct z, z';
    solve [ apply ap; assumption
          | contradiction ].
Defined.

(** Sums don't preserve hprops in general, but they do for disjoint sums. *)

Instance IsHProp_sum A B 

  `{HA: IsHProp A} 
  `{HB: IsHProp B}
   (Hdisj: A -> B -> False)
(*----------------*) : 
  IsHProp (A + B).

Proof.
  intros x y. apply path_sum. 
  destruct x, y; 
    solve [ apply is_hprop
          | now apply Hdisj ].
Defined.

(** Results requiring functional extensionality *)

Definition not T := T -> empty.

Instance IsHProp_not 
  (P : Type)
(*---------------*) :
  IsHProp (not P).

Proof.
  intros x y. apply funext. intros. destruct (x x0), (y y0); reflexivity. 
Defined.

Instance IsHProp_forall P (Q : P -> Type) 

 `{HQ : forall x, IsHProp (Q x)}
(*----------------*) : 
   IsHProp (forall x, Q x).

Proof.
  intros f g. apply funext. intros x. apply is_hprop. 
Defined.

Instance IsHProp_implies P Q 

 `{HQ : IsHProp Q}
(*----------------*) : 
   IsHProp (P -> Q).
Proof.
  typeclasses eauto.
Defined.

(** ** HSet *)

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

Definition path_contr {A} `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

Definition path2_contr {A} `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; now apply inverse_left_inverse.
  transitivity (path_contr x y). auto. symmetry; auto. 
Defined.

Definition contr_paths_contr A `{Contr A} (x y : A) : Contr (x = y) := let c := {|
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
|} in c.

Instance IsHProp_contr A `{IsHProp A} (x y : A) : Contr (x = y).
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr. exact C.   
Defined.

(* =IsHSet= *)
Class IsHSet A := is_hset:> forall a b: A, IsHProp (a = b).
(* =end= *)

Hint Extern 1 (IsHProp (?a = ?b)) => apply (is_hprop (IsHProp := is_hset a b)) : typeclass_instances.

Instance HSet_HProp A `{IsHSet A} : forall (a b : A), IsHProp (a = b)  :=
  fun a b => is_hprop (IsHProp := is_hset a b).

Instance HProp_IsHSet A `{IsHProp A} : IsHSet A.
Proof.
  intros a b. pose (IsHProp_contr A a b).
  intros e e'. etransitivity. symmetry ; apply contr. apply contr.
Defined. 

(* Definition IsHSet_equiv A {B} (f : A -> B) *)
(*   `{IsHSet A} `{IsEquiv A B f} *)
(*   : IsHSet B. *)
(* Proof. *)
(*   generalize dependent B; generalize dependent A. *)
(*   simple_induction n n IH; simpl; intros A ? B f ?. *)
(*   - exact (contr_equiv _ f). *)
(*   - intros x y. *)
(*     exact (IH (f^-1 x = f^-1 y) (H (f^-1 x) (f^-1 y)) (x = y) ((ap (f^-1))^-1) _). *)
(* Qed. *)

(* HoTT machinery *)


Definition path_sigma_uncurried_equiv A `{P : A -> Type} {u v : sigT P}
           (p q : {p : u.1 = v.1 & p # u.2 = v.2}) (e : p.1 = q.1) : transport (fun X => transport P X u .2 = v .2) e p.2 = q.2 -> p = q. 
Proof.
  destruct p, q. simpl in *. destruct e. simpl. destruct 1. reflexivity.  
Defined.

Definition path_sigma_equiv A `{P : A -> Type} {u v : sigT P}
           (p q : u = v) (e : p..1 = q..1) : transport (fun X => transport P X u .2 = v .2) e p..2 = q..2 -> p = q. 
Proof.
  intro e'. 
  pose (path_sigma_uncurried_equiv A (p..1; p..2) (q..1;q..2) e e').
  etransitivity; try apply eta_path_sigma_uncurried.
  etransitivity; try (symmetry; apply eta_path_sigma_uncurried).
  apply ap. auto. 
Defined.

Instance trunc_sigma C (P: C -> Type)
   `{forall c, IsHSet (P c)}
   {HSet_C : IsHSet C} : IsHSet {c:C & P c}.
Proof.
  intros x y u v. unshelve refine (path_sigma_equiv _ _ _ _ _).
  apply is_hprop. apply is_hprop.
Defined.

Record HSet := hset { 
    _typeS :> Type;
    _isHSet : IsHSet _typeS
}.

(* =HProp= *)
Record HProp := hprop {
    _typeP:> Type;
    _isHProp: IsHProp _typeP
}.
(* =end= *)

Arguments hset _ {_}.
Arguments hprop _ {_}.
          
Instance HSet_isHSet (S:HSet) : IsHSet S := S.(_isHSet).

Instance HProp_isHProp (S:HProp) : IsHProp S := S.(_isHProp).

Module Export Trunc.
Delimit Scope trunc_scope with trunc.

Private Inductive Trunc (A :Type) : Type :=
  tr : A -> Trunc A.
Bind Scope trunc_scope with Trunc.
Arguments tr {A} a.

Axiom istrunc_hprop : forall A, IsHProp (Trunc A).

Global Instance _istrunc_hprop (A : Type) : IsHProp (Trunc A) := istrunc_hprop A.

Definition Trunc_ind_prop {A}
  (P : Trunc A -> Type) {Pt : forall aa, IsHProp (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).

(* Remark: it is _strictly_ forbidden to pattern-match on [Trunc]: you
   can only use [Trunc_ind_prop] to deconstruct it. *)

End Trunc.


Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @ p = p
  :=
  match p with eq_refl => eq_refl end.

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ eq_refl = p
  :=
  match p with eq_refl => eq_refl end.

Definition concat_cong {A : Type} {x y z : A} (p p': x = y) (q q': y = z) : p = p' -> q = q' -> p @ q = p' @ q'.
Proof.
  destruct 1; destruct 1. reflexivity.
Defined.

Definition concat_inv {A : Type} {x y z : A} (p : x = y) (q : y = z) : (p @ q)^ = q^@ p^.
Proof.
  destruct p; destruct q. reflexivity.
Defined.


Lemma inverse_right_inverse A (x y : A) (p : x = y) : eq_refl = (p @ p ^).
Proof.
  destruct p; auto.
Defined.

Definition ap_inv {A B : Type} (f : A -> B) {x y : A} (e : x = y) :
  (ap f e)^ = ap f e^
  :=
    match e with eq_refl => eq_refl end.

Definition dummy {A : Type} {x y : A} (e : x = y) :
  match e with eq_refl => eq_refl end = e := match e with eq_refl => eq_refl end.




Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f eq_refl = eq_refl :> (f x = f x)
  :=
  eq_refl.

Definition inv_1 {A : Type} (x : A) :
  eq_refl^ = eq_refl :> (x = x)
  :=
  eq_refl.


Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with eq_refl =>
    match q with eq_refl =>
                 match p with eq_refl => eq_refl
                 end end end .
 



Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr. auto. 
Defined.


Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with eq_refl =>
    match q with eq_refl =>
      match p with eq_refl => eq_refl
      end end end.



Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact eq_refl.
Defined.

Lemma transport_forall {A} B (g g': B) P {x : A} (e : g = g')
      (f : forall x, P g x)  :
  transport (fun G => forall x, P G x) e f x = transport (fun G => P G x) e (f x).
Proof. 
  destruct e. simpl. reflexivity.
Defined.

(* =IsHSet_forall= *)
Instance IsHSet_forall P (Q : P -> Type) `{HQ : forall x, IsHSet (Q x)}: IsHSet (forall x, Q x).
(* =end= *)
Proof.
  intros f g.
  assert (IsHProp (forall x, f x = g x)). typeclasses eauto.
  intros e e'.
  etransitivity. symmetry.
  apply (@e_sect _ _ _ (funext _ _ f g)).
  etransitivity. Focus 2. 
  apply (@e_sect _ _ _ (funext _ _ f g)).
  unfold compose. apply ap.
  exact (H (apD10 f g e) (apD10 f g e')).
Defined. 

Definition moveR_equiv_M {A B f} `{IsEquiv A B f} (x : A) (y : B) (p : x = e_inv f y)
  : (f x = y)
  := ap f p @ e_retr f y.

Lemma contr_equiv A {B} (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  refine (BuildContr _ (f center) _).
  intro y. 
  apply moveR_equiv_M. apply contr. 
Qed.


Instance IsHProp_compose A B (f : A -> B) P (H : forall b, IsHProp (P b)) a :
  IsHProp (P (f a)) := H (f a).





Instance HSet_HProp_Path A `{IsHSet A} : forall (a b : A), IsHProp (a = b) :=
  fun a b => is_hprop (IsHProp := is_hset a b).

Definition sigT_HSet (A:HSet) (P : A -> HProp) : HSet.
Proof.
  refine (hset (sigT P)).
Defined. 


  