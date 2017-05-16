Require Import TErrorMonad Showable Decidable HoTT PartialOrder. 

Set Universe Polymorphism.

(** * Equivalences (first-order) *)

(** ** [Functor] class *)

Definition compose {A B C} : (A -> B) -> (B -> C) -> A -> C := fun f g x => g (f x).

Notation "g ° f" := (compose f g) (at level 1).

Class Functor A B (relA : A -> A -> Type) (relB : B -> B -> Type) (f:A -> B) :=
  { ap :forall x y, relA x y -> relB (f x) (f y)}.

Arguments ap {_ _ _ _} _ {_ _ _} _.

Instance FunctorOnEq A B (f : A -> B) : Functor A B eq eq f :=
  {| ap := fun x y e => HoTT.ap f e |}.

Hint Extern 0 (Functor ?A ?B _ _ ?f) => exact (FunctorOnEq A B f) : typeclass_instances.
     
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

(* =IsEquiv= *)
Class IsEquiv {A B : Type} (f : A -> B) := {
  e_inv : B -> A ;
  e_sect : e_inv ° f == id;
  e_retr : f ° e_inv == id;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x)
}.
(* =end= *)

Arguments e_inv {_ _} _ {_}.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.

(** A class that includes all the data of an adjoint equivalence. *)
(* =Equiv= *)
Record Equiv (A B: Type) := 
  {  e_fun : A -> B ;
     e_isequiv : IsEquiv e_fun
  }.
Notation "A ≃ B" := (Equiv A B)
(* =end= *)
                      (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_isequiv {_ _ _}.

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (issect : g° f == id) (isretr : f  ° g == id).

  Let issect' := fun x =>
    HoTT.ap g (ap f (issect x)^)  @  HoTT.ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = HoTT.ap f (issect' a).
  Admitted.
  
  Definition isequiv_adjointify : IsEquiv f
    := Build_IsEquiv A B f g issect' isretr is_adjoint'.

End Adjointify.


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


(** ** Monotone type-theoretic Galois connection *)

(** A monotone function is a functor over pointed preorders. *)

Instance FunctorOnPreorder A B `{PartialOrder_pp A} `{PartialOrder_pp B} (f : A --> B) :
  Functor A B rel rel f :=
  {| ap := fun x y e => f.(mon) e|}.

Hint Extern 1 (Functor ?X ?Y _ _ ?f) => apply FunctorOnPreorder : typeclass_instances.

(* Pierre: is there a relationship with antitone/monotone Galois
connections? *)

Arguments rel_trans {_ _ _ _ _} _ _.

(* =NotationRel= *)
Notation "f °H g" := (rel_trans f g) (at level 60).
Notation "'idK' f" := (rel_refl f) (at level 60).
(* =end= *)

(* =IsPartialEquiv= *)
Class IsConnection {A B} `{PartialOrder_pp A} `{PartialOrder_pp B} (f: A --> B) :=
  {  c_inv :  B --> A;
     c_sect : id ≼  c_inv ° f ;
     c_retr : f ° c_inv ≼ id;
  }.
(* =end= *)

     (* c_adj : forall x, (ap f (c_sect x)) °H (c_retr (f x)) = idK (f x); *)

Arguments c_inv {_ _ _ _} _ {_}.
Arguments c_sect {_ _ _ _} _ {_} _.
Arguments c_retr {_ _ _ _} _ {_} _.
(* Arguments c_adj {_ _ _ _} _ {_} _. *)

(* =CanonicalPartialEquiv= *)
Class Coercion A B `{PartialOrder_pp A} `{PartialOrder_pp B} :=
  {  c_fun : A --> B ;
     c_isconn : IsConnection c_fun
  }.
Notation "A ≲ B" := (Coercion A B)
(* =end= *)
                       (at level 20).

(* =IsConnectionIsHProp= *)
Instance IsConnectionIsHProp A B `{PartialOrder_pp A} `{PartialOrder_pp B}
           (f: A --> B) : IsHProp (IsConnection f).
(* =end= *)
Proof.
  intros g g'. destruct g, g'.
  assert (c_inv0 = c_inv1).
  destruct c_inv0, c_inv1.
  assert (f_ord = f_ord0). 
  {
    apply rel_antisym.
    - intro x. eapply rel_trans. apply c_sect1. simpl. apply mon0. apply c_retr0.
    - intro x. eapply rel_trans. apply c_sect0. simpl. apply mon. apply c_retr1.
  }
  subst.
  assert (mon = mon0).
  apply is_hprop. 
  assert (p_mon = p_mon0).
  apply is_hprop. 
  subst. reflexivity.
  subst. 
  assert (c_sect0 = c_sect1). apply is_hprop. 
  assert (c_retr0 = c_retr1). apply is_hprop. 
  subst. reflexivity. 
Defined. 

  (* Definition PartialEquiv_unique_up_to_iso {X Y} `{PartialOrder_p X} `{PartialOrder_p Y} (f:X --> Y) (Hf Hf' : IsPartialEquiv f) : c_inv  *)

(** ** Monotone type-theoretic partial Galois connection  *)

(**

A monotone function [f: A → B] defines a partial coercion
[PartialCoercion] if some of the [b: B] maps back to the same [a: A]
they come from. Think of [A] as being a refinement of [B] and [f] as
dropping the refinement: not all [B]'s are valid [A]'s but the one
which are can easily be mapped back to [A].

 *)


Definition compV {A B C : HSet} {f f':A ⇀ B} {g g' : B ⇀ C} : f ≼ f' -> g ≼ g' ->
                                                       g °° f ≼ (g' °° f').
Proof.
  intros e e' x. unfold kleisliComp. generalize dependent (e x). clear e.
  cbn. destruct (f x) as [y|]; simpl; eauto. intro e.
  generalize dependent (e' y). clear e'.
  cbn. destruct (g y); simpl; eauto. intro e'.
  apply (transport (fun X => _ = b <- X ; _) e). auto.
Defined.

Notation "f °V g" := (compV f g) (at level 20).

Definition α {A B C D : HSet} (f:A ⇀ B) (g:B ⇀ C) (h:C ⇀ D):
    (h °° (g °° f)) ≼ ((h °° g) °° f).
Proof.
  intro x.
  unfold kleisliComp.
  destruct (f x); simpl; eauto.
  apply (rel_refl (PartialOrder_pp := PartialOrderTError _)).
Defined.

Definition idR {A B : HSet} (f:A ⇀ B):
  (creturn °° f) ≼ f.
Proof.
  intro x. unfold kleisliComp. destruct (f x); reflexivity.
Defined.

Definition idL {A B : HSet} (f:A ⇀ B):
  (f °° creturn) ≼ f := rel_refl f.


(* Pierre: Again, it really matters here that [c_retr] is defined in the
"wrong" direction. Let's consider the preorder over the [TError]
type. We are currently saying: [f ° c_inv] is at most as defined as
[id] (which is always true) while we might be more informative by
going in the "right" direction, asking for [f ° c_inv] to be as
defined as [id], ie. always defined:

<<
  id ≼ f ° c_inv
  <=> forall mx, mx ≼ mx >>= c_inv >> f
  <=> /\. forall x, Some x = f (c_inv x)
      /\. bot ≼ bot
  <=> forall x, x = f (c_inv x)
>>

 Currently, both [f] and [c_inv] can throw away information. If we
 make the switch, then [f] must be total on [Im c_inv]. *)

(* =IsPartialEquivK= *)
Class IsConnectionK {A B : HSet} (f: A ⇀ B) :=
  { pc_inv :  B ⇀ A;
    pc_sect : creturn ≼ (pc_inv °° f);
    pc_retr : (f °° pc_inv) ≼ creturn ;
    }.
(* =end= *)

    (* pc_adj : forall x, *)
    (*   (idL f °H (pc_sect °V (idK f)) °H *)
    (*       (α _ _ _ °H ((idK f) °V pc_retr) °H idR f)) x = idK _ *)

(* extra bits, not necessary for the moment *)


Arguments pc_inv {_ _} _ {_}.
Arguments pc_sect {_ _} _ {_} _.
Arguments pc_retr {_ _} _ {_} _.
(* Arguments pc_adj {_ _} _ {_} _. *)

(* =PartialEquivK= *)
Record CoercionK (A B : HSet) := {
  pc_fun : A ⇀ B ;
  pc_isconn : IsConnectionK pc_fun
}.
Notation "A ≲K B" := (CoercionK A B)
(* =end= *)
                        (at level 20).

Arguments pc_fun {_ _} _ _.
Arguments pc_isconn {_ _ _}.

(* =IsAPartialEquivK= *)
Class IsAntiConnectionK {A B : HSet} (f: A ⇀ B) :=
  { ac_inv :  B ⇀ A;
    ac_sect : (ac_inv °° f) ≼ creturn;
    ac_retr : (f °° ac_inv) ≼ creturn ;
    }.
(* =end= *)

Arguments ac_inv {_ _} _ {_}.
Arguments ac_sect {_ _} _ {_} _.
Arguments ac_retr {_ _} _ {_} _.

(* =APartialEquivK= *)
Record AntiCoercionK (A B : HSet) := {
  ac_fun : A ⇀ B ;
  ac_isconn : IsAntiConnectionK ac_fun
}.
Notation "A ≲AK B" := (AntiCoercionK A B)
(* =end= *)
                        (at level 20).

Arguments ac_fun {_ _} _ _.
Arguments ac_isconn {_ _ _}.

(* Definition path_IsPartialEquivK  {X Y} (f: X ⇀ Y) (u v : IsPartialEquivK f) : forall  *)
(*     (p : pc_inv (IsPartialEquivK := u) f = pc_inv (IsPartialEquivK := v) f) *)
(*     (q : transport (fun pc_inv =>  creturn ≼ (pc_inv °° f)) p (pc_sect (IsPartialEquivK := u) f) = (pc_sect (IsPartialEquivK := v) f)) *)
(*     (q' : transport (fun pc_inv =>  (f °° pc_inv) ≼ creturn ) p (pc_retr (IsPartialEquivK := u) f) = (pc_retr (IsPartialEquivK := v) f)), *)
(*   u = v. *)
(*   destruct u, v.  cbn. intros. destruct p,q,q'. simpl in *. *)
(* Admitted.  *)

Definition path_IsConnectionK_HSet {A B : HSet} {HX: IsHSet A} {HY: IsHSet B} (f: A ⇀ B)
           (u v : IsConnectionK f) :  
  pc_inv (IsConnectionK := u) f = pc_inv (IsConnectionK := v) f ->
  u = v.
  destruct u, v.  cbn. intros p. destruct p.
  assert (pc_sect0 = pc_sect1).
  apply funext. intro x. refine (TError_HSet_preorder A (creturn x) ((pc_inv0 °° f) x) _ _).
  assert (pc_retr0 = pc_retr1).
  apply funext. intro y. refine (TError_HSet_preorder B ((f °° pc_inv0) y) (creturn y)  _ _).
  destruct H, H0. reflexivity. 
  (* assert (pc_adj0 = pc_adj1). *)
  (* apply funext; intro x. apply contr_paths_contr. *)
  (* apply IsHProp_contr. intros e e'. apply (TError_HSet_preorder B).  *)
  (* destruct H; reflexivity. *)
Defined. 

Definition always_iso {A B : HSet} {f f':A ⇀ B} :
    f ≼ f' -> f' ≼ f -> forall x, f x = f' x. 
Proof.
  intros e e' x.
  specialize (e x); specialize (e' x).
  destruct (f x), (f' x); auto. apply (ap (@Fail B _)). apply is_hprop.
Defined. 

Definition idR' {A B : HSet} (f:A ⇀ B):
  f ≼ (creturn °° f).
Proof.
  intro x. unfold kleisliComp. destruct (f x); reflexivity.
Defined.

Definition α' {A B C D :HSet} (f:A ⇀ B) (g:B ⇀ C) (h:C ⇀ D):
    ((h °° g) °° f) ≼ (h °° (g °° f)).
Proof.
  intro x.
  unfold kleisliComp.
  destruct (f x); simpl; eauto.
  apply (rel_refl (PartialOrder_pp := PartialOrderTError _)).
Defined.

Definition IsConnection_IsHProp_fun {A B : HSet} (f: A -> B) (H H' : IsConnectionK (clift f))
  : pc_inv (clift f) (IsConnectionK := H) ≼ pc_inv (clift f) (IsConnectionK := H'). 
Proof.
  eapply rel_trans.
  exact (idR' (pc_inv (clift f)) °H ( (idK (pc_inv (clift f))) °V pc_sect (clift f) (IsConnectionK := H'))).
  eapply rel_trans.
  apply α'.
  exact ((pc_retr (clift f) (IsConnectionK := H) °V idK _ ) °H idL ( pc_inv (clift f))).
Defined.

Definition IsConnection_IsHProp_HSet (A B : HSet) (f: A -> B) {HX: IsHSet A} {HY: IsHSet B}
           : IsHProp (IsConnectionK (clift f)).
Proof.
  intros H H'.
  unshelve eapply path_IsConnectionK_HSet; cbn; auto.
  apply funext. unshelve eapply always_iso; auto.
  apply IsConnection_IsHProp_fun; auto.
  apply IsConnection_IsHProp_fun; auto.
Defined.

(* Definition preorder_app {X Y Z} {g g': Y ⇀ Z} *)
(*            (e : g ≼ g') (f: X ⇀ Y)  : g °° f ≼ (g' °° f) := (idK f) °V e. *)

(* Definition refl_H_bicat_preorder X Z (h h': X ⇀ Z) (H : h ≼ h') `{funext:Funext} : *)
(*   H = (H °H (idK h')). *)
(* Proof. *)
(*   apply funext. intro x. simpl. *)
(*   set (H x). clearbody r; clear H. generalize r. simpl. *)
(*   destruct (h x), (h' x); simpl; intros. *)
(*   destruct r0. reflexivity.  *)
(*   inversion r. reflexivity.  *)
(*   destruct r0. reflexivity.  *)
(* Defined. *)

(* Definition transport_preorder X Y Z (f: X ⇀ Y) (g g': Y ⇀ Z) (h: X ⇀ Z) *)
(*            (e : g = g') (H : h ≼ (g °° f)) `{funext:Funext} : *)
(*   transport (fun X => h ≼ (X °° f)) e H *)
(*   = H °H (transport (fun X => g °° f ≼ (X °° f)) e (rel_refl _)).  *)
(* Proof. *)
(*   destruct e. apply refl_H_bicat_preorder; auto.  *)
(* Defined. *)


(* (* Definition transport_match {A : Type} {x y y': TError A} (p : y = y') X  *) *)
(* (*   : transport (fun y => x ≼ y) p X = match x with Some _ =>  . *) *)
(* (* Proof. *) *)
(* (*   destruct p.  exact eq_refl. *) *)
(* (* Defined. *) *)

(* Definition transport_always_iso X Y Z (f: X ⇀ Y) (g g': Y ⇀ Z) (h: X ⇀ Z) *)
(*            (e : g ≼ g') (e' : g' ≼ g) (H : h ≼ (g °° f)) `{funext:Funext} : *)
(*   transport (fun X => h ≼ (X °° f)) (funext _ _ _ _ (always_iso e e')) H *)
(*   = H °H (preorder_app e f).  *)
(* Proof. *)
(*   rewrite transport_preorder; auto. *)
(*   apply (ap (fun X => H °H X)). clear H.  *)
(*   apply funext. unfold preorder_app, kleisli_comp. intro x. simpl. *)
(*   rewrite transport_forall.  *)
(*   (* destruct (f x). simpl. Focus 2. simpl. refine (transport_const _ _). *) *)
(*   (* etransitivity. *) *)
(*   (* set (P := fun X => g y ≼ X). simpl in P.  *) *)
(*   (* apply (@transport_funext Y (TError Z) g g' y (always_iso e e') P); auto. *) *)
(*   (* simpl. unfold always_iso. set (g y). *) *)
(* Admitted.  *)

(* Definition IsPartialEquiv_IsHProp X Y (f: X -> Y) *)
(*            `{funext:Funext} : IsHProp (IsPartialEquivK (clift f)). *)
(* Proof. *)
(*   intros H H'. *)
(*   unshelve eapply path_IsPartialEquivK. *)
(*   apply funext; unshelve apply always_iso; auto. *)
(*   apply IsPartialEquiv_IsHProp_fun; auto.  *)
(*   apply IsPartialEquiv_IsHProp_fun; auto. *)
(*   rewrite transport_always_iso. *)
(*   unfold preorder_app. unfold IsPartialEquiv_IsHProp_fun. *)
  
(* Admitted.  *)


Definition hor_comp_assoc (A B:HSet) (f g h i: A ⇀ B) 
  (e1 : f ≼ g) (e2 : g ≼ h) (e3 : h ≼ i) :
  (e1 °H e2) °H e3 = e1 °H (e2 °H e3).
Proof.
  apply funext.
  intro x. simpl. generalize (e1 x). clear e1.
  generalize (e2 x). clear e2.
  generalize (e3 x). clear e3.
  destruct (f x) as [fx|], (g x) as [gx|] , (h x) as [hx|]; simpl; intros r r0 r1; try inversion r0; try inversion r1; try reflexivity. 
  apply concat_pp_p.
Defined.
 
Definition IsConnection_IsHProp_iso {A B : HSet} (f: A -> B) (H H' : IsConnectionK (clift f))
           :
  IsConnection_IsHProp_fun f H H' °H IsConnection_IsHProp_fun f H' H = idK _. 
Abort.

(**
  Sanity Check: lifting an equivalance yields
  a partial equivalence in the Kleisli category
*)

Ltac etransitivity := eapply concat. 

(* =EquivToPartialEquivK= *)
Definition EquivToConnectionK (A B:HSet) (f :A -> B) :
  IsEquiv f -> IsConnectionK (clift f).
(* =end= *)
Proof.
  intro H.
  simple refine (Build_IsConnectionK _ _ _ (clift (e_inv f)) _ _).
  - intro x. exact (HoTT.ap Some (e_sect f x))^. 
  - intro x. exact (HoTT.ap Some (e_retr f x)). 
  (* - intro x. unfold compV. cbn.  *)
  (*   pose (e_adj f x). *)
  (*   rewrite e. clear e.  *)
  (*   rewrite concat_p1. *)
  (*   etransitivity. repeat rewrite dummy. eapply concat_cong. *)
  (*   apply transport_bind. reflexivity.  *)
  (*   etransitivity. symmetry. apply (ap_pp creturn (HoTT.ap f (e_sect f x)^) (ap f (e_sect f x))) . *)
  (*   etransitivity. *)
  (*   eapply (ap (HoTT.ap creturn)). unfold ap; simpl. rewrite <- ap_pp. *)
  (*   eapply (ap (HoTT.ap f)). symmetry. apply inverse_left_inverse. *)
  (*   etransitivity. eapply (ap (HoTT.ap creturn)). apply ap_1. *)
  (*   unfold creturn. refine (ap_1 _ _). *)
Defined.

Definition hfiber {A B} (f : A -> B) b := {a :A & f a = b}. 

Definition Im {A B} (f : A -> B) := {b : B & Trunc (hfiber f b)}. 

Definition restriction {A B} (f : A -> B) : A -> Im f :=
  fun a => (f a; tr (a; eq_refl)).

Definition ConnectionK_Im_fail_false {A B :HSet} (f :A -> B) (g : B -> TError A info_str)
           (H : creturn ≼ (g °° (clift f)))
           (b : Im f) c : g b.1 = Fail c -> False.
Proof.
  intro e. 
  refine (Trunc_ind_prop (fun _ => False) _ b.2).
  intros a. pose (r := H a.1).
  cbn in r. rewrite <- a.2 in e. rewrite e in r. inversion r. 
Defined.

Definition ConnectionK_To_Equiv_fun {A B : HSet} (f :A -> B) (g : B -> TError A info_str)
           (H : creturn ≼ (g °° (clift f)))
           (b : Im f) : {a:A & g b.1 = Some a}.
Proof.
  case_eq (g b.1).
  - intros a e. exact (a; eq_refl).
  - intros cast e. exact (match
      ConnectionK_Im_fail_false f g H b cast e
      return {a : A & Fail cast = Some a}
    with
                           end).
Defined. 

Instance Hprop_empty : IsHProp empty.
Proof.
  intros x y. destruct x.
Defined. 

Definition ConnectionK_To_Im_Dec {A B : HSet} (f :A -> B) (g : B -> TError A info_str)
           (H : creturn ≼ (g °° (clift f)))
           (H' : ((clift f) °° g) ≼ creturn) 
           b
  : Decidable (hprop (Trunc (hfiber f b))).
Proof. 
  case_eq (g b).
  - intros a e. apply inl, tr. exists a.
    pose (r := H' b). unfold kleisliComp in r; cbn in r. rewrite e in r.
    inversion r; reflexivity.
  - intros cast e. apply inr.
    intro hb. refine (Trunc_ind_prop (fun _ => empty) _ hb).
    clear hb; intros [a hb]. pose (r :=H a). cbn in r. rewrite hb in r.
    rewrite e in r. inversion r. 
Defined. 

Definition extendable_inverse {A B} (f :A -> B) := {H : IsEquiv (restriction f) & forall b, Decidable (hprop (Trunc (hfiber f b)))}.


(*
Definition IsConnectionK_To_Equiv {A B} {f :A -> B} (H : IsConnectionK (clift f)) : extendable_inverse f.
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _; _). 
  - intro b. exact (ConnectionK_To_Equiv_fun f _ (pc_sect (clift f)) b).1.
  - intro x. unfold compose, ConnectionK_To_Equiv_fun.
    cbn. set (pc_sect (clift f) x). cbn in *.    
    set (pc_inv (clift f) (f x)) in *.
    rewrite <- r. reflexivity.
  - intro y. unfold compose, restriction. 
    unshelve refine (path_sigma _ _ _ _ _); [idtac | apply is_hprop].
    destruct y as [y Hy]. cbn. unfold ConnectionK_To_Equiv_fun. simpl. 
    set (F := ConnectionK_Im_fail_false f (pc_inv (clift f)) 
                                          (pc_sect (clift f)) (y; Hy)).
    clearbody F. simpl in *. set ((pc_inv (clift f) y)) in *.
    generalize dependent F.
    pose (λ c0 : TError A,
                 ∀ (e : c = c0) (F : ∀ c1 : _, c0 = Fail A c1 → False),
                   f
                     (match c0 as c1 return (c0 = c1 → {a : A & c1 = Some a}) with
                      | Some a => λ _ : c0 = Some a, (a; eq_refl)
                      | Fail _ cast =>
                        λ e0 : c0 = Fail A cast,
                               match F cast e0 return {a : A & Fail A cast = Some a} with
                               end
                      end (e^@ e)) .1 = y).
    unshelve refine (TError_rect P _ _ c eq_refl); unfold P, c in *; intros; simpl. 
    pose (pc_retr (clift f) y). unfold kleisliComp in r; cbn in r.
    rewrite e in r. simpl in r. inversion r. reflexivity.
    exact (match
      ConnectionK_Im_fail_false f (pc_inv (clift f)) (pc_sect (clift f)) (y;Hy) i e
    with
            end).
  - apply (ConnectionK_To_Im_Dec _ (pc_inv (clift f))
                                   (pc_sect (clift f)) (pc_retr (clift f))).
Defined.


Definition ap_restriction {A B : Type} (f : A -> B) {x y : A} (p : x = y):
  (ap (restriction f) p)..1 = ap f p
  :=
    match p with eq_refl => eq_refl end.

Definition hprop_uip A {H : IsHProp A} (x:A) : is_hprop x x = eq_refl x. 
Proof.
Admitted. 
 

Definition EquivImToConnectionK {A B} {f :A -> B} (H : extendable_inverse f) : IsConnectionK (clift f).
Proof.
  destruct H as [H H'].
  simple refine (Build_IsConnectionK _ _ _ _ _ _ _).
  - intro b. destruct (H' b) as [t | n].
    + apply (Some (e_inv (restriction f) (b;t))).
    + refine (Fail _ (tr (String.EmptyString))). 
  - intro a. unfold kleisliComp. simpl.
    destruct (H' (f a)).
    + symmetry. apply (ap Some). 
      pose (e_sect (restriction f) a). cbn in *. 
      etransitivity; try exact e. unfold compose.
      apply (ap (e_inv (restriction f))).
      unshelve refine (path_sigma _ _ _ _ _); try reflexivity. 
      apply is_hprop.
    + destruct (n (tr (a;eq_refl))). 
  - intro b. unfold kleisliComp. simpl.
    destruct (H' b) as [t | n]; simpl.
    + apply (ap Some). exact (e_retr (restriction f) (b;t))..1.
    + exact I.
  - intro x. unfold compV, kleisliComp. cbn. 
    destruct (H' (f x)) as [t | n]; simpl.
    + repeat rewrite dummy. 
      pose (e_adj (restriction f) x).
      assert (t = tr (x;eq_refl)).
      apply is_hprop.
      rewrite H0. simpl. 
      unfold restriction in *. simpl in *. rewrite e. clear e H0. 
      rewrite concat_p1.
      etransitivity. repeat rewrite dummy. eapply concat_cong.
      apply transport_bind. reflexivity. 
      etransitivity. symmetry.
      refine (ap_pp creturn _ _). 
      etransitivity.
      eapply (ap (HoTT.ap creturn)). apply concat_cong. reflexivity.
      apply ap_restriction.
      etransitivity; try apply (ap_1 (f x) creturn).
      apply (HoTT.ap). etransitivity. symmetry. apply ap_pp.
      etransitivity; try apply (ap_1 _ f).
      apply HoTT.ap.
      rewrite concat_inv. rewrite hprop_uip. simpl. 
      (* etransitivity. eapply concat_cong. eapply concat_cong. *)
      (* reflexivity. etransitivity; try apply inv_1. *)
      (* apply (ap inverse). *)
      (* etransitivity; try apply (ap_1 _ (e_inv (λ a : A, (f a; tr (a; eq_refl))))). *)
      (* apply HoTT.ap. rewrite hprop_uip. reflexivity. *)
      rewrite concat_p1. symmetry; apply inverse_left_inverse.
    + destruct (n (tr (x;eq_refl))).
Defined.

Definition ConnectionK_To_Equiv_sect {A B} `{funext: Funext} (f :A -> B) (H : IsConnectionK (clift f)) : @pc_inv _ _ _ (EquivImToConnectionK (IsConnectionK_To_Equiv H)) = @pc_inv _ _ _ H.
Proof.
  apply funext. intro b. cbn.
  destruct (ConnectionK_To_Im_Dec f (pc_inv (clift f)) (pc_sect (clift f))
                                                                (pc_retr (clift f)) b).
  - pose (pc_retr (clift f) b). unfold ConnectionK_To_Equiv_fun.
    simpl. 
    generalize dependent r; unfold kleisliComp; cbn. 
    set (pc_inv (clift f) b); cbn.
    
    admit. 
  - pose (pc_retr (clift f) b).
    generalize dependent r; unfold kleisliComp; cbn. 
    destruct (pc_inv (clift f) b); simpl.
    intro e; inversion e. destruct (n (tr (a; H1))).
    intro; apply HoTT.ap. apply is_hprop. 
Abort.


*)
    
(**

we have a subset equivalence between [B] and [{C,P}]
if the type family [B] is isomorphic with a (computationally-relevant)
type [C] and a (computationally-irrelevant) relation [P], ie.

<<
     [B a ≅ { c : C & P a c }]
>>

Remarks:
 - [C] is non-dependent in [a : A], by definition.

 - Usually, [A] plays the role of the indices, [B] is an inductive
   family indexed over [A]. [C] are the "raw", computational terms
   while [P] is a validity predicate.

*)


Notation π1 := (@projT1 _ _). 


Instance HSet_HProp A `{IsHSet A} : forall (a b : A), IsHProp (a = b) :=
  fun a b => is_hprop (IsHProp := is_hset a b).

Definition sigT_HSet (A:HSet) (P : A -> HProp) : HSet.
Proof.
  refine (hset (sigT P)).
Defined. 

Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.


(* =to_subset= *)
Definition to_subset {C:HSet} {P} `{forall c, Decidable (P c)}: C ⇀ ({c:C & P c})
  := fun c =>
       match dec (P c) with
       | inl p => Some (c;p)
       | inr _ => Fail (_with ("subset conversion"))
       end.
(* =end= *)

Arguments check _ {_}.

(* =to_subsetC= *)
Definition to_subsetC {C:HSet} {P} `{forall c, Checkable (P c)}: C ⇀ ({c:C & P c})
  := fun c =>
       match dec (check (P c)) with
       | inl p => Some (c; convert p)
       | inr _ => Fail (_with ("subset conversion (Checkable)"))
       end.
(* =end= *)

(* =Decidable_PartialEquivK= *)
Instance Decidable_IsConnectionK (C:HSet) P `{forall c, Decidable (P c)}:
  IsConnectionK (clift π1 : {c:C & P c} ⇀ C).
(* =end= *)
Proof.
  unshelve refine ({| pc_inv := to_subset |}).
  - intro c. unfold kleisliComp. 
    unfold to_subset in *. simpl. 
    destruct dec; simpl;
      [ 
      | eauto ].
    simpl. unfold creturn. apply HoTT.ap. refine (path_sigma_uncurried _ _ _ _).
    exists eq_refl. apply is_hprop.
    destruct (n c.2).
  - intro c. unfold kleisliComp. 
    unfold to_subset in *. 
    destruct (dec (P c)); simpl;
      [ 
      |  eauto]. 
    reflexivity.  
    (* - intro. apply is_hprop. *)
    (* cbn. unfold kleisliComp. cbn. unfold apK, natK, assocK, idR. *)
    (* destruct x. cbn. simpl. apply is_hprop. destruct (to_subset x).  *)
    (* set (to_subset (π1 x)). *)
    (* match goal with | |- ?e = ?e' => set e; set e' end. *)
    (* destruct x. cbn in *. revert y; revert y0. destruct c.   *)
Defined.


Definition Decidable_ConnectionK  (C:HSet) P `{forall c, Decidable (P c)}:
  {c:C & P c} ≲K C :=
  {|  pc_fun :=  (clift π1 : {c:C & P c} ⇀ C) |}.

(* =Decidable_AntiPartialEquivK= *)
Instance Decidable_IsAntiConnectionK (C:HSet) P `{forall c, Checkable (P c)}:
  IsAntiConnectionK (clift π1 : {c:C & P c} ⇀ C).
(* =end= *)
Proof.
  unshelve refine ({| ac_inv := to_subsetC |}).
  - intro c. unfold kleisliComp. 
    unfold to_subsetC in *. simpl. 
    destruct dec; simpl;
      [ 
      | eauto ].
    simpl. unfold creturn. apply HoTT.ap. refine (path_sigma_uncurried _ _ _ _).
    exists eq_refl. apply is_hprop.
  - intro c. unfold kleisliComp. 
    unfold to_subsetC in *. 
    destruct (dec); simpl;
      [ |  eauto]. 
    reflexivity.  
Defined.


Definition Decidable_AntiConnectionK  (C:HSet) P `{forall c, Checkable (P c)}:
  {c:C & P c} ≲AK C :=
  {| ac_fun :=  (clift π1 : {c:C & P c} ⇀ C) |}.

(** ** Injective functions *)

(** This class is particularly useful to reflect constructors and take
advantage of their injectivity *)

(* =IsInjective= *)
Class IsInjective {A B : HSet} (f : A -> B) :=
   {  i_inv : B ⇀ A;
      i_sect : i_inv ° f == creturn ;
      i_retr : clift f °° i_inv ≼ creturn
   }.
(* =end= *)

Notation "f ^?-1" := (@i_inv _ _ f _) (at level 3, format "f '^?-1'").

Instance Injective_comp {A B C : HSet}
         (f : A -> B) (g : B -> C)
         `{IsInjective A B f} `{IsInjective B C g}:
  IsInjective (g ° f)
  := {| i_inv := (f^?-1 °° g^?-1) |}.
Proof.
  - unfold compose, kleisliComp. intro a.
    pose (i_sect (f:=g) (f a)). unfold compose in e.
    rewrite e.
    exact (i_sect (f:=f) a).
  - intros c. cbn.
    pose (r := i_retr (f:=g) c).
    unfold compose, kleisliComp in *.
    cbn in *.
    generalize dependent r. destruct (g^?-1 c) as [b|]; cbn in *; [| eauto].
    pose (r := i_retr (f:=f) b).
    unfold compose, kleisliComp in *.
    generalize dependent r. destruct (f^?-1 b); cbn in *; [| eauto].
    unfold clift. intros.
    apply HoTT.ap.
    inversion r0. inversion r. auto.
Defined.

(** *** Instances of IsInjective *)

(** The identity is an injection : *)

Definition IsInjective_id {A:HSet}: IsInjective (@id A).
Proof.
  simple refine (Build_IsInjective _ _ _ (@Some A _) _ _).
  intro a. reflexivity.
  intros a. reflexivity.
Defined.

(** The predecessor over natural numbers is a partial equivalence: *)

Definition S_inv (n: nat) :=
  match n with
    | O => Fail (_with "invalid index")
    | S n' => Some n'
  end.

Definition Hnat : HSet := hset nat.

Instance IsInjective_S: @IsInjective Hnat Hnat S :=
  {| i_inv := S_inv : Hnat ⇀ Hnat |}.
Proof.
  intro a. reflexivity.
  intros n. destruct n; cbn in *; eauto.
Defined.

(* Example *)

Inductive color : Type := Red | Black.

Inductive rbtree (A:Type) : color -> nat -> Type :=
| RBLeaf : rbtree A Black 0
| RedNode : forall n, rbtree A Black n -> A -> rbtree A Black n -> rbtree A Red n
| BlackNode : forall c1 c2 n, rbtree A c1 n -> A -> rbtree A c2 n -> rbtree A Black (S n).

Arguments RBLeaf {_}.
Arguments RedNode {_} _ _ _ _.
Arguments BlackNode {_} _ _ _ _ _ _.

Inductive tree (A: Type) : Type :=
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A
| Node' : tree A -> A -> tree A -> tree A.

Arguments Leaf {_}.
Arguments Node {_} _ _ _.
Arguments Node' {_} _ _ _.

Fixpoint rbtree_to_tree {A c n} (rbt : rbtree A c n) : tree A :=
  match rbt with
  | RBLeaf => Leaf
  | RedNode n t a t' => Node (rbtree_to_tree t) a (rbtree_to_tree t)
  | BlackNode _ _ n t a t' => Node' (rbtree_to_tree t) a (rbtree_to_tree t)
  end.

Fixpoint depth f {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node t1 _ t2 => S (f (depth f t1) (depth f t2))
  | Node' t1 _ t2 => S (f (depth f t1) (depth f t2))
  end.

Definition balanced A (t:tree A) : Prop := 2 * depth min t + 1 >= depth max t.

Require Import Vector VectorDef VectorSpec List. 

Definition vector := VectorDef.t.

Fixpoint vector_to_list A (n:nat):
  vector A n -> list A :=
  match n return vector A n -> list A with
  | O => fun _ => nil
  | S n => fun v => let IHn :=  vector_to_list A n (VectorDef.tl v) in
           (VectorDef.hd v) :: IHn end.

Definition embedding {A B} (f : A -> B) := forall x y, IsEquiv (@HoTT.ap A B f x y).

Definition vnil {A} := VectorDef.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := VectorDef.cons A val _ v.

Definition destruct_eq_list A (l l' : list A) x y : x :: l = y :: l' ->
                                                    prod (x = y) (l = l').
Proof.
  intros e. 
  set (ll := x ::l) in * ; set(ll' := y :: l') in *.
  replace x with (hd x ll) by reflexivity. 
  replace y with (hd x ll') by reflexivity.
  replace l with (tl ll) by reflexivity.
  replace l' with (tl ll') by reflexivity.
  destruct e. split;  reflexivity.
Defined. 


(*
Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with eq_refl => match q with eq_refl => eq_refl end end.

Definition ap3 {A A' A'' B:Type} (f:A -> A' -> A'' -> B) {x y:A} (p:x = y)
  {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'') : f x x' x''= f y y' y''
  := match p with eq_refl => match p' with eq_refl => match p'' with eq_refl => eq_refl end end end.

Definition vector_to_list_embedding A n : embedding (vector_to_list A n). 
Proof.
  intros v v'.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intro e. induction v.
    + simpl in *. unshelve refine (VectorDef.case0 _ _ _). reflexivity. 
    + simpl in *. specialize (IHv (VectorDef.tl v')).
      apply destruct_eq_list in e. destruct e as [ex el].
      etransitivity; try exact (VectorSpec.eta v')^. rewrite ex.
                     refine (ap _ _).
      apply (IHv el).
  - intro e; unfold compose; cbn.
    induction v; simpl in *.
    + destruct e. reflexivity.
    + set (H := ap (VectorDef.tl) e). simpl in H.
      specialize (IHv _ H). unfold H in *; clear H.
                                                 
      rewrite  (VectorSpec.eta v') in e. 
    destruct e. simpl. admit.
  - intro e; unfold compose; cbn.  
Abort.     

Axiom nat_irr : forall (n m : nat) (e e' : n = m), e = e'. 

Instance nat_hset : IsHSet nat.
Proof.
  intros x y e e'. apply nat_irr.
Defined. 

Definition Prop_vect_list A n (l: list A) :
  Trunc (hfiber (vector_to_list A n) l) -> length l = n.
Proof.
  apply (Trunc_ind_prop (fun _ => length l = n)); intros [v Hv].
  generalize dependent l; induction v; simpl in *; intros; subst. 
  - reflexivity. 
  - apply (ap S). apply IHv. reflexivity.
Defined. 

Fixpoint list_to_vector A (n:nat) l (H : length l = n) : Vector.t A n
  := match l return length l = n -> Vector.t A n with
     | nil => fun H => H # vnil
     | cons a l => fun H => H # vcons a (list_to_vector A (length l) l eq_refl)
     end H.

Definition transport_vector A n a (s:vector A n) k (e : n = k):
  HoTT.ap S e # vcons a s  = vcons a (e # s).
  destruct e. reflexivity.
Defined.

Definition Prop_vect_list_inv A n (l: list A) :
  length l = n -> Trunc (hfiber (vector_to_list A n) l).
Proof.
  intros e; apply tr. exists (list_to_vector _ _ l e).
  generalize dependent l. induction n.
  + intros l Hl.
    destruct l; try inversion Hl. reflexivity. 
  + intros l Hl.
    destruct l; try inversion Hl. simpl.  
    assert (Hl = ap S H0). apply nat_irr.  
    rewrite H in *. clear H Hl. simpl. 
    rewrite transport_vector. simpl. apply (ap (cons a)).
    destruct H0. apply IHn. 
Defined.   

 *)



