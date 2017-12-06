Require Import TErrorMonad Showable Decidable HoTT PartialOrder. 

Set Universe Polymorphism.


(** ** Monotone type-theoretic Galois connection *)

(* =IsPartialEquiv= *)
Class IsConnection {A B} `{IsPartialOrder_pp A} `{IsPartialOrder_pp B} 
      (f: A --> B) := { 
    c_inv:  B --> A;
    c_sect: id ≼  c_inv ° f ;
    c_retr: f ° c_inv ≼ id;
}.
(* =end= *)

Arguments c_inv {_ _ _ _} _ {_}.
Arguments c_sect {_ _ _ _} _ {_} _.
Arguments c_retr {_ _ _ _} _ {_} _.

(* =CanonicalPartialEquiv= *)
Class Connection A B `{IsPartialOrder_pp A} `{IsPartialOrder_pp B} := {
    c_fun: A --> B ;
    c_isconn:> IsConnection c_fun
}.
Notation "A ≲ B" := (Connection A B)
(* =end= *)
                       (at level 20).

(* =IsConnectionIsHProp= *)
Instance IsConnectionIsHProp A B
         `{IsPartialOrder_pp A}`{IsPartialOrder_pp B}(f: A --> B): 
           IsHProp (IsConnection f).
(* =end= *)
Proof.
  intros g g'. destruct g, g'.
  assert (c_inv0 = c_inv1).
  { 
    destruct c_inv0, c_inv1.
    assert (f_ord = f_ord0). 
    {
      apply rel_antisym.
      - intro x. eapply rel_trans. apply c_sect1. simpl. apply mon0. apply c_retr0.
      - intro x. eapply rel_trans. apply c_sect0. simpl. apply mon. apply c_retr1.
    }
    subst.
    assert (mon = mon0) by apply is_hprop.
    assert (p_mon = p_mon0) by apply is_hprop. 
    subst. reflexivity.
  }
  subst. 
  assert (c_sect0 = c_sect1) by apply is_hprop. 
  assert (c_retr0 = c_retr1) by apply is_hprop. 
  subst. reflexivity. 
Defined. 

(** ** Monotone type-theoretic partial Galois connection  *)

(**

A monotone function [f: A → B] defines a partial coercion
[PartialConnection] if some of the [b: B] maps back to the same [a: A]
they come from. Think of [A] as being a refinement of [B] and [f] as
dropping the refinement: not all [B]'s are valid [A]'s but the one
which are can easily be mapped back to [A].

 *)


(* =IsPartialEquivK= *)
Class IsConnectionK {A B: HSet} (f: A ⇀ B) := {
    pc_inv:  B ⇀ A;
    pc_sect: creturn ≼ pc_inv °° f;
    pc_retr: f °° pc_inv ≼ creturn ;
}.
(* =end= *)

Arguments pc_inv {_ _} _ {_}.
Arguments pc_sect {_ _} _ {_} _.
Arguments pc_retr {_ _} _ {_} _.

(* =PartialEquivK= *)
Record ConnectionK (A B: HSet) := {
  pc_fun: A ⇀ B ;
  pc_isconn: IsConnectionK pc_fun
}.
Notation "A ≲K B" := (ConnectionK A B)
(* =end= *)
                        (at level 20).

Arguments pc_fun {_ _} _ _.
Arguments pc_isconn {_ _ _}.

(* =IsPartialEquiv= *)
Class IsAnticonnection {A B} 
      `{IsPartialOrder_pp A} `{IsPartialOrder_pp B} (f: A --> B) := { 
    ac_inv:  B --> A;
    ac_sect: ac_inv ° f ≼ id ;
    ac_retr: f ° ac_inv ≼ id;
}.
(* =end= *)

Arguments ac_inv {_ _ _ _} _ {_}.
Arguments ac_sect {_ _ _ _} _ {_} _.
Arguments ac_retr {_ _ _ _} _ {_} _.

(* =CanonicalPartialEquiv= *)
Class Anticonnection A B `{IsPartialOrder_pp A} `{IsPartialOrder_pp B} :=
  {  ac_fun: A --> B ;
     ac_isconn:> IsAnticonnection ac_fun
  }.
Notation "A ≈ B" := (Anticonnection A B)
(* =end= *)
                       (at level 20).


(* =IsAPartialEquivK= *)
Class IsAnticonnectionK {A B: HSet} (f: A ⇀ B) :=
  { apc_inv:  B ⇀ A;
    apc_sect: apc_inv °° f ≼ creturn;
    apc_retr: f °° apc_inv ≼ creturn ;
}.
(* =end= *)

Arguments apc_inv {_ _} _ {_}.
Arguments apc_sect {_ _} _ {_} _.
Arguments apc_retr {_ _} _ {_} _.


(* =APartialEquivK= *)
Record AnticonnectionK (A B: HSet) := {
  apc_fun: A ⇀ B ;
  apc_isconn: IsAnticonnectionK apc_fun
}.
Notation "A ≈K B" := (AnticonnectionK A B)
(* =end= *)
                        (at level 20).

Arguments apc_fun {_ _} _ _.
Arguments apc_isconn {_ _ _}.

(**
  Sanity Check: lifting an equivalance yields
  a partial equivalence in the Kleisli category
*)

Ltac etransitivity := eapply concat. 

(* =EquivToPartialEquivK= *)
Definition EquivToConnectionK (A B: HSet) (f: A -> B) :
  IsEquiv f -> IsConnectionK (clift f).
(* =end= *)
Proof.
  intro H.
  simple refine (Build_IsConnectionK _ _ _ (clift (e_inv f)) _ _).
  - intro x. exact (HoTT.ap Some (e_sect f x))^. 
  - intro x. exact (HoTT.ap Some (e_retr f x)). 
Defined.


    
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


(* conversion between coercion and anticoercion *)

(* =Coercion_AntiCoercion= *)
Definition Connection_Anticonnection (A B: HSet) : A ≲K B -> A ≈K B.
(* =end= *)
Proof. 
  intro H; unshelve econstructor.
  - exact (pc_fun H). 
  - unshelve econstructor.
    + refine (pc_inv (pc_fun H)). exact pc_isconn. 
    + intro a. pose (foo := @pc_sect _ _ (pc_fun H) pc_isconn a). cbn in *.
      clearbody foo. revert foo.
      destruct ((pc_inv (pc_fun H)) °° (pc_fun H) a). symmetry. exact foo. 
      intro; exact I.
    + exact (pc_retr (pc_fun H)). 
Defined.

Instance Connection_IsAnticonnectionK (A B: HSet) 
  (H : A ≈K B) : IsAnticonnectionK (apc_fun H) := apc_isconn.

(* =AntiCoercion_Coercion= *)
Definition Anticonnection_Connection (A B: HSet) (H : A ≈K B):
           creturn ≼ (apc_inv (apc_fun H)) °° (apc_fun H) -> A ≲K B.
(* =end= *)
Proof. 
  intro H'; unshelve econstructor.
  - exact (apc_fun H). 
  - unshelve econstructor.
    + exact (apc_inv (apc_fun H)). 
    + exact H'.
    + exact (apc_retr (apc_fun H)). 
Defined.

Instance Connection_Anticonnection_K (A B: Type)
         `{IsPartialOrder_pp A} `{IsPartialOrder_pp B}
         (H : A ≈ B) (H' : id ≼ (ac_inv ac_fun) ° (@ac_fun _ _ _ _ H)) :
  A ≲ B.
Proof. 
  destruct H1; unshelve econstructor; try solve [auto]. 
  destruct ac_isconn; unshelve econstructor; try solve [auto].
Defined. 

Instance Anticonnection_Connection_K (A B: Type)
         `{IsPartialOrder_pp A} `{IsPartialOrder_pp B}
         (H : A ≲ B) (H' : (c_inv c_fun) ° (@c_fun _ _ _ _ H) ≼ id ) :
  A ≈ B.
Proof. 
  destruct H1; unshelve econstructor; try solve [auto]. 
  destruct c_isconn; unshelve econstructor; try solve [auto].
Defined. 


Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.

(* =to_subset= *)
Definition to_subset {C: HSet} {P} `{forall c, Checkable (P c)}: C ⇀ ({c:C & P c})
  := fun c =>
       match dec (check (P c)) with
       | inl p => Some (c; convert p)
       | inr _ => Fail (_with ("subset conversion"))
       end.
(* =end= *)


Instance Checkable_IsAnticonnectionK (C: HSet) P `{forall c, Checkable (P c)}:
  IsAnticonnectionK (clift π1: {c: C & P c} ⇀ C).
Proof.
  unshelve refine ({| apc_inv := to_subset |}).
  - intro c. unfold kleisliComp. 
    unfold to_subset in *. simpl. 
    destruct dec; simpl;
      [ 
      | eauto ].
    simpl. unfold creturn. apply HoTT.ap. refine (path_sigma_uncurried _ _ _ _).
    exists eq_refl. apply is_hprop.
  - intro c. unfold kleisliComp. 
    unfold to_subset in *. 
    destruct (dec); simpl;
      [ |  eauto]. 
    reflexivity.  
Defined.

(* =Checkable_AntiPartialEquivK= *)
Definition Checkable_AnticonnectionK  (C:HSet) P `{forall c, Checkable (P c)}:
  {c:C & P c} ≈K C :=
  {| apc_fun :=  clift π1 : {c:C & P c} ⇀ C |}.
(* =end= *)

(* =Decidable_ConnectionK= *)
Definition Decidable_ConnectionK  (C:HSet) P `{forall c, Decidable (P c)}:
  {c:C & P c} ≲K C.
(* =end= *)
Proof.
  unshelve eapply Anticonnection_Connection.
  - apply Checkable_AnticonnectionK; typeclasses eauto.
  - intro c. unfold kleisliComp. 
    cbn. unfold to_subset in *. simpl. 
    destruct dec; simpl;
      [ 
      | eauto ].
    simpl. unfold creturn. apply HoTT.ap. refine (path_sigma_uncurried _ _ _ _).
    exists eq_refl. apply is_hprop.
    destruct (n c.2).
Defined.




(** ** Injective functions *)

(** This class is particularly useful to reflect constructors and take
advantage of their injectivity *)

(* =IsInjective= *)
Class IsInjective {A B: HSet} (f: A -> B) := {
    i_inv: B ⇀ A;
    i_sect: i_inv ° f == creturn ;
    i_retr: (clift f) °° i_inv ≼ creturn
}.
(* =end= *)

Notation "f ^?-1" := (@i_inv _ _ f _) (at level 3, format "f '^?-1'").

Instance Injective_comp {A B C : HSet}
         (f : A -> B) (g : B -> C)
         `{IsInjective A B f} `{IsInjective B C g}:
  IsInjective (g ° f)
  := {| i_inv := (f^?-1 °° (g^?-1)) |}.
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
Definition IsInjective_id {A:HSet}: IsInjective (fun x:A => x).
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

Instance IsInjective_S: @IsInjective Hnat Hnat S :=
  {| i_inv := S_inv : Hnat ⇀ Hnat |}.
Proof.
  intro a. reflexivity.
  intros n. destruct n; cbn in *; eauto.
Defined.