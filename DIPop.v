Require Import String Showable Equiv DepEquiv Decidable HODepEquiv HoTT.
Require Import Vector List.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).
 

Set Universe Polymorphism.

Definition vector A := Vector.t A.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.
  
   
(** * Pop from list *)

(** This example is taken from the "Dependent Interoperability"
paper. The objective is to cast a simply-typed pop to a precise type
on indexed vectors. *)

Definition pop' {A} (l: list A): list A :=
  match l with
    | nil => nil
    | x :: l' => l' 
  end.

Definition bad_pop {A} (l: list A): list A :=
  match l with
    | nil => nil
    | x :: l' => l  (* a bad implementation *)
  end.


(** ** Type equivalence *)

(** We establish the following equivalence:
<<
 {n:nat & Vector.t A n} ~ {l : list A & length l = n}
>>
*)

Fixpoint vector_to_list A (n:nat):
  Vector.t A n -> {l : list A & clift (length (A:=A))  l = Some n} :=
  match n return Vector.t A n -> {l : list A & clift (info:=Cast_info) (length (A:=A))  l = Some n} with
  | O => fun _ => (nil; eq_refl)
  | S n => fun v => let IHn :=  vector_to_list A n (Vector.tl v) in
           ((Vector.hd v) :: IHn.1 ; ap _ (ap S (Some_inj (IHn.2)))) end.

Definition list_to_vector A (n:nat) : {l : list A & clift (info := Cast_info) (length (A:=A)) l = Some n} -> Vector.t A n.
  destruct 1 as [l H]. generalize dependent n. induction l; simpl; intros.
  - exact (Some_inj H # vnil).
  - exact (Some_inj H # vcons a (IHl (length l) eq_refl)). 
Defined.

Definition transport_vector A n a (s:vector A n) k (e : n = k):
  ap S e # vcons a s  = vcons a (e # s).
  destruct e. reflexivity.
Defined.

Definition S_length :
  forall (A : Type) (l : list A) (n: nat),
    length l = S n -> length (tail l) = n.
  intros; induction l; inversion H; simpl; reflexivity.
Defined.

 
Instance DepEquiv_vector_list_simpl A `{Show A} `{DecidablePaths A}  :
  (vector A) ≈ list A  :=
  @DepEquiv_eq nat (vector A) (list A) _ _ _ (clift (length (A:=A)))
              (vector_to_list A) (list_to_vector A) _ _ _.
Proof.
   - intro n. (* Sect (nvector_to_nlist a) (nlist_to_nvector a) *)
    induction n.
    + intro v. apply Vector.case0. reflexivity.
    + intro v. revert IHn. 
      refine (Vector.caseS (fun n v => (∀ x : vector A n, list_to_vector A n (vector_to_list A n x) = x)
                                                            → list_to_vector A (S n) (vector_to_list A (S n) v) = v) _ _).
      clear. intros. simpl. rewrite Some_inj_sect. 
      rewrite transport_vector.
      apply ap. specialize (H t). destruct (vector_to_list A n t).
      simpl in *. inversion e.
      assert (e = ap Some H1). apply is_hprop. subst.
      reflexivity.
  - intro n.  (* Sect (nlist_to_nvector a) (nvector_to_nlist a) *)
    induction n.
    + intro rl. simpl. destruct rl as [l Hl].
      destruct l; try inversion Hl.
      refine (path_sigma_uncurried _ _ _ _).
      simple refine (existT _ _ _). reflexivity. apply is_hprop.
    + intro rl. destruct rl as [l Hl].
      destruct l; try inversion Hl.  
      specialize (IHn (l;ap Some H2)). refine (path_sigma_uncurried _ _ _ _).
      simple refine (existT _ _ _). simpl. simpl in Hl.
      assert (Hl = ap Some (ap S  H2)) by apply is_hprop.
      rewrite H1. rewrite Some_inj_sect, transport_vector. apply ap.
      destruct H2. exact IHn..1. apply is_hprop. 
  - intros n v.
    induction n. reflexivity. simpl. unfold clift. apply ap.
    specialize (IHn(Vector.tl v)). inversion IHn. simpl. apply ap. assumption. 
Defined.


    
(** ** Monadic Liftings *)

Arguments Vector.map {_ _} _ _ _. 
Arguments Vector.tl {_} _ _. 

(** We simply lifting the domain *)

Definition map_list (f : nat -> nat) : list nat ⇀ list nat :=
  lift (Vector.map f).

Definition pop : list nat ⇀ list nat := lift (Vector.tl).

Eval compute in (pop nil).

