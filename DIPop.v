Require Import String Showable Connection DepEquiv Decidable HODepEquiv HoTT.
Require Import Vector List.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).
 
Arguments length {_} l.

Set Universe Polymorphism.

Instance Vector_HSet A {HA:DecidablePaths A} n : IsHSet (Vector.t A n).
apply Hedberg. revert n. 
assert (forall (n n' : Hnat) (e:n=n') (v: Vector.t A n) (v' : Vector.t A n'),
           (transport (Vector.t A) e v = v') + not (transport (Vector.t A) e v = v')).
intros n n' e v. revert n' e.
induction v; destruct v';
  try assert (He : e = eq_refl) ; try apply is_hprop; subst; cbn; try exact (inl eq_refl); inversion e.
subst. 
try assert (He : e = eq_refl) ; try apply is_hprop; subst; cbn.
destruct (dec_paths h h0) as [ e | n].  destruct e. 
specialize (IHv _ eq_refl v'). destruct IHv.
cbn in e. subst. exact (inl eq_refl).
right. intro H; apply n. cbn. apply cons_inj in H. destruct H. exact H0. 
right. intro H; apply n. cbn. apply cons_inj in H. destruct H. exact H. 
intros;  apply (X _ _ eq_refl). 
Defined. 

Definition vector A `{HA:DecidablePaths A} : Hnat -> HSet := fun n => hset (Vector.t A n).
Definition vnil {A} := Vector.nil A.
Definition vcons {A} `{HA:DecidablePaths A} {n} (val:A) (v:vector A n) := Vector.cons A val _ v.
  
   
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

Fixpoint vector_to_list {A} (n:nat):
  Vector.t A n -> {l : list A & clift (length (A:=A))  l = Some n} :=
  match n return Vector.t A n -> {l : list A & clift (length (A:=A))  l = Some n} with
  | O => fun _ => (nil; eq_refl)
  | S n => fun v => let IHn :=  vector_to_list n (Vector.tl v) in
           ((Vector.hd v) :: IHn.1 ; ap _ (ap S (Some_inj (IHn.2)))) end.

Definition list_to_vector {A} `{HA:DecidablePaths A} (n:nat) : {l : list A & clift (length (A:=A)) l = Some n} -> Vector.t A n.
  destruct 1 as [l H]. generalize dependent n. induction l; simpl; intros.
  - exact (Some_inj H # vnil).
  - exact (Some_inj H # vcons a (IHl (length l) eq_refl)). 
Defined.

Definition transport_vector A `{HA:DecidablePaths A} n a (s:vector A n) k (e : n = k):
  ap S e # vcons a s  = vcons a (e # s).
  destruct e. reflexivity.
Defined.

Definition S_length :
  forall (A : Type) (l : list A) (n: nat),
    length l = S n -> length (tail l) = n.
  intros; induction l; inversion H; simpl; reflexivity.
Defined.

Definition list A  `{DecidablePaths A} := {| _typeS := list A |} : HSet.

(* =DepEquiv_vector_list_simpl= *)
Instance DepEquiv_vector_list_nat: vector Hnat ≲K□ list Hnat  :=
  DepConnection_eq (vector Hnat) (list Hnat) (clift length)
                 vector_to_list list_to_vector.
(* =end= *)
Proof.
   - intro n. (* Sect (nvector_to_nlist a) (nlist_to_nvector a) *)
     (* XXX: this proof is not manageable at the next truncation level *)
    induction n.
    + intro v; induction v using Vector.case0.
      reflexivity.
    + intro v; induction n, v using Vector.caseS.
      unfold compose in *; simpl in *. unfold creturn. 
      rewrite Some_inj_sect. rewrite (transport_vector Hnat). 
      apply ap. specialize (IHn t). destruct (vector_to_list n t).
      simpl in *. inversion e.
      assert (e = ap Some H0) by apply is_hprop. subst.
      reflexivity.
  - intro n.  (* Sect (nlist_to_nvector a) (nvector_to_nlist a) *)
    (* XXX: this proof is not manageable at the next truncation level *)
    induction n.
    + intro rl. simpl. destruct rl as [l Hl].
      unfold compose; simpl.
      destruct l; try inversion Hl.
      refine (path_sigma_uncurried _ _ _ _).
      simple refine (existT _ _ _). reflexivity. apply is_hprop.
    + intro rl. destruct rl as [l Hl].
      destruct l; try inversion Hl.  
      specialize (IHn (l;ap Some H0)). refine (path_sigma_uncurried _ _ _ _).
      simple refine (existT _ _ _). simpl. simpl in Hl.
      assert (Hl = ap Some (ap S H0)) by apply is_hprop.
      rewrite H. rewrite Some_inj_sect, (transport_vector Hnat). apply ap.
      destruct H0. exact IHn..1. apply is_hprop. 
  - intros n v.
    induction n. reflexivity. simpl. unfold clift. apply ap.
    specialize (IHn(Vector.tl v)). inversion IHn. simpl. apply ap. assumption. 
Defined.
    
(** ** Monadic Liftings *)

Arguments Vector.map {_ _} _ _ _. 
Arguments Vector.tl {_} _ _. 

(** We simply lifting the domain *)

(* =map_list= *)
Definition map_list (f: Hnat -> Hnat): list Hnat ⇀ list Hnat := lift (Vector.map f).
(* =end= *)

(* =pop= *)
Definition pop: list Hnat ⇀ list Hnat := 
    lift (Vector.tl: forall n:Hnat, @vector Hnat DecidablePaths_nat (S n) -> vector Hnat n).
(* =end= *)

Eval compute in (pop (2::3::nil)).

(* =vpop= *)
Definition vpop: forall n: Hnat, vector Hnat (S n) ⇀ vector Hnat n :=
    unlift (B_1 := λ n : Hnat, vector Hnat (S n)) (List.tl (A := Hnat)).
(* =end= *)

Eval compute in (vpop _ (vcons (2: Hnat) (vcons (3: Hnat) vnil))).

