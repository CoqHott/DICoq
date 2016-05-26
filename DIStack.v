Set Universe Polymorphism.
Require Import Showable String Decidable List DepEquiv HODepEquiv HoTT.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).


(** * Dependent Stack/Instr *)

(** A [dstack] is a bunch of nested pairs of depth [n] *)

Fixpoint dstack (n : nat) : Type :=
  match n with
    | O => unit 
    | S n' => nat * dstack n'
  end%type.

(** The dependent instructions [dinstr] are explicit about their
effect on the depth of the dstack *)

Inductive dinstr : nat -> nat -> Type :=
| IConst : forall (k:nat) {n}, dinstr n (S n)
| IPlus : forall {n}, dinstr (S (S n)) (S n).

(** The stach machine satisfies those depth invariants **)

Definition exec n n' (i : dinstr n n') : dstack n -> dstack n' :=
  match i with
    | IConst n => fun s => (n, s)
    | IPlus => fun s =>
                  let '(arg1, (arg2, s')) := s in (* note the direct pattern match *)
                  (arg1 + arg2, s')
  end.


Eval compute in exec 1 _ (IConst 1) (2,tt).
Eval compute in exec 2 _ IPlus (2, (1, tt)).
(* bad use does not type check: the given dstack is not of depth 2 *)
(* Eval compute in exec 2 _ (IPlus _) (1, tt). *)


(** ** Plain [stack] & [instr] *)

(** There is no need to define plain [dstacks]: we just use lists of
   nats, with a condition on their length.

   Plain instructions are another inductive, with its [Show] instance,
   and the condition is expressed with the [valid_instr] predicate
   below (which is decidable).  *)

Inductive instr@{i} : Type@{i} :=
| NConst : nat -> instr
| NPlus  : instr.

Instance show_instr : Show instr :=
  {| show s := 
       match s with
         | NConst n => "NConst " ++ show n
         | NPlus => "NPlus"
       end
  |}.

Definition instr_index n (i:instr) : Cast nat :=
  match i with
    | NConst _ => creturn (S n)
    | NPlus => match n with
                 | S (S n) => creturn (S n)
                 | _ => Fail _ (Cast_info_wrap "invalid instruction" nat)
               end
  end.


(** ** Equivalences *)

(** [dstack] is equivalent to lists through
<<
  {n:nat & dstack n} ~ {l : list nat & length l = n} 
>> 
*)

Definition dstack_to_list {n} : dstack n -> {l : list nat & clift (info := Cast_info) (length (A:=nat)) l = Some n}.
  intro s; induction n.
  - exact (nil; eq_refl).
  - exists (fst s :: (IHn (snd s)).1). unfold clift. apply ap. simpl. apply ap. 
    pose ((IHn (snd s)).2). simpl in e. inversion e. auto.
Defined.

(* Or equivalently, as a program: *)
(*
Definition dstack_to_list : forall {n}, dstack n -> {l : list nat & clift (length (A:=nat)) l = Some n}.
fix 1.
refine (fun n =>
          match n with
            | 0 => fun _ => (nil; _)
            | S n => fun s =>
                       let (x, s) := s in
                       let (l, q) := dstack_to_list n s in
                       (x :: l; _)
          end); eauto.
inversion_clear q; unfold clift, length; auto.
Defined.
*)

Definition list_to_dstack {n} : {l : list nat & clift (info := Cast_info) (length (A:=nat)) l = Some n} -> dstack n.
  destruct 1 as [l H]. generalize dependent n; induction l; cbn in *; intros. 
  - inversion H. exact tt.
  - specialize (IHl (length l) eq_refl). inversion H. exact (a,IHl).
Defined.

Definition Hlist A  `{DecidablePaths A} := {| _typeS := list A |} : HSet.

Instance DepEquiv_dstack :
  dstack ≈ (Hlist nat) :=
  @DepEquiv_eq _ _ (Hlist nat) _ _ (clift (length (A:=nat))) (@dstack_to_list) (@list_to_dstack) _ _ _.
{ unfold compose. intro n. 
  induction n; intro s; simpl. 
  - destruct s. reflexivity.
  - destruct s as [a s]. simpl. 
    specialize (IHn s). unfold compose in IHn. simpl in *.
    destruct (dstack_to_list s). 
    simpl in *. inversion e.
    assert (e = ap Some H0). apply is_hprop. subst. simpl in *.
    refine (path_prod_uncurried _ _ _); split; try reflexivity.
    simpl. exact IHn. 
 }
{ - intros n [l e]. unfold compose.  generalize dependent n.
    induction l; intros. 
    + inversion e. simpl. assert (e = ap Some H0). apply is_hprop. subst.
      reflexivity.
    + specialize (IHl (length l) eq_refl). 
      inversion e. assert (e = ap Some H0). apply is_hprop. subst.
      simple refine (path_sigma _ _ _ _ _). simpl. apply ap.
      exact IHl..1. apply is_hprop. }
{ intro n; induction n. reflexivity. intro s; simpl. unfold clift.
  apply ap. simpl. apply ap. specialize (IHn (snd s)). inversion IHn; eauto. }
Defined.

(** [dinstr] is equivalent to [instr] through
<<
 {n n': nat & dinstr n n'} ~ {i: instr & valid_instr n i n'}
>>
*)

Definition valid_instr i n n' := instr_index n i = Some n'.

Definition dinstr_to_instr n n' :
  dinstr n n' -> {i: instr & valid_instr i n n'} := fun i =>
  match i with                                                      
    IConst k => (NConst k; eq_refl)
  | IPlus    => (NPlus; eq_refl) end.

Definition Fail_is_not_Some {A info i R} {x:A} :
  @Fail A info i = Some x -> R. 
    inversion 1.
Defined.

Definition instr_to_dinstr n n' :
  {i: instr & valid_instr i n n'} -> dinstr n n' := fun x =>
match x with (i;v) => match i return valid_instr i n n' → dinstr n n' with
  (* to provide : Some (S n) = Some n' => dinstr n n' *)
  | NConst k => fun v => transport (fun X => dinstr _ X) (Some_inj v) (IConst k)
  | NPlus    => match n return valid_instr NPlus n n' → dinstr n n'
     with
  (* to provide : None = Some n' -> dinstr 0 n' *)
       0 => fun v => Fail_is_not_Some v
  (* to provide :  None = Some n' -> dinstr 1 n' *)
     | S 0 => fun v => Fail_is_not_Some v
  (* to provide : Some (S n) = Some n' => dinstr (S (S n)) n' *)
     | S (S n) => fun v => transport (fun X => dinstr _ X) (Some_inj v) (IPlus) end end v end.

Instance DecidablePaths_instr : DecidablePaths instr.
econstructor. intros x y. destruct x, y.
- case (dec (n = n0)); intro e; subst. 
  + exact (inl eq_refl).
  + apply inr. intro H. apply e. inversion H. reflexivity. 
- apply inr. intro H; inversion H.
- apply inr. intro H; inversion H.
- exact (inl eq_refl).   
Defined.

Definition transport_instr_Const (n m n0 : nat) (e : S n = m) :
   dinstr_to_instr _ _
     (transport (λ X : nat, dinstr n X) e (IConst n0)) =
   (NConst n0; ap Some e).
     destruct e. reflexivity.
Defined.

Definition transport_instr_Plus (n m : nat) (e : S n = m) :
   dinstr_to_instr _ _
     (transport (λ X : nat, dinstr (S (S n)) X) e IPlus) =
   (NPlus; ap Some e).
     destruct e. reflexivity.
Defined.

Definition DepEquiv_instr_retr n m (x:{i:instr & instr_index n i = Some m}) :
  (dinstr_to_instr _ _) ° (instr_to_dinstr _ _) x = x :=
  match x with (i;v) =>
          match i return forall v :valid_instr i n m,
              (dinstr_to_instr _ _) ° (instr_to_dinstr _ _) (i; v) = id (i; v) with
(* |- creturn (S n) = Some m -> 
      dinstr_to_instr n m (Some_inj v # IConst n0) (NConst n0; v) = (NConst n0; v) *)
   NConst n0 => fun v => transport_instr_Const _ _ _ _ @
                        path_sigma _ (NConst n0; ap (Some (A:=nat)) (Some_inj v))
                                     (NConst n0; v) eq_refl (is_hprop _ _)
 | NPlus => match n return ∀ v : valid_instr NPlus n m,
                (dinstr_to_instr _ _) ° (instr_to_dinstr _ _) (NPlus; v) = (NPlus; v)
            with
(* |- Fail nat "wrong argument" nat = Some m -> 
      dinstr_to_instr 0 m (Fail_is_not_Some v) = (Nplus; v) *)
              0 => fun v => Fail_is_not_Some v
(* |- Fail nat "wrong argument" nat = Some m -> 
      dinstr_to_instr 1 m (Fail_is_not_Some v) = (Nplus; v) *)
            | S 0 => fun v => Fail_is_not_Some v
(* |- creturn (S n) = Some m -> 
      dinstr_to_instr (S (S n)) m (Some_inj v # IPlus) = (NPlus; v) *)
            | S (S n) => fun v => transport_instr_Plus _ _ _ @
                               path_sigma _ (NPlus; ap (Some (A:=nat)) (Some_inj v))
                               (NPlus; v) eq_refl (is_hprop _ _) end
            end v end.

Definition Hinstr := {| _typeS := instr |} : HSet.

Instance DepEquiv_instr n :
  (dinstr n) ≈ Hinstr
  :=
    @DepEquiv_eq _ _ Hinstr _ _
                 (instr_index n)
                 (dinstr_to_instr n) 
                 (instr_to_dinstr n) _ _ _.
{intros m x. destruct x; reflexivity. }
{ apply DepEquiv_instr_retr. }
{ intros m i. destruct n, i; cbn; reflexivity. }
Defined.

(** ** Lifting *)

(** Lifting exec to safely accept instr and list nat **)

Definition simple_exec : Hinstr → Hlist nat ⇀ Hlist nat := lift2 exec.

Arguments lift2 {_ _ _ _ _ _ _ _ } _ _ _ _.

(* Pretty Printing of safe_exec *)

Arguments HODepEquiv {_ _ _}  _ {_ _} _.
Arguments HODepEquiv2 {_ _ _ _ _ _ _ _}  _ _.
Arguments HODepEquiv2_sym {_ _ _ _ _ _ _ _} _. 
Print simple_exec. 

(*
Definition sanity_check : simple_exec =
          fun  (i : instr) (l : list nat) =>
          b <- (c' <- to_subset l; Some (list_to_dstack c'));
          a <- instr_index (Datatypes.length l) i;
          b0 <- (c' <- to_subset i;
               Some (instr_to_dinstr (Datatypes.length l) a c'));
          Some (dstack_to_list (exec (Datatypes.length l) a b0 b)) .1:=
  eq_refl.
*)

Eval compute in simple_exec NPlus (1 :: 2 :: nil).
Eval compute in simple_exec NPlus (1 :: nil).

Print Assumptions simple_exec.

(** ** Extraction *)

Require Import ExtrOcamlString ExtrOcamlNatInt.
Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction "didstack" exec simple_exec.

(** 
<<
$ ocaml -init didstack.ml
# (exec 0 0 (IPlus 0) [1;2] : int list);;
- : int list = [3]
# exec 0 0 (IPlus 0) [];;
Segmentation fault: 11 
>>
 *)

(**
<< 
$ ocamlc didstack.mli didstack.ml
# #load "didstack.cmo";;
# open Didstack;;
# simple_exec NPlus [1;2];;
- : int list = [3]                                                                              
# simple_exec NPlus [];;
Exception: (Failure "Cast failure: invalid instruction").   
>>
 *)

(* to run exec in compiled mode, need to use coercions *)

