Set Universe Polymorphism.
Require Import Showable String Decidable List DepEquiv HODepEquiv HoTT.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).

Arguments length {_} l.

(** * Dependent Stack/Instr *)

(** A [dstack] is a bunch of nested pairs of depth [n] *)

Section TypeScopeSection.
Local Open Scope type.
(* =dstack= *)
Fixpoint dstack (n: Hnat): Type :=
  match n with
    | O => unit 
    | S n' => nat * dstack n'
  end.
(* =end= *)
Local Close Scope type.
End TypeScopeSection.



Definition Decidable_eq_dstack n : forall (x y : dstack n), (x = y) + not (x = y).
  intros x y. induction n; cbn in *.
  - left. destruct x, y; reflexivity.
  - destruct x as (nx,x), y as (ny,y). case (Decidable_eq_nat nx ny).
    + destruct 1. case (IHn x y).
      * destruct 1. left. reflexivity.
      * right. intro H. apply n0. inversion H. reflexivity.
    + right. intro H. apply n0. inversion H. reflexivity.
Defined. 

Instance dstack_HSet n : IsHSet (dstack n) := Hedberg (Decidable_eq_dstack n).

Definition Hdstack n := hset (dstack n).

(** The dependent instructions [dinstr] are explicit about their
effect on the depth of the dstack *)

(* =dinstr= *)
Inductive dinstr: Hnat -> Hnat -> Type :=
| IConst: forall n, nat -> dinstr n (S n)
| IPlus: forall n, dinstr (S (S n)) (S n).
(* =end= *)

Definition SS_absurd {n :nat}: S (S n) = n -> empty. 
Proof.
  induction n. intro e; inversion e.
  intro e. inversion e. exact (IHn H0).
Defined. 


Definition Decidable_eq_dinstr n m n' m' (en : n = n') (em:m=m') :
  forall (x : dinstr n m) (y: dinstr n' m'),
    (transport (fun X => dinstr X _) en (transport (fun X => dinstr _ X) em x) = y) + not (transport (fun X => dinstr X _) en (transport (fun X => dinstr _ X) em x) = y).
Proof.
  intros x y. destruct x, y.
- destruct en. assert (em = eq_refl). apply is_hprop. rewrite H. cbn. 
  case (Decidable_eq_nat n0 n2); intro e; subst; cbn. 
  + exact (inl eq_refl).
  + apply inr. intro H. apply e. inversion H. reflexivity. 
- pose (transport (fun X => S X = _) en em). clearbody e. cbn in e.
  inversion e. destruct (SS_absurd H0).
- apply inr. inversion em. subst. destruct (SS_absurd H0^).
- inversion em. subst.
  assert (em = eq_refl). apply is_hprop. rewrite H. cbn. clear H. 
  assert (en = eq_refl). apply is_hprop. rewrite H. cbn. clear H. 
  exact (inl eq_refl). 
Defined.

Instance dinstr_HSet n m: IsHSet (dinstr n m) := Hedberg (Decidable_eq_dinstr n m n m eq_refl eq_refl).

Definition Hdinstr n m := hset (dinstr n m).

Arguments IConst {n} k.
Arguments IPlus {n}.

(** The stach machine satisfies those depth invariants **)

(* =exec= *)
Definition exec n m (i: Hdinstr n m): Hdstack n -> Hdstack m :=
  match i with
    | IConst n => fun s => (n, s)
    | IPlus => fun s =>
                let '(arg1, (arg2, s)) := s in (arg1 + arg2, s)
  end.
(* =end= *)


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

(* =instr= *)
Inductive instr: Type :=
| NConst: nat -> instr
| NPlus: instr.
(* =end= *)

Instance show_instr : Show instr :=
  {| show s := 
       match s with
         | NConst n => "NConst " ++ show n
         | NPlus => "NPlus"
       end
  |}.

(* =instr_index= *)
Definition instr_index n (i: instr): TError Hnat _ :=
  match i with
    | NConst _ => Some (S n)
    | NPlus => match n with
                 | S (S n) => Some (S n)
                 | _ => Fail (_with "invalid instruction")
               end
  end.
(* =end= *)


(** ** Equivalences *)

(** [dstack] is equivalent to lists through
<<
  {n:nat & dstack n} ~ {l : list nat & length l = n} 
>> 
*)

Definition dstack_to_list n : dstack n -> {l : list Hnat & clift (length (A:=nat)) l = Some n}.
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

Definition list_to_dstack n : {l : list Hnat & clift (length (A:=nat)) l = Some n} -> dstack n.
  destruct 1 as [l H]. generalize dependent n; induction l; cbn in *; intros. 
  - inversion H. exact tt.
  - specialize (IHl (length l) eq_refl). inversion H. exact (a,IHl).
Defined.

Definition list A  `{DecidablePaths A} := {| _typeS := list A |} : HSet.

(* =DepEquiv_dstack= *)
Instance Connection_dstack: Hdstack ≲K□ list Hnat :=
  DepConnection_eq Hdstack (list Hnat) (clift length)
                 dstack_to_list list_to_dstack.
(* =end= *)
{ unfold compose. intro n. 
  induction n; intro s; simpl. 
  - destruct s. reflexivity.
  - destruct s as [a s]. simpl. 
    specialize (IHn s). unfold compose in IHn. simpl in *.
    destruct (dstack_to_list _ s). 
    simpl in *. inversion e.
    assert (e = ap Some H0). apply is_hprop. subst. simpl in *.
    refine (path_prod_uncurried _ _ _); split; try reflexivity.
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

Definition Decidable_eq_instr :  forall (x y : instr), (x = y) + not (x = y).
intros x y. destruct x, y.
- case (Decidable_eq_nat n n0); intro e; subst. 
  + exact (inl eq_refl).
  + apply inr. intro H. apply e. inversion H. reflexivity. 
- apply inr. intro H; inversion H.
- apply inr. intro H; inversion H.
- exact (inl eq_refl).   
Defined.

Instance IsHSet_instr : IsHSet instr := Hedberg Decidable_eq_instr.

Instance DecidablePaths_instr : DecidablePaths (hset instr) := 
  { dec_paths := Decidable_eq_instr }.

(* Arguments dinstr_to_instr {_}{_} e. *)

(* =transport_instr_Const= *)
Definition transport_instr_Const (n m k: nat) (e: S n = m) :
   dinstr_to_instr _ _ (e # (IConst k)) = (NConst k; ap Some e).
(* =end= *)
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

Definition instr_to_dinstr' n n' :
  {i: instr & valid_instr i n n'} -> dinstr n n'.
  destruct 1 as [[] e]; cbn in *.
  - destruct (Some_inj e). exact (IConst n0).
  - destruct n. inversion e.
    destruct n. inversion e.
    destruct (Some_inj e). exact IPlus. 
Defined.

Reset instr_to_dinstr'.

(* =convoy_instr_to_dinstr= *)
Definition instr_to_dinstr' n n' 
    (iv: {i: instr & valid_instr i n n'}): dinstr n n' :=
  match iv with 
  | (i; v) => 
    match i return (valid_instr i n n' -> dinstr n n') with
    | NConst n0 => 
      fun v => 
        let e := Some_inj v in
        match e in (_ = m) 
              return (valid_instr (NConst n0) n m -> dinstr n m) 
        with
        | eq_refl => fun _ => IConst n0
        end v
    | NPlus => (* ... *)
(* =end= *)
      fun v => 
        match n 
              return (valid_instr NPlus n n' -> dinstr n n') 
        with
        | 0 => 
          fun v => Fail_is_not_Some v
        | S n => 
          fun v => 
            match n
                  return (valid_instr NPlus (S n) n' -> dinstr (S n) n') 
            with
            | 0 => 
              fun v => Fail_is_not_Some v
            | S n => 
              fun v => 
                let e := Some_inj v in
                match e in (_ = m) 
                      return (valid_instr NPlus (S (S n)) m -> dinstr (S (S n)) m) 
                with
                | eq_refl => fun _ => IPlus
                end v
            end v
        end v
    end v
  end.

Definition DepEquiv_instr_retr' n m (x:{i:instr & instr_index n i = Some m}) :
  (dinstr_to_instr _ _) ° (instr_to_dinstr' _ _) x = x.
Proof. 
  destruct x as [[] e]; unfold compose; cbn. 
  - unshelve eapply path_sigma. cbn.
    set (Some_inj e).
    change ((dinstr_to_instr n m
     (match
        e0 in (_ = y) return (valid_instr (NConst n0) n y → dinstr n y)
      with
      | eq_refl => λ _ : valid_instr (NConst n0) n (S n), IConst n0
      end e)) .1 = NConst n0).
    clearbody e0. destruct e0. reflexivity.
    apply (is_hprop _ _). 
  - destruct n. inversion e.
    destruct n; inversion e.
    unshelve eapply path_sigma. cbn.
    set (Some_inj e).
    change ((dinstr_to_instr (S (S n)) m
     (match
        e0 in (_ = y)
        return (valid_instr NPlus (S (S n)) y → dinstr (S (S n)) y)
      with
      | eq_refl => λ _ : valid_instr NPlus (S (S n)) (S n), IPlus
      end e)) .1 = NPlus).
    clearbody e0. destruct e0. reflexivity.
    apply (is_hprop _ _). 
Defined.
  
Definition Hinstr := {| _typeS := instr |} : HSet.

(* =DepEquiv_instr= *)
Instance Connection_instr n: Hdinstr n ≲K□ Hinstr :=
  DepConnection_eq (Hdinstr n) Hinstr (instr_index n) (dinstr_to_instr n) (instr_to_dinstr n).
(* =end= *)
{intros m x. destruct x; reflexivity. }
{ apply DepEquiv_instr_retr. }
{ intros m i. destruct n, i; cbn; reflexivity. }
Defined.

(** ** Lifting *)

(** Lifting exec to safely accept instr and list nat **)

(* =simple_exec= *)
Definition simple_exec: instr → List.list nat ⇀ List.list nat.
  refine (lift2 exec). typeclasses eauto.
Defined.
(* =end= *)

Arguments lift2 {_ _ _ _ _ _ _ _ _ _ _} _.

(* Pretty Printing of safe_exec *)

(* Arguments HOConnection {_ _ _} _ {_ _} _. *)
Arguments HOConnection_2 {_ _ _ _ _ _ _ _}  _ _.
Arguments HOConnection_2_sym {_ _ _ _ _ _ _ _} _. 
(* Print simple_exec.  *)
  
(* Definition sanity_check : simple_exec = *)
(*                           fun  (i : instr) (l : list Hnat) =>                *)
(*             b <- (c' <- to_subset l; Some (list_to_dstack c')); *)
(*           a <- instr_index (Datatypes.length l) i; *)
(*           b0 <- (c' <- to_subset i; *)
(*                Some (instr_to_dinstr (Datatypes.length l) a c')); *)
(*           Some (dstack_to_list _ (exec (Datatypes.length l) a b0 b)) .1:= *)
(*   eq_refl. *)

Eval compute in simple_exec NPlus (1 :: 2 :: nil).
Eval compute in simple_exec NPlus (1 :: nil).

(* we only use istrunc_hprop and funext *)
(* commented for compilation time *)
(* Print Assumptions simple_exec. *)

(** ** Extraction *)

Extract Constant IsPartialOrderTError => "let f _  = Obj.magic 0 in f".

Require Import ExtrOcamlString ExtrOcamlNatInt.
Extract Inductive List.list => "list" [ "[]" "(::)" ].

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
# simple_exec NPlus [1;2] ;;
- : int list = [3]  
# simple_exec NPlus [] ;;
Exception: (Failure "Coercion failure: invalid instruction").   
>>
 *)

(* to run exec in compiled mode, need to use coercions *)

