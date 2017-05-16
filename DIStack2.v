Set Universe Polymorphism.
Require Import Showable String Decidable List.
Require Import TErrorMonad.
Require Import HoTT.
(* Require Import DepEquiv HODepEquiv HoTT. *)
Local Open Scope string_scope.

Import ListNotations.

(* Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope. *)
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).


(** * Dependent Stack/Instr *)

Inductive typ := Nat | Bool.

Definition  Decidable_eq_typ :  forall (x y : typ), (x = y) + not (x = y).
intros a b; destruct a, b;
  try exact (inl eq_refl);
  apply inr; inversion 1; contradiction.
Defined.

Instance IsHSet_typ : IsHSet typ := Hedberg Decidable_eq_typ.

Instance DecidablePaths_typ : DecidablePaths (hset typ) := 
  { dec_paths := Decidable_eq_typ }.

Definition sem (T: typ): Type := 
  match T with
  | Nat => nat 
  | Bool => bool 
  end.

Definition stack_typ := list typ.

Definition  Decidable_eq_stack_typ :  forall (x y : stack_typ), (x = y) + not (x = y).
intro a; induction a;
  intro b; destruct b;
    try exact (inl eq_refl);
    try (apply inr; inversion 1; now contradiction).
destruct (Decidable_eq_typ a t); subst.
- destruct (IHa b); subst.
  + exact (inl eq_refl).
  + apply inr; inversion 1; now contradiction.
- apply inr; inversion 1; now contradiction.
Defined.

Instance IsHSet_stack_typ : IsHSet stack_typ := Hedberg Decidable_eq_stack_typ.

Instance DecidablePaths_stack_typ : DecidablePaths (hset stack_typ) := 
  { dec_paths := Decidable_eq_stack_typ }.

(*
Lemma stack_eq_dec_refl : forall (S: stack_typ), dec (S = S) = inl eq_refl.
intro S.
destruct (dec (S = S)).
destruct e.
Admitted.
*)
(*
Lemma stack_eq_decP : forall a b, stack_eq_dec a b = true -> a = b.
Admitted.
*)

Section TypeScopeSection.
Local Open Scope type.

(*
Inductive dstack : stack_typ -> Type :=
| eps : dstack nil
| cns : forall {T}{S}, sem T -> dstack S -> dstack (cons T S).
*)

(* =dstack= *)
Fixpoint dstack (s: stack_typ) : Type :=
  match s with
    | nil => unit 
    | cons ty s => sem ty * dstack s
  end.
(* =end= *)
Local Close Scope type.
End TypeScopeSection.

(** The dependent instructions [dinstr] are explicit about their
effect on the depth of the dstack *)

(* =dinstr= *)
Inductive dinstr : stack_typ -> stack_typ -> Type :=
| ISkip : forall{S}, dinstr S S
| ISeq : forall{S1 S2 S3}, dinstr S1 S2 -> dinstr S2 S3 -> dinstr S1 S3
| IPUSH : forall{T S}, sem T -> dinstr S (T :: S)
| IPLUS : forall{S}, dinstr (Nat :: Nat :: S) (Nat :: S)
| IIFTE : forall{S S'}, dinstr S S' -> dinstr S S' -> dinstr (Bool :: S) S'.
(* =end= *)

Arguments ISkip {S}.
Arguments ISeq {S1 S2 S3} c1 c2.
Arguments IPUSH {T S} v.
Arguments IPLUS {S}.
Arguments IIFTE {S S'} c1 c2.

(** The stach machine satisfies those depth invariants **)

(* =exec= *)
Fixpoint exec {S S'} (c: dinstr S S'): dstack S -> dstack S' :=
  match c with
  | ISkip => fun s => s
  | ISeq c1 c2 => fun s => exec c2 (exec c1 s)
  | IPUSH v => fun s => (v , s)
  | IPLUS => 
    fun s => 
      let '(a , (b ,  s'')) := s in
      (a + b , s'')
  | IIFTE c1 c2 => 
    fun s => 
      match s with
      | (true , s') => exec c1 s'
      | (false , s') => exec c2 s'
      end
  end.
(* =end= *)


Eval compute in @exec [ Bool ] _ (@IPUSH Nat _ 1) (true,tt).
Eval compute in @exec [ Nat ; Nat ] _ IPLUS (2, (1, tt)).
(* bad use does not type check: the given dstack is not of depth 2 *)
(* Eval compute in @exec (cons Nat (cons Nat nil)) _ IPLUS (1, tt). *)


(** ** Plain [stack] & [instr] *)

(** There is no need to define plain [dstacks]: we just use lists of
   nats, with a condition on their length.

   Plain instructions are another inductive, with its [Show] instance,
   and the condition is expressed with the [valid_instr] predicate
   below (which is decidable).  *)

Module Instr.

(* =instr= *)
Inductive instr : Type :=
| NSkip : instr
| NSeq : instr -> instr -> instr
| NPUSH : forall T, sem T -> instr
| NPLUS : instr
| NIFTE : instr -> instr -> instr.
(* =end= *)

End Instr.

Import Instr.

(* Instance show_instr : Show instr := *)
(*   {| show s :=  *)
(*        match s with *)
(*        | NSkip => "NSkip" *)
(*        | NSeq c1 c2 => "NSeq (" ++ show c1 ++ ") (" ++ show c2 ++ ")" *)
(*        | NPUSH T v => "NPUSH " ++ show v *)
(*        | NPLUS => "NPLUS" *)
(*        | NIFTE c1 c2 => "NIFTE (" ++ show c1 ++ ") (" ++ show c2 ++ ")" *)
(*        end *)
(*   |}. *)

(* =instr_index= *)
Fixpoint instr_index (S: stack_typ)(i:instr) : TError stack_typ _ :=
  match i with
  | NSkip => 
    creturn S
  | NSeq c1 c2 => 
    S1 <- instr_index S c1 ;
    instr_index S1 c2
  | NPUSH T _ => 
    creturn (T :: S)
  | NPLUS => match S with
            | Nat :: Nat :: s => creturn (Nat :: s)
            | _ => Fail (_with "invalid instruction")
            end
  | NIFTE c1 c2 => 
    match S with
    | Bool :: s => 
      S1 <- instr_index s c1 ;
      S2 <- instr_index s c2 ;
      if (Decidable_eq_stack_typ S1 S2) then
        creturn S1
      else
        Fail (_with "invalid instruction")
    | _ => Fail (_with "invalid instruction")
    end
  end.
(* =end= *)


(** ** Equivalences *)


Fixpoint stack_typ_of (l: list (nat + bool)): stack_typ :=
  match l with
  | [] => []
  | inl _ :: xs => Nat :: stack_typ_of xs
  | inr _ :: xs => Bool :: stack_typ_of xs
  end.

Definition dstack_to_list {S} : dstack S -> {l : list (nat + bool) & clift stack_typ_of l = Some S }.
  intro s; induction S.
  - exact (nil; eq_refl).
  - destruct s as [v s].
    destruct (IHS s) as [s' IHS'].
    destruct a; [exists (inl v :: s') | exists (inr v :: s')];
    unfold clift; try do 2 apply ap; inversion IHS'; auto.
Defined.

Definition list_to_dstack {S} : {l : list (nat + bool) & clift stack_typ_of l = Some S} -> dstack S.
  destruct 1 as [l H]. generalize dependent S; induction l; cbn in *; intros. 
  - inversion H. exact tt.
  - specialize (IHl (stack_typ_of l) eq_refl). inversion H. 
    destruct a as [n | b].
    + exact (n,IHl).
    + exact (b,IHl).
Defined.

Definition list A  `{DecidablePaths A} := hset (list A) : HSet.


(*
(* =DepEquiv_dstack= *)
Instance DepEquiv_dstack :
  dstack ≈ list nat :=
  @DepEquiv_eq _ _ (list nat) _ _ (clift (length (A:=nat))) (@dstack_to_list) (@list_to_dstack) _ _ _.
(* =end= *)
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
*)

(** [dinstr] is equivalent to [instr] through
<<
 {n n': nat & dinstr n n'} ~ {i: instr & valid_instr n i n'}
>>
*)

Definition valid_instr i S S' := instr_index S i = Some S'.

Fixpoint dinstr_to_instr S S'
  (i : dinstr S S'): {i: instr & valid_instr i S S'}.
refine (
  match i with                                                      
  | ISkip => (NSkip ; _)
  | ISeq c1 c2 => 
    let '(i1 ; q1) := dinstr_to_instr _ _ c1 in 
    let '(i2 ; q2) := dinstr_to_instr _ _ c2 in 
    (NSeq i1 i2 ; _)
  | IPUSH k => (NPUSH _ k ; _)
  | IPLUS    => (NPLUS ; _) 
  | IIFTE c1 c2 => 
    let '(i1 ; q1) := dinstr_to_instr _ _ c1 in 
    let '(i2 ; q2) := dinstr_to_instr _ _ c2 in 
    (NIFTE i1 i2 ; _)
  end); try reflexivity.
- unfold valid_instr; simpl.
  rewrite q1; simpl. exact q2.
- unfold valid_instr; simpl.
  rewrite q1, q2. simpl.
  destruct (Decidable_eq_stack_typ s0 s0); auto.
  apply empty_rect; auto.
Defined.


Definition Fail_is_not_Some {A info i R} {x:A} :
  @Fail A info i = Some x -> R. 
    inversion 1.
Defined.

Fixpoint instr_to_dinstrH Sin Sout (i: instr) : valid_instr i Sin Sout -> dinstr Sin Sout :=
  match i return valid_instr i Sin Sout → dinstr Sin Sout with
  | NSkip => 
    fun v => 
      transport (fun X => dinstr _ X) (Some_inj v) ISkip
  | NSeq c1 c2 => 
    fun v => 
      let '(Sinter ; (v1 , v2)) := cbind_Some _ _ _ v in 
      ISeq (instr_to_dinstrH Sin Sinter c1 v1) 
           (instr_to_dinstrH Sinter Sout c2 v2)
  | NPUSH _ k => 
    fun v => 
      transport (fun X => dinstr _ X) (Some_inj v) (IPUSH k)
  | NPLUS    => 
    match Sin return valid_instr NPLUS Sin Sout → dinstr Sin Sout with
    | [] => 
      fun v => Fail_is_not_Some v
    | [_] => 
      fun v => Fail_is_not_Some v
    | Bool :: _ => 
      fun v => Fail_is_not_Some v
    | Nat :: Bool :: _ => 
      fun v => Fail_is_not_Some v
    | Nat :: Nat :: Sin => 
      fun v => transport (fun X => dinstr _ X) (Some_inj v) IPLUS
    end
  | NIFTE c1 c2 => 
    match Sin return valid_instr (NIFTE c1 c2) Sin Sout → dinstr Sin Sout with
    | [] => 
      fun v => Fail_is_not_Some v
    | Nat :: _ => 
      fun v => Fail_is_not_Some v
    | Bool :: Sin => 
      fun v => 
        let '(S1 ; (v1 , q1)) := cbind_Some _ _ _ v in
        let '(S2 ; (v2 , q2)) := cbind_Some _ _ _ q1 in
        match Decidable_eq_stack_typ S1 S2 as b
              return (if b then creturn S1
                      else Fail (_with "invalid instruction")) = Some Sout
                     -> dinstr (Bool :: Sin)  Sout with
        | inl H => fun q2 => 
                   transport (fun X => dinstr _ X) (Some_inj q2)
                             (IIFTE (instr_to_dinstrH _ _ c1 v1)
                                    (transport (fun X => dinstr _ X)
                                               (eq_sym H) 
                                               (instr_to_dinstrH _ _ c2 v2)))
        | inr _ => fun q2 => Fail_is_not_Some q2
        end q2
    end
  end.

Definition instr_to_dinstr Sin Sout : { i: instr & valid_instr i Sin Sout} -> dinstr Sin Sout := fun x => instr_to_dinstrH Sin Sout x.1 x.2.


(*
Fixpoint DecidablePaths_instr (a : instr) : forall b, Decidable (a = b).
induction a; intro b; destruct b;
  try exact (inl eq_refl);
  try (apply inr; now inversion 1).
- case (IHa1 b1).
  + case (IHa2 b2).
    * intros -> -> .
      exact (inl eq_refl).
    * intros; apply inr; inversion 1; contradiction.
  + intros; apply inr; inversion 1; contradiction.
- case (dec (T = T0)).
  + intros <-.
    destruct T.
    * {
        case (dec (s = s0)).
        - intros ->.
          exact (inl eq_refl).
        - intro. apply inr. intro. apply n. inversion H.
          admit. (* XXX: painful equality over sigma-type *)
      }
    * admit. (* XXX: copy/paste proof above *)
  + intros. apply inr; inversion 1; contradiction.
- case (IHa1 b1).
  + case (IHa2 b2).
    * intros -> -> .
      exact (inl eq_refl).
    * intros; apply inr; inversion 1; contradiction.
  + intros; apply inr; inversion 1; contradiction.
Admitted.
 *)

Arguments dinstr_to_instr {_}{_} i.

Definition transport_instr_Skip {S1 S2} (e : S1 = S2) :
   dinstr_to_instr
     (transport (λ X, dinstr S1 X) e ISkip) =
   (NSkip; ap Some e).
  destruct e; reflexivity.
Defined.

(*
Definition transport_instr_Seq {S1 S2 c1 c2 i1 i2} (e : S1 = S2) :
   dinstr_to_instr
     (transport (λ X, dinstr S1 X) e (ISeq c1 c2)) =
   (NSeq i1 i2; ap Some e).
  destruct e; reflexivity.
Defined.
*)

(* =transport_instr_Const= *)
Definition transport_instr_PUSH {T S1 S2 k} (e : T :: S1 = S2) :
   dinstr_to_instr (e # (IPUSH k)) = (NPUSH _ k; ap Some e).
(* =end= *)
     destruct e. reflexivity.
Defined.

Definition transport_instr_PLUS {S1 S2} (e : Nat :: S1 = S2) :
   dinstr_to_instr
     (transport (λ X, dinstr (Nat :: Nat :: S1) X) e IPLUS) =
   (NPLUS; ap Some e).
     destruct e. reflexivity.
Defined.

(* XXX: Update *)
(*
Definition DepEquiv_instr_retr n m (x:{i:instr & instr_index n i = Some m}) :
  (dinstr_to_instr) ° (instr_to_dinstr _ _) x = x :=
  match x with (i;v) =>
          match i return forall v :valid_instr i n m,
              (dinstr_to_instr) ° (instr_to_dinstr _ _) (i; v) = id (i; v) with
(* |- creturn (S n) = Some m -> 
      dinstr_to_instr n m (Some_inj v # IConst n0) (NConst n0; v) = (NConst n0; v) *)
   NConst n0 => fun v => transport_instr_Const _ _ _ _ @
                        path_sigma _ (NConst n0; ap (Some (A:=nat)) (Some_inj v))
                                     (NConst n0; v) eq_refl (is_hprop _ _)
 | NPlus => match n return ∀ v : valid_instr NPlus n m,
                (dinstr_to_instr) ° (instr_to_dinstr _ _) (NPlus; v) = (NPlus; v)
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

Definition instr := {| _typeS := instr |} : HSet.

(* =DepEquiv_instr= *)
Instance DepEquiv_instr n : dinstr n ≈ instr :=
    @DepEquiv_eq _ (dinstr n) instr _ _
                 (instr_index n)
                 (@dinstr_to_instr n) 
                 (instr_to_dinstr n) _ _ _.
(* =end= *)
{intros m x. destruct x; reflexivity. }
{ apply DepEquiv_instr_retr. }
{ intros m i. destruct n, i; cbn; reflexivity. }
Defined.

(** ** Lifting *)

(** Lifting exec to safely accept instr and list nat **)

(* =simple_exec= *)
Definition simple_exec : instr → list nat ⇀ list nat := lift2 exec.
(* =end= *)

Arguments lift2 {_ _ _ _ _ _ _ _ } _ _ _ _.

(* Pretty Printing of safe_exec *)

Arguments HODepEquiv {_ _ _}  _ {_ _} _.
(*Arguments HODepEquiv2 {_ _ _ _ _ _ _ _}  _ _. *)
Arguments HODepEquiv2_sym {_ _ _ _ _ _ _ _} _. 
Print simple_exec. 


Definition sanity_check : simple_exec =
          fun  (i : instr) (l : list nat) =>
          b <- (c' <- to_subset l; Some (list_to_dstack c'));
          a <- instr_index (Datatypes.length l) i;
          b0 <- (c' <- to_subset i;
               Some (instr_to_dinstr (Datatypes.length l) a c'));
          Some (dstack_to_list (exec (Datatypes.length l) a b0 b)) .1:=
  eq_refl.

Eval compute in simple_exec NPlus (1 :: 2 :: nil).
Eval compute in simple_exec NPlus (1 :: nil).

Print Assumptions simple_exec.

(** ** Extraction *)

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
# simple_exec NPlus [1;2];;
- : int list = [3]                                                                              
# simple_exec NPlus [];;
Exception: (Failure "Cast failure: invalid instruction").   
>>
 *)

(* to run exec in compiled mode, need to use coercions *)

*)