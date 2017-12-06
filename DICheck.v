Require Import String Showable Connection DepEquivAnti Decidable  HoTT.
Require Import Vector List.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).
 
Arguments length {_} l.

Set Universe Polymorphism.

Definition Hbool := hset bool. 

(* =listz= *)
Inductive listZ : bool -> Type :=
| nilZ : listZ false
| cons_zero : forall (n:nat) b, n = 0 -> listZ b -> listZ true
| cons_pos : forall (n:nat) b, not (n = 0) -> listZ b -> listZ b.
(* =end= *)

Definition listZ_inv_zero n b e n' l b' e' l' :
  cons_zero n b e l = cons_zero n' b' e' l' ->
  {eb : b = b' & transport listZ eb l = l'}.
  intro H. inversion H. exists eq_refl. reflexivity.
Defined. 

Definition path_sigma_inv {A : Type} (P : A -> Type) (u v : Specif.sigT P):
  u = v -> {p : Specif.projT1 u = Specif.projT1 v & p # (Specif.projT2 u) = Specif.projT2 v}.
Proof.
  destruct 1. exists eq_refl. exact eq_refl. 
Defined.

Definition listZ_inv_pos n b e n' l e' l' :
  cons_pos n b e l = cons_pos n' b e' l' ->
  l = l'.
  intro H. inversion H.
  apply path_sigma_inv in H3. destruct H3. cbn in *.
  assert (x = eq_refl); try apply is_hprop. subst. reflexivity. 
Defined. 

Instance list_with_HSet (b: Hbool) : IsHSet (listZ b).
apply Hedberg. revert b. 
assert (forall (b b' : Hbool) (e:b=b') (l: listZ b) (l' : listZ b'),
           (transport listZ e l = l') + not (transport listZ e l = l')).
intros b b' e l. revert b' e. 
induction l ; intros b' e' l'; destruct l'; try solve [inversion e'];
  try assert (He : e' = eq_refl); try apply is_hprop; subst; cbn;
    try solve [right; intro H; inversion H];
    try exact (inl eq_refl).
destruct b, b0. specialize (IHl _ eq_refl l'); cbn in IHl. 
destruct IHl. subst. exact (inl eq_refl).
right. intro H. apply n. apply listZ_inv_zero in H.
destruct H. assert (He : x = eq_refl); try apply is_hprop; subst; cbn.
reflexivity. 
right. intro H; inversion H.
right. intro H; inversion H.
specialize (IHl _ eq_refl l'); cbn in IHl. 
destruct IHl. subst. exact (inl eq_refl).
right. intro H. apply n. apply listZ_inv_zero in H.
destruct H. assert (He : x = eq_refl); try apply is_hprop; subst; cbn.
reflexivity. 
specialize (IHl _ eq_refl l'); cbn in IHl. destruct IHl.
subst.
destruct (Decidable_eq_nat n n1). subst.
assert (n0 = n2). apply funext. intro x. destruct (n0 x). subst.
exact (inl eq_refl).
right. intro H. apply n3. inversion H. reflexivity.
right. intro H. apply n3. apply listZ_inv_pos in H. assumption. 
intros; apply (X _ _ eq_refl). 
Defined.

Definition HlistZ (b: Hbool) := hset (listZ b).

Fixpoint contains (A:HSet) `{DecidablePaths A} (a:A) (l:list A) : Hbool :=
  match l with
    nil => false
  | a'::l => match @dec (hprop (a = a')) _ with
               inl _ => true
             | inr _ => contains A a l
             end
  end.
                                                                     
Fixpoint contains_bound (bound a: Hnat) (l:list nat) : Hbool :=
  match bound with
    0 => false
  | S bound => 
    match l with
      nil => false
    | a'::l =>
      match @dec (hprop (a = a')) _ with
                 inl _ => true
               | inr _ => contains_bound bound a l
               end
    end
  end.

(* =listz_p= *)
Definition listZ_P (b:Hbool) (l:list Hnat) : HProp := hprop (contains Hnat 0 l = b).
(* =end= *)

(* =listz_p_bound= *)
Definition listZ_P_bound (b:Hbool) (k :Hnat) (l:list Hnat) : HProp :=
  if b then hprop (contains_bound k 0 l = true) else hprop False.
(* =end= *)

Instance listZ_P_bound_decidable b bound l : Decidable (listZ_P_bound b bound l).
Proof.
  destruct b; typeclasses eauto.
Defined. 

(* =listz_checkable= *)
Instance listZ_P_checkable bound b l : Checkable (listZ_P b l) :=
  {| check := listZ_P_bound b bound l |}.
(* =end= *)
Proof.
  destruct b.
  - revert l. induction bound; cbn. 
    + intros l H; inversion H.
    + destruct l.
      * intro H; inversion H.
      * destruct n; cbn. apply id. apply IHbound.
  - inversion 1. 
Defined. 
  
Definition list A  `{DecidablePaths A} := {| _typeS := list A |} : HSet.

Definition contains_true A  `{DecidablePaths A} a a' l:
  a = a' -> contains A a (a' :: l) = true.
Proof.
  cbn. destruct (@dec (hprop (a = a')) _). reflexivity.
  intro e. destruct (n e).
Defined.

Definition contains_false (n : nat) (b : bool)
  (n0 : not (n = 0))
  (l : listZ b)
  (X : {l : list Hnat & listZ_P b l}): 
  listZ_P b (n :: X .1).
Proof.
    destruct n.
    destruct (n0 eq_refl).
    cbn. exact X.2.
Defined.

Definition listZ_to_list (b:Hbool) (l:listZ b) :
  {l : list Hnat & listZ_P b l}.
  revert l. revert b.
  unshelve refine (listZ_rect _ _ _ _); intros.
  - exists nil. reflexivity. 
  - exists (n :: X.1).
    exact (contains_true Hnat 0 n X.1 e^).
  - exists (n :: X.1). 
    exact (contains_false n b n0 l X).
Defined. 
     
Definition list_to_listZ  (b:Hbool): {l : list Hnat & listZ_P b l} -> listZ b.
  intros [l H]. generalize dependent b. induction l; simpl; intros.
  - destruct b. inversion H. 
    exact nilZ.
  - destruct (@dec (hprop (0 = a))) as [Heq | neg]; simpl in *.
    + exact (H # cons_zero a (contains Hnat 0 l) Heq^ (IHl _ eq_refl)).
    + exact (H # cons_pos a (contains Hnat 0 l) (fun H => neg (H^)) (IHl _ eq_refl)). 
Defined. 

Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.

Definition DepEquiv_C_list_with_list b bound :
  {l : list Hnat & listZ_P b l} ≈K (list Hnat) :=
  @Checkable_AntiConnectionK (list Hnat) _ (listZ_P_checkable bound b).

Notation "{ x : A & P }" := (sigT (fun x => P)) : type_scope.

Definition decompose_true b (l : listZ b) n e :
  listZ_to_list true (cons_zero n b e l)
  = (cons n (listZ_to_list b l).1 ; contains_true Hnat 0 n (listZ_to_list b l).1 e^).
Proof.
  reflexivity.
Defined.

Definition decompose_false b (l : listZ b) n e :
  listZ_to_list b (cons_pos n b e l) 
  = (cons n (listZ_to_list b l).1 ; contains_false n b e l (listZ_to_list b l)).
Proof.
  reflexivity.
Defined.

(* =DepEquiv_listz= *)
Instance DepEquiv_listZ_list (bound : Hnat) : HlistZ ≈K□ list Hnat.
(* =end= *)
Proof. 
  unshelve refine (IsDepAntiConnection _ HlistZ _ _ _ listZ_to_list list_to_listZ _ _ _ _).
  - induction 1.
    + exact (Some false).
    + destruct (dec (hprop (a = 0))) as [Heq | neg]; simpl in *.
      * exact (Some true).
      * exact IHlist.
  - clear bound. unfold compose.
    unshelve refine (listZ_rect _ _ _ _).
    + reflexivity.
    + intros. rewrite decompose_true, e. clear e.  cbn. 
      destruct ((listZ_to_list b l)) as [l' Hl].
      destruct Hl. apply ap. exact H.  
    + intros.
      assert (exists m, n = S m).
      destruct n. destruct (n0 eq_refl).
      exists n. reflexivity.
      destruct H0. 
      assert (not (S x = 0)). intro X; inversion X.
      assert (cons_pos n b n0 l = cons_pos (S x) b X l).
      destruct H0. apply (ap (fun Y => cons_pos n b Y l)).
      apply is_hprop.
      rewrite H1. clear n0 H0 H1 n.
      rewrite decompose_false.
      cbn. 
      destruct ((listZ_to_list b l)) as [l' Hl]. cbn in *. 
      destruct Hl. cbn.
      assert (Heq : (λ H0 : S x = 0,
                            match H0^ in (_ = y) return (y = S x → empty) with
                            | eq_refl =>
       λ H1 : 0 = S x,
              False_rect empty
           (eq_ind 0 (λ e : nat, match e with
                                 | 0 => True
                                 | S _ => False
                                 end) I (S x) H1)
     end eq_refl) = X). apply is_hprop. rewrite Heq. apply ap.
      exact H.
  - intros b [l Hl]. revert b Hl. induction l; unfold compose; intros. 
    + destruct b; simpl. cbn in Hl.
      inversion Hl. 
      apply path_sigma_uncurried. cbn. exists eq_refl. apply is_hprop.
    + cbn.
      specialize (IHl _ eq_refl). cbn in IHl.
      cbn in Hl. destruct Hl. 
      unshelve eapply path_sigma.
      destruct a; cbn; apply ap; exact IHl..1.
      apply is_hprop. 
  -  unshelve refine (listZ_rect _ _ _ _); unfold compose; simpl. 
     + reflexivity.
     + intros.  destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
       reflexivity. destruct (neg e).
    + simpl; intros. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      destruct b.
      * reflexivity. 
      * destruct (n0 Heq).
      * assert (n0 = neg) by apply is_hprop. destruct H0. exact H.
Defined. 

