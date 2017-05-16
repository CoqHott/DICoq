Require Import String Showable Equiv DepEquivCheckable Decidable HODepEquiv HoTT.
Require Import Vector List.
Local Open Scope string_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).  
Notation " ( x ; p ) " := (existT _ x p).
 
Arguments length {_} l.

Set Universe Polymorphism.

Definition Hbool := hset bool. 

Inductive listZ : bool -> Type :=
| nilZ : listZ false
| cons_zero : forall (n:nat), n = 0 -> list nat -> listZ true
| cons_pos : forall (n:nat) b, not (n = 0) -> listZ b -> listZ b.

Definition listZ_induction : ∀ P : ∀ b : bool, listZ b → Type,
       P false nilZ
       → (∀ (n : nat) (e : n = 0) (l : list nat), P true (cons_zero n e l))
         → (∀ (n : nat) (n0 : not (n = 0)) (l : listZ true), P true l → P true (cons_pos n true n0 l))
         → (∀ (n : nat) (n0 : not (n = 0)) (l : listZ false), P false l → P false (cons_pos n false n0 l))  
             → ∀ (b : bool) (l : listZ b), P b l.
  intros. induction l; auto.
  destruct b. apply X1; auto.  apply X2; auto.
Defined.   

Instance list_with_HSet (b:Hbool) : IsHSet (listZ b).
Admitted. 

Definition HlistZ (b:Hbool) := hset (listZ b).

Fixpoint nth_error (l : list Hnat) (n : Hnat) {struct n} : TError Hnat _ :=
  match n with
  | 0 => match l with
         | Datatypes.nil => Fail (_with "not_found")
         | x :: _ => Some x
         end
  | S n0 => match l with
            | Datatypes.nil => Fail (_with "not_found")
            | _ :: l0 => nth_error l0 n0
            end
  end.

Definition listZ_P (b:Hbool) (l:list Hnat) : HProp :=
  hprop (Trunc (if b then {n : nat & nth_error l n = Some 0}
                else forall n, not (nth_error l n =Some 0))).            

Definition listZ_P_bound (b:Hbool) (bound :Hnat) (l:list Hnat) : HProp :=
  hprop (Trunc (if b then {n : nat & ((n <= bound) * (nth_error l n = Some 0))%type}
                else False)).

Opaque nth_error.

Require Import Omega. 

Definition empty_map_product {A B} (f : A -> empty) (g : B -> empty) : Trunc (A + B) -> empty
  := Trunc_ind_prop _ (fun x => match x with inl a => f a | inr b => g b end).

Definition le_S_split n bound : n <= S bound -> ((n <= bound) + (n = S bound)).
Admitted.

Instance listZ_P_bound_decidable b bound l : Decidable (listZ_P_bound b bound l).
Proof.
  unfold Decidable. destruct b; [ idtac | right; refine (Trunc_ind_prop _ _); destruct 1]. 
  induction bound.
  destruct (@dec (hprop (nth_error l 0 = Some 0))) as [e|neg].
  unfold Decidable. apply (Decidable_eq_TError Hnat _). 
  cbn in *. 
  left. apply tr. exists 0. split; auto.
  right. intro H; apply neg. revert H. clear neg. 
  refine (Trunc_ind_prop _ _). simpl.  intros [n [H1 H2]].
  assert (n=0). omega. rewrite H in H2; exact H2.  
  destruct (@dec (hprop (nth_error l (S bound) = Some 0))) as [e|neg].
  unfold Decidable. apply (Decidable_eq_TError Hnat _). 
  left. apply tr. exists (S bound). split; auto.
  destruct IHbound as [H | H].
  left. revert H. refine (Trunc_ind_prop _ _). simpl.  intros [n [H1 H2]].
  apply tr. exists n. split; [omega | auto].
  right. intro H'. cbn in *. apply (empty_map_product H neg). clear H neg.
  revert H'. refine (Trunc_ind_prop _ _). simpl.  intros [n [H1 H2]].
  assert ((n <= bound) + (n =  S bound)). clear H2.
  apply le_S_split; auto. 
  destruct H; apply tr. 
  left. apply tr. exists n; split; [omega| auto].
  right. rewrite <- e. auto. 
Defined.

Instance listZ_P_checkable bound b l : Checkable (listZ_P b l) :=
  {| check := listZ_P_bound b bound l |}.
Proof.
  refine (Trunc_ind_prop _ _). destruct b. 
  - intros [n [H H']]. apply tr. exists n; auto.
  - intro H. inversion H.  
Defined.

Transparent nth_error.

Definition list A  `{DecidablePaths A} := {| _typeS := list A |} : HSet.

Fixpoint listZ_to_list (b:Hbool) (l:listZ b) {struct l} :
  {l : list Hnat & listZ_P b l}.
  revert l. revert b. unshelve refine (listZ_induction _ _ _ _ _); intros. 
  - exists nil. apply tr; intro. intro H; destruct n; inversion H.
  - exists (n :: l). apply tr. exists 0. exact (ap _ e).
  - exists (n :: (listZ_to_list true l).1).
    pose (t := (listZ_to_list true l).2). clearbody t. simpl in t.
    revert t.  refine (Trunc_ind_prop _ _). intro H; apply tr.
    destruct H as  [k H]. exists (S k). exact H.
  - exists (n :: (listZ_to_list false l).1).
    simpl. pose (t := (listZ_to_list false l).2). clearbody t. simpl in t.
    revert t.  refine (Trunc_ind_prop _ _). intro H; apply tr.
    intro k; destruct k. intro H'; exact (n0 (Some_inj H')). exact (H k).      
Defined. 

Definition list_to_listZ  (b:Hbool): {l : list Hnat & listZ_P b l} -> listZ b.
  intros [l H]. induction l; simpl; intros.
  - simpl in H. destruct b.
    assert empty. revert H.  refine (Trunc_ind_prop _ _).
    intros [a Ha]. destruct a; inversion Ha. destruct X.
    exact nilZ.
  - simpl in *.
    destruct (@dec (hprop (a = 0))) as [Heq | neg]; simpl in *.
    + exact (Decidable_eq_nat _ _). 
    + destruct b.
      * exact (cons_zero _ Heq l).
      * assert empty. revert H. refine (Trunc_ind_prop _ _). simpl.  intros f.
        apply (f 0). simpl. apply ap. exact Heq. destruct X. 
    + destruct b.
      * refine (cons_pos a true neg (IHl _)).
        revert H. refine (Trunc_ind_prop _ _). simpl.  intros [n Hn].
        apply tr. destruct n. inversion Hn. destruct (neg H0).
        exists n. exact Hn. 
      * refine (cons_pos a false neg (IHl _)).
        revert H. refine (Trunc_ind_prop _ _). simpl.  intros f.
        apply tr. intro n. exact (f (S n)). 
Defined.

Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.

Definition DepEquiv_C_list_with_list b bound :
  {l : list Hnat & listZ_P b l} ≲AK (list Hnat) :=
  @Decidable_AntiConnectionK (list Hnat) _ (listZ_P_checkable bound b).

Notation "{ x : A & P }" := (sigT (fun x => P)) : type_scope.

Instance DepEquiv_vector_list_nat (bound : Hnat) : HlistZ ≲AK□ list Hnat.
Proof. 
  unshelve refine (IsDepAntiCoercion _ HlistZ _ _ _ listZ_to_list list_to_listZ _ _ _ _).
  - induction 1.
    + exact (Some false).
    + destruct (dec (hprop (a = 0))) as [Heq | neg]; simpl in *.
      * exact (Some true).
      * exact IHlist.
  - apply listZ_P_checkable. exact bound.
  - unshelve refine (listZ_induction _ _ _ _ _); unfold compose.
    + reflexivity.
    + intros; simpl. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      assert (Heq = e) by apply is_hprop. destruct H. reflexivity.
      destruct (neg e).
    + simpl; intros. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      destruct (n0 Heq).
      assert (n0 = neg) by apply is_hprop. destruct H0. apply (ap (cons_pos n true n0)).
      destruct (listZ_to_list true l) as [x Hx]. simpl in *. unfold id in H. rewrite <- H.
      apply ap. apply is_hprop.
    + simpl; intros. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      destruct (n0 Heq).
      assert (n0 = neg) by apply is_hprop. destruct H0. apply (ap (cons_pos n false n0)).
      destruct (listZ_to_list false l) as [x Hx]. simpl in *. unfold id in H. rewrite <- H.
      apply ap. apply is_hprop.
  - intros b l. destruct l as [l Hl]. induction l; unfold compose; simpl.
    + destruct b; simpl. cbn in Hl.
      assert empty. revert Hl.  refine (Trunc_ind_prop _ _). intros [n Hn].
      destruct n; inversion Hn. destruct X.
      apply path_sigma_uncurried. exists eq_refl. apply is_hprop.
    + destruct (@dec (hprop (a = 0))) as [Heq | neg]; simpl in *.
      destruct b. simpl.
      apply path_sigma_uncurried. exists eq_refl. apply is_hprop.
      assert empty. revert Hl.  refine (Trunc_ind_prop _ _). intros f.
      destruct (f 0 (ap _ Heq)). destruct X.
      destruct b. simpl.
      apply path_sigma_uncurried. unshelve refine (existT _ _ _); try apply is_hprop. 
      simpl. apply ap. assert ( Trunc {n : nat & nth_error l n = Some 0}).
      revert Hl.  refine (Trunc_ind_prop _ _). intros [n Hn].
      destruct n. destruct (neg (Some_inj Hn)).
      exact (tr (n; Hn)).
      specialize (IHl X). pose (IHl..1).
      etransitivity; try exact e. clear e. 
      unfold compose. simpl. repeat apply ap. apply is_hprop. 
      simpl.  apply path_sigma_uncurried. unshelve refine (existT _ _ _); try apply is_hprop. 
      simpl. apply ap. assert (Trunc (∀ n : nat, not (nth_error l n = Some 0))).
      revert Hl.  refine (Trunc_ind_prop _ _). intros f. apply tr; intro n.
      exact (f (S n)).
      specialize (IHl X). pose (IHl..1).
      etransitivity; try exact e. clear e. 
      unfold compose. simpl. repeat apply ap. apply is_hprop. 
  -  unshelve refine (listZ_induction _ _ _ _ _); unfold compose; simpl. 
     + reflexivity.
     + intros.  destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
       reflexivity. destruct (neg e).
    + simpl; intros. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      reflexivity. 
      assert (n0 = neg) by apply is_hprop. destruct H0. exact H. 
    + simpl; intros. destruct (dec (hprop (n = 0))) as [Heq | neg]; simpl in *.
      destruct (n0 Heq).
      assert (n0 = neg) by apply is_hprop. destruct H0. exact H.
Defined. 
