Set Universe Polymorphism.
Require Import Showable String List DepEquiv HoTT.

(** * Higher-order dependent equivalences *)

(** 

We enrich the dependent equivalence class with instances matching
higher-order types.

 *)


Axiom FunExt : Funext.


(** Triggers for lifting and unlifing search: *)

Definition lift {A} {B: A -> Type} {C : A -> Type} {B_ C_} `{(forall a, B a ⇀ (C a))  ≃? (B_ ⇀ C_)} : (forall a, B a -> C a) -> B_ ⇀ C_  := fun f => pe_fun (fun a b => creturn (f a b)).

Definition unlift {A} {B: A -> Type} {C : A -> Type} {B_ C_}
           {H :(forall a, B a ⇀ (C a))  ≃? (B_ ⇀ C_)} :
  (B_ -> C_) -> forall a, B a ⇀ (C a) := fun ff => pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H)) (clift ff).

Definition lift2 {A A'} {B: A -> A' -> Type} {C: A -> A' -> Type} {D : A -> A' -> Type} {B_ C_ D_}
           `{(forall a a', B a a' -> C a a' ⇀ D a a') ≃? (B_ -> C_ ⇀ D_)} :
  (forall a a', B a a' -> C a a' -> D a a') -> B_ -> C_ ⇀ D_ :=
  fun ff => pe_fun (fun a a' b c => creturn (ff a a' b c)).

(** ** Domain transformation: *)

Instance HODepEquiv_easy A (B: A -> Type) (C:HSet) (C': HSet)
           (H:B ≈ C) 
   : (forall a, B a ⇀ C')  ≃? (C ⇀ C')  | 0
  :=
    {| pe_fun := Build_Mon (to_simpl_dom : (∀ a : A, B a ⇀ C') -> C ⇀ C') _ _;
       pe_isequiv := {| pe_inv := Build_Mon to_dep_dom _ _ |}|}. 
Proof.
  + intros f g Hfg c. cbn in *. unfold to_simpl_dom.
    destruct (c_to_a c); simpl; eauto.
    destruct (to_dep a c); simpl; eauto.
    specialize (Hfg a b). revert Hfg. destruct (f a b); simpl; eauto.
  + cbn. unfold to_simpl_dom. intro x.
    destruct (c_to_a x); simpl; eauto; try apply irr_Fail.
    destruct (to_dep a x); simpl; eauto; apply irr_Fail.
  + intros f g Hfg a b. cbn in *. unfold to_dep_dom, kleisli_comp.
    destruct (to_simpl b) as [c | c]; simpl; eauto. 
    specialize (Hfg c). revert Hfg. simpl. destruct (f c) as [c' | c']; simpl; eauto.
  + cbn. unfold to_dep_dom, kleisli_comp. intros a b. 
    destruct (to_simpl b) as [c | c]; simpl; eauto; try apply irr_Fail.
+ intros f a b. simpl. 
  unfold compose, to_dep_dom, to_simpl_dom in *; simpl in *.
  
  assert (H'1'1: (c_to_a °° (pek_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
    by apply prop_c_to_a.
  unfold kleisli_comp in H'1'1. unfold to_simpl, b_to_c.
  unfold to_dep, to_rich. simpl. 
pose (pek_sect (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ _ )) b).
  generalize dependent r. unfold kleisli_comp, to_simpl. cbn in *.  simpl. 
  unfold to_simpl, to_dep, b_to_c, compose.
  revert H'1'1.
  destruct (pek_fun _ (e_fun _ b)) as [c | c]; simpl; eauto.
  intro e; rewrite e. clear e. simpl in *. 
  destruct (pek_inv c); simpl; eauto.
  intro e; inversion e. unfold id. 
  destruct (f a (e_inv s)); simpl; eauto. 
+ intros f c.
  unfold compose, to_dep_dom, to_simpl_dom, to_dep, to_rich, to_simpl in *; simpl in *.
  destruct (c_to_a c); simpl; eauto.
  pose (pek_retr (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ a)) c). unfold kleisli_comp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
  destruct (pek_inv c); simpl ; eauto.
  destruct (pek_fun _ (e_fun _ (e_inv s))); simpl ; eauto. 
  intro e. inversion e. clear e.   
  unfold id. destruct (f c); simpl ; eauto.
+ intro f. apply FunExt. intro. apply is_hprop. 
Defined.

(** ** Domain & co-domain transformation: *)

Instance HODepEquiv {A} {B: A -> Type} {C} 
           `{B ≈ C} {B': A -> Type} {C'} 
           `{B' ≈ C'} 
  : (forall a, B a ⇀ (B' a))  ≃? (C ⇀ C'):=
  {| pe_fun := Build_Mon (fun f => to_simpl_dom (fun a b => x <- f a b;  to_simpl x)) _ _ ; 
     pe_isequiv := {| pe_inv := Build_Mon (fun f a b => x <- to_dep_dom f a b; to_dep _ x) _ _ |}|}.
Proof.
+ intros f g Hfg c. cbn in *. unfold to_simpl_dom.
  destruct (c_to_a c); simpl; eauto.
  destruct (to_dep a c); simpl; eauto.
  specialize (Hfg a b). revert Hfg. destruct (f a b); simpl; eauto.
  destruct (g a b); simpl; intro e; inversion e; try reflexivity.
  destruct (to_simpl b1); simpl; eauto.
+ cbn. unfold to_simpl_dom. intro x.
  destruct (c_to_a x); simpl; eauto; try apply irr_Fail.
  destruct (to_dep a x); simpl; eauto; apply irr_Fail.
+ intros f g Hfg a b. cbn in *. unfold to_dep_dom, to_dep_dom, kleisli_comp.
  destruct (to_simpl b) as [c | c]; simpl; eauto. 
  specialize (Hfg c). revert Hfg. destruct (f c); simpl; eauto.
  destruct (g c) as [c1 | c1]; simpl; intro e; inversion e.
  subst. destruct (to_dep a c1); simpl; eauto.
+ cbn. unfold to_dep_dom, kleisli_comp. intros a b. 
  destruct (to_simpl b); simpl; eauto; try apply irr_Fail.
+ intros f a b.  unfold compose, id in *. cbn in *. 
  unfold to_dep_dom, to_dep_dom, to_simpl_dom in *.

    assert (H'1'1: (c_to_a °° (pek_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
    by apply prop_c_to_a.
  unfold kleisli_comp in H'1'1. unfold to_simpl, b_to_c.


    unfold to_dep, to_rich. simpl. 
    pose (pek_sect (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ a )) b).
  generalize dependent r. unfold kleisli_comp, to_simpl. cbn in *.  simpl. 
  unfold to_simpl, to_dep, b_to_c,compose.
  revert H'1'1.
  destruct (pek_fun _ (e_fun _ b)) as [c | c]; simpl; eauto.
  intro e; rewrite e. clear e. simpl in *. unfold to_rich. 
  destruct (pek_inv c); simpl; eauto.
  intro e; inversion e. unfold id. destruct (f a (e_inv s)); simpl; eauto. 
  pose (pek_sect (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ _ )) b0). simpl in r.
  generalize dependent r. unfold kleisli_comp, to_simpl, to_dep, b_to_c, c_to_b,compose. 
  destruct (pek_fun _ (e_fun _ b0)); simpl; eauto. 
+ intros f x. cbn in *. 
  unfold compose, id, to_dep_dom, to_dep_dom, to_simpl_dom, to_simpl, clift, to_dep, to_rich in *;
    simpl in *.
  destruct (c_to_a x); simpl ; eauto. 
  pose (pek_retr (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _  a)) x). unfold kleisli_comp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
  destruct (pek_inv x); simpl ; eauto.
  destruct (pek_fun _ (e_fun _ (e_inv s)))as [c | c]; simpl; eauto.
  intro e. inversion e. simpl. 
  destruct (f x) as [c0 | c0]; simpl; eauto. 
  pose (pek_retr (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ a)) c0). unfold kleisli_comp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl. 
  destruct (pek_inv c0); simpl ; eauto.
+ intro f. apply FunExt. intro. simpl. apply is_hprop. 
Defined.
  
(** ** Argument reordering: *)

Instance HODepEquiv2_sym A A' B_1 B_2 (B_3 : A -> A' -> Type) {C_1 C_2 C_3 : HSet}
         (H: (forall a a', B_2 a a' -> B_1 a a' ⇀ B_3 a a') ≃? (C_2 -> C_1 ⇀ C_3)) :
  (forall a a', B_1 a a' -> B_2 a a' ⇀ B_3 a a') ≃? (C_1 -> C_2 ⇀ C_3) | 100
    :=
  {| pe_fun := Build_Mon (fun ff b_ c_ => pe_fun (fun a a' c b => ff a a' b c) c_ b_) _ _; 
     pe_isequiv := {|pe_inv := Build_Mon (fun ff a a' b c => (pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H))) (fun c b => ff b c) _ _ c b) _ _ |}|}.
Proof.
  - intros x y H0 b c.
    pose (x' := fun a a' c b => x a a' b c).
    pose (y' := fun a a' c b => y a a' b c).
    assert (e : x' ≼ y'). intros x1 x2 x3 x4. apply H0. 
    apply ((pe_fun (CanonicalPartialEquiv := H)).(mon) e).
  - intros b c.
    exact ((pe_fun (CanonicalPartialEquiv := H)).(p_mon _ _) c b).
  - intros x y H0 a a' b c.
    pose (x' := fun c b => x b c).
    pose (y' := fun c b => y b c).
    assert (e : x' ≼ y'). intros x1 x2. apply H0. 
    apply ((pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H))).(mon) e).
  - intros a a' b c. 
    exact ((pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H))).(p_mon _ _) a a' c b).
  - intros f a a' b c. 
    exact (pe_sect (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H)) (fun a a' c b => f a a' b c) a a' c b).
  - intros f b c.
    exact (pe_retr (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H)) (fun c b => f b c) _ _).
  - simpl. intros f. apply FunExt. intro b.
    apply FunExt; intro c. apply is_hprop. 
Defined.

(** ** Arity 2 types: *)

Hint Extern 1 (IsPartialEquiv ?f) => apply (pe_isequiv (CanonicalPartialEquiv := _)) :
             typeclass_instances.

Definition to_simpl_dom2 {A A' B_1 B_2} {B_3 : A -> A' -> Type} {C_1 C_2 C_3 : HSet}
           `{forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a')  ≃? (C_2 ⇀ C_3))}
           `{DepEquiv A B_1 C_1}:
         (∀ a a', B_1 a → B_2 a a' ⇀ B_3 a a') → C_1 → C_2 ⇀ C_3 :=
  fun f => let f' := fun a b => pe_fun (fun a' => f a a' b) in 
        fun b_ c => to_simpl_dom (fun a b => f' a b c) b_.

Definition to_dep_dom2 {A A' B_1 B_2} {B_3 : A -> A' -> Type} {C_1 C_2 C_3 : HSet}
         `{forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a')  ≃? (C_2 ⇀ C_3))} `{DepEquiv A B_1 C_1}:
         (C_1 → C_2 ⇀ C_3) -> ∀ a a', B_1 a → B_2 a a' ⇀ B_3 a a' :=
  fun f a a' b c =>
    pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a))
           (fun x => c <- to_simpl b; f c x) a' c.

Instance HODepEquiv2
         A A' (B_1: A -> Type) (B_2: A -> A' -> Type) (B_3 : A -> A' -> Type)
         (C_1 C_2 C_3 : HSet)
         (H:forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a')  ≃? (C_2 ⇀ C_3))) `{DepEquiv A B_1 C_1} :
  (forall a a', B_1 a -> B_2 a a' ⇀ B_3 a a') ≃? (C_1 -> C_2 ⇀ C_3)
  :=
  {| pe_fun := Build_Mon to_simpl_dom2 _ _ ; 
     pe_isequiv := {|  pe_inv := Build_Mon to_dep_dom2 _ _ |}|}.
  
(* Remaining terms/proofs *)
Proof.
  + intros f g e b c. simpl. unfold to_simpl_dom2, to_simpl_dom.
    destruct (c_to_a b) ;simpl; eauto. 
    destruct (to_dep a b) ;simpl; eauto.
    refine ((pe_fun (CanonicalPartialEquiv := H a)).(mon) _ _).
    intros x1 x2. apply e.
  + cbn. unfold to_simpl_dom2, to_simpl_dom. intros b c.
    destruct (c_to_a b); simpl; eauto; try apply fail_contr.
    destruct (to_dep a b); simpl; eauto; try apply fail_contr.
    apply (pe_fun (CanonicalPartialEquiv := H a) .(p_mon _ _) c).
  + intros f g e a a' b c. simpl. unfold to_dep_dom2.
    refine ((pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a))).(mon) _ _ _).
    intros x1. cbn. destruct (to_simpl b) as [c'| c']; simpl ; eauto. apply e.
  + cbn. unfold to_dep_dom2, to_simpl_dom. intros a a' b c.
    destruct (to_simpl b) as[s | s]; simpl; try apply fail_contr; auto.
    apply (pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) .(p_mon _ _) a' c).
    assert ((λ _ : C_2, Fail C_3 s) = (λ _ : C_2, Fail C_3 (Cast_info_wrap "cast" C_3))).
    apply FunExt. intro. apply ap. apply is_hprop.
    rewrite H1. apply (pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) .(p_mon _ _) a' c).
  + intros ff a a' b c.
     unfold compose, to_dep_dom2, to_simpl_dom2, to_simpl_dom in *; simpl in *.
  assert (H'1'1: (c_to_a °° (pek_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
    by apply prop_c_to_a.
  unfold kleisli_comp in H'1'1. unfold to_simpl, b_to_c.
  unfold to_dep, to_rich. simpl. 
pose (pek_sect (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ _ )) b).
  generalize dependent r. unfold kleisli_comp, to_simpl. cbn in *.  simpl. 
  unfold to_simpl, to_dep, b_to_c,compose.
  revert H'1'1. cbn. 
  destruct (pek_fun _ (e_fun _ b)) as [c0 | c0]; simpl; eauto.
  intro e; rewrite e. clear e. simpl in *. unfold to_rich. 
  destruct (pek_inv c0); simpl; eauto.
  intro e. inversion e. rewrite H2.
     
    exact (pe_sect (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := _)) (fun a' c => ff a a' b c) a' c).
    
    intro. pose (pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) .(p_mon _ _) a' c). cbn in r0.
    assert ((λ _ : C_2, Fail C_3 c1) = (λ _ : C_2, Fail C_3 (Cast_info_wrap "cast" C_3))).
    apply FunExt. intro; apply ap, is_hprop.
    rewrite H1. clear H1. generalize dependent r0.
    destruct ( pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) (λ _ : C_2, Fail C_3 (Cast_info_wrap "cast" C_3)) a' c); simpl; eauto.  inversion 1.
    inversion 1. 
  + intros ff b c. 
    unfold compose, to_simpl_dom2, to_simpl_dom, to_dep_dom2 in *; simpl in *.
    destruct (c_to_a b);simpl; [ |eauto].
    unfold to_dep, to_rich.
    pose (pek_retr (IsPartialEquivK := pek_isequiv (p := DepEquiv_PartialEquivK _ _ _ a)) b). unfold kleisli_comp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
  destruct (pek_inv b); simpl ; eauto.
  pose (e_retr (IsEquiv := e_isequiv (e := total_equiv a)) s).
  pose (pe_retr (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) (DepEquiv.to_dep_dom2 ff a (c_to_b s)) c).
  generalize dependent r.
  unfold DepEquiv.to_dep_dom2; cbn. unfold id, to_simpl. simpl. 
  unfold compose, b_to_c, c_to_b in *. rewrite e. clear e. unfold id. 
  destruct (pek_fun _ s); simpl; eauto. 
  intros e' e; inversion e. rewrite <- H2 in *. clear e H2. revert e'. 
  exact id. 

  intros e _. revert e. 
  pose (F := pe_fun (pe_inv (IsPartialEquiv := pe_isequiv (CanonicalPartialEquiv := H a)) (λ _ : C_2, Fail C_3 c0))).
  simpl in *.
  change (F c ≼ Fail C_3 c0 -> F c ≼ ff b c).
  destruct (F c); simpl; eauto. 
  intro e; inversion e. 
  + intro f. apply FunExt. intro. simpl. apply FunExt. intro.
    apply is_hprop. 
  Defined.

(* This instance must be here because before, it would break some
   type class inferences, I don't understand why ?*)

Instance DepEquiv_with_pe A A' B C (f : A' -> A) {Hf: IsInjective f}
         {HP : B ≈ C} : (fun a => B (f a)) ≈ C :=
  Build_DepEquiv A' (fun a => B (f a)) C (fun a c => P (f a) c)
                (fun a' => total_equiv (f a'))
                (λ a : A', partial_equiv (f a))
                (fun c => a <- c_to_a c; f^?-1 a) _ showC. 
Proof.
  intros a' b. simpl. 
  pose (prop_c_to_a (f a') b). generalize dependent e. unfold kleisli_comp, b_to_c.
  destruct (pek_fun _ (e_fun _ b)); simpl; intro e;inversion e.
  rewrite e. simpl. 
  apply (i_sect a').
Defined.