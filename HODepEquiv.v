Set Universe Polymorphism.
Require Import Showable String List DepEquiv HoTT.

Notation "{ x : A & P }" := (sigT_HSet A (fun x => P)) : type_scope.

(** * Higher-order dependent equivalences *)

(** 

We enrich the dependent equivalence class with instances matching
higher-order types.

 *)

(** Triggers for lifting and unlifing search: *)

(* =lift= *)
Definition lift {A:HSet} {B_1 B_2: A ->HSet}{C_1 C_2: HSet}
    `{(forall a, B_1 a ⇀ B_2 a)  ≲ (C_1 ⇀ C_2)} :
    (forall a, B_1 a -> B_2 a) -> C_1 ⇀ C_2  := 
  fun f => c_fun (fun a b => creturn (f a b)).
(* =end= *)

Definition unlift {A:HSet} {B: A -> HSet} {C : A -> HSet} {B_ C_:HSet}
           {H :(forall a, B a ⇀ (C a)) ≲ (B_ ⇀ C_)} :
  (B_ -> C_) -> forall a, B a ⇀ (C a)
  := fun ff => c_inv _ (IsConnection := c_isconn (Coercion := H)) (clift ff).

Definition lift2 {A A': HSet} 
           {B: A -> A' -> HSet} {C: A -> A' -> HSet} {D : A -> A' -> HSet}
           {B_ C_ D_:Type}
           {HB_: IsHSet B_}
           {HC_: IsHSet C_}
           {HD_: IsHSet D_}
           `{(forall a a', B a a' -> C a a' ⇀ D a a') ≲ (hset B_ -> hset C_ ⇀ hset D_)} :
  (forall a a', B a a' -> C a a' -> D a a') -> B_ -> C_ ⇀ D_.
  intros ff. pose (c := fun a a' b c => creturn (ff a a' b c)).
  refine (c_fun c).
  exact H.
Defined. 
  (* := *)
  (* fun ff => c_fun (fun a a' (b:hset B_ _) (c : hset C_ _) => creturn (ff a a' b c)). *)

(** ** Domain transformation: *)

Instance HOCoercion_easy (A:HSet) (B: A -> HSet) (C:HSet)(C': HSet)
         
         (H: B ≲K□ C) 
  : (* ------------------------------------*)
         (forall a, B a ⇀ C')  ≲ (C ⇀ C')  
  | 0
  := {| c_fun := Build_Mon (to_simpl_dom : (∀ a : A, B a ⇀ C') -> C ⇀ C') _ _;
        c_isconn := {| c_inv := Build_Mon to_dep_dom _ _ |}|}. 
Proof.
  + intros f g Hfg c. cbn in *. unfold to_simpl_dom.
    destruct (c_to_a c) as [a|]; simpl; eauto.
    destruct (to_dep a c) as [b|]; simpl; eauto.
    specialize (Hfg a b). revert Hfg. destruct (f a b); simpl; eauto.
  + cbn. unfold to_simpl_dom. intro x.
    destruct (c_to_a x) as [a|]; simpl; eauto; try apply irr_Fail.
    destruct (to_dep a x); simpl; eauto; apply irr_Fail.
  + intros f g Hfg a b. cbn in *. unfold to_dep_dom, kleisliComp.
    destruct (to_simpl b) as [c | c]; simpl; eauto. 
    specialize (Hfg c). revert Hfg. simpl. destruct (f c) as [c' | c']; simpl; eauto.
  + cbn. unfold to_dep_dom, kleisliComp. intros a b. 
    destruct (to_simpl b) as [c | c]; simpl; eauto; try apply irr_Fail.
  + intros f a b. simpl. 
    unfold compose, to_dep_dom, to_simpl_dom in *; simpl in *.
    assert (H'1'1: (c_to_a °° (pc_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
      by apply prop_c_to_a.
    unfold kleisliComp in H'1'1. unfold to_simpl, b_to_c.
    unfold to_dep, to_rich. simpl. 
    pose (r:=pc_sect (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ _ ))  _ b).
    generalize dependent r. unfold kleisliComp, to_simpl. cbn in *.  simpl. 
    unfold to_simpl, to_dep, b_to_c, compose.
    revert H'1'1. 
    Set Printing All. simpl. 
    destruct ((@pc_fun (sigT_HSet C (fun c : _typeS C => @P A B C H a c)) C
                 (@partial_equiv A B C H a)
                 (@e_fun (_typeS (B a))
                    (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H a x)))
                    (@total_equiv A B C H a) b))) as [c|c]; simpl ; eauto. 
    simpl; intro e. rewrite e. clear e. simpl in *.
    Unset Printing All. 
    destruct (pc_inv _ c) as [c0|]; simpl; eauto.
    intro e. inversion e. unfold id. rewrite <- H1. 
    destruct (f a b) as [c''|]; simpl; eauto. 
    intro e; inversion e.
    intro e; inversion e.
  + intros f c.
    unfold compose, to_dep_dom, to_simpl_dom, to_dep, to_rich, to_simpl in *; simpl in *.
    destruct (c_to_a c) as [a|]; simpl; eauto.
    pose (r:= pc_retr (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ a)) _ c). unfold kleisliComp in *.
    generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
    destruct (pc_inv _ c) as [s|]; simpl ; eauto.
    destruct ( @pc_fun (sigT_HSet C (fun c0 : _typeS C => @P A B C H a c0)) C
            (@partial_equiv A B C H a)
            (@e_fun (_typeS (B a))
               (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H a x)))
               (@total_equiv A B C H a)
               (@e_inv (_typeS (B a))
                  (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H a x)))
                  (@e_fun (_typeS (B a))
                     (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H a x)))
                     (@total_equiv A B C H a))
                  (@e_isequiv (_typeS (B a))
                     (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H a x)))
                     (@total_equiv A B C H a)) s))) as [s'|]; simpl; eauto. 
    intro e. inversion e. clear e.   
    unfold id. destruct (f c); simpl ; eauto.
  (* + intro f. apply funext. intro. cbn. apply is_hprop. *)
Defined.

(** ** Domain & co-domain transformation: *)

(* =HODepEquiv= *)
Instance HOCoercion 
  {A:HSet} {B_1 B_2: A -> HSet} {C_1 C_2 : HSet}: 
  (B_1 ≲K□ C_1) -> (B_2 ≲K□ C_2) -> (forall a, B_1 a ⇀ (B_2 a))  ≲ (C_1 ⇀ C_2)
  := fun _ _ =>
       {| c_fun := Build_Mon
                    (fun f => to_simpl_dom (fun a b => x <- f a b; to_simpl x)) _ _ ; 
        c_isconn := {| c_inv := Build_Mon 
                    (fun f a b => x <- to_dep_dom f a b; to_dep _ x) _ _ |}|}.
(* =end= *)
Proof.
+ intros f g Hfg c. cbn in *. unfold to_simpl_dom.
  destruct (c_to_a c) as [a|]; simpl; eauto.
  destruct (to_dep a c) as [b|]; simpl; eauto.
  specialize (Hfg a b). revert Hfg. destruct (f a b); simpl; eauto.
  destruct (g a b) as [b1|]; simpl; intro e; inversion e; try reflexivity.
  destruct (to_simpl b1); simpl; eauto.
+ cbn. unfold to_simpl_dom. intro x.
  destruct (c_to_a x) as [a|]; simpl; eauto; try apply irr_Fail.
  destruct (to_dep a x); simpl; eauto; apply irr_Fail.
+ intros f g Hfg a b. cbn in *. unfold to_dep_dom, to_dep_dom, kleisliComp.
  destruct (to_simpl b) as [c | c]; simpl; eauto. 
  specialize (Hfg c). revert Hfg. destruct (f c); simpl; eauto.
  destruct (g c) as [c1 | c1]; simpl; intro e; inversion e.
  subst. destruct (to_dep a c1); simpl; eauto.
+ cbn. unfold to_dep_dom, kleisliComp. intros a b. 
  destruct (to_simpl b); simpl; eauto; try apply irr_Fail.
+ intros f a b.  unfold compose, id in *. cbn in *. 
  unfold to_dep_dom, to_dep_dom, to_simpl_dom in *.

    assert (H'1'1: (c_to_a °° (pc_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
    by apply prop_c_to_a.
  unfold kleisliComp in H'1'1. unfold to_simpl, b_to_c.


    unfold to_dep, to_rich. simpl. 
    pose (r := pc_sect (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ a )) _ b).
    generalize dependent r. unfold kleisliComp, to_simpl. cbn in *.  simpl. 
  unfold to_simpl, to_dep, b_to_c,compose.
  revert H'1'1.
  Set Printing All. simpl. 
  destruct (@pc_fun (sigT_HSet C_1 (fun c : _typeS C_1 => @P A B_1 C_1 d a c)) C_1
                 (@partial_equiv A B_1 C_1 d a)
                 (@e_fun (_typeS (B_1 a))
                    (@sigT (_typeS C_1)
                       (fun x : _typeS C_1 => _typeP (@P A B_1 C_1 d a x)))
                    (@total_equiv A B_1 C_1 d a) b)) as [c | c]; simpl; eauto.
  Unset Printing All. 
  intro e; rewrite e. clear e. simpl in *. unfold to_rich. 
  destruct (pc_inv _ c) as [s | ]; simpl; eauto.
  intro e; inversion e. unfold id.
  destruct (f a
      (@e_inv (_typeS (B_1 a))
         (@sigT (_typeS C_1) (fun x : _typeS C_1 => _typeP (@P A B_1 C_1 d a x)))
         (@e_fun (_typeS (B_1 a))
            (@sigT (_typeS C_1) (fun x : _typeS C_1 => _typeP (@P A B_1 C_1 d a x)))
            (@total_equiv A B_1 C_1 d a))
         (@e_isequiv (_typeS (B_1 a))
            (@sigT (_typeS C_1) (fun x : _typeS C_1 => _typeP (@P A B_1 C_1 d a x)))
            (@total_equiv A B_1 C_1 d a)) s) ) as [b0 |]; simpl; eauto. 
  pose (r := pc_sect (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ _ )) _ b0). simpl in r.
  generalize dependent r. unfold kleisliComp, to_simpl, to_dep, b_to_c, c_to_b,compose. 
  Set Printing All. simpl. 
  destruct (@pc_fun (sigT_HSet C_2 (fun c0 : _typeS C_2 => @P A B_2 C_2 d0 a c0)) C_2
                (@partial_equiv A B_2 C_2 d0 a)
                (@e_fun (_typeS (B_2 a))
                   (_typeS (sigT_HSet C_2 (fun c0 : _typeS C_2 => @P A B_2 C_2 d0 a c0)))
                   (@total_equiv A B_2 C_2 d0 a) b0)) as [c' | ]; simpl; eauto.
  Unset Printing All. 
  intro e; inversion e. 
  intro e; inversion e. 
  (* destruct (pc_inv _ c'); simpl; eauto.  *)
+ intros f x. cbn in *. 
  unfold compose, id, to_dep_dom, to_dep_dom, to_simpl_dom, to_simpl, clift, to_dep, to_rich in *;
    simpl in *.
  destruct (c_to_a x) as [a|]; simpl ; eauto. 
  pose (r := pc_retr (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _  a)) _ x). unfold kleisliComp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
  destruct (pc_inv _ x) as [s|]; simpl ; eauto.
  destruct (@pc_fun (sigT_HSet C_1 (fun c : _typeS C_1 => @P A B_1 C_1 d a c)) C_1
            (@partial_equiv A B_1 C_1 d a)
            (@e_fun (_typeS (B_1 a))
               (@sigT (_typeS C_1) (fun x0 : _typeS C_1 => _typeP (@P A B_1 C_1 d a x0)))
               (@total_equiv A B_1 C_1 d a)
               (@e_inv (_typeS (B_1 a))
                  (@sigT (_typeS C_1)
                     (fun x0 : _typeS C_1 => _typeP (@P A B_1 C_1 d a x0)))
                  (@e_fun (_typeS (B_1 a))
                     (@sigT (_typeS C_1)
                        (fun x0 : _typeS C_1 => _typeP (@P A B_1 C_1 d a x0)))
                     (@total_equiv A B_1 C_1 d a))
                  (@e_isequiv (_typeS (B_1 a))
                     (@sigT (_typeS C_1)
                        (fun x0 : _typeS C_1 => _typeP (@P A B_1 C_1 d a x0)))
                     (@total_equiv A B_1 C_1 d a)) s))) as [c | c]; simpl; eauto.
  intro e. inversion e. simpl. 
  destruct (f x) as [c0 | c0]; simpl; eauto. 
  pose (r := pc_retr (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ a)) _ c0). unfold kleisliComp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl. 
  destruct (pc_inv _ c0); simpl ; eauto.
(* + intro f. apply funext. intro. simpl. apply is_hprop. *)
Defined.
  
(** ** Argument reordering: *)

(* =HODepEquiv2_sym= *)
Instance HOCoercion2_sym
   (A A':HSet) (B_1 B_2 B_3 : A -> A' -> HSet) {C_1 C_2 C_3 : HSet}
  `{ (forall a a', B_2 a a' -> B_1 a a' ⇀ B_3 a a') ≲ (C_2 -> C_1 ⇀ C_3) } :
    (forall a a', B_1 a a' -> B_2 a a' ⇀ B_3 a a') ≲ (C_1 -> C_2 ⇀ C_3) 
(* =end= *)
  | 100
  := {| c_fun := Build_Mon (fun ff b_ c_ => c_fun (fun a a' c b => ff a a' b c) c_ b_) _ _; 
        c_isconn :=
          {|c_inv := Build_Mon (fun ff a a' b c => (c_inv _ (IsConnection := c_isconn (Coercion := H))) (fun c b => ff b c) _ _ c b) _ _ |}|}.
Proof.
  - intros x y H0 b c.
    pose (x' := fun a a' c b => x a a' b c).
    pose (y' := fun a a' c b => y a a' b c).
    assert (e : x' ≼ y'). intros x1 x2 x3 x4. apply H0. 
    apply ((c_fun (Coercion := H)).(mon) e).
  - intros b c.
    exact ((c_fun (Coercion := H)).(p_mon _ _) c b).
  - intros x y H0 a a' b c.
    pose (x' := fun c b => x b c).
    pose (y' := fun c b => y b c).
    assert (e : x' ≼ y'). intros x1 x2. apply H0. 
    apply ((c_inv _ (IsConnection := c_isconn (Coercion := H))).(mon) e).
  - intros a a' b c. 
    exact ((c_inv _ (IsConnection := c_isconn (Coercion := H))).(p_mon _ _) a a' c b).
  - intros f a a' b c. 
    exact (c_sect _ (IsConnection := c_isconn (Coercion := H)) (fun a a' c b => f a a' b c) a a' c b).
  - intros f b c.
    exact (c_retr _ (IsConnection := c_isconn (Coercion := H)) (fun c b => f b c) _ _).
  (* - simpl. intros f. apply funext. intro b. *)
  (*   apply funext; intro c. apply is_hprop. *)
Defined.

(** ** Arity 2 types: *)

Hint Extern 1 (IsConnection ?f) => apply (c_isconn (Coercion := _)) :
             typeclass_instances.

(* =HOCoercion_2_fun= *)
Definition HOCoercion_2_fun 
  {A A':HSet} {B_1: A -> HSet} {B_2 B_3 : A -> A' -> HSet} {C_1 C_2 C_3:HSet} :
  (B_1 ≲K□ C_1) -> (forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a')  ≲ (C_2 ⇀ C_3))) -> 
  (forall a a', B_1 a → B_2 a a' ⇀ B_3 a a') -> C_1 -> C_2 ⇀ C_3 :=
  fun _ _ f c_1 c_2 => to_simpl_dom (fun a b_1 => c_fun (fun a' => f a a' b_1) c_2) c_1. 
(* =end= *)

(* =to_dep_dom2= *)
Definition HOCoercion_2_inv  {A A':HSet} {B_1: A -> HSet} {B_2 B_3 : A -> A' -> HSet} {C_1 C_2 C_3:HSet} :
  (B_1 ≲K□ C_1) -> (forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a') ≲ (C_2 ⇀ C_3))) ->
  (C_1 → C_2 ⇀ C_3) -> ∀ a a', B_1 a → B_2 a a' ⇀ B_3 a a' :=
  fun _ H f a a' b_1 b_2 => 
    c_inv (c_fun (Coercion := H a)) (fun x => c_1 <- to_simpl b_1; f c_1 x) _ b_2.
(* =end= *)

(* =HODepEquiv2= *)
Instance HOCoercion_2 
  (A A':HSet) (B_1: A -> HSet) (B_2 B_3  : A -> A' -> HSet) (C_1 C_2 C_3: HSet) :
  (B_1 ≲K□ C_1) -> (forall a, ((forall a':A', B_2 a a' ⇀ B_3 a a')  ≲ (C_2 ⇀ C_3))) ->
  (forall a a', B_1 a -> B_2 a a' ⇀ B_3 a a') ≲ (C_1 -> C_2 ⇀ C_3).
(* =end= *)
Proof.
    unshelve refine (fun H H' => 
  {| c_fun := Build_Mon (HOCoercion_2_fun H H') _ _ ; 
     c_isconn := {|  c_inv := Build_Mon (HOCoercion_2_inv H H') _ _ |}|}).
  + intros f g e b c. simpl. unfold HOCoercion_2_fun, to_simpl_dom.
    destruct (c_to_a b) as [a|] ;simpl; eauto. 
    destruct (to_dep a b) ;simpl; eauto.
    refine ((c_fun (Coercion := H' a)).(mon) _ _).
    intros x1 x2. apply e.
  + cbn. unfold HOCoercion_2_fun, to_simpl_dom. intros b c.
    destruct (c_to_a b) as [a|]; simpl; eauto; try apply fail_contr.
    destruct (to_dep a b); simpl; eauto; try apply fail_contr.
    apply (c_fun (Coercion := H' a) .(p_mon _ _) c).
  + intros f g e a a' b c. simpl. unfold to_dep_dom2.
    refine ((c_inv _ (IsConnection := c_isconn (Coercion := H' a))).(mon) _ _ _).
    intros x1. cbn. destruct (to_simpl b) as [c'| c']; simpl ; eauto. apply e.
  + cbn. unfold HOCoercion_2_inv, to_simpl_dom. intros a a' b c.
    destruct (to_simpl b) as[s | s]; simpl; try apply fail_contr; auto.
    apply (c_inv _ (IsConnection := c_isconn (Coercion := H' a)) .(p_mon _ _) a' c).
    assert ((λ _ : C_2, @Fail C_3 _ s) = (λ _ : C_2, @Fail C_3 _ (_with "bot"))).
    apply funext. intro. apply ap. apply is_hprop.
    rewrite H0. apply (c_inv _ (IsConnection := c_isconn (Coercion := H' a)) .(p_mon _ _) a' c).
  + intros ff a a' b c.
     unfold compose, HOCoercion_2_inv, HOCoercion_2_fun, to_simpl_dom in *; simpl in *.
  assert (H'1'1: (c_to_a °° (pc_fun (partial_equiv a))) (e_fun (total_equiv a) b) = Some a)
    by apply prop_c_to_a.
  unfold kleisliComp in H'1'1. unfold to_simpl, b_to_c.
  unfold to_dep, to_rich. simpl. 
pose (r := pc_sect (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ _ )) _ b).
  generalize dependent r. unfold kleisliComp, to_simpl. cbn in *.  simpl. 
  unfold to_simpl, to_dep, b_to_c,compose.
  revert H'1'1. cbn.
  Set Printing All. simpl. 
  destruct (@pc_fun (sigT_HSet C_1 (fun c0 : _typeS C_1 => @P A B_1 C_1 H a c0)) C_1
                 (@partial_equiv A B_1 C_1 H a)
                 (@e_fun (_typeS (B_1 a))
                    (@sigT (_typeS C_1)
                       (fun x : _typeS C_1 => _typeP (@P A B_1 C_1 H a x)))
                    (@total_equiv A B_1 C_1 H a) b)) as [c0 | c0]; simpl; eauto.
  intro e; rewrite e. clear e. simpl in *. unfold to_rich.
  Unset Printing All. 
  destruct (pc_inv _ c0); simpl; eauto.
  intro e. inversion e. rewrite <- H1.
     
    exact (c_sect (IsConnection := c_isconn (Coercion := _)) _ (fun a' c => ff a a' b c) a' c).
    intro e; inversion e. 
    intro e; inversion e. 
  + intros ff b c. 
    unfold compose, HOCoercion_2_fun, to_simpl_dom, HOCoercion_2_inv in *; simpl in *.
    destruct (c_to_a b) as [a|];simpl; [ |eauto].
    unfold to_dep, to_rich.
    pose (r := pc_retr (IsConnectionK := pc_isconn (c := DepCoercion_ConnectionK _ _ _ a)) _ b). unfold kleisliComp in *.
  generalize dependent r. cbn in *. unfold to_dep, to_rich, to_simpl,compose. 
  destruct (pc_inv _ b) as [s|]; simpl ; eauto.
  pose (e_retr (IsEquiv := e_isequiv (e := total_equiv a)) _ s).
  pose (r := c_retr (IsConnection := c_isconn (Coercion := H' a)) _ (DepEquiv.to_dep_dom2 ff a (c_to_b s)) c).
  generalize dependent r.
  unfold DepEquiv.to_dep_dom2; cbn. unfold id, to_simpl. simpl. 
  unfold compose, b_to_c, c_to_b in *.
  Set Printing All. simpl in *. rewrite e. clear e. unfold id. Unset Printing All. 
  destruct (pc_fun (partial_equiv a) s) as [c'|i]; simpl; eauto. 
  intros e' e; inversion e. rewrite <- H1 in *. clear e H1. revert e'. 
  exact id. 
  intros e _. revert e. 
  pose (F := c_fun (c_inv _ (IsConnection := c_isconn (Coercion := H' a)) (λ _ : C_2, @Fail C_3 _ i))).
  simpl in *.
  change (F c ≼ @Fail _ info_str i -> F c ≼ ff b c).
  destruct (F c); simpl; eauto. 
  intro e; inversion e. 
  (* + intro f. apply funext. intro. simpl. apply funext. intro. *)
  (*   apply is_hprop. *)
Defined.

(* This instance must be here because before, it would break some
   type class inferences, I don't understand why ?*)

(* =DepEquivInj= *)
Instance Coercion_Inj (A A': HSet)(B: A -> HSet)(C: HSet) 
  (f : A' -> A) `{IsInjective _ _ f} 
  `{B ≲K□ C} : (fun a => B (f a)) ≲K□ C 
(* =end= *)                       
  := Build_DepCoercion A' (fun a => B (f a)) C (fun a c => P (f a) c)
                    (fun a' => total_equiv (f a'))
                    (λ a : A', partial_equiv (f a))
                    (fun c => a <- c_to_a c; f^?-1 a) _. 
Proof.
  intros a' b. simpl. 
  pose (prop_c_to_a (f a') b). generalize dependent e. unfold kleisliComp, b_to_c.
  Set Printing All. simpl. 
  destruct (@pc_fun (sigT_HSet C (fun c : _typeS C => @P A B C H0 (f a') c)) C
                (@partial_equiv A B C H0 (f a'))
                (@e_fun (_typeS (B (f a')))
                   (@sigT (_typeS C) (fun x : _typeS C => _typeP (@P A B C H0 (f a') x)))
                   (@total_equiv A B C H0 (f a')) b)) as [c|]; simpl; intro e;inversion e. 
  rewrite e. simpl.
  Unset Printing All. 
  apply (i_sect a').
Defined.