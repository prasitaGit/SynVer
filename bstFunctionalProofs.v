Require Import VST.floyd.proofauto.

Definition key := Z.
Definition value := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> value -> tree -> tree.


Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : Z :=
  match t with
  | E => (-1)
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint lookupn (x: key) (t : tree) : bool :=
  match t with
  | E => false
  | T tl k v tr => if x <? k then lookupn x tl
                           else if k <? x then lookupn x tr
                           else true
  end.

Fixpoint isSkewed (t : tree) : Prop :=
  match t with
  | E => True
  | T tl k v tr => match (tl, tr) with 
                   | (E, _) => isSkewed tr 
                   | (_, E) => isSkewed tl 
                   | (_, _) => False 
                  end 
  end.

Fixpoint insert (x: key) (v: Z) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint inorderSuccessor (t: tree) : tree :=
  match t with
  | E => t
  | T lt k v rt => match lt with 
                   | E => t 
                   | _ => inorderSuccessor lt 
                   end
  end.

Fixpoint inorderSuccessorKey (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                    | E => k 
                    | _ => inorderSuccessorKey lt 
                    end
  end.

Fixpoint inorderMaxKey (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match rt with 
                   | E => k 
                   | _ => inorderMaxKey rt 
                   end
  end.


Fixpoint inorderSuccessorValue (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                   | E => v 
                   | _ => inorderSuccessorValue lt 
                   end
  end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else (match (a, b) with 
                             | (E, _) => b 
                             | (_, E) => a 
                             | (_, _) => let k' := inorderSuccessorKey b in 
                                        (let v'' := inorderSuccessorValue b in 
                                          T a k' v'' (delete k' b)
                                        )
                            end)
 end.

Fixpoint deleteWand (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if  x <? y then T (deleteWand x a) y v' b
                         else if y <? x then T a y v' (deleteWand x b)
                         else (match (a, b) with 
                              | (E, _) => b 
                              | (_, E) => a 
                              | (_, _) => let xn := inorderSuccessor b in 
                                           match xn with 
                                           | E => b
                                           | T lt key v rt => T a key v (deleteWand key b)
                                           end  
                             end)
  end.

Fixpoint ForallS (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => ((l = E) \/ (r = E)) /\ ForallS l /\ ForallS r
  end. 
  
Fixpoint ForallLookup (k' : key) (t: tree) : Prop :=
  match t with
  | E => False
  | T l k v r => (k = k') \/ ( k' < k /\ ForallLookup k' l) \/ (k' > k /\ ForallLookup k' r)
  end. 
  
Fixpoint ForallT (P: key -> Prop) (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => P k /\ ForallT P l /\ ForallT P r
  end.

Inductive BST : tree -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
      ForallT (fun y => y < x) l ->
      ForallT (fun y => y > x) r ->
      BST l ->
      BST r ->
      BST (T l x v r).  


Lemma nullIsBST:  BST E.
Proof.
  constructor.
Qed.

Lemma leafIsBST: forall k v, BST (T E k v E).
Proof.
  intros. constructor. simpl. auto. 
  simpl. auto. constructor. constructor.
Qed.

Lemma lookupCorrectness: forall k t, BST t -> (lookupn k t = true <-> ForallLookup k t).
Proof. 
  induction t; intros; simpl. 
  split; intros. inversion H0. inversion H0. 
  split; intros. destruct (k =? k0) eqn:Hkk0. assert (k = k0) by lia; subst. 
  left. reflexivity. destruct (k <? k0) eqn:Hkl. assert (k < k0) by lia. 
  right. left. split. lia. apply IHt1. inversion H; subst. assumption. assumption. 
  assert (k > k0) by lia. right. right. apply Z.gt_lt in H1. apply Z.ltb_lt in H1. 
  rewrite H1 in H0. split. lia. apply IHt2. inversion H; subst. assumption. assumption. 
  destruct H0 as [? | ?]. subst. rewrite Z.ltb_irrefl. reflexivity. 
  destruct H0 as [? | ?]. destruct H0 as [? ?]. apply Z.ltb_lt in H0. rewrite H0. 
  apply IHt1 in H1. assumption. inversion H; subst. assumption. 
  destruct H0 as [? ?]. assert (~ k < k0) by lia. 
  apply Z.ltb_nlt in H2. rewrite H2. apply Z.gt_lt in H0. apply Z.ltb_lt in H0. 
  rewrite H0. apply IHt2 in H1. assumption. inversion H; subst. assumption.
Qed.

Lemma skewedCorrectness: forall t, (isSkewed t <-> ForallS t).
Proof. 
  induction t; split; intros. 
  simpl. auto. 
  simpl. reflexivity. 
  simpl. simpl in H. destruct t1 eqn:Ht1.  split. left. reflexivity. 
  split. simpl. auto. apply IHt2. assumption. 
  destruct t2 eqn:Ht2. split. right. reflexivity. 
  split. apply IHt1. assumption. simpl. auto. inversion H. 
  simpl. inversion H; subst. destruct H1 as [? ?]. destruct H0 as [? | ?]. 
  subst.  apply IHt2. assumption. 
  subst.  destruct t1 eqn:Ht1.  simpl. auto. 
  apply IHt1. assumption.
Qed.

Lemma insertUBFacts: forall t x k v, 
ForallT (fun y => y < x) t -> k < x ->
ForallT (fun y => y < x) (insert k v t).
Proof. 
  induction t; intros; simpl. 
  split. assumption. auto. 
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  inversion H. destruct H3 as [? ?]. constructor. assumption. 
  split. specialize IHt1 with x k0 v0. apply IHt1 in H3. assumption. 
  lia. assumption. assert (k0 >= k) by lia. apply Z.ge_le in H1. 
  destruct (k <? k0) eqn:Hkk0. assert (k < k0) by lia. constructor. lia. 
  inversion H; subst. destruct H4 as [? ?]. split. assumption. 
  specialize IHt2 with x k0 v0. apply IHt2 in H5. assumption. lia. 
  constructor. lia. inversion H; subst. assumption.
Qed.

Lemma insertLBFacts: forall t x k v, 
ForallT (fun y => y > x) t -> k > x ->
ForallT (fun y => y > x) (insert k v t).
Proof. 
  induction t; intros; simpl. 
  split. assumption. auto. 
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  inversion H. destruct H3 as [? ?]. constructor. assumption. 
  split. specialize IHt1 with x k0 v0. apply IHt1 in H3. assumption. 
  lia. assumption. assert (k0 >= k) by lia. apply Z.ge_le in H1. 
  destruct (k <? k0) eqn:Hkk0. assert (k < k0) by lia. inversion H; subst. 
  constructor. lia. destruct H4 as [? ?]. split.  assumption. 
  specialize IHt2 with x k0 v0. apply IHt2 in H5. assumption. lia. 
  constructor. lia. inversion H; subst. assumption.
Qed.

Lemma inorderSuccBaseCase: forall k v lr, inorderSuccessorKey (T E k v lr) = k.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma inSuccLemma: forall k v lr lt' k' v' lr', inorderSuccessorKey (T (T lt' k' v' lr') k v lr) = inorderSuccessorKey (T lt' k' v' lr').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma inMaxLemma: forall k v lt lt' k' v' lr', inorderMaxKey (T lt k v (T lt' k' v' lr')) = inorderMaxKey (T lt' k' v' lr').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma inSuccNodeLemma: forall k v lr lt' k' v' lr', inorderSuccessor (T (T lt' k' v' lr') k v lr) = inorderSuccessor (T lt' k' v' lr').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma forallLessThanProperty: forall t x, ForallT (fun y => y < x) t -> ForallT (fun y => y <= x) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. destruct H1 as [? ?]. simpl. split. 
  lia. split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma forallGreaterThanProperty: forall t x, ForallT (fun y => y > x) t -> ForallT (fun y => y >= x) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. destruct H1 as [? ?]. simpl. split. 
  lia. split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma succHelper: forall lt k v lr,  BST (T lt k v lr) -> (lt <> E) -> k > inorderSuccessorKey lt.
Proof.
  induction lt; intros. 
  contradiction. 
  destruct lt1 eqn:Hlt1. simpl. inversion H; subst. 
  inversion H5; subst. lia. 
  rewrite inSuccLemma. apply IHlt1 with v0 lr. constructor.
  inversion H; subst.  inversion H5; subst. destruct H2 as [? ?]. 
  assumption. inversion H; subst. assumption. 
  inversion H; subst. inversion H7; subst. assumption. 
  inversion H; subst. assumption. unfold not. intros. inversion H1. 
Qed.

Lemma forallTProperty: forall t x k, x > k -> ForallT (fun y => y > x) t -> ForallT (fun y => y > k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H0; subst. destruct H2 as [? ?]. split. lia. 
  split. apply IHt1 with x. lia. assumption. 
  apply IHt2 with x. lia. assumption.
Qed.

Lemma forallTLtProperty: forall t x k, x < k -> ForallT (fun y => y < x) t -> ForallT (fun y => y < k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H0; subst. destruct H2 as [? ?]. split. lia. 
  split. apply IHt1 with x. lia. assumption. 
  apply IHt2 with x. lia. assumption.
Qed.

Lemma forallTGtNotProperty: forall t k, ForallT (fun y => y > k) t -> ForallT (fun y => y <> k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H; subst. destruct H1 as [? ?]. split. lia. 
  split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma forallTNotLtGtProperty: forall t k, ForallT (fun y => y <> k) t <-> ForallT (fun y => y < k \/ y > k) t. 
Proof.
  induction t; split; intros. 
  simpl. auto. simpl. auto. 
  inversion H; subst. destruct H1 as [? ?].  
  simpl. split. lia. split. apply IHt1. assumption.
  apply IHt2. assumption. simpl. inversion H; subst. 
  split. lia. split. apply IHt1. destruct H1 as [? ?]. 
  assumption. apply IHt2. destruct H1 as [? ?]. 
  assumption. 
Qed.

Lemma forallTLtNotProperty: forall t k, ForallT (fun y => y < k) t -> ForallT (fun y => y <> k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H; subst. destruct H1 as [? ?]. split. lia. 
  split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma inorderSuccRange: forall t lo hi, BST t -> t <> E -> ForallT (fun y => y > lo) t -> ForallT (fun y => y < hi) t -> 
lo < inorderSuccessorKey t < hi.
Proof.
  induction t; intros. contradiction.  
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. inversion H2; subst. lia. 
  rewrite inSuccLemma. apply IHt1.
  inversion H; subst. assumption. unfold not. intros. inversion H3. 
  inversion H1; subst. destruct H4 as [? ?]. assumption. 
  inversion H2; subst. destruct H4 as [? ?]. assumption.
Qed.

Lemma inorderSuccHi: forall t hi, BST t -> t <> E ->  ForallT (fun y => y < hi) t -> 
inorderSuccessorKey t < hi.
Proof.
  induction t; intros. contradiction.   
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. lia.  
  rewrite inSuccLemma. apply IHt1. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderSuccLo: forall t lo, BST t -> t <> E ->  ForallT (fun y => y > lo) t -> 
inorderSuccessorKey t > lo.
Proof.
  induction t; intros. contradiction.   
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. lia.  
  rewrite inSuccLemma. apply IHt1. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderMaxHi: forall t hi, BST t -> t <> E ->  ForallT (fun y => y < hi) t -> 
inorderMaxKey t < hi.
Proof.
  induction t; intros. contradiction.   
  destruct t2 eqn:Ht2. simpl. 
  inversion H1; subst. lia.  
  rewrite inMaxLemma. apply IHt2. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderMaxLo: forall t lo, BST t -> t <> E ->  ForallT (fun y => y > lo) t -> 
inorderMaxKey t > lo.
Proof.
  induction t; intros. contradiction.   
  destruct t2 eqn:Ht2. simpl. 
  inversion H1; subst. lia.  
  rewrite inMaxLemma. apply IHt2. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderSuccHelperRoot: forall lt k v lr,
BST (T lt k v lr) -> lt <> E -> inorderSuccessorKey (T lt k v lr) < k.
Proof.
  induction lt; intros. contradiction.  
  inversion H; subst. inversion H5; subst. 
  destruct lt1 eqn:Hlt1. simpl. lia. 
  apply IHlt1 with k v lt2 in H7. rewrite inSuccLemma. lia. 
  unfold not. intros. inversion H3.
Qed.

Lemma inorderSuccProperty: forall lr lt k v, BST (T lt k v lr) -> (lr <> E) ->
ForallT (fun y => y >= (inorderSuccessorKey lr)) lr /\ (k < (inorderSuccessorKey lr)).
Proof.
  induction lr; intros. 
  contradiction. 
  inversion H; subst. destruct lr1 eqn:Hlr1. split. 
  rewrite inorderSuccBaseCase. simpl. split. lia. split. 
  auto. inversion H8; subst. apply forallGreaterThanProperty. assumption. 
  simpl. inversion H6; subst. lia.  rewrite inSuccLemma.
  assert (T t1 k1 v1 t2 <> E). unfold not. intros. inversion H1. 
  apply IHlr1 with lt k0 v in H1. destruct H1 as [? ?].  split. 
  split.  inversion H8; subst. inversion H6; subst. destruct H4 as [? ?]. 
  apply inorderSuccRange with (T t1 k1 v1 t2) k0 k in H13. lia. 
  unfold not. intros. inversion H10. assumption. assumption.  
  split. assumption. apply forallGreaterThanProperty.  
  inversion H8; subst. apply inorderSuccRange with (T t1 k1 v1 t2) k0 k in H13. 
  apply forallTProperty with k. lia. assumption. unfold not. intros. inversion H3. 
  inversion H6; subst. destruct H4 as [? ?]. assumption. assumption. assumption.
  constructor. assumption. inversion H6; subst. destruct H3 as [? ?]. 
  assumption. assumption. inversion H8; subst. assumption. 
Qed.

Lemma minKeyProperty: forall t, BST t -> ForallT (fun y => y >= (inorderSuccessorKey t)) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. simpl. split. 
  destruct t1. lia. apply inorderSuccHi with (T t1_1 k0 v0 t1_2) k in H4. lia. 
  assumption. unfold not. intros. inversion H0. 
  split. destruct t1. simpl. auto. 
  apply IHt1 in H6. assumption. 
  destruct t1. apply forallGreaterThanProperty. assumption. 
  apply IHt1 in H6. apply inorderSuccHi in H4. eapply forallTProperty in H5. 
  apply forallGreaterThanProperty. eassumption. lia. inversion H; subst. inversion H10; subst.
  constructor; try assumption. unfold not. intros. inversion H0. 
Qed.

Lemma maxKeyProperty: forall t, BST t -> ForallT (fun y => y <= (inorderMaxKey t)) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. simpl. split. 
  destruct t2. lia. apply inorderMaxLo with (T t2_1 k0 v0 t2_2) k in H5.  lia.
  assumption. unfold not. intros. inversion H0. 
  split. destruct t2. apply forallLessThanProperty. assumption. 
  apply inorderMaxLo in H5. eapply forallTLtProperty in H4. 
  apply forallLessThanProperty. eassumption. lia. 
  assumption. unfold not. intros. inversion H0. 
  destruct t2. simpl. auto. 
  apply IHt2 in H7. assumption. 
Qed.

Lemma deleteUBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y < x) t ->
ForallT (fun y => y < x) (delete k t).
Proof. 
  induction t; intros; simpl. auto.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. inversion H0; subst. destruct H3 as [? ?].
  split. lia. split. apply IHt1. inversion H; subst. assumption. assumption. assumption. 
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  assert (k < k0) by lia. simpl. inversion H0; subst. destruct H4 as [? ?]. 
  split. lia. split. assumption. apply IHt2. inversion H; subst. assumption.  assumption.
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.  
  inversion H0; subst. destruct H3 as [? ?]. destruct t2 eqn:Ht2. 
  destruct t1 eqn:Ht1. simpl. auto. assumption. 
  destruct t1 eqn:Ht1. assumption. split. apply inorderSuccHi. inversion H; subst. 
  assumption. unfold not. intros. inversion H5. assumption. split. assumption. 
  apply IHt2. inversion H; subst. assumption. assumption.
Qed.

Lemma deleteLBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y > x) t ->
ForallT (fun y => y > x) (delete k t).
Proof. 
  induction t; intros; simpl. auto.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. inversion H0; subst. destruct H3 as [? ?].
  split. lia. split. apply IHt1. inversion H; subst. assumption. assumption. assumption. 
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  assert (k < k0) by lia. simpl. inversion H0; subst. destruct H4 as [? ?]. 
  split. lia. split. assumption. apply IHt2. inversion H; subst. assumption.  assumption.
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.  
  inversion H0; subst. destruct H3 as [? ?]. destruct t2 eqn:Ht2. 
  destruct t1 eqn:Ht1. simpl. auto. assumption. 
  destruct t1 eqn:Ht1. assumption. split. apply inorderSuccLo. inversion H; subst. 
  assumption. unfold not. intros. inversion H5. assumption. split. assumption. 
  apply IHt2. inversion H; subst. assumption. assumption.
Qed.

Lemma deleteNoDup: forall t k, BST t -> ForallT (fun y => y <> k) (delete k t).
Proof.
  induction t; intros. simpl. auto. 
  simpl. inversion H; subst.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. split. lia. split. apply IHt1. assumption. apply Z.lt_gt in H0. 
  apply forallTProperty with t2 k k0 in H0. apply forallTGtNotProperty. assumption. 
  assumption. assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0.  assert (k < k0) by lia.
  simpl.  split. lia. split. apply forallTLtProperty with t1 k k0 in H1. 
  apply forallTLtNotProperty. assumption. assumption. 
  apply IHt2. assumption. assert (k = k0) by lia. subst. 
  clear Hkk0. clear Hk0k. destruct t1 eqn:Ht1. apply forallTGtNotProperty. 
  assumption. destruct t2 eqn:Ht2. apply forallTLtNotProperty. assumption. 
  split. inversion H; subst. apply inorderSuccProperty in H. 
  lia. unfold not. intros. inversion H1. split. apply forallTLtNotProperty. 
  assumption. apply forallTGtNotProperty. apply deleteLBFacts. 
  assumption. assumption.
Qed.

Lemma insertPreservesBST: forall t k v, BST t -> BST (insert k v t).
Proof. 
  induction t; intros; simpl. 
  apply leafIsBST. 
  destruct (k0 <? k) eqn:Hkk0.  assert (k0 < k) by lia.  constructor. 
  eapply insertUBFacts. inversion H; subst. assumption. lia. inversion H; subst. assumption. 
  inversion H; subst. apply IHt1; try assumption. inversion H; subst. assumption. 
  assert (k0 >= k) by lia. apply Z.ge_le in H0. destruct (k <? k0)  eqn:Hk0k. 
  assert (k < k0) by lia. constructor. inversion H; subst.  assumption. 
  apply insertLBFacts. inversion H; subst. assumption. lia. inversion H; subst. assumption. 
  apply IHt2. inversion H; subst. assumption. assert (k = k0) by lia. subst. 
  inversion H; subst. constructor; try assumption.
Qed.

Lemma forallTContradiction: forall t x, t <> E -> ForallT (fun y => y >= x) t -> ~ (ForallT (fun y => y < x) t). 
Proof.
  induction t; intros. contradiction. 
  unfold not. intros. inversion H0; subst. 
  inversion H1; subst. contradiction.
Qed.

Lemma delKeyProperty: forall t k, BST t -> ForallT (fun y => y >= k) t -> ForallT (fun y => y > k) (delete k t).
Proof.
  induction t; intros. 
  simpl. auto.  
  destruct (k =? k0) eqn:Hkk0. assert (k = k0) by lia. subst. 
  simpl. rewrite Z.ltb_irrefl. destruct t1 eqn:Ht1. inversion H; subst. assumption. 
  inversion H0; subst. destruct H2 as [? ?]. 
  inversion H; subst.  apply forallTContradiction in H2. contradiction. unfold not. 
  intros. inversion H4. destruct (k <? k0) eqn:Hkk. assert (k < k0) by lia.  
  inversion H0; subst. contradiction. assert (k0 < k) by lia. simpl.
  apply Z.ltb_lt in H1. rewrite H1. inversion H0; subst. assert (k0 < k) by lia. constructor. 
  lia. inversion H; subst. destruct H3 as [? ?]. split. apply IHt1. assumption. assumption. 
  apply Z.lt_gt in H4. apply forallTProperty with t2 k k0 in H4. assumption. assumption. 
Qed.


Lemma deletePreservesBST: forall t k, BST t -> BST (delete k t).
Proof. 
  induction t; intros. 
  simpl. constructor.  
  simpl. inversion H; subst.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.   
  constructor. apply deleteUBFacts. assumption. assumption. assumption. 
  apply IHt1. assumption. assumption.
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  constructor. assumption. apply deleteLBFacts. assumption. assumption. 
  assumption. auto. 
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.
  (*destruct t1: E case -> discharged; else destruct t2*)
  destruct t1 eqn:Ht1. assumption. 
  (*destruct t2: E case -> resolved; else -> problemmatic*)
  destruct t2 eqn:Ht2. assumption. constructor. 
  apply inorderSuccProperty in H. destruct H as [? ?]. 
  apply forallTLtProperty with (T t3 k v0 t4) k0 (inorderSuccessorKey (T t5 k1 v1 t6)) in H1. 
  assumption. assumption. unfold not. intros. inversion H1. apply inorderSuccProperty in H. 
  destruct H as [? ?]. apply delKeyProperty. assumption. assumption. unfold not. intros. 
  inversion H1. assumption. apply IHt2. assumption.
  Qed.


Definition insListSpec (l : list Z) (t : tree) := fold_left (fun t k => insert k 0 t) l t.

Lemma insListDistribute : forall a l t, insListSpec (a :: l) t = insListSpec l (insert a 0 t).
Proof.
  intros. simpl. reflexivity.
Qed.

(*sorted array and skewedness*)
Fixpoint insertarray (i : Z) (l : list Z) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insertarray i t
  end.

Fixpoint sortarr (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insertarray h (sortarr t)
  end.

Inductive sorted : list Z -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma insert_sorted: forall l a, sorted l -> sorted (insertarray a l).
Proof. 
  induction l; intros. 
  simpl. constructor. 
  simpl. destruct (a0 <=? a) eqn:Ha0a. 
  inversion H; subst. repeat constructor. lia.
  inversion H; subst. constructor. lia. assumption.   
  specialize IHl with a0. simpl. inversion H; subst. 
  simpl. repeat constructor. lia. simpl. 
  destruct (a0 <=? y) eqn:Ha0y.  
  apply sorted_cons. lia. constructor. lia. assumption. 
  apply IHl in H3. simpl in H3. 
  rewrite Ha0y in H3. constructor. lia. assumption.
Qed.

Theorem sort_sorted: forall l, sorted (sortarr l).
Proof.
  induction l. 
  simpl. constructor. 
  simpl. apply insert_sorted. assumption.
Qed.

Lemma sortedInSame: forall a l, In a (insertarray a l).
Proof.
  induction l; intros. 
  simpl. left. reflexivity. 
  simpl.  destruct (a <=? a0) eqn:Haa0. simpl. left. reflexivity. 
  simpl. right. assumption.
Qed.

Lemma sortedInAdd: forall a x l, In a l -> In a (insertarray x l).
Proof.
  induction l; intros. 
  simpl. inversion H. 
  simpl in H. destruct H as [? | ?]. 
  subst. simpl. destruct (x <=? a) eqn:Hxa. simpl. right. left. reflexivity. 
  simpl. left. reflexivity. 
  simpl. destruct (x <=? a0) eqn:Hxa0. simpl. right. right. assumption. 
  simpl. right. apply IHl. assumption.
Qed.

Lemma sortedInReverse: forall a x l, In a (insertarray x l) /\ (x <> a) -> In a l.
Proof. 
  induction l; intros. 
  destruct H as [? ?]. inversion H. contradiction. 
  assumption. 
  destruct H as [? ?]. simpl. 
  destruct (a0 =? a) eqn:Haa0. left. lia. 
  right. assert (a <> a0) by lia. simpl in H. destruct (x <=? a0) eqn:Hxa0. 
  simpl in H. destruct H as [? | ?]. contradiction. destruct H as [? | ?]. 
  rewrite H in H1. list_solve. assumption. 
  simpl in H. destruct H as [? | ?].  list_solve. apply IHl. auto.
Qed.

Lemma sortedMembership: forall x l, In x l <-> In x (sortarr l).
Proof.
  induction l. 
  simpl. split; auto. 
  split; intros. simpl in H. destruct H as [? | ?]. 
  subst. simpl. apply sortedInSame.  
  simpl. apply sortedInAdd. apply IHl. assumption. 
  simpl in H. simpl. destruct (a =? x) eqn:Hax. left. lia. 
  assert (x <> a) by lia. right. apply IHl. apply sortedInReverse with a. auto.
Qed.

Lemma sortedNonMembership: forall x l, ~In x l <-> ~In x (sortarr l).
Proof.
  intros. apply not_iff_compat. apply sortedMembership.
Qed.

Lemma noDupInsertProof: forall a l, 
(~In a l /\ NoDup l) <-> NoDup (insertarray a l).
Proof.
  induction l; split; intros.
  simpl. apply NoDup_cons. auto. destruct H as [? ?]. assumption. 
  simpl in H. split. simpl. auto. apply NoDup_nil. 
  simpl. destruct H as [? ?]. simpl in H. apply Decidable.not_or in H. 
  inversion H0; subst. destruct H as [? ?]. destruct (a <=? a0) eqn:Haa0. 
  assert (a < a0) by lia. apply NoDup_cons_iff. split. simpl.  
  unfold not. intros. destruct H5 as [? | ?]; try list_solve. 
  assumption. apply NoDup_cons_iff. split.  unfold not. intros. 
  assert (In a0 (insertarray a l) /\ a <> a0). split; first[assumption | lia]. 
  apply sortedInReverse in H5. list_solve. apply IHl. split; assumption. 
  split. simpl in H. destruct (a <=? a0) eqn:Haa0. apply NoDup_cons_iff in H. 
  destruct H as [? ?]. assumption. assert (a > a0) by lia. 
  apply NoDup_cons_iff in H. destruct H as [? ?]. apply IHl in H1. 
  simpl. unfold not. intros. destruct H1 as [? ?]. destruct H2 as [? | ?]; try list_solve. 
  simpl in H. destruct (a <=? a0) eqn:Haa0. apply NoDup_cons_iff in H. 
  destruct H as [ ? ?]. assumption. assert (a > a0) by lia. 
  apply NoDup_cons_iff in H. destruct H as [? ?]. apply NoDup_cons_iff. 
  split. unfold not. intros. apply sortedInAdd with a0 a l in H2. 
  list_solve. apply IHl in H1. destruct H1 as [ ? ?]. assumption.
Qed.

Lemma noDupSorted: forall l, NoDup l <-> NoDup (sortarr l).
Proof.
  induction l; split; intros. 
  simpl. assumption. simpl in H. assumption.  
  apply NoDup_cons_iff in H. destruct H as [? ?]. 
  simpl. apply noDupInsertProof. split. apply sortedNonMembership in H. assumption. 
  apply IHl. assumption.  simpl in H. apply noDupInsertProof in H. 
  apply NoDup_cons_iff. destruct H as [? ?]. split. apply sortedNonMembership. 
  assumption. apply IHl. assumption.
Qed.

Lemma lengthPlus1Insert: forall a l, Zlength (insertarray a l) = 1 + Zlength l. 
Proof. 
  induction l; intros. 
  simpl. list_solve. 
  simpl. destruct (a <=? a0) eqn:Haa0. list_solve. 
  rewrite Zlength_cons. rewrite IHl. list_solve.
Qed.

Theorem lengthPreservedSorted: forall l, Zlength (sortarr l) = Zlength l. 
Proof. 
  induction l; intros.
  simpl. reflexivity.  
  simpl. rewrite lengthPlus1Insert. rewrite IHl. list_solve.
Qed.

Lemma sortedAll: forall l a, sorted(a :: l) <-> Forall (fun x => a <= x) l /\ sorted l. 
Proof.
  induction l; split; intros. 
  split. list_solve. constructor. 
  constructor. inversion H; subst. split.  
  apply Forall_cons_iff. split. lia. apply IHl in H4. 
  destruct H4 as [? ?]. list_solve. assumption. 
  destruct H as [? ?]. apply Forall_cons_iff in H. 
  apply sorted_cons.   lia. assumption.
Qed.

Lemma insertListSorted: forall l k v tl tr, Forall (fun x => k < x) l -> insListSpec l (T tl k v tr) = T tl k v (insListSpec l tr).
Proof.
  induction l; intros. 
  simpl. reflexivity. simpl. 
  apply Forall_cons_iff in H. destruct H as [? ?].  
  assert (a <? k = false) by lia. rewrite H1. 
  assert (k <? a = true) by lia. rewrite H2. apply IHl. assumption.
Qed.

Lemma treeSkewed: forall l, NoDup l /\ sorted l -> isSkewed (insListSpec l E). 
Proof.
  induction l; intros. 
  simpl. auto. 
  simpl. destruct H as [? ?]. inversion H; subst. 
  apply sortedAll in H0. destruct H0 as [? ?]. rewrite insertListSorted. 
  simpl. apply IHl. auto. list_solve.
Qed.

Lemma relationPreservedSorted: forall l r, Forall r l <-> Forall r (sortarr l). 
Proof.
  intros; split; intros. apply Forall_forall. rewrite Forall_forall in H. 
  intros. apply H. apply sortedMembership. assumption. 
  apply Forall_forall. rewrite Forall_forall in H. intros. 
  apply H. apply sortedMembership in H0. assumption.
Qed.
