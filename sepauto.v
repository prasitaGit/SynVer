Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.treelistdef. 
Require Import GenProof.bstFunctionalProofs.
(*Require Import GenProof.mapListToIndex. *)
(*queried ltac: first stage*)
(*
Dealing with the comparison operators: =, <>, <, >, <=, >=,
arithmetic operators: +, -, *, /, %
Types: Z, bool, strings, signed and unsigned supported, some double
Data structures: arrays, linked lists, trees)
C programs recognized by verified compiler Compcert
*)
(*Receive in parameters - spec and everything*)
(*Lemma for nested unfolding*)

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = false -> Q.
Proof.
  intros P Q a. destruct a; simpl. intros. inversion H. intros. assumption.
Qed.

Lemma forceval_cast: forall b, force_val (sem_cast_i2bool (bool2val b)) = bool2val b. 
Proof.
  destruct b; simpl; reflexivity.
Qed.

Lemma modu_repr : forall a b, 0 <= a <= Int.max_unsigned -> 0 < b <= Int.max_unsigned ->
  Int.modu (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof.
  intros.
  unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma nModulom: forall n m: Z, m > 0 -> -m < Z.modulo n m < m.
Proof.
  intros. assert (0 < m) by lia.
  assert (m <> 0) by lia.
  generalize (Z.div_eucl_eq n m H1) (Z.mod_pos_bound n m) (Z.mod_neg_bound n m). 
  unfold Z.modulo. destruct Z.div_eucl. intros. lia.
Qed.

Lemma nmodulomRange: forall n m:Z, 0 < m <= Int.max_signed -> 
-m < Z.modulo n m < m -> Int.min_signed <= Z.modulo n m <= Int.max_signed.
Proof.
  intros. destruct H0. split. assert (Int.min_signed <= -m) by rep_lia. lia. lia.
Qed. 

Lemma repr_byte_signed:
  forall i j,
    Byte.min_signed <= i <= Byte.max_signed -> 
    Byte.min_signed <= j <= Byte.max_signed -> 
    Byte.repr i = Byte.repr j -> i=j.
Proof.
intros.
rewrite <- (Byte.signed_repr i) by rep_lia.
rewrite <- (Byte.signed_repr j) by rep_lia.
congruence.
Qed.

Lemma repr_byte_neq_e:
 forall i j, Byte.repr i <> Byte.repr j -> i <> j.
Proof. intros. contradict H. subst. auto. Qed.

Lemma byteZRelation: forall k: Z, Byte.min_signed <= k <= Byte.max_signed -> 
Int.min_signed <= k <= Int.max_signed.
Proof.
    intros. rep_lia.
Qed.

Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, (P |-- Q) -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Ltac try_forward n :=
  match n with
  | S ?n' =>  try (try_forward n')
  | (0)%nat => forward
  end.

Ltac clearMatch H :=
  repeat match goal with
  | [ H' : ?g |- _ ] => progress (tryif (unify H g) then clear H' else idtac )
  end.  

Ltac unifyLeft H g :=
  repeat match goal with
  | [ H' : ?h |- g ] => progress (tryif (unify H h) then left; assumption else idtac)
  end.  

Ltac unifyRight H g :=
  repeat match goal with
  | [ H' : ?h |- g ] => progress (tryif (unify H h) then right; assumption else idtac )
  end. 
  
(*analyze fail forward wrt Int.repr: *)
Ltac failForward g :=
  match goal with
  | [X: Int.repr _ = Int.mone |- g] => inversion X
  | [X: true = false |- g] => inversion X
  | [X: false = true |- g] => inversion X
  | [X: False |- g] => inversion X
  | [X: Int.repr _ <> Int.repr _ |- g] =>  apply repr_neq_e in X; failForward g
  | [X: Int.repr (Z.modulo _ _) = Int.repr _ |- g] => apply repr_inj_signed in X; 
                                                [ | unfold repable_signed; apply nmodulomRange; [first[rep_lia | list_solve] | apply nModulom; first[rep_lia | list_solve]] | first[rep_lia | list_solve]]; failForward g
  | [X: Int.repr ?a = Int.repr _ |- g] =>  (tryif (assert (repable_signed a) by first[list_solve | rep_lia | unfold repable_signed; apply byteZRelation; first[rep_lia | list_solve]]) 
                                           then clearMatch (repable_signed a); apply repr_inj_signed in X else apply repr_inj_unsigned in X); 
                                           try solve[rep_lia | list_solve | unfold repable_signed; apply byteZRelation; first[rep_lia | list_solve]]; failForward g
  | [X: Int.repr ?a = Int.add (Int.repr _) (Int.repr _) |- g] => rewrite add_repr in X; failForward g
  | [X: Int.repr ?a = Int.sub (Int.repr _) (Int.repr _) |- g] => rewrite sub_repr in X; failForward g
  | [X: Int.repr ?a = Int.mul (Int.repr _) (Int.repr _) |- g] => rewrite mul_repr in X; failForward g
  | [X: Int.repr _ <> Int.add (Int.repr _) (Int.repr _) |- g] => rewrite add_repr in X; apply repr_neq_e in X; failForward g
  | [X: Int.repr _ <> Int.sub (Int.repr _) (Int.repr _) |- g] => rewrite sub_repr in X; apply repr_neq_e in X; failForward g
  | [X: Int.repr _ <> Int.mul (Int.repr _) (Int.repr _) |- g] => rewrite mul_repr in X; apply repr_neq_e in X; failForward g
  (*| [X: _ /\ Int.repr _ = Int.mone |- g] => destruct X; failForward g
  | [X: Int.repr _ = Int.mone /\ _ |- g] =>  destruct X; failForward g *)
  | [X: ?h |- g] => match h with 
                    | context [Int.signed (Int.repr _)] => rewrite !Int.signed_repr in X by first[list_solve | rep_lia | apply byteZRelation; first[rep_lia | list_solve]] ; failForward g
                    | context [Int.unsigned (Int.repr _)] => rewrite !Int.unsigned_repr in X by first[list_solve | rep_lia] ; failForward g
                    | context [Int.mods (Int.repr _) (Int.repr _)] => rewrite mods_repr in X by first[rep_lia | list_solve]; failForward g 
                    | context [Int.modu (Int.repr _) (Int.repr _)] => rewrite modu_repr in X by first[rep_lia | list_solve]; failForward g 
                    end
  | [X: ?t = false |- g] => match t with 
                            | context[zeq _ _] => apply proj_sumbool_false in X; failForward g
                            | context[zle _ _] => apply proj_sumbool_false in X; failForward g
                            | context[zlt _ _] => apply proj_sumbool_false in X; failForward g
                            end 
  | [X: ?t = true |- g] => match t with 
                           | context[zeq _ _] => apply proj_sumbool_true in X; failForward g
                           | context[zle _ _] => apply proj_sumbool_true in X; failForward g
                           | context[zlt _ _] => apply proj_sumbool_true in X; failForward g
                           end 
  | [X: Int.repr _ = Int.repr _ |- g] => inversion X 
  | [X: Int.repr _ = _ |- g] => inversion X 
  | [X: context[Znth ?i ?l] |- g] => tryif (assert (i < 0) by lia) then first [rewrite Znth_underflow in X by lia; list_solve | inversion X | idtac] 
                                     else (tryif (assert (i >= (Zlength l)) by lia) then first [rewrite Znth_overflow in X by lia; list_solve | inversion X | idtac] else idtac)
  | [X: _ <> _ |- g] => try (inversion X)
  | [X: _ |- g] => idtac 
  | [X: _ |- ?g'] => idtac
  end.

Ltac matchTreeAndSubstitute := 
  repeat match goal with 
  | [X: T ?lt ?k ?v ?lr = ?ot |- _] => progress (match ot with 
                                       | T lt k v lr => idtac
                                       | T _ _ _ _ => inversion X; subst 
                                      end)
  end.

Ltac matchListAndSubstitute := 
  repeat match goal with 
  | [X: ?h :: ?hs = ?ot |- _] => progress (match ot with 
                                         | h :: hs => idtac
                                         | _ :: _ => inversion X; subst
                                         | _ => subst 
                                        end)
  | [X: _ = _ :: _ |- _] => subst
  end.
  
Ltac rewriteWrapperInGoal := 
  match goal with 
  | |- ?g => match g with 
             | context[Int.unsigned (Int.repr _)] => rewrite !Int.unsigned_repr by first[rep_lia | list_solve]
             | context[Int.signed (Int.repr _)] => rewrite !Int.signed_repr by first[rep_lia | list_solve | apply byteZRelation; first[rep_lia | list_solve]]
             | _ => idtac
             end
  end.

Ltac matchAndrewrite G tac g :=
  repeat match goal with 
  | [X: ?h |- g ] => progress (tryif (unify G h) then apply tac in X; rewrite X; clear X else idtac) 
  end. 

Ltac checkOperatorDischarge2 op o1 o2 g := 
  match op with
  | Z.eqb => match o1 with
              | o2 => rewrite Z.eqb_refl; first[progress entailer! | entailer!!]
              | _ =>  tryif (assert (o1 = o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 = o2) Z.eqb_eq g 
                      else (tryif (assert (o1 <> o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 <> o2) Z.eqb_neq g 
                      else (destruct (o1 =? o2); [ assert (o1 = o2) by lia; matchAndrewrite (o1 = o2) Z.eqb_eq g | 
                      assert (o1 <> o2) by lia; matchAndrewrite (o1 <> o2) Z.eqb_neq g])) 
              end
  | Z.ltb =>  tryif (assert (o1 < o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 < o2) Z.ltb_lt g 
              else (tryif (assert (o2 <= o1) by first[rep_lia | list_solve]) then matchAndrewrite (o2 <= o1) Z.ltb_ge g 
              else (destruct (o1 <? o2); [ assert (o1 < o2) by lia; matchAndrewrite (o1 < o2) Z.ltb_lt g | 
              assert (o2 <= o1) by lia; matchAndrewrite (o2 <= o1) Z.ltb_ge g]))
  | Z.leb => tryif (assert (o1 <= o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 <= o2) Z.leb_le g 
             else (tryif (assert (o2 < o1) by first[rep_lia | list_solve]) then matchAndrewrite (o2 < o1) Z.leb_gt g 
             else (destruct (o1 <=? o2); [ assert (o1 <= o2) by lia; matchAndrewrite (o1 <= o2) Z.leb_le g | 
             assert (o2 < o1) by lia; matchAndrewrite (o2 < o1) Z.leb_gt g])) 
  | Z.gtb => rewrite Z.gtb_ltb; checkOperatorDischarge2 Z.ltb o2 o1 g
  | Z.geb => rewrite Z.geb_leb; checkOperatorDischarge2 Z.leb o2 o1 g  
end. 

Ltac matchModulo a b Op o g :=
  match goal with
  | [X: ?o' (Int.repr (Z.modulo a b)) (Int.repr o) |- g] => checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: not (?o' (Int.repr (Z.modulo a b)) (Int.repr o)) |- g] => checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: ?o' (Int.mods (Int.repr a) (Int.repr b)) (Int.repr o) |- g] => rewrite mods_repr in X; try first[rep_lia | list_solve]; apply repr_inj_signed in X; try rep_lia; checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: not (?o' (Int.mods (Int.repr a) (Int.repr b)) (Int.repr o)) |- g] => rewrite mods_repr in X; try first[rep_lia | list_solve]; apply repr_neq_e in X; checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: ?o' (Int.modu (Int.repr a) (Int.repr b)) (Int.repr o) |- g] => rewrite modu_repr in X; try first[rep_lia | list_solve]; apply repr_inj_signed in X; try rep_lia; checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: not (?o' (Int.modu (Int.repr a) (Int.repr b)) (Int.repr o)) |- g] => rewrite modu_repr in X; try first[rep_lia | list_solve]; apply repr_neq_e in X; checkOperatorDischarge2 Op (Z.modulo a b) o g
  end.

Ltac assignandRewrite arg v :=
  match goal with
  | [X:  malloc_compatible ?n v |- _] => assert (sizeof arg = n) as Hszassert by reflexivity; rewrite <- Hszassert
  end.

Ltac fireTreeOrListNotNull sx ind := 
  match sx with
  | nil => idtac
  | tree_rep _ ind :: _ => rewrite (tree_rep_notnull _ ind) by auto;
                           match goal with 
                           | |- ?g => 
                            match g with
                            | context [EX (k : _) (v : _) (a : _) (b : _) (pa : _) (pb : _), _] => 
                              tryif (progress timeout 10 (let hkv := fresh k in (let hvv := fresh v in (let hav := fresh a in (let hbv := fresh b in 
                              (let hpav := fresh pa in (let hpbv := fresh pb in Intros hkv hvv hav hbv hpav hpbv))))))) then idtac else idtac 
                            | _ => idtac "not matched"
                            end
                           end 
  | listrep _ ind :: _ => rewrite (listrep_nonnull _ ind) by auto;
                          match goal with 
                          | |- context [EX (h : _) (hs : _) (y : _), _] => 
                            let hvv := fresh h in (let hsv := fresh hs in (let hyv := fresh y in Intros hvv hsv hyv))
                          end
  | listrepc _ ind :: _ => rewrite (listrepc_nonnull _ ind) by auto;
                          match goal with 
                          | |- context [EX (h : _) (hs : _) (y : _), _] => 
                            let hvv := fresh h in (let hsv := fresh hs in (let hyv := fresh y in Intros hvv hsv hyv))
                          end
  | _ :: ?sx' => fireTreeOrListNotNull sx' ind 
  end.
  
Ltac fireTreeOrListNull sx ind := 
  match sx with
  | nil => idtac
  | tree_rep _ ind :: _ => rewrite (tree_rep_null _ ind) by auto 
  | _ :: ?sx' => fireTreeOrListNull sx' ind 
  end.
  
Ltac triggerNullNoNullTreeOrList sx g :=
  repeat match goal with
  | [X: ?ind <> nullval |- g] =>  progress (fireTreeOrListNotNull sx ind)
  | [X: ?ind = nullval |- g] => progress(fireTreeOrListNull sx ind) 
  end.

(*Tree null, non-null. List non-null only*)
Ltac triggerNullNoNullMatch g :=
  match g with 
  | semax _ (PROPx _ (LOCALx _ (SEPx ?sx))) _ _ => triggerNullNoNullTreeOrList sx g 
  end. 
  
(* null check lemma *) 
Ltac triggerNullList :=
 match goal with
 | [X : nullval = nullval <-> ?l = [] |- _] => progress (assert (l = (@nil Z)) by (apply X; reflexivity); subst; clear X)
 end.

Ltac is_var_in_hyps var :=
  match goal with
  | [ H: context[var] |- _ ] => true
  | _ => false
  end. 

Ltac matchSepListBool sx l := 
  match sx with 
  | nil => false 
  | listrep l _ :: _ => true 
  | listrepc l _ :: _ => true 
  | _ :: ?sx' => matchSepListBool sx' 
  end.

Ltac rewriteLengthNullNotNull := 
  repeat match goal with 
  | [H: Zlength ?l = _ |- ?g] => progress (
                                 match g with 
                                 | semax _ (PROPx _ (LOCALx _ (SEPx ?sx))) _ _ => 
                                  let x := matchSepListBool sx l in 
                                  match x with 
                                  | true => tryif (assert (Zlength l = 0) by list_solve) then  
                                            clearMatch (Zlength l = 0); first[rewrite (listrep_null_length l _) by list_solve | rewrite (listrepc_null_length l _) by list_solve]; subst 
                                            else (tryif (assert (Zlength l > 0) by list_solve) then
                                            clearMatch (Zlength l > 0); first[rewrite (listrep_nonnull_length l _) by list_solve | rewrite (listrepc_nonnull_length l _) by list_solve];
                                            match goal with 
                                            | |- context [EX (h : _) (hs : _) (y : _), _] => 
                                                let hvv := fresh h in (let hsv := fresh hs in (let hyv := fresh y in Intros hvv hsv hyv))
                                            end else idtac) 
                                  | false => idtac
                                  end
                                | _ => idtac
                                end)
  end. 
  
Ltac sepListMatch sx h :=
  match sx with 
  | nil => constr:((tt))
  | (data_at ?sh _ (Vint (Int.repr ?a')) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                          | true => constr:((sh, a')) 
                                                          | false => constr:((a', tt))
                                                          end)
  | (data_at ?sh _ (map Vint (map Int.repr ?a')) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                                  | true => constr:((sh, a')) 
                                                                  | false => constr:((a', tt))
                                                                  end) 
  | (data_at ?sh _ (Vint (Int.repr ?a'), nullval) h) :: _ => let x := (is_var_in_hyps sh) in (match x with 
                                                                  | true => constr:((sh, [a'])) 
                                                                  | false => constr:(([a'], tt))
                                                                  end)
  | (data_at ?sh _ (Vint (Int.repr ?a'), ?h0) h) :: _ =>  let x := (is_var_in_hyps sh) in (let x' :=  sepListMatch sx h0 in 
                                                                  match x with 
                                                                  | true => match x' with 
                                                                            | (?v,tt) => constr:((sh, a' :: v))
                                                                            end 
                                                                  | false => match x' with 
                                                                             | (?v,tt) => constr:((a' :: v, tt))
                                                                            end               
                                                                  end)
  | (data_at ?sh _ (Vint (Int.repr ?keyv), (Vint (Int.repr ?valv), (?pladd, ?pradd))) h) :: _ => 
                let x := (is_var_in_hyps sh) in (let xl := sepListMatch sx pladd in 
                (let xr := sepListMatch sx pradd in   
                 match x with 
                 | true => match xl with 
                           | (?tl,tt) => match xr with 
                                         | (?tr,tt) => constr:((sh, T tl keyv valv tr))
                                         end
                           end 
                 | false => match xl with 
                            | (?tl,tt) => match xr with 
                                          | (?tr,tt) => constr:((T tl keyv valv tr, tt))
                                          end
                            end               
                end))
  | (data_at ?sh _  ?h0 h) :: _ =>  sepListMatch sx h0
  | listrep ?l h :: _ =>  constr:((l,tt))
  | listrepc ?l h :: _ =>  constr:((l,tt))
  | tree_rep ?a h :: _ => constr:((a,tt))
  | sllbox_rep ?l h :: _ => constr:((l,tt))
  | sllbox_repc ?l h :: _ => constr:((l,tt))
  | memory_block _ ?n h :: _ => constr:((n,tt))
  | _ :: ?sx' => sepListMatch sx' h
  end.

  
Ltac listMatchReturn lx sx h ty :=
  match lx with
  | nil => constr:((h,tt))
  | temp h (Vint (Int.repr ?v)) :: _ => constr:((v,tt))
  | temp h (Vlong ?vw) :: _ => (*tryif (unify nullval (Vlong a)) then *)
                              match ty with 
                              | context [Tstruct ?lt noattr] => constr:(ltac:(tryif (unify t_struct_tree (Tstruct lt noattr)) then exact((nullval, (E, tt))) else exact((nullval, (@nil Z, tt)))))
                              | _ => constr:((vw,tt))
                              end 
  | temp h ?v :: _ => let x := sepListMatch sx v in constr:((v, x)) (*value,share,variable*)
  | _ :: ?lx' => listMatchReturn lx' sx h ty
  end.


Ltac listMatchReturnVariable lx h :=
  match lx with
  | nil => h
  | temp h (Vint (Int.repr ?v)) :: _ => v
  | temp h ?v :: _ => v
  | _ :: ?lx' => listMatchReturnVariable lx' h
  end.  

Ltac returnMatchOperand o lx :=
  match o with
  | (Econst_int (Int.repr ?h) tint) => h 
  | (Etempvar ?p _) => listMatchReturnVariable lx p
  end.
  
Ltac listTravIdtac l lx sx :=
  match l with
  | nil => constr:((tt))
  | (Etempvar ?p ?ty) :: ?l' => let x := (listMatchReturn lx sx p ty) in (let x' := listTravIdtac l' lx sx in 
                                                                       match x with 
                                                                       | (?v,tt) => constr:((v,x'))
                                                                       | (?v,(?a,tt)) => constr:((v,(a,x')))
                                                                       | (?v,(?sh,?a)) => constr:((v,(sh,(a,x'))))
                                                                       end)
  | (Econst_int (Int.repr ?h) tint) :: ?l' => let x := listTravIdtac l' lx sx in constr:((h,x))
  | (Ebinop Oadd ?o1 ?o2 _) :: ?l' =>  let x := listTravIdtac l' lx sx in (let ro1 := returnMatchOperand o1 lx in 
                                       (let ro2 := returnMatchOperand o2 lx in constr:((ro1 + ro2,x))))
  | (Ebinop Osub ?o1 ?o2 _) :: ?l' =>  let x := listTravIdtac l' lx sx in (let ro1 := returnMatchOperand o1 lx in 
                                       (let ro2 := returnMatchOperand o2 lx in constr:((ro1 - ro2,x))))
  | (Esizeof ?o _) :: ?l' => let x := listTravIdtac l' lx sx in constr:((sizeof o,x))                                    
  | ?h :: ?l' => let x := listTravIdtac l' lx sx in constr:((h,x))
  end.  
  
Ltac forwardCallExplicit tup := 
  match tup with
  | (?a',tt) => forward_call(a')
  | (?a',(?b',tt)) => forward_call(a',b')
  | (?a',(?b',(?c',tt))) => forward_call(a',b',c')
  | (?a',(?b',(?c',(?d',tt)))) => forward_call(a',b',c',d')
  | (?a',(?b',(?c',(?d',(?e',tt))))) => forward_call(a',b',c',d',e')
  | (?a', (?b', (?c', (?d', (?e', (?f', tt)))))) => forward_call(a',b',c',d',e',f')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',tt))))))) => forward_call(a',b',c',d',e',f',g')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',tt)))))))) => forward_call(a',b',c',d',e',f',g',h')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',(?i',tt))))))))) => forward_call(a',b',c',d',e',f',g',h',i')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',(?i',(?j',tt)))))))))) => forward_call(a',b',c',d',e',f',g',h',i',j')
  end.

 Ltac fireFailForward :=
  match goal with
  | |- ?g => failForward g
  end. 

Ltac checkPresenceConclusion H :=
  repeat match goal with
  | [ H' : ?a <-> ?b |- H ] => progress (tryif (unify H b) then apply H' 
                               else (tryif (unify H a) then apply H' else idtac ))
  | [ H' : ?a -> ?b |- H ] => progress (tryif (unify H b) then apply H' else idtac )
  end.

Ltac applyPresentHypothesis H h g :=
  repeat match goal with
  | [ H' : ?a <-> ?b |- g ] => progress (tryif (unify h b) then apply H' in H; clear H'
                               else (tryif (unify h a) then apply H' in H; clear H' else idtac))
  | [ H' : ?a -> ?b |- g ] => progress (tryif (unify h a) then apply H' in H; clear H' else idtac )
  end.

Ltac is_hypothesis_present H g :=
  match goal with
  | [ H' : ?h |- g ] => tryif (unify H H') then applyPresentHypothesis H' h g else idtac
  | [H' : _ |- _] => idtac
  end.

Ltac conjunctHypothesis :=
  match goal with
  | [ H' : _ /\ _ <-> _ |- _ ] => idtac 
  | [ H' : _ <-> _ /\ _ |- _ ] => idtac 
  | [ H' : NoDup (_ :: _) |- _ ] => apply NoDup_cons_iff in H';  conjunctHypothesis
  | [ H' : Forall _ (_ :: _) |- _] => apply Forall_cons_iff in H'; destruct H' as [? ?]; conjunctHypothesis
  | [ H' : Forall2 _ (_ :: _) (_ :: _) |- _] => apply Forall2_cons_iff in H'; destruct H' as [? ?]; conjunctHypothesis
  | [ H' : _ /\ _ |- _ ] => destruct H' as [? ?]; conjunctHypothesis
  | [H' :  _ |- _] => idtac 
  end.

Ltac disjunctHypothesis :=
  repeat match goal with
  | [ H' : _ \/ _ |- _ ] => destruct H' as [? | ?]
  | _ => idtac "No further disjunctions present"
  end.

Ltac disjunctHypothesisFname H' :=
  repeat match goal with
  | [ H : _ \/ _ |- _ ] => progress (tryif (unify H H') then destruct H as [H | H] else idtac ) 
  end.

Ltac fireAppropriateConclusion := (*used for others*)
  match goal with 
  | |- ?g => checkPresenceConclusion g
  end.

Ltac fireAppropriateHypothesis H := (*used for lists*)
  match goal with 
  | |- ?g => try move H at bottom; is_hypothesis_present H g
  end.  

Ltac checkPresenceForall H' :=
  match goal with
  | [H : Forall2 _ (sublist ?lo1 ?hi1 ?l1) (sublist ?lo2 ?hi2 ?l2) |- ?g] => tryif (unify H H') then  
                                                                                match g with 
                                                                                | Forall2 _ (sublist ?lo1' hi1 l1) (sublist ?lo2' hi2 l2) => 
                                                                                  tryif (assert (lo1 = lo1' + 1 /\ lo2 = lo2' + 1) by lia) then clearMatch (lo1 = lo1' + 1 /\ lo2 = lo2' + 1);
                                                                                  rewrite sublist_split with lo1' (lo1' + 1) hi1 l1 by list_solve; rewrite sublist_split with lo2' (lo2' + 1) hi2 l2 by list_solve; 
                                                                                  apply Forall2_app; try rewrite !sublist_one by list_solve
                                                                                  else (tryif (assert (lo1 + 1 = lo1' /\ lo2 + 1 = lo2') by lia) then clearMatch (lo1 + 1 = lo1' /\ lo2 + 1 = lo2'); 
                                                                                  rewrite sublist_split with lo1 (lo1 + 1) hi1 l1 in H by list_solve; rewrite sublist_split with lo2 (lo2 + 1) hi2 l2 in H by list_solve; apply Forall2_app_inv in H; 
                                                                                  try (destruct H as [Hf1 Hf2]; rewrite !sublist_one in Hf1 by list_solve; apply Forall2_cons_iff in Hf1; destruct Hf1 as [? ?])
                                                                                  else (tryif (assert (lo1' > lo1 /\ lo2' > lo2) by lia) then clearMatch (lo1' > lo1 /\ lo2' > lo2); 
                                                                                  rewrite sublist_split with lo1 lo1' hi1 l1 in H by list_solve;  
                                                                                  rewrite sublist_split with lo2 lo2' hi2 l2 in H by list_solve; apply Forall2_app_inv in H; (*splits*)
                                                                                  try (destruct H as [? ?]) 
                                                                                  else (tryif (assert (lo1' < lo1 /\ lo2' < lo2) by lia) then clearMatch (lo1' < lo1 /\ lo2' < lo2);
                                                                                  rewrite sublist_split with lo1' lo1 hi1 l1 by list_solve; rewrite sublist_split with lo2' lo2 hi2 l2 by list_solve; 
                                                                                  apply Forall2_app else idtac )))
                                                                                end else idtac "Not unified"  
  | [H: Forall2 _ (sublist ?lo ?hi ?l)(?he :: ?ta) |- ?g] => tryif (unify H H') then 
                                                        match g with
                                                        | Forall2 _ (sublist (lo + 1) hi l) ta => rewrite sublist_split with lo (lo + 1) hi l in H by list_solve; 
                                                          rewrite !sublist_len_1 in H by list_solve; simpl in H; 
                                                          apply Forall2_cons_iff in H; destruct H as [? ?]
                                                        end else idtac
  | [H: Forall2 _ (sublist (?lo + 1) ?hi ?l) ?ta |- ?g] => tryif (unify H H') then 
                                                        match g with
                                                        | Forall2 _ (sublist lo hi l) (_ :: ta) => rewrite sublist_split with lo (lo + 1) hi l by list_solve; 
                                                          rewrite !sublist_len_1 by list_solve; simpl; apply Forall2_cons_iff
                                                        end else idtac
  | [H : In _ (sublist ?lo ?hi ?l) |- ?g] => tryif (unify H H') then  
                                             match g with 
                                             | In _ (sublist ?lo' hi l) => tryif (assert (lo = lo' + 1) by lia) then clearMatch (lo = lo' + 1);
                                               rewrite sublist_split with lo' (lo' + 1) hi l by list_solve; 
                                               rewrite !sublist_len_1 by list_solve; simpl
                                               else (tryif (assert (lo + 1 = lo') by lia) then clearMatch (lo + 1 = lo');
                                               rewrite sublist_split with lo (lo + 1) hi l in H by list_solve;
                                               rewrite !sublist_len_1 in H by list_solve; simpl in H; destruct H
                                               else (tryif (assert (lo' > lo) by lia) then clearMatch (lo' > lo); 
                                               rewrite sublist_split with lo lo' hi l in H by list_solve;  apply in_app_iff in H (*disjunction*)
                                               else (tryif (assert (lo > lo') by lia) then clearMatch (lo > lo'); 
                                               rewrite sublist_split with lo' lo hi l by list_solve; apply in_app_iff else idtac)))(*disjuction*)
                                             end else idtac "Not unified"
  | [H : Forall _ (sublist ?lo ?hi ?l) |- ?g] => tryif (unify H H') then 
                                                 match g with 
                                                 | Forall _ (sublist ?lo' hi l) => tryif (assert (lo = lo' + 1) by lia) then clearMatch (lo = lo' + 1);
                                                   rewrite sublist_split with lo' (lo' + 1) hi l by list_solve; apply Forall_app; 
                                                   split; try rewrite !sublist_one by list_solve
                                                   else (tryif (assert (lo' = lo + 1) by lia) then clearMatch (lo' = lo + 1); 
                                                   rewrite sublist_split with lo (lo + 1) hi l in H by list_solve; apply Forall_app in H; 
                                                   destruct H as [Hf11 Hf12]; rewrite !sublist_one in Hf11 by list_solve; 
                                                   apply Forall_cons_iff in Hf11; destruct Hf11 as [? ?]
                                                   else (tryif (assert (lo' > lo) by lia) then clearMatch (lo' > lo); 
                                                   rewrite sublist_split with lo lo' hi l in H by list_solve; apply Forall_app in H; destruct H as [? ?](*splits - conjunction*)
                                                   else (tryif (assert (lo > lo') by lia) then clearMatch (lo > lo'); 
                                                   rewrite sublist_split with lo' lo hi l by list_solve; apply Forall_app; split else idtac)))
                                                 end else idtac "Not unified"
  
  | [ H : _ |- _ ] => idtac "Not matched with any of the above"
  end.

Ltac resolveContradiction :=  
  match goal with 
  | [H: Forall2 _ (sublist ?lo ?hi ?l)(_ :: _) |- _] => rewrite sublist_split with lo (lo + 1) hi l in H by list_solve; 
                                                        rewrite !sublist_len_1 in H by list_solve; simpl in H; 
                                                        apply Forall2_cons_iff in H; destruct H as [? ?]; list_solve
  | [H: Forall2 _ (sublist ?lo1 ?hi1 ?l1)(sublist ?lo2 ?hi2 ?l2) |- _] => rewrite sublist_split with lo1 (lo1 + 1) hi1 l1 in H by list_solve; 
                                                          rewrite sublist_split with lo2 (lo2 + 1) hi2 l2 in H by list_solve; 
                                                          rewrite !sublist_len_1 in H by list_solve; simpl in H; 
                                                          apply Forall2_cons_iff in H; destruct H as [? ?]; list_solve                                               
  end.

Ltac substituteIndValue val := 
  match goal with
  | [H : _ = val |- _ ] => rewrite <- H
  | [H : val = _ |- _ ] => rewrite H
  | [H : _ |- _] => idtac "No rewrite equality found for In" 
  end.
  
Ltac fireHypothesisOnSublist fname := 
  match goal with 
  | |- ?g => match g with 
             | context[sublist ?lo ?hi _] => tryif (assert (hi = lo) by lia) then clearMatch (hi = lo); rewrite !sublist_nil' by list_solve 
                                             else (tryif (assert (hi = lo + 1) by lia) then clearMatch (hi = lo + 1); rewrite !sublist_one by list_solve 
                                             else checkPresenceForall fname; try solve[list_solve])
             | _ =>  checkPresenceForall fname; try solve[list_solve]                                                                           
            end
  end.

Ltac matchMin g :=
  match g with
  | Z.min ?aa ?bb => match bb with 
                      | Z.min _ _ => matchMin bb
                      | _ =>  tryif (assert (aa <= bb) by first[rep_lia | list_solve]) then rewrite Z.min_l by lia; clearMatch (aa <= bb) 
                              else (tryif (assert (bb <= aa) by first[rep_lia | list_solve]) then rewrite Z.min_r by lia; clearMatch (bb <= aa) 
                              else destruct (aa <=? bb); [ assert (aa <= bb) by lia; rewrite Z.min_l by lia | 
                              assert (bb <= aa) by lia; rewrite Z.min_r by lia]) 
                      end
  end.
  
Ltac fireMinTactic := 
  match goal with 
  | |- ?g => match g with 
             | context [Z.min ?aa ?bb] => matchMin (Z.min aa bb)
            end
  end.

Ltac forwardCallExplicitList := 
  try rewrite !add_repr; try rewrite !sub_repr; try rewrite !mul_repr; 
  try rewrite !upd_Znth_map; 
  match goal with 
  | |- semax _ (PROPx ?px' (LOCALx ?lx' (SEPx ?sx'))) (Scall _ (Evar ?n' _) ?l') _ => let x := listTravIdtac l' lx' sx' in forwardCallExplicit x
  | |- semax _ (PROPx ?px' (LOCALx ?lx' (SEPx ?sx'))) (Ssequence (Scall _ (Evar ?n' _) ?l') _) _ => let x := listTravIdtac l' lx' sx' in forwardCallExplicit x
  end.

Ltac forwardFollowMalloc :=
   match goal with 
   | |- ?t => match t with 
              | semax _ (EX v : _, _ _ _) _ _ =>  let fv := fresh v in (Intros fv; 
                               rewrite memory_block_data_at_ by auto)
              | _ => idtac
              end
   end.

Ltac simplifyLists := 
  match goal with 
  | |- context [ Zlength []] => rewrite Zlength_nil; simplifyLists
  | |- context [ Zlength (_ :: _)] => rewrite Zlength_cons; simplifyLists
  | |- context [sublist _ _ []] => rewrite sublist_of_nil; simplifyLists 
  | |- _ => try rewrite Zlength_nil_inv by first[rep_lia | list_solve]
  end.

Ltac tryInstantiateExistsValue Qr := 
  match Qr with
  | context [ !! (?v = ?a)] => first[progress entailer! | entailer!!]
  | context [ !! (_ = ?a)] => Exists a; first[progress entailer! | entailer!!]
  | context [ !! (?v = _)] => Exists v; first[progress entailer! | entailer!!]  
  end. 

Ltac freeLocalParameterInference lx h := 
  match lx with
  | nil => false
  | temp h ?v :: _ => v
  | _ :: ?lx' =>  freeLocalParameterInference lx' h 
  end.
  
Ltac freeForwardCall lx l :=
  match l with 
  | Etempvar ?h (tptr ?sof) :: nil => let x := freeLocalParameterInference lx h in forward_call(x, sizeof sof)
  end. 

Ltac simplifyEntailment P Q :=  
  match Q with
  | EX (_:_) (_:_) (_:_), _ => idtac 
  | EX (_:_) (_:_) (_:_) (_:_), _ => idtac 
  | EX (_:_) (_:_) (_:_) (_:_) (_:_), _ => idtac 
  | context [EX _: _, _]  => first[ 
                              progress (
                                match Q with 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), (?v, (?lt, ?lr))) ?r] => first[progress entailer! | entailer!!] 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), (?v, (_, _))) ?r] =>
                                  match P with 
                                  | context [data_at sh _ (Vint (Int.repr k), (v, (?lt', ?lr'))) r] => Exists lt' lr'; entailer!! 
                                  | context [data_at sh _ (Vint (Int.repr ?k0), (v, (?lt', ?lr'))) r] => tryif (assert (k = k0) by lia) then subst; Exists lt' lr'; entailer!! else idtac
                                  end
                                | context [data_at ?sh _ (Vint (Int.repr ?k), ?padd) ?r] => first [progress entailer! | entailer!!] 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), _) ?r] => 
                                  match P with 
                                  | context [data_at sh _ (Vint (Int.repr k), ?padd') r] => Exists padd'; entailer!! 
                                  | context [data_at sh _ (Vint (Int.repr ?k0), ?padd') r] => tryif (assert (k = k0) by lia) then subst; Exists padd'; entailer!! else idtac
                                  end
                                | context [data_at ?sh _ ?padd ?padd2] => first [progress entailer! | entailer!!] 
                                | context [data_at ?sh _ _ ?padd2] => 
                                  match P with 
                                  | context [data_at sh _ ?padd' padd2] => Exists padd'; entailer!! 
                                  end
                                | context [data_at ?sh _ ?padd _] (*outer address*)=>
                                  match P with 
                                  | context [data_at sh _ padd ?padd2] => Exists padd2; entailer!! 
                                  end
                               end) | tryInstantiateExistsValue Q | simpl ]
  | context [ !! ?f ] => first[progress entailer! | entailer!!] 
  | context G [tree_rep (?f ?t') ?r] => 
            let x := eval simpl in (tree_rep (f t') r) in (*simplify will unfold and fold - no need to do explicitly*)
            let y := context G[x] in change (P |-- y)
  | context G [listrep (?f ?l') ?r] => 
            let x := eval simpl in (listrep (f l') r) in 
            let y := context G[x] in change (P |-- y)
  | context G [listrepc (?f ?l') ?r] => 
            let x := eval simpl in (listrepc (f l') r) in 
            let y := context G[x] in change (P |-- y)
  | context G [sllbox_rep ?l' ?r] => (*simplify does not unfold here*)
            let x := eval simpl in (sllbox_rep l' r) in
            let x' := eval unfold sllbox_rep in x in 
            let x' := eval fold sllbox_rep in x' in
            let y := context G[x'] in change (P |-- y)
  | context G [sllbox_repc ?l' ?r] => (*simplify does not unfold here*)
            let x := eval simpl in (sllbox_repc l' r) in
            let x' := eval unfold sllbox_repc in x in 
            let x' := eval fold sllbox_repc in x' in
            let y := context G[x'] in change (P |-- y)
  | context G [lseg ?l' ?st ?ed] => 
            let x := eval simpl in (lseg l' st ed) in 
            let y := context G[x] in change (P |-- y)
  | _ =>   first [progress entailer! | progress entailer!! | simpl]
  end.   

Ltac simplifyEntailmentSubset P Q :=  
  match Q with
  | context G [tree_rep (?f ?t') ?r] => 
            let x := eval simpl in (tree_rep (f t') r) in (*simplify will unfold and fold - no need to do explicitly*)
            let y := context G[x] in change (P |-- y)
  | context G [listrep (?f ?l') ?r] => 
            let x := eval simpl in (listrep (f l') r) in 
            let y := context G[x] in change (P |-- y)
  | context G [listrepc (?f ?l') ?r] => 
            let x := eval simpl in (listrepc (f l') r) in 
            let y := context G[x] in change (P |-- y)
  | context G [sllbox_rep ?l' ?r] => (*simplify does not unfold here*)
            let x := eval simpl in (sllbox_rep l' r) in
            let x' := eval unfold sllbox_rep in x in 
            let x' := eval fold sllbox_rep in x' in
            let y := context G[x'] in change (P |-- y)
  | context G [sllbox_repc ?l' ?r] => (*simplify does not unfold here*)
            let x := eval simpl in (sllbox_repc l' r) in
            let x' := eval unfold sllbox_repc in x in 
            let x' := eval fold sllbox_repc in x' in
            let y := context G[x'] in change (P |-- y)
  | context G [lseg ?l' ?st ?ed] => 
            let x := eval simpl in (lseg l' st ed) in 
            let y := context G[x] in change (P |-- y)
  | _ => idtac
  end.

Ltac destructHform H' :=
  match goal with 
  | [H: and _ _ |- _] => tryif (unify H H') then destruct H as [? H] else idtac 
  | [H: _ |- _] => idtac
  end.

Ltac sortedSolve f' l':=
  match goal with 
  | [H: Forall f' (sortarr l') |- _] => apply relationPreservedSorted; try assumption
  end.  

Ltac progltac g' fname freefuncName count :=
  tryif (assert (count = 100) by (simpl; reflexivity)) then idtac "matched: "count else 
  (match goal with
   | |- ?g'' => 
             match g' with 
             | g'' => idtac "Aborting, same goal: "g''" and: "g'

             | _ => try (triggerNullNoNullMatch g''); (*try triggerNullList;* try rewriteLengthNullNotNull; *)
                    try matchTreeAndSubstitute; try matchListAndSubstitute; conjunctHypothesis; fireFailForward;
                    try contradiction; rewriteWrapperInGoal; try solve[list_solve]; (*try solve[entailer!! | entailer! | entailer]; *)
  match goal with 
  | |- ?g => (*idtac g;*)
  match g with  
  | semax _ _ (Ssequence (Ssequence _ _) _)  _ => apply seq_assoc1; progltac g fname freefuncName (count + 1)
  | semax _ _ (Sloop _)  _ => fail "Error - loops not supported"
  | semax _ _ (Ssequence (Sloop _) _)  _ => fail "Error - loops not supported"
  | semax _ (EX v : _, _ _ _) _ _ =>  tryif (progress timeout 10 let fv := fresh v in (Intros fv)) then progltac g fname freefuncName (count + 1) else idtac
  | semax _ _ (Sifthenelse _ _ _)  _ => forward_if; progltac g fname freefuncName (count + 1)
  | semax _ _ (Ssequence (Sifthenelse _ _ _) _)  _ =>  apply semax_if_seq; progltac g fname freefuncName (count + 1)
  | semax _ (PROPx ?px (LOCALx ?lx (SEPx ?sx))) (Ssequence (Scall _ (Evar ?n _) ?l) _)  _ => match n with 
                                                                                             | freefuncName => first[freeForwardCall lx l; try (entailer!; rewrite memory_block_data_at_ by auto; entailer!); progltac g fname freefuncName (count + 1) | idtac "Unable to infer forward call witness for free"]
                                                                                             | _ => first[forwardCallExplicitList; try (forwardFollowMalloc); progltac g fname freefuncName (count + 1) |  idtac "Error - Failed to infer forward call witness - Please provide them"]
                                                                                             end
  | semax _ (PROPx ?px (LOCALx ?lx (SEPx ?sx))) (Scall _ (Evar ?n _) ?l) _ =>  match n with        
                                                                               | freefuncName => first[freeForwardCall lx l; try(entailer!; rewrite memory_block_data_at_ by auto; entailer!); progltac g fname freefuncName (count + 1) | idtac "Unable to infer forward call witness for free"]
                                                                               | _ => first[ forwardCallExplicitList; try (forwardFollowMalloc); progltac g fname freefuncName (count + 1) |  idtac "Error - Failed to infer forward call witness - Please provide them"]
                                                                               end 
  |semax _ _ ?c  _ => tryif  (progress timeout 30 (try_forward (1000)%nat)) then (progltac g fname freefuncName (count + 1)) else idtac "Error - Can't move forward here"
  (*idtac "Identified "; first [progress (try_forward (1000)%nat); progltac g fname freefuncName (count + 1) |  idtac "Error - Can't move forward here"] *)
  | context[_ -* _] => idtac 
  | ENTAIL _, _ |-- _ => tryif solve[entailer! | entailer!! | list_solve | entailer!; list_solve | entailer!!; list_solve] then idtac else idtac 
  | EX v : _, _ |-- _ => let fv := fresh v in (Intros fv; progltac g fname freefuncName (count + 1))
  | data_at _ _ _ _ |-- data_at _ _ _ _ => tryif solve[entailer! | entailer!! | list_solve] then idtac else idtac 
  | ?t |-- emp => simpl; entailer!!
  | emp |-- ?t =>  match t with 
                   | context [EX _: _, _] => Exists nullval; simpl; entailer!!
                   | _ =>  simpl; entailer!! 
                  end
  | ?Pr |-- ?Qr =>  match Qr with 
                    | Pr => entailer! 
                    | _ => simplifyEntailmentSubset Pr Qr
                    end 
  | _ => tryif solve[rep_lia | list_solve] then idtac else idtac 
  end
  end
  end
  end).
  (*end).
  end).*) 
