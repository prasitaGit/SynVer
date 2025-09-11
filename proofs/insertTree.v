Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.insertTreeC.
Require Import GenProof.bstFunctionalProofs.
Require Import GenProof.sepauto.

Definition malloc_spec :=
  DECLARE _malloc
    WITH n: Z
    PRE [ tulong]
    PROP ()
    PARAMS (Vlong (Int64.repr n))
    SEP ()
    POST [ tptr tvoid ]
    EX v: val,
    PROP (malloc_compatible n v)
    RETURN (v)
    SEP (memory_block Tsh n v).

Definition free_spec :=
  DECLARE _free
  WITH p : val , n : Z
  PRE [ tptr tvoid]
  PROP() 
  PARAMS(p)
  SEP (memory_block Tsh n p)
  POST [ tvoid ]
  PROP () RETURN ( ) SEP ().

Definition insertTree_spec :=
  DECLARE _insertTree
  WITH b: val, t: tree, k: Z, v: Z
  PRE  [ tptr t_struct_tree, tint, tint ]
  PROP( Int.min_signed <= k <= Int.max_signed; Int.min_signed <= v <= Int.max_signed)
  PARAMS(b; Vint (Int.repr k); Vint (Int.repr v))
  SEP (tree_rep t b)
  POST [ tptr t_struct_tree ]
  EX q: val, 
  PROP()
  RETURN(q)
  SEP (tree_rep (insert k v t) q). 

Definition Gprog := [malloc_spec; free_spec; insertTree_spec].

Lemma insertTreeSynth: semax_body Vprog Gprog f_insertTree insertTree_spec.
Proof.
Admitted.