Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.findMinNodeC.
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

Definition findMinNode_spec :=
  DECLARE _findMinNode
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tptr t_struct_tree ]
  EX q: val,
  PROP( q <> nullval )
  RETURN(q)
  SEP (tree_rep (inorderSuccessor t) q; tree_rep (inorderSuccessor t) q -* tree_rep t p).

Definition Gprog := [malloc_spec; free_spec; findMinNode_spec].

Lemma findMinNodeSynth: semax_body Vprog Gprog f_findMinNode findMinNode_spec.
Proof.
Admitted.