Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.findMinKeyC.
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

Definition findMinKey_spec :=
  DECLARE _findMinKey
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tint ]
  PROP(Int.min_signed <= (inorderSuccessorKey t) <= Int.max_signed)
  RETURN(Vint (Int.repr (inorderSuccessorKey t)))
  SEP (tree_rep t p). 

Definition Gprog := [malloc_spec; free_spec; findMinKey_spec].

Lemma findMinKeySynth: semax_body Vprog Gprog f_findMinKey findMinKey_spec.
Proof.
Admitted.