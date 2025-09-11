Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.findMinValueC.
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

Definition findMinValue_spec :=
  DECLARE _findMinValue
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tint ]
  PROP(Int.min_signed <= (inorderSuccessorValue t) <= Int.max_signed)
  RETURN(Vint (Int.repr (inorderSuccessorValue t)))
  SEP (tree_rep t p).

Definition Gprog := [malloc_spec; free_spec; findMinValue_spec].

Lemma findMinValueSynth: semax_body Vprog Gprog f_findMinValue findMinValue_spec.
Proof.
Admitted.