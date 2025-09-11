Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.bstLookupC.
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

Definition bstLookup_spec :=
  DECLARE _bstLookup
  WITH root: val, t: tree, x : Z
  PRE  [ tptr t_struct_tree,tint ]
  PROP( Int.min_signed <= x <= Int.max_signed)
  PARAMS(root; Vint (Int.repr x))
  SEP ( tree_rep t root)
  POST [ tbool ]
  PROP()
  RETURN(bool2val (lookupn x t))
  SEP (tree_rep t root).

Definition Gprog := [malloc_spec; free_spec; bstLookup_spec].

Lemma bstLookupSynth: semax_body Vprog Gprog f_bstLookup bstLookup_spec.
Proof.
Admitted.