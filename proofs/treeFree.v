Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.treeFreeC.
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

Definition treeFree_spec :=
  DECLARE _treeFree
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP() PARAMS (p) SEP (tree_rep t p)
  POST [ Tvoid ]
  PROP()
  RETURN()
  SEP (emp).

Definition Gprog := [malloc_spec; free_spec; treeFree_spec].

Lemma treeFreeSynth: semax_body Vprog Gprog f_treeFree treeFree_spec.
Proof.
Admitted.