Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.freeListC.
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

Definition freeList_spec :=
    DECLARE _freeList
      WITH p: val, l : list Z
      PRE  [ tptr t_list ]
      PROP() PARAMS (p) SEP (listrep l p)
      POST [ Tvoid ]
      PROP()
      RETURN()
      SEP (emp).

Definition Gprog := [malloc_spec; free_spec; freeList_spec].

Lemma freeListSynth: semax_body Vprog Gprog f_freeList freeList_spec.
Proof.
Admitted.