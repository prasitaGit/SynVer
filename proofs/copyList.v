Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.copyListC.
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

Definition copyList_spec :=
  DECLARE _copyList
  WITH p: val, l: list Z
  PRE  [ tptr t_list ]
  PROP()
  PARAMS (p)
  SEP (listrep l p)
  POST [ tptr t_list ]
  EX c:val,
  PROP()
  RETURN(c)
  SEP (listrep l p; listrep l c).

Definition Gprog := [malloc_spec; free_spec; copyList_spec].

Lemma copyListSynth: semax_body Vprog Gprog f_copyList copyList_spec.
Proof.
Admitted.