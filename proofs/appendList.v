Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.appendListC.
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


Definition appendList_spec :=
    DECLARE _appendList
      WITH p1: val, l1 : list Z, p2: val, l2: list Z
      PRE  [ tptr t_list, tptr t_list ]
      PROP() PARAMS (p1; p2) 
      SEP (listrep l1 p1; listrep l2 p2)
      POST [ tptr t_list ]
      EX q:val,
      PROP()
      RETURN(q)
      SEP (listrep (l1 ++ l2) q).

Definition Gprog := [malloc_spec; free_spec; appendList_spec].

Lemma appendListSynth: semax_body Vprog Gprog f_appendList appendList_spec.
Proof.
Admitted.