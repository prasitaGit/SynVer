Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.deleteendC.
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

Definition deleteend_spec : ident * funspec :=
  DECLARE _deleteend
  WITH p: val, sigma : list Z
  PRE  [ tptr t_list]
  PROP ()
  PARAMS (p)
  SEP (listrep sigma p)
  POST [ tptr t_list ]
  EX q:val,
  PROP ()
  RETURN (q)
  SEP (listrep (sublist 0 (Zlength sigma - 1) sigma) q).

Definition Gprog := [malloc_spec; free_spec; deleteend_spec].

Lemma deleteendSynth: semax_body Vprog Gprog f_deleteend deleteend_spec.
Proof.
Admitted.