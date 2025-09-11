Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.isListEmptyC.
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

Definition isListEmpty_spec :=
   DECLARE _isListEmpty
    WITH p: val, sig : list Z
    PRE  [ tptr (tptr t_list) ]
    PROP() PARAMS (p) 
    SEP (sllbox_rep sig p)
    POST [ tbool ]
    PROP()
    RETURN(if Zlength sig =? 0 then (bool2val true) else (bool2val false))
    SEP (sllbox_rep sig p).

Definition Gprog := [malloc_spec; free_spec; isListEmpty_spec].

Lemma isListEmptySync: semax_body Vprog Gprog f_isListEmpty isListEmpty_spec.
Proof.
Admitted.