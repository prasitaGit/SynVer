Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.listLengthC.
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

Definition listLength_spec :=
    DECLARE _listLength
    WITH p: val, l : list Z
    PRE  [ tptr t_list ]
    PROP() PARAMS (p) 
    SEP (listrep l p)
    POST [ tuint ]
    PROP()
    RETURN(Vint (Int.repr (Zlength l)))
    SEP (listrep l p).

Definition Gprog := [malloc_spec; free_spec; listLength_spec].

Lemma listLengthSynth: semax_body Vprog Gprog f_listLength listLength_spec.
Proof.
Admitted.