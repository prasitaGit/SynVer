Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.delStartC.
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

Definition delStart_spec :=
  DECLARE _delStart
    WITH p: val, l : list Z
    PRE  [ tptr (tptr t_list) ]
    PROP()
    PARAMS (p)
    SEP (sllbox_rep l p)
    POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (sllbox_rep (sublist 1 (Zlength l) l) p).


Definition Gprog := [malloc_spec; free_spec; delStart_spec].

Lemma delStartSynth: semax_body Vprog Gprog f_delStart delStart_spec.
Proof.
Admitted.