Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.addLastC.
Require Import GenProof.listAddAPI.


Definition malloc_spec :=
  DECLARE _malloc
  WITH n: Z
  PRE [ tulong]
  PROP ((*4 <= n <= Int.max_unsigned)*))
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

Definition addHelper_spec :=
  DECLARE _addHelper
    WITH p: val, l : list Z, x: Z
    PRE  [ tptr t_list, tint ]
    PROP(Zlength l > 0; Int.min_signed <= x <= Int.max_signed) 
    PARAMS (p; Vint (Int.repr x)) 
    SEP (listrep l p)
    POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (listrep (l ++ [x]) p).

Definition addLast_spec :=
  DECLARE _addLast
    WITH p: val, l : list Z, x: Z
    PRE  [ tptr (tptr t_list), tint ]
    PROP(Int.min_signed <= x <= Int.max_signed) 
    PARAMS (p; Vint (Int.repr x)) 
    SEP (sllbox_rep l p)
    POST [ Tvoid ]
    PROP()
    RETURN()
    SEP (sllbox_rep (l ++ [x]) p).

Definition Gprog : funspecs :=
    ltac:(with_library prog 
         [malloc_spec; free_spec; addHelper_spec; addLast_spec]).   


Lemma addLastSynth: semax_body Vprog Gprog f_addLast addLast_spec.
Proof.
Admitted.