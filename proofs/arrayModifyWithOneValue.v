Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.arrayModifyWithOneValueC.
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

Definition arrayModifyWithOneValue_spec : ident * funspec :=
  DECLARE _arrayModifyWithOneValue
    WITH a: val, sh : share, contents : list Z, value: Z, index: Z, length: Z
    PRE [ tptr tint, tint, tuint, tuint ]
    PROP  (0 <= index <= length; 0 <= length <= Int.max_unsigned;
    Zlength contents = length; writable_share sh; Int.min_signed <= value <= Int.max_signed)
    PARAMS (a; Vint (Int.repr value); Vint (Int.repr index); Vint (Int.repr length))
    SEP   (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
    POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr (sublist 0 index contents ++ Zrepeat value (length - index)))) a).

Definition Gprog := [malloc_spec; free_spec; arrayModifyWithOneValue_spec].

Lemma arrayModifyWithOneValueSynth: semax_body Vprog Gprog f_arrayModifyWithOneValue arrayModifyWithOneValue_spec.
Proof.
Admitted.