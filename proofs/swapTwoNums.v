Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.swapTwoNumsC.
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

Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, sh1 : share, a : Z, y: val, sh2: share, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= b <= Int.max_signed; Int.min_signed <= a <= Int.max_signed;
    Int.min_signed <= b + 1 <= Int.max_signed;  Int.min_signed <= a + 2 <= Int.max_signed
    )
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
   PROP () RETURN ()
   SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr a)) y). 
   
Definition Gprog := [malloc_spec; free_spec; swap_spec].

Lemma swapSynth: semax_body Vprog Gprog f_swap swap_spec.
Proof.
Admitted.