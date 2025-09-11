Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.swapYwithXandAdd3toYC.
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

Definition swapYwithXandAdd3toY_spec : ident * funspec :=
  DECLARE _swapYwithXandAdd3toY
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
   PROP  (writable_share sh1; writable_share sh2;
          Int.min_signed <= Int.signed (Int.repr a) + Int.signed (Int.repr 3) <= Int.max_signed
    )
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr (a + 3))) y).

Definition Gprog := [malloc_spec; free_spec; swapYwithXandAdd3toY_spec].

Lemma swapYwithXandAdd3toYSynth: semax_body Vprog Gprog f_swapYwithXandAdd3toY swapYwithXandAdd3toY_spec.
Proof.
Admitted.