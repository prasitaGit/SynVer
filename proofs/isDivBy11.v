Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.isDivBy11C.
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

Definition isDivBy11_spec : ident * funspec :=
    DECLARE _isDivBy11
      WITH n : Z
       PRE [ tint ]
        PROP  (0 <= n <= Int.max_signed)
        PARAMS ( Vint (Int.repr n))
        SEP (TT)
       POST [ tbool ]
        PROP ()
        RETURN (if (Z.modulo n 11 =? 0) then (bool2val true) else (bool2val false))
        SEP(TT).

Definition Gprog := [ malloc_spec; free_spec; isDivBy11_spec].

Lemma isDivBy11Synth: semax_body Vprog Gprog f_isDivBy11 isDivBy11_spec.
Proof.
Admitted.