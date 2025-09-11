Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.mulTwoNumsC.
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

Definition mulTwoNums_spec : ident * funspec :=
    DECLARE _mulTwoNums
      WITH a : Z, b : Z
       PRE [tint, tint ]
        PROP  (Int.min_signed <= a <= Int.max_signed;
        Int.min_signed <= b <= Int.max_signed; Int.min_signed <= (Z.mul a b) <= Int.max_signed)
        PARAMS (Vint (Int.repr a); Vint (Int.repr b))
        SEP (TT)
       POST [ tint ]
        PROP ()
        RETURN (Vint (Int.repr (Z.mul a b)))
        SEP(TT).


Definition Gprog := [ malloc_spec; free_spec; mulTwoNums_spec].

Lemma mulTwoNumsSynth: semax_body Vprog Gprog f_mulTwoNums mulTwoNums_spec.
Proof.
Admitted.