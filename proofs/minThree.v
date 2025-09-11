Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.minThreeC.
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

Definition minThree_spec : ident * funspec :=
  DECLARE _minThree
  WITH a : Z, b : Z, c :Z
  PRE [ tint, tint, tint ]
  PROP  (Int.min_signed <= a <= Int.max_signed;
        Int.min_signed <= b <= Int.max_signed; Int.min_signed <= c <= Int.max_signed)
  PARAMS ( Vint (Int.repr a); Vint (Int.repr b);  Vint (Int.repr c))
  SEP (TT)
  POST [ tint ]
  PROP ()
  RETURN (Vint (Int.repr (Z.min a (Z.min b c))))
  SEP(TT).

Definition Gprog := [malloc_spec; free_spec; minThree_spec].

Lemma minThreeSynth: semax_body Vprog Gprog f_minThree minThree_spec.
Proof.
Admitted.