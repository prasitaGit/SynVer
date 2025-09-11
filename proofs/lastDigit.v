Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.lastDigitC.
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

Definition lastDigit_spec : ident * funspec :=
  DECLARE _lastDigit
    WITH n : Z 
      PRE [ tuint ]
      PROP  ( 0 <= n <= Int.max_unsigned)
      PARAMS (Vint (Int.repr n))
      SEP (TT)
      POST [ tuint ]
      PROP ()
      RETURN (Vint (Int.repr (Z.modulo n 10)))
      SEP(TT).

Definition Gprog := [malloc_spec; free_spec; lastDigit_spec].

Lemma lastDigitSynth: semax_body Vprog Gprog f_lastDigit lastDigit_spec.
Proof.
Admitted.