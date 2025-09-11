Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.isOddAtIndexOddC.
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

Definition isOddAtIndexOdd_spec : ident * funspec :=
  DECLARE _isOddAtIndexOdd
  WITH a : val, sh : share, contents : list Z, ind : Z, length : Z
  PRE [ tptr tint, tuint, tuint ]
  PROP  (readable_share sh; Zlength contents = length;
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Forall (fun x => 0 <= x <= Int.max_signed) contents)
  PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
  SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
  POST [ tbool ]
  EX b : bool,
  PROP (
    Forall2 (fun x y => Z.modulo (y + ind) 2 = 1 -> Z.modulo x 2 = 1) (sublist ind length contents) (upto (Z.to_nat (length - ind))) <-> (b = true)
  )
  RETURN (bool2val b)
  SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [malloc_spec; free_spec; isOddAtIndexOdd_spec].

Lemma isOddAtIndexOddXSynth: semax_body Vprog Gprog f_isOddAtIndexOdd isOddAtIndexOdd_spec.
Proof.
Admitted.