Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.checkTwoArrayTypesSameC.
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

Definition checkTwoArrayTypesSame_spec : ident * funspec :=
  DECLARE _checkTwoArrayTypesSame
  WITH a: val, sha : share, contentsa : list Z, b : val, shb : share,
  contentsb: list Z, index: Z, length: Z
  PRE [ tptr tschar, tptr tint, tuint, tuint ]
  PROP  (0 <= index <= length; 0 <= length <= Int.max_unsigned;
        Zlength contentsa = length; Zlength contentsb = length;
        readable_share sha; readable_share shb;
        Forall (fun x => Byte.min_signed <= x <= Byte.max_signed) contentsa;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contentsb)
  PARAMS (a; b; Vint (Int.repr index); Vint (Int.repr length))
  SEP   (data_at sha (tarray tschar length) (map Vint (map Int.repr contentsa)) a;
  data_at shb (tarray tint length) (map Vint (map Int.repr contentsb)) b)
  POST [ tbool ]
  EX bv: bool,
  PROP (Forall2 eq (sublist index length contentsa)(sublist index length contentsb) <-> bv = true)
  RETURN (bool2val bv)
  SEP (data_at sha (tarray tschar length) (map Vint (map Int.repr contentsa)) a;
  data_at shb (tarray tint length) (map Vint (map Int.repr contentsb)) b).

Definition Gprog := [malloc_spec; free_spec; checkTwoArrayTypesSame_spec].

Lemma checkTwoArrayTypesSameSynth: semax_body Vprog Gprog f_checkTwoArrayTypesSame checkTwoArrayTypesSame_spec.
Proof.
Admitted.