Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.firstOddIndexC.
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

Definition firstOddIndex_spec : ident * funspec :=
  DECLARE _firstOddIndex
    WITH a : val, sh : share, contents : list Z, ind : Z, length : Z
     PRE [ tptr tint, tint, tint ]
      PROP  (readable_share sh; Zlength contents = length;
      0 <= length <= Int.max_signed; 0 <= ind <= length;
      Forall (fun x => 0 <= x <= Int.max_signed) contents)
      PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
      SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
     POST [ tint ]
      EX tind : Z,
      PROP (((Z.modulo (Znth tind contents) 2 = 1) /\ Forall (fun x => Z.modulo x 2 = 0) (sublist ind tind contents)) <-> (ind <= tind < length))
      RETURN (Vint (Int.repr tind))
      SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [malloc_spec; free_spec; firstOddIndex_spec].

Lemma firstOddIndexSynth: semax_body Vprog Gprog f_firstOddIndex firstOddIndex_spec.
Proof.
Admitted.