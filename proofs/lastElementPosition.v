Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.lastElementPositionC.
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

Definition lastElementPosition_spec : ident * funspec :=
  DECLARE _lastElementPosition
    WITH a : val, sh : share, contents : list Z, ele : Z, ind : Z, length : Z
     PRE [ tptr tint, tint, tint, tint ]
      PROP  (readable_share sh; Zlength contents = length;
      0 <= length <= Int.max_signed; -1 <= ind <= length;
      Int.min_signed <= ele <= Int.max_signed; ele <> Inhabitant_Z;
      Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
      PARAMS (a; Vint (Int.repr ele); Vint (Int.repr ind); Vint (Int.repr length))
      SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
     POST [ tint ]
      EX tind : Z,
      PROP (((Znth tind contents = ele) /\ Forall (fun x => x <> ele) (sublist (tind + 1) (ind + 1) contents)) <-> tind >= 0)
      RETURN (Vint (Int.repr tind))
      SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [malloc_spec; free_spec; lastElementPosition_spec].

Lemma lastElementPositionSynth: semax_body Vprog Gprog f_lastElementPosition lastElementPosition_spec.
Proof.
Admitted.