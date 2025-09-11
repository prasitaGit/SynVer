Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.allNumsSameC.
Require Import GenProof.sepauto.


Definition allNumsSame_spec : ident * funspec :=
  DECLARE _allNumsSame
  WITH a : val, sh : share, contents : list Z, ind : Z, length : Z
  PRE [ tptr tint, tuint, tuint ]
  PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind < length; 
        Forall (fun x =>  Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
  SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
  POST [ tbool ]
  EX bv: bool,
    PROP ((Forall (fun x => x = Znth ind contents) (sublist ind length contents)) <-> (bv = true))
    RETURN (bool2val bv)
    SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

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

Definition Gprog := [allNumsSame_spec; malloc_spec; free_spec].

Lemma allNumsSameSynth: semax_body Vprog Gprog f_allNumsSame allNumsSame_spec.
Proof.
Admitted.