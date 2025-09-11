Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.checkListArraySameC.
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

Definition checkListArraySame_spec :=
  DECLARE _checkListArraySame
    WITH p: val, lp : list Z, a: val, sh: share, la: list Z, index: Z, length: Z
    PRE  [ tptr t_list, tptr tint, tuint, tuint ]
    PROP(readable_share sh; Zlength la = length; Zlength lp = length - index;
         0 <= length <= Int.max_unsigned; 0 <= index <= length;
         Forall (fun x => Int.min_signed <= x <= Int.max_signed) la)
    PARAMS (p; a; Vint (Int.repr index); Vint (Int.repr length))
    SEP (listrep lp p; data_at sh (tarray tint length) (map Vint (map Int.repr la)) a)
    POST [ tbool ]
    EX bv: bool,
    PROP((Forall2 eq (sublist index length la) lp) <-> (bv = true))
    RETURN(bool2val bv)
    SEP (listrep lp p; data_at sh (tarray tint length) (map Vint (map Int.repr la)) a).

Definition Gprog := [malloc_spec; free_spec; checkListArraySame_spec].

Lemma checkListArraySameSynth: semax_body Vprog Gprog f_checkListArraySame checkListArraySame_spec.
Proof.
Admitted.