Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.addAllElementsInRangeBy1C.
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

Definition addAllElementsInRangeBy1_spec : ident * funspec :=
  DECLARE _addAllElementsInRangeBy1
    WITH a: val, sh : share, contents : list Z, ind : Z, length : Z
     PRE [ tptr tint, tuint, tuint ]
     PROP  (writable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind <= length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
        Forall (fun x => Int.min_signed <= x + 1 <= Int.max_signed) (sublist ind length contents))
     PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
     POST [ tvoid ]
     PROP ()
     RETURN () 
     SEP (data_at sh (tarray tint length) (map Vint (map Int.repr ((sublist 0 ind contents) ++ map (fun x => x + 1) (sublist ind length contents)))) a).

Definition Gprog := [malloc_spec; free_spec; addAllElementsInRangeBy1_spec].

Lemma addAllElementsInRangeBy1Synth: semax_body Vprog Gprog f_addAllElementsInRangeBy1 addAllElementsInRangeBy1_spec.
Proof.
Admitted.