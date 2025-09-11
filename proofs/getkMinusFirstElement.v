Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.getkMinusFirstElementC.
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

Definition getkMinusFirstElement_spec : ident * funspec :=
    DECLARE _getkMinusFirstElement
      WITH a : val, sh : share, contents : list Z, k : Z, length : Z
       PRE [ tptr tuint, tint, tint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_signed;  Int.min_signed <= k <= Int.max_signed;
        Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
        PARAMS (a; Vint (Int.repr k); Vint (Int.repr length))
        SEP (data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
       PROP ()
        RETURN(if (k <? 1) then Vint (Int.repr (-1)) else if (k >? length) then Vint (Int.repr (-1))
        else Vint (Int.repr (Znth (k - 1) contents)))
        SEP(data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [malloc_spec; free_spec; getkMinusFirstElement_spec].

Lemma getkMinusFirstElementSynth: semax_body Vprog Gprog f_getkMinusFirstElement getkMinusFirstElement_spec.
Proof.
Admitted.