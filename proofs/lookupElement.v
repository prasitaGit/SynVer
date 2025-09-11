Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.lookupElementC.
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

Definition lookupElement_spec : ident * funspec :=
  DECLARE _lookupElement
   WITH p: val, sigma : list Z, value : Z
   PRE  [ tptr t_list, tint ]
   PROP (Int.min_signed <= value <= Int.max_signed)
   PARAMS (p; Vint (Int.repr value))
   SEP (listrep sigma p)
   POST [ tbool ]
   EX bv: bool,
   PROP ((In value sigma) <-> (bv = true))
   RETURN (bool2val bv)
   SEP (listrep sigma p).

Definition Gprog := [malloc_spec; free_spec; lookupElement_spec].

Lemma lookupElementSynth: semax_body Vprog Gprog f_lookupElement lookupElement_spec.
Proof.
Admitted.