Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.addList1C.
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


Definition addList1_spec :=
  DECLARE _addList1
    WITH p: val, l: list Z
        PRE  [ tptr t_list ]
        PROP(Forall (fun x => Int.min_signed <= x <= Int.max_signed) l; 
        Forall (fun x => Int.min_signed <= Z.add x 1 <= Int.max_signed) l
        ) 
        PARAMS (p) 
        SEP (listrep l p)
        POST [ tptr t_list ]
        PROP()
        RETURN(p)
        SEP (listrep (map (fun x => x + 1) l) p).

Definition Gprog := [malloc_spec; free_spec; addList1_spec].

Lemma addList1Synth: semax_body Vprog Gprog f_addList1 addList1_spec.
Proof.
Admitted.