Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.countOccurenceC.
Require Import GenProof.countOccurenceC.
Require Import GenProof.bstFunctionalProofs.


(*specifications*)
Definition malloc_spec :=
  DECLARE _malloc
  WITH n: Z
  PRE [ tulong]
  PROP ((*4 <= n <= Int.max_unsigned)*))
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
                            
  
Definition sortasc_spec :=
  DECLARE _sortasc
  WITH a: val, sh: share, contents: list Z, n : Z
  PRE  [ tptr tint, tuint ]
  PROP(0 <= n <= Int.max_unsigned; Zlength contents = n; 
    writable_share sh; Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS(a; Vint (Int.repr n))
  SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
  POST [ Tvoid ] 
    PROP()
    RETURN()
    SEP (data_at sh (tarray tint n) (map Vint (map Int.repr (sortarr contents))) a).


Definition initialize_spec :=
    DECLARE _initialize
    WITH a: val, sh: share, contents: list Z, n : Z, value : Z
    PRE  [ tptr tint, tuint, tint ]
    PROP(0 <= n <= Int.max_unsigned; Zlength contents = n; Int.min_signed <= value <= Int.max_signed; 
      writable_share sh; Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS(a; Vint (Int.repr n); Vint (Int.repr value))
    SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
    POST [ Tvoid ] 
      PROP()
      RETURN()
      SEP (data_at sh (tarray tint n) (map Vint (map Int.repr (Zrepeat value n))) a).

Definition update_spec :=
    DECLARE _update
      WITH a: val, sh: share, contents: list Z, index : Z, n : Z, value : Z
      PRE  [ tptr tint, tuint, tuint, tint ]
      PROP(0 <= n <= Int.max_unsigned; Zlength contents = n; Int.min_signed <= value <= Int.max_signed; 
        0 <= index <= Int.max_unsigned; writable_share sh; 
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
      PARAMS(a; Vint (Int.repr index); Vint (Int.repr n); Vint (Int.repr value))
      SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
      POST [ Tvoid ] 
        PROP()
        RETURN()
        SEP (data_at sh (tarray tint n) (map Vint (map Int.repr (upd_Znth index contents value))) a).


Definition lookupfirst_spec : ident * funspec :=
    DECLARE _lookupfirst
    WITH a : val, sh : share, contents : list Z, length : Z, num : Z
    PRE [ tptr tint, tuint, tint ]
    PROP  (readable_share sh; Zlength contents = length;
            0 <= length <= Int.max_unsigned; 
            Int.min_signed <= num <= Int.max_signed; In num contents;
            Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint (Int.repr length); Vint (Int.repr num))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
    POST [ tuint ]
    EX tind : Z,
    PROP ((Znth tind contents = num) /\ Forall (fun x => x <> num) (sublist 0 tind contents)) (*reasoning about the full array*)
    RETURN (Vint (Int.repr tind))
    SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

        

Definition lookuplast_spec : ident * funspec :=
    DECLARE _lookuplast
    WITH a : val, sh : share, contents : list Z, length : Z, num : Z
    PRE [ tptr tint, tuint, tint ]
    PROP  (readable_share sh; Zlength contents = length;
        0 <= length <= Int.max_unsigned; 
        Int.min_signed <= num <= Int.max_signed; In num contents;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint (Int.repr length); Vint (Int.repr num))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
    POST [ tuint ]
    EX tind : Z,
    PROP ((Znth tind contents = num) /\ Forall (fun x => x <> num) (sublist (tind + 1) length contents)) (*reasoning about the full array*)
    RETURN (Vint (Int.repr tind))
    SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).


Definition member_spec : ident * funspec :=
    DECLARE _member
    WITH a: val, sh: share, contents: list Z, n : Z, num : Z
    PRE  [ tptr tint, tuint, tint ]
    PROP (readable_share sh; 0 <= n <= Int.max_unsigned; Zlength contents = n;
    Int.min_signed <= num <= Int.max_signed; 
    Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint (Int.repr n); Vint (Int.repr num))
    SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
    POST [ tbool ]
    EX bv: bool,
    PROP ((In num contents) <-> (bv = true))
    RETURN (bool2val bv)
    SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a).

 
Definition countOccurence_spec : ident * funspec :=
    DECLARE _countOccurence
    WITH a : val, sh : share, contents : list Z, length : Z, num : Z
    PRE [ tptr tint, tuint, tint ]
    PROP  (writable_share sh; Zlength contents = length;
        0 <= length <= Int.max_unsigned; 
        Int.min_signed <= num <= Int.max_signed; 
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS (a; Vint (Int.repr length); Vint (Int.repr num))
    SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
    POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (fold_right (fun x => fun y => if x =? num then Z.add 1 y else y) 0 contents)))
    SEP(data_at sh (tarray tint length) (map Vint (map Int.repr (sortarr contents))) a).


Definition Gprog : funspecs :=
  ltac:(with_library prog 
       [malloc_spec; free_spec; initialize_spec; update_spec; sortasc_spec;
       lookupfirst_spec; lookuplast_spec; member_spec; countOccurence_spec
        ]).   

Lemma countOccurenceSynth: semax_body Vprog Gprog f_countOccurence countOccurence_spec.
Proof.
Admitted.