Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.popHighestC.
Require Import GenProof.stackLLAPI.
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
  WITH a: val, sh: share, contents: list Z
  PRE  [ tptr tint ]
  PROP(writable_share sh; Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS(a)
  SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ Tvoid ] 
    PROP()
    RETURN()
    SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr (sortarr contents))) a).
                            
  
Definition push_spec : ident * funspec :=
  DECLARE _push
   WITH p: val, sigma : list Z, value : Z
   PRE  [ tptr t_list, tint ]
   PROP (Int.min_signed <= value <= Int.max_signed)  
   PARAMS (p; Vint (Int.repr value))  
   SEP (listrep sigma p)
   POST [ tptr t_list ]
   EX q:val,
   PROP ()  
   RETURN (q)  
   SEP (listrep (value :: sigma) q).

Definition pop_spec :=
   DECLARE _pop
     WITH p: val, l : list Z
     PRE  [ tptr t_list ]
     PROP()
     PARAMS (p)
     SEP (listrep l p)
     POST [ tptr t_list ]
     EX q:val,
     PROP()
     RETURN(q)
     SEP (listrep (sublist 1 (Zlength l) l) q).

Definition peek_spec :=
    DECLARE _peek
       WITH p: val, l : list Z
       PRE  [ tptr t_list ]
       PROP()
       PARAMS (p)
       SEP (listrep l p)
       POST [ tint ]
       EX v:Z,
       PROP(if Zlength l =? 0 then v = -10 else v = Znth 0 l)
       RETURN(Vint (Int.repr v))
       SEP (listrep l p).

Definition isEmpty_spec :=
    DECLARE _isEmpty
    WITH p: val, sig : list Z
    PRE  [ tptr t_list ]
    PROP() PARAMS (p) 
    SEP (listrep sig p)
    POST [ tbool ]
    PROP()
    RETURN(if Zlength sig =? 0 then (bool2val true) else (bool2val false))
    SEP (listrep sig p).

Definition pushOneAtATime_spec :=
    DECLARE _pushOneAtATime
    WITH a: val, sh: share, contents: list Z
    PRE  [ tptr tint ]
    PROP(readable_share sh; Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS(a)
    SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
    POST [ tptr t_list ]
    EX t: val, 
    PROP()
    RETURN(t)
    SEP (listrep (rev contents) t; data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).
 
Definition popHighest_spec :=
    DECLARE _popHighest
    WITH a: val, sh: share, contents: list Z
    PRE  [ tptr tint ]
    PROP(writable_share sh; Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
    PARAMS(a)
    SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
    POST [ tptr t_list ]
    EX t: val, 
    PROP()
    RETURN(t)
    SEP (listrep (sublist 1 (Zlength contents) (rev (sortarr contents))) t; data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr (sortarr contents))) a).

Definition Gprog : funspecs :=
  ltac:(with_library prog 
       [malloc_spec; free_spec; push_spec; pop_spec; sortasc_spec;
       peek_spec; isEmpty_spec; pushOneAtATime_spec; popHighest_spec]).   

Lemma popHighestSynth: semax_body Vprog Gprog f_popHighest popHighest_spec.
Proof.
Admitted.