Require Import VST.floyd.proofauto.
Require Import GenProof.sllProof.
Require Import GenProof.skewedTreeC.
Require Import GenProof.bstAPI.
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

                           
Definition treebox_new_spec :=
  DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
  PROP() PARAMS() SEP ()
  POST [ tptr (tptr t_struct_tree) ]
  EX v:val,
  PROP()
  RETURN(v)
  SEP (data_at Tsh (tptr t_struct_tree) nullval v).
                            
Definition insertTree_spec :=
  DECLARE _insertTree
  WITH b: val, t: tree, k: Z, v: Z
  PRE  [ tptr t_struct_tree, tint, tint ]
  PROP( Int.min_signed <= k <= Int.max_signed; Int.min_signed <= v <= Int.max_signed)
  PARAMS(b; Vint (Int.repr k); Vint (Int.repr v))
  SEP (tree_rep t b)
  POST [ tptr t_struct_tree ]
  EX q: val, 
  PROP()
  RETURN(q)
  SEP (tree_rep (insert k v t) q). 

                           
Definition  inorderSucc_spec :=
  DECLARE _inorderSucc
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tptr t_struct_tree ]
  EX q: val,
  PROP( q <> nullval )
  RETURN(q)
  SEP (tree_rep (inorderSuccessor t) q; tree_rep (inorderSuccessor t) q -* tree_rep t p).
                           
Definition inorderSuccKey_spec :=
  DECLARE _inorderSuccKey
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tint ]
  PROP(Int.min_signed <= (inorderSuccessorKey t) <= Int.max_signed)
  RETURN(Vint (Int.repr (inorderSuccessorKey t)))
  SEP (tree_rep t p).  
                           
Definition inorderSuccValue_spec :=
  DECLARE _inorderSuccValue
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP( p <> nullval )
  PARAMS(p)
  SEP (tree_rep t p)
  POST [ tint ]
  PROP(Int.min_signed <= (inorderSuccessorValue t) <= Int.max_signed)
  RETURN(Vint (Int.repr (inorderSuccessorValue t)))
  SEP (tree_rep t p).
                           
Definition deleteTree_spec :=
  DECLARE _deleteTree
  WITH p: val, t: tree, x: Z
  PRE  [ tptr t_struct_tree, tint]
  PROP(Int.min_signed <= x <= Int.max_signed)
  PARAMS(p; Vint (Int.repr x))
  SEP (tree_rep t p)
  POST [ tptr t_struct_tree ]
  EX q:val, 
  PROP()
  RETURN(q)
  SEP (tree_rep (delete x t) q). 
                             
Definition deleteTreeWand_spec :=
  DECLARE _deleteTreeWand
  WITH p: val, t: tree, x: Z
  PRE  [ tptr t_struct_tree, tint]
  PROP(Int.min_signed <= x <= Int.max_signed)
  PARAMS(p; Vint (Int.repr x))
  SEP (tree_rep t p)
  POST [ tptr t_struct_tree ]
  EX q:val, 
  PROP()
  RETURN(q)
  SEP (tree_rep (deleteWand x t) q). 
                           
Definition lookup_spec :=
  DECLARE _lookup
  WITH root: val, t: tree, x : Z
  PRE  [ tptr t_struct_tree,tint ]
  PROP( Int.min_signed <= x <= Int.max_signed)
  PARAMS(root; Vint (Int.repr x))
  SEP ( tree_rep t root)
  POST [ tbool ]
  PROP()
  RETURN(bool2val (lookupn x t))
  SEP (tree_rep t root).
                           
Definition tree_free_spec :=
  DECLARE _tree_free
  WITH p: val, t: tree
  PRE  [ tptr t_struct_tree ]
  PROP() PARAMS (p) SEP (tree_rep t p)
  POST [ Tvoid ]
  PROP()
  RETURN()
  SEP (emp).
                           
Definition treebox_free_spec :=
  DECLARE _treebox_free
  WITH b: val, t: tree
  PRE  [ tptr (tptr t_struct_tree) ]
  PROP() PARAMS(b) SEP (treebox_rep t b)
  POST [ Tvoid ]
  PROP()
  RETURN()
  SEP (emp).

Definition insOneAtATime_spec :=
  DECLARE _insOneAtATime
  WITH p: val, t: tree, a: val, sh: share, contents: list Z, index: Z, n : Z
  PRE  [ tptr t_struct_tree, tptr tint, tuint, tuint ]
  PROP(0 <= n <= Int.max_unsigned; Zlength contents = n;
  0 <= index <= n; readable_share sh;
  Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS(p; a; Vint (Int.repr index); Vint (Int.repr n))
  SEP (tree_rep t p; data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
  POST [ tptr t_struct_tree ]
  EX q: val, 
  PROP()
  RETURN(q)
  SEP (tree_rep (insListSpec (sublist index n contents) t) q; data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a).
  
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

Definition skewedTree_spec :=
  DECLARE _skewedTree
  WITH a: val, sh: share, contents: list Z, n : Z
  PRE  [ tptr tint, tuint ]
  PROP(0 <= n <= Int.max_unsigned; Zlength contents = n;
      writable_share sh; NoDup contents;
      Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
  PARAMS(a; Vint (Int.repr n))
  SEP (data_at sh (tarray tint n) (map Vint (map Int.repr contents)) a)
  POST [ tptr t_struct_tree ]
  EX q: val, 
  PROP(isSkewed (insListSpec (sortarr contents) E))
  RETURN(q)
  SEP (tree_rep (insListSpec (sortarr contents) E) q; 
  data_at sh (tarray tint n) (map Vint (map Int.repr (sortarr contents))) a).
 
                                                      
Definition Gprog : funspecs :=
  ltac:(with_library prog 
       [malloc_spec; free_spec; treebox_new_spec; deleteTreeWand_spec; insOneAtATime_spec;
        tree_free_spec; treebox_free_spec; inorderSucc_spec; inorderSuccKey_spec; sortasc_spec;
        inorderSuccValue_spec; insertTree_spec; lookup_spec; deleteTree_spec; skewedTree_spec
        ]).   

Lemma skewedTreeSynth: semax_body Vprog Gprog f_skewedTree skewedTree_spec.
Proof.
Admitted.