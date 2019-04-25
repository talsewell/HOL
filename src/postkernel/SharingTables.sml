structure SharingTables :> SharingTables =
struct

open Term Type

local open Feedback
in val ERR = mk_HOL_ERR "SharingTables" end

structure Map = Redblackmap
structure Set = Redblackset

(* ----------------------------------------------------------------------
    Shared Types and per-Theory stored vectors
   ---------------------------------------------------------------------- *)

type theory_ref = {ThyId : int, Id : int}
type thy_name = string

datatype shared_id = IDStr of string | IDRef of theory_ref
datatype shared_type = TYV of int
                     | TYOP of int list
                     | TYRef of theory_ref
datatype shared_term = TMV of int * int
                     | TMC of int * int * int
                     | TMAp of int * int
                     | TMAbs of int * int
                     | TMRef of theory_ref

type idv = (string * shared_id) Vector.vector
type typev = (Type.hol_type * shared_type) Vector.vector
type termv = (Term.term * shared_term) Vector.vector
type vectors = {ids : idv, types : typev, terms : termv,
                sharing_parents : thy_name Vector.vector}
type vv = vectors Vector.vector

val thy_vectors = ref (Map.mkDict String.compare : (string, vectors) Map.dict)
fun register_theory_vectors thy vs
  = (thy_vectors := Map.insert (! thy_vectors, thy, vs))

fun mk_vv (parents : thy_name Vector.vector) : vv = let
    val tv = ! thy_vectors
    fun find s = Map.find (tv, s) handle NotFound => raise ERR "mk_vv" s
  in Vector.map find parents end

fun lookup_vectors thy_id = Map.find (! thy_vectors, thy_id)
  handle NotFound => raise ERR "lookup_vectors" thy_id

val peek_theory_vectors = lookup_vectors

fun lookup_vv (parents : vv) f (i : theory_ref) =
    Vector.sub (f (Vector.sub (parents, #ThyId i)), #Id i)

fun vec_to_list v = Vector.foldr (op ::) [] v

fun get_share_parents (parents : thy_name list) = let
    (* maps parents to ancestors in compatible order *)
    fun loop [] (anc_set, ancs) = ancs
      | loop (p :: ps) (anc_set, ancs) = let
        val p_ancs = vec_to_list (#sharing_parents (lookup_vectors p))
        val fresh = Lib.filter (fn s => not (Set.member (anc_set, s))) p_ancs
      in loop ps (Set.addList (anc_set, fresh), ancs @ fresh @ [p]) end
    val ancs = loop parents (Set.empty String.compare, [])
  in Vector.fromList ancs end

(* ----------------------------------------------------------------------
    Unique Tuple Encoding

    Maps values encoded as strings or tuples of values to a unique
    identifier. This must be done recursively, as a tuple's ID is
    calculated from the unique IDs of its components.
   ---------------------------------------------------------------------- *)

type uniq_id = int

fun next_uniq_id x = x + 1

(* values that unique ids can represent *)
datatype id_value = TypeID of shared_type
    | TermID of shared_term

(* tuple kinds:
   - TYV - string * string
   - TYOp - n-tuple - string * string and n-tuple * type
   - TMV - string * type
   - TMC - 3-tuple - type * string, n-tuple * string
   - TMAp - term * term
   - TMAbs - term * term
*)

type uniqtable = {nextid : uniq_id,
                  strings : (string, uniq_id) Map.dict,
                  tuples : ((uniq_id * uniq_id * int), uniq_id) Map.dict,
                  vals : (uniq_id * id_value) list}

val cmp_tuple = let
    fun f (x, y, k) = (x, (y, k))
    val p = Lib.pair_compare
  in Lib.inv_img_cmp f (p (Int.compare, p (Int.compare, Int.compare))) end

(* kind tags used to avoid accidental collisions on tuples *)
val [TYVKind, TYOPKind, TMVKind, TMCKind, TMAbsKind, TMApKind] = Lib.upto 1 6

exception HasID of uniq_id

val empty_uniqtable : uniqtable = {nextid = 0,
    strings = Map.mkDict String.compare, tuples = Map.mkDict cmp_tuple,
    vals = []}

fun encode_string (t : uniqtable) s = let
    val {nextid, strings, tuples, vals} = t
    fun upd NONE = nextid | upd (SOME id) = raise (HasID id)
    val map = Map.update (strings, s, upd)
  in ({nextid = next_uniq_id nextid, strings = map,
       tuples = tuples, vals = vals}, nextid)
  end handle HasID id => (t, id)

fun lookup_string (t : uniqtable) s = Redblackmap.find (#strings t, s)

fun encode_tuple (t : uniqtable) tup = let
    val {nextid, strings, tuples, vals} = t
    fun upd NONE = nextid | upd (SOME id) = raise (HasID id)
    val map = Map.update (tuples, tup, upd)
  in ({nextid = next_uniq_id nextid, strings = strings, tuples = map,
       vals = vals}, nextid)
  end handle HasID id => (t, id)

fun lookup_tuple _ (~1, _, _) = raise Map.NotFound
  | lookup_tuple _ (_, ~1, _) = raise Map.NotFound
  | lookup_tuple (t : uniqtable) tup = Redblackmap.find (#tuples t, tup)

fun encode_ntuple t k [x, y] = encode_tuple t (x, y, k)
  | encode_ntuple t k (x :: y :: zs) = let
    val (t, id) = encode_tuple t (x, y, k)
  in encode_ntuple t k (id :: zs) end
  | encode_ntuple _ _ _ = raise ERR "encode_ntuple" "assumes 2+ elements"

fun lookup_ntuple t k [x, y] = lookup_tuple t (x, y, k)
  | lookup_ntuple t k (x :: y :: zs)
    = lookup_ntuple t k (lookup_tuple t (x, y, k) :: zs)
  | lookup_ntuple _ _ _ = raise ERR "lookup_nutple" "assumes 2+ elements"

fun add_value v (t : uniqtable, n) = let
    val {nextid, strings, tuples, vals} = t
  in ({nextid = nextid, strings = strings, tuples = tuples,
       vals = (n, v) :: vals}, n)
  end

fun encode_tuple_val v t tup = add_value v (encode_tuple t tup)

(* ----------------------------------------------------------------------
    Encoding Phase 1: Assign unique IDs to elements
   ---------------------------------------------------------------------- *)

fun replicate n v = map (fn _ => v) (Lib.upto 1 n)

fun type_id (t : uniqtable, typ) = if is_vartype typ
  then let
    val (t, s_id) = encode_string t (dest_vartype typ)
  in encode_tuple_val (TypeID (TYV s_id)) t (s_id, s_id, TYVKind) end
  else let
    val {Thy, Tyop, Args} = dest_thy_type typ
    val (t, thy_id) = encode_string t Thy
    val (t, op_id) = encode_string t Tyop
    val (t, arg_ids) = Lib.foldl_map type_id (t, Args)
  in add_value (TypeID (TYOP (thy_id :: op_id :: arg_ids)))
    (encode_ntuple t TYOPKind (thy_id :: op_id :: arg_ids)) end

fun term_id (t : uniqtable, term) = if is_var term
  then let
    val (nm, typ) = dest_var term
    val (t, nm_id) = encode_string t nm
    val (t, ty_id) = type_id (t, typ)
  in
    encode_tuple_val (TermID (TMV (nm_id, ty_id))) t (nm_id, ty_id, TMVKind)
  end
  else if is_const term then let
    val {Thy, Name, Ty} = dest_thy_const term
    val (t, thy_id) = encode_string t Thy
    val (t, nm_id) = encode_string t Name
    val (t, ty_id) = type_id (t, Ty)
    val (t, id) = encode_ntuple t TMCKind [ty_id, thy_id, nm_id]
  in add_value (TermID (TMC (thy_id, nm_id, ty_id))) (t, id) end
  else if is_comb term then let
    val (f, x) = dest_comb term
    val (t, f_id) = term_id (t, f)
    val (t, x_id) = term_id (t, x)
  in
    encode_tuple_val (TermID (TMAp (f_id, x_id))) t (f_id, x_id, TMApKind)
  end
  else (* must be an abstraction *) let
    val (v, body) = dest_abs term
    val (t, v_id) = term_id (t, v)
    val (t, b_id) = term_id (t, body)
  in
    encode_tuple_val (TermID (TMAbs (v_id, b_id))) t (v_id, b_id, TMAbsKind)
  end

(* ----------------------------------------------------------------------
    Encoding Phase 2: Scan parent elements, map to IDs
   ---------------------------------------------------------------------- *)

fun scan_parent_wrapper (v : 'a Vector.vector)
                        (f : int Array.array -> 'a -> int) (thy_id : int)
                        (refs : theory_ref option Array.array)
  = let
    val arr = Array.array (Vector.length v, ~1)
    fun g (i, x) = let
        val id = f arr x
      in (id = ~1 orelse raise Map.NotFound);
        Array.update (refs, id, SOME {ThyId = thy_id, Id = i});
        Array.update (arr, i, id)
      end handle Map.NotFound => ()
  in Vector.appi g v; arr end

fun share_parent_ids thy_id arrs (idv : idv) t refs = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    fun f (s, IDRef r) = arrs_ref r
      | f (s, IDStr _) = lookup_string t s
  in scan_parent_wrapper idv (Lib.K f) thy_id refs end

fun share_parent_tys thy_id id_arr arrs (typev : typev) t refs = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    val id_sub = Lib.curry Array.sub id_arr
    fun f _ (_, TYRef r) = arrs_ref r
      | f _ (_, TYV i) = lookup_tuple t (id_sub i, id_sub i, TYVKind)
      | f arr (_, TYOP (thy_id :: nm_id :: args))
        = lookup_ntuple t TYOPKind (id_sub thy_id :: id_sub nm_id ::
            map (Lib.curry Array.sub arr) args)
      | f _ (_, TYOP _) = raise ERR "share" "TYOP: not enough arguments"
  in scan_parent_wrapper typev f thy_id refs end

fun share_parent_tms thy_id id_arr ty_arr arrs (termv : termv) t refs = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    fun tup_sub (arr, i) (arr2, j) k = lookup_tuple t
        (Array.sub (arr, i), Array.sub (arr2, j), k)
    fun f _ (_, TMRef r) = arrs_ref r
      | f _ (_, TMV (i, j)) = tup_sub (id_arr, i) (ty_arr, j) TMVKind
      | f _ (_, TMC (i, j, k)) = lookup_ntuple t TMCKind
          [Array.sub (id_arr, i), Array.sub (id_arr, j), Array.sub (ty_arr, k)]
      | f arr (_, TMAp (i, j)) = tup_sub (arr, i) (arr, j) TMApKind
      | f arr (_, TMAbs (i, j)) = tup_sub (arr, i) (arr, j) TMAbsKind
  in scan_parent_wrapper termv f thy_id refs end

fun share_all parent_thys t = let
    val refs = Array.array (#nextid t, NONE)
    val parents = get_share_parents parent_thys
    val id_arrs = Array.array (Vector.length parents, Array.array (0, ~1))
    val ty_arrs = Array.array (Vector.length parents, Array.array (0, ~1))
    val tm_arrs = Array.array (Vector.length parents, Array.array (0, ~1))
    val thy_ids = Map.fromList String.compare
        (Lib.mapi (fn i => fn s => (s, i)) (vec_to_list parents))
    fun find_id s = Map.find (thy_ids, s)
    fun gather arrs ids = Vector.fromList
        (map (fn i => Array.sub (arrs, i)) ids)
    fun doit (i, thy_id) = let
        val vectors = lookup_vectors thy_id
        val parent_ids = map find_id (vec_to_list (#sharing_parents vectors))
        val _ = Lib.all (fn j => j < i) parent_ids
            orelse raise ERR "share_all: parent_ids" thy_id
        val id_arr = share_parent_ids i (gather id_arrs parent_ids)
            (#ids vectors) t refs
        val _ = Array.update (id_arrs, i, id_arr)
        val ty_arr = share_parent_tys i id_arr (gather ty_arrs parent_ids)
            (#types vectors) t refs
        val _ = Array.update (ty_arrs, i, ty_arr)
        val tm_arr = share_parent_tms i id_arr ty_arr
            (gather tm_arrs parent_ids) (#terms vectors) t refs
        val _ = Array.update (tm_arrs, i, tm_arr)
      in () end
  in Vector.appi doit parents; refs end
 
(* ----------------------------------------------------------------------
    Encoding Phase 3: Assign final IDs to required unique IDs
   ---------------------------------------------------------------------- *)

fun get_required refs (t : uniqtable) reqss = let
    val deps = Array.array (#nextid t, [])
    fun f ((i, j, _), id) = Array.update (deps, id, [i, j])
    val _ = Map.app f (#tuples t)
    val req = Array.array (Array.length refs, false)
    fun f [] = ()
      | f (n :: ns) = if Array.sub (req, n) then f ns
      else let
        val xs = if Option.isSome (Array.sub (refs, n))
          then [] else Array.sub (deps, n)
      in Array.update (req, n, true); f (xs @ ns) end
  in app f reqss; req end

fun finalise_shared refs (t : uniqtable) req = let
    val state = ((0, []), (0, []), (0, []))
    fun id v ((n, ids), tys, tms) = (n, ((n + 1, v :: ids), tys, tms))
    fun ty v (ids, (n, tys), tms) = (n, (ids, (n + 1, v :: tys), tms))
    fun tm v (ids, tys, (n, tms)) = (n, (ids, tys, (n + 1, v :: tms)))
    val fin_arr = Array.array (Array.length refs, ~1)
    fun sh_id (s, i, st) = if Array.sub (req, i) then let
        val sh = case Array.sub (refs, i) of NONE => IDStr s
          | SOME r => IDRef r
        val (j, st) = id sh st
      in Array.update (fin_arr, i, j); st end
      else st
    val state = Map.foldl sh_id state (#strings t)
    val fin = Lib.curry Array.sub fin_arr
    fun fin_sh_tm (TMV (i, j)) = TMV (fin i, fin j)
      | fin_sh_tm (TMAp (i, j)) = TMAp (fin i, fin j)
      | fin_sh_tm (TMAbs (i, j)) = TMAbs (fin i, fin j)
      | fin_sh_tm (TMC (i, j, k)) = TMC (fin i, fin j, fin k)
      | fin_sh_tm (TMRef _) = raise ERR "fin_sh_tm" "TMRef unexpected"
    fun fin_sh_ty (TYOP ids) = TYOP (map fin ids)
      | fin_sh_ty (TYV i) = TYV (fin i)
      | fin_sh_ty (TYRef _) = raise ERR "fin_sh_ty" "TYRef unexpected"
    fun sh_val ((i, v), st) = if Array.sub (req, i) then let
        val (n, st) = case v of
            TypeID sh_ty => ty (fin_sh_ty sh_ty) st
          | TermID sh_tm => tm (fin_sh_tm sh_tm) st
      in Array.update (fin_arr, i, n); st end
      else st
    val ((_, ids), (_, tys), (_, tms)) = List.foldr sh_val state (#vals t)
  in (rev ids, rev tys, rev tms, fin_arr) end

(* ----------------------------------------------------------------------
    IDs (strings)
   ---------------------------------------------------------------------- *)

type idtable = {idsize : int,
                idmap : (string, (int * int option)) Map.dict,
                idlist : shared_id list}

fun build_id_vector parent_thys sh_ids = let
  val parents = mk_vv parent_thys
  fun conv_id (IDStr s) = s
    | conv_id (IDRef i) = #1 (lookup_vv parents (#ids) i)
  in Vector.fromList (map (fn s => (conv_id s, s)) sh_ids) end

val CB = PP.block PP.CONSISTENT 0
val out = PP.add_string
val NL = PP.NL

fun pad_thy_ref s (i : theory_ref) =
    Int.toString (#ThyId i) ^ s ^ Int.toString (#Id i)

fun theoryout_idtable (idlist : shared_id list) = let
  fun print_id (IDStr s) = out ("IDStr " ^ Lib.mlquote s)
    | print_id (IDRef i) = out ("IDRef " ^ pad_thy_ref " " i)
  val print_ids = PP.pr_list print_id [PP.add_string ",", PP.add_break(1,0)]
in
  CB [out "[",
      PP.block PP.INCONSISTENT 1 (print_ids idlist),
      out "]"
  ]
end

(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

val default_type = Type.mk_vartype "'SharingTables_out_of_order"

fun build_type_vector parent_thys idv sh_tys = let
  val parents = mk_vv parent_thys
  val ty_arr = Array.array (length sh_tys, default_type)
  fun id i = #1 (Vector.sub (idv, i))
  fun conv_ty (TYV i) = Type.mk_vartype (id i)
    | conv_ty (TYOP (thy_id :: nm_id :: args)) = let
        val arg_tys = map (Lib.curry Array.sub ty_arr) args
      in Type.mk_thy_type {Thy = id thy_id, Tyop = id nm_id, Args = arg_tys} end
    | conv_ty (TYOP _) = raise ERR "conv_ty" "TYOP: not enough arguments"
    | conv_ty (TYRef i) = #1 (lookup_vv parents (#types) i)
  val tys = Lib.mapi (fn n => fn x => let val ty = conv_ty x in
    Array.update (ty_arr, n, ty); (ty, x) end) sh_tys
  in Vector.fromList tys end

fun theoryout_typetable (tylist : shared_type list) = let
  fun output_shtype shty =
      case shty of
        TYV i => out ("TYV "^ Int.toString i)
      | TYOP args =>
        out ("TYOP "^ String.concatWith " " (map Int.toString args))
      | TYRef i => out ("TYRef " ^ pad_thy_ref " " i)
  val output_shtypes = PP.pr_list output_shtype [out ",", PP.add_break (1,0)]
in
  CB [
    out "[",
    PP.block PP.INCONSISTENT 1 (output_shtypes tylist),
    out "]"
  ]
end

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

(* sort terms by equality. Term.compare sorts alpha-equivalent terms equal. *)
fun term_compare (t1, t2) = if is_abs t1 andalso is_abs t2
    then Lib.pair_compare (term_compare, term_compare) (dest_abs t1, dest_abs t2)
    else if is_comb t1 andalso is_comb t2
    then Lib.pair_compare (term_compare, term_compare) (dest_comb t1, dest_comb t2)
    else Term.compare (t1, t2)

val default_term = Term.mk_var ("SharingTables_out_of_order", default_type)

fun build_term_vector parent_thys idv tyv sh_tms = let
  open Term
  val parents = mk_vv parent_thys
  val tm_arr = Array.array (length sh_tms, default_term)
  val tm_sub = Lib.curry Array.sub tm_arr
  fun id i = #1 (Vector.sub (idv, i))
  fun ty i = #1 (Vector.sub (tyv, i))
  fun conv_tm (TMV (s_id, ty_id)) = mk_var (id s_id, ty ty_id)
    | conv_tm (TMC (thy_id, nm_id, ty_id)) = mk_thy_const
        {Name = id nm_id, Thy = id thy_id, Ty = ty ty_id}
    | conv_tm (TMAp (f_id, x_id)) = mk_comb (tm_sub f_id, tm_sub x_id)
    | conv_tm (TMAbs (v_id, b_id)) = mk_abs (tm_sub v_id, tm_sub b_id)
    | conv_tm (TMRef i) = #1 (lookup_vv parents (#terms) i)
  val tms = Lib.mapi (fn n => fn x => let val tm = conv_tm x in
    Array.update (tm_arr, n, tm); (tm, x) end) sh_tms
  in Vector.fromList tms end

fun theoryout_termtable (termlist : shared_term list) =
  let
    val pad_ints = String.concatWith " " o map Int.toString
    fun output_shtm shtm =
      case shtm of
          TMV (i, tyn) =>
            out ("TMV " ^ Int.toString i ^" "^Int.toString tyn)
        | TMC (x, y, z) => out ("TMC "^pad_ints [x, y, z])
        | TMAp (x, y) => out ("TMAp "^pad_ints [x, y])
        | TMAbs (x, y) => out ("TMAbs "^pad_ints [x, y])
        | TMRef i => out ("TMRef "^pad_thy_ref " " i)
    val output_shtms = PP.pr_list output_shtm [out ",", PP.add_break(1,0)]
  in
    CB [
      out ("["),
      PP.block PP.INCONSISTENT 1 (output_shtms termlist),
      out ("]")
    ]
  end

(* ----------------------------------------------------------------------
    Toplevel Encoding
   ---------------------------------------------------------------------- *)

fun share_values parent_thys ss tys tms = let
    val t = empty_uniqtable
    val (t, s_ids) = Lib.foldl_map (Lib.uncurry encode_string) (t, ss)
    val (t, ty_ids) = Lib.foldl_map type_id (t, tys)
    val (t, tm_ids) = Lib.foldl_map term_id (t, tms)
    val refs = share_all parent_thys t
    val req = get_required refs t [s_ids, ty_ids, tm_ids]
    val (sh_ids, sh_tys, sh_tms, fin_arr) = finalise_shared refs t req
    val finl = map (Lib.curry Array.sub fin_arr)
  in ((sh_ids, finl s_ids), (sh_tys, finl ty_ids), (sh_tms, finl tm_ids)) end

end; (* struct *)
