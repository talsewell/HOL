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
                parents : thy_name Vector.vector}
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

fun lookup_vv (parents : vv) f (i : theory_ref) =
    Vector.sub (f (Vector.sub (parents, #ThyId i)), #Id i)

(* ----------------------------------------------------------------------
    IDs (strings)
   ---------------------------------------------------------------------- *)

type idtable = {idsize : int,
                idmap : (string, (int * int option)) Map.dict,
                idlist : shared_id list}
type idv = (string * shared_id) Vector.vector

fun make_shared_string (s : string) (idtable : idtable) =
    case Map.peek(#idmap idtable, s) of
      SOME (i, NONE) => (i, idtable)
    | v => let
        val {idsize, idmap, idlist} = idtable
        val sh_s = case v of
            SOME (i, SOME thy_id) => IDRef {ThyId = thy_id, Id = i}
          | _ => IDStr s
      in
        (idsize, {idsize = idsize + 1,
                  idmap = Map.insert(idmap, s, (idsize, NONE)),
                  idlist = sh_s :: idlist})
      end

val empty_idtable : idtable = {idsize = 0,
                               idmap = Map.mkDict String.compare,
                               idlist = []}

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

fun theoryout_idtable (idtable : idtable) = let
  val idlist = List.rev (#idlist idtable)
  fun print_id (IDStr s) = out ("IDStr " ^ Lib.mlquote s)
    | print_id (IDRef i) = out ("IDRef " ^ pad_thy_ref " " i)
  val print_ids = PP.pr_list print_id [PP.add_string ",", PP.add_break(1,0)]
in
  CB [out "[",
      PP.block PP.INCONSISTENT 1 (print_ids idlist),
      out "]"
  ]
end

exception NoUpdate

fun update_id_map f s (tab : idtable) = let
    val {idsize, idmap, idlist} = tab
  in
    {idsize = idsize, idmap = Map.update (idmap, s, f), idlist = idlist}
      handle NoUpdate => tab
  end

fun add_thy_id thy_id (idn, s) (tab : idtable)
    = update_id_map (fn NONE => (idn, SOME thy_id) | SOME v => raise NoUpdate)
        s tab

fun scan_parent_wrapper (v : 'a Vector.vector)
                        (f : bool Array.array * int * 'a * 'b -> bool * 'b)
                        (acc : 'b)
  = let
    val arr = Array.array (Vector.length v, false)
    fun g (i, x, acc) = let
        val (useful, acc) = f (arr, i, x, acc)
        val _ = if useful then Array.update (arr, i, true) else ()
      in acc end
    val acc = Vector.foldri g acc v
  in (arr, acc) end

fun if_upd b f x = (b, if b then f x else x)

fun share_all () = Option.isSome (Portable.getEnv "HOL4_SHARE_NO_SCAN")

fun share_parent_ids thy_id arrs ss (idv : idv) tab = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    val add = case thy_id of NONE => Lib.K Lib.I | SOME i => add_thy_id i
    val all = share_all ()
    fun f (_, _, (_, IDRef r), tab) = (arrs_ref r, tab)
      | f (_, i, (s, IDStr _), tab) = if_upd (all orelse Set.member (ss, s))
        (add (i, s)) tab
  in scan_parent_wrapper idv f tab end

(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

type typetable = {tysize : int,
                  tymap : (hol_type, (int * int option)) Map.dict,
                  tylist : shared_type list}
type typev = (Type.hol_type * shared_type) Vector.vector

fun add_typetable ty sh_ty ({tysize, tymap, tylist} : typetable)
  = {tysize = tysize + 1,
     tymap = Map.insert(tymap, ty, (tysize, NONE)),
     tylist = sh_ty :: tylist} : typetable

fun make_shared_type ty idtable table =
    case Map.peek(#tymap table, ty) of
      SOME (i, NONE) => (i, idtable, table)
    | SOME (i, SOME thy_id) => (#tysize table, idtable,
        add_typetable ty (TYRef {ThyId = thy_id, Id = i}) table)
    | NONE => let
      in
        if is_vartype ty then let
            val (nm_id, idtable) = make_shared_string (dest_vartype ty) idtable
          in
            (#tysize table, idtable, add_typetable ty (TYV nm_id) table)
	  end
        else let
            val {Thy, Tyop, Args} = dest_thy_type ty
            val (thy_id, idtable1) = make_shared_string Thy idtable
            val (op_id, idtable2) = make_shared_string Tyop idtable1
            fun foldthis (tyarg, (results, idtable, table)) = let
              val (result, idtable', table') =
                  make_shared_type tyarg idtable table
            in
              (result::results, idtable', table')
            end
            val (newargs, idtable', table') =
                List.foldr foldthis ([], idtable2, table) Args
            val sh_ty = TYOP (thy_id :: op_id :: newargs)
          in
            (#tysize table', idtable', add_typetable ty sh_ty table')
          end
      end

val empty_tytable : typetable =
    {tysize = 0, tymap = Map.mkDict Type.compare, tylist = [] }

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

fun theoryout_typetable (tytable : typetable) = let
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
    PP.block PP.INCONSISTENT 1 (output_shtypes (List.rev (#tylist tytable))),
    out "]"
  ]
end

fun update_ty_map f ty (tab : typetable) = let
    val {tysize, tymap, tylist} = tab
  in
    {tysize = tysize, tymap = Map.update (tymap, ty, f), tylist = tylist}
      handle NoUpdate => tab
  end

fun add_thy_ty thy_id (idn, ty) (tab : typetable)
    = update_ty_map (fn NONE => (idn, SOME thy_id) | SOME v => raise NoUpdate)
        ty tab

fun share_parent_tys thy_id id_arr arrs tys (typev : typev) tab = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    val add = case thy_id of NONE => Lib.K Lib.I | SOME i => add_thy_ty i
    val all = share_all ()
    fun ifu rs idn ty = if_upd (all orelse
        (List.all Array.sub rs andalso Set.member (tys, ty))) (add (idn, ty))
    fun f (_, _, (_, TYRef r), tab) = (arrs_ref r, tab)
      | f (_, idn, (ty, TYV i), tab) = ifu [(id_arr, i)] idn ty tab
      | f (arr, idn, (ty, TYOP (thy_id :: nm_id :: args)), tab) = ifu
            ([(id_arr, thy_id), (id_arr, nm_id)] @ map (Lib.pair arr) args)
            idn ty tab
      | f (_, _, (_, TYOP _), _) = raise ERR "scan" "TYOP: not enough arguments"
  in scan_parent_wrapper typev f tab end

fun add_types [] (tyset, ss) = (tyset, ss)
  | add_types (typ :: typs) (tyset, ss) = if is_vartype typ
  then add_types typs (Set.add (tyset, typ), Set.add (ss, dest_vartype typ))
  else let
    val {Args, Thy, Tyop} = dest_thy_type typ
    val ss = Set.add (Set.add (ss, Thy), Tyop)
  in add_types (Args @ typs) (Set.add (tyset, typ), ss) end

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

(* sort terms by equality. Term.compare sorts alpha-equivalent terms equal. *)
fun term_compare (t1, t2) = if is_abs t1 andalso is_abs t2
    then Lib.pair_compare (term_compare, term_compare) (dest_abs t1, dest_abs t2)
    else if is_comb t1 andalso is_comb t2
    then Lib.pair_compare (term_compare, term_compare) (dest_comb t1, dest_comb t2)
    else Term.compare (t1, t2)

type termtable = {termsize : int,
                  termmap : (term, (int * int option)) Map.dict,
                  termlist : shared_term list}

val empty_termtable : termtable =
    {termsize = 0, termmap = Map.mkDict term_compare, termlist = [] }

fun add_termtable tm sh_tm {termsize, termmap, termlist} =
  ({termsize = termsize + 1,
    termmap = Map.insert(termmap, tm, (termsize, NONE)),
    termlist = sh_tm :: termlist})

fun make_shared_term tm (tables as (idtable,tytable,tmtable)) =
    case Map.peek(#termmap tmtable, tm) of
      SOME (i, NONE) => (i, tables)
    | SOME (i, SOME thy_id) => (#termsize tmtable, (idtable, tytable,
        add_termtable tm (TMRef {ThyId = thy_id, Id = i}) tmtable))
    | NONE => let
      in
        if is_var tm then let
            val (s, ty) = dest_var tm
            val (ty_i, idtable, tytable) = make_shared_type ty idtable tytable
            val (s_i, idtable) = make_shared_string s idtable
          in
            (#termsize tmtable, (idtable, tytable,
                                 add_termtable tm (TMV (s_i, ty_i)) tmtable))
          end
        else if is_const tm then let
            val {Thy,Name,Ty} = dest_thy_const tm
            val (thy_id, idtable) = make_shared_string Thy idtable
            val (nm_id, idtable) = make_shared_string Name idtable
            val (ty_id, idtable, tytable) =
                make_shared_type Ty idtable tytable
            val sh_tm = TMC (thy_id, nm_id, ty_id)
          in
            (#termsize tmtable, (idtable, tytable,
                                 add_termtable tm sh_tm tmtable))
          end
        else if is_comb tm then let
            val (f, x) = dest_comb tm
            val (f_i, tables) = make_shared_term f tables
            val (x_i, tables) = make_shared_term x tables
            val (idtable, tytable, tmtable) = tables
          in
            (#termsize tmtable, (idtable, tytable,
                                 add_termtable tm (TMAp (f_i, x_i)) tmtable))
          end
        else  (* must be an abstraction *) let
            val (v, body) = dest_abs tm
            val (v_i, tables) = make_shared_term v tables
            val (body_i, tables) = make_shared_term body tables
            val (idtable, tytable, tmtable) = tables
          in
            (#termsize tmtable,
             (idtable, tytable,
              add_termtable tm (TMAbs (v_i, body_i)) tmtable))
          end
      end

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

fun theoryout_termtable (tmtable: termtable) =
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
      PP.block PP.INCONSISTENT 1 (output_shtms (List.rev (#termlist tmtable))),
      out ("]")
    ]
  end

fun update_tm_map f tm (tab : termtable) = let
    val {termsize, termmap, termlist} = tab
  in
    {termsize = termsize, termmap = Map.update (termmap, tm, f),
     termlist = termlist}
    handle NoUpdate => tab
  end

fun add_thy_tm thy_id (idn, tm) (tab : termtable)
    = update_tm_map (fn NONE => (idn, SOME thy_id) | SOME v => raise NoUpdate)
        tm tab

fun share_parent_tms thy_id id_arr ty_arr arrs tms (termv : termv) tab = let
    fun arrs_ref r = Array.sub (Vector.sub (arrs, #ThyId r), #Id r)
    val add = case thy_id of NONE => Lib.K Lib.I | SOME i => add_thy_tm i
    val all = share_all ()
    fun ifu rs idn tm = if_upd (all orelse
        (List.all Array.sub rs andalso Set.member (tms, tm))) (add (idn, tm))
    fun f (_, _, (_, TMRef r), tab) = (arrs_ref r, tab)
      | f (_, idn, (tm, TMV (i, j)), tab) = ifu [(id_arr, i), (ty_arr, j)]
                idn tm tab
      | f (_, idn, (tm, TMC (i, j, k)), tab) = ifu [(id_arr, i), (id_arr, j),
                (ty_arr, k)] idn tm tab
      | f (arr, idn, (tm, TMAp (i, j)), tab) = ifu [(arr, i), (arr, j)]
                idn tm tab
      | f (arr, idn, (tm, TMAbs (i, j)), tab) = ifu [(arr, i), (arr, j)]
                idn tm tab
  in scan_parent_wrapper termv f tab end

fun add_terms [] (tmset, tyset, ss) = (tmset, tyset, ss)
  | add_terms (tm :: tms) (tmset, tyset, ss) = if is_var tm
  then let
    val (nm, ty) = dest_var tm
    val (tyset, ss) = add_types [ty] (tyset, ss)
  in add_terms tms (Set.add (tmset, tm), tyset, ss) end
  else if is_const tm
  then let
    val {Name, Thy, Ty} = dest_thy_const tm
    val ss = Set.add (Set.add (ss, Thy), Name)
    val (tyset, ss) = add_types [Ty] (tyset, ss)
  in add_terms tms (Set.add (tmset, tm), tyset, ss) end
  else let
    val (x, y) = if is_comb tm then dest_comb tm else dest_abs tm
  in add_terms (x :: y :: tms) (tmset, tyset, ss) end

fun vec_to_list v = Vector.foldr (op ::) [] v

fun setup_shared_tables parent_thys ss tys tms = let
    val ss = Set.fromList String.compare ss
    val (tyset, ss) = add_types tys (Set.empty Type.compare, ss)
    val (tmset, tyset, ss) = add_terms tms (Set.empty term_compare, tyset, ss)
    val parents = vec_to_list parent_thys
    val thy_ids = Map.fromList String.compare
        (Lib.mapi (fn i => fn s => (s, i)) parents)
    fun doit ((arrs, tabs), (thy_id : thy_name)) = case Map.peek (arrs, thy_id) of
        SOME arr_tup => ((arrs, tabs), arr_tup)
      | NONE => let
        val vectors = lookup_vectors thy_id
        val ((arrs, tabs), arr_tup_list)
            = Lib.foldl_map doit ((arrs, tabs), vec_to_list (#parents vectors))
        val thy_id_n = Map.peek (thy_ids, thy_id)
        val (id_tab, ty_tab, tm_tab) = tabs
        val (id_arr, id_tab) = share_parent_ids thy_id_n
            (Vector.fromList (map #1 arr_tup_list)) ss (#ids vectors) id_tab
        val (ty_arr, ty_tab) = share_parent_tys thy_id_n id_arr
            (Vector.fromList (map #2 arr_tup_list)) tyset (#types vectors)
            ty_tab
        val (tm_arr, tm_tab) = share_parent_tms thy_id_n id_arr ty_arr
            (Vector.fromList (map #3 arr_tup_list)) tmset (#terms vectors)
            tm_tab
        val arr_tup = (id_arr, ty_arr, tm_arr)
        val arrs = Map.insert (arrs, thy_id, arr_tup)
      in ((arrs, (id_tab, ty_tab, tm_tab)), arr_tup) end
    val tabs = (empty_idtable, empty_tytable, empty_termtable)
    val arrs = Map.mkDict String.compare
    val ((_, tabs), _) = Lib.foldl_map doit ((arrs, tabs), parents)
    val tabs = List.foldl (fn (tm, tabs) => #2 (make_shared_term tm tabs))
        tabs tms
    val (idtable, tytable, termtable) = tabs
    val (idtable, tytable) = List.foldl (fn (ty, (idtable, tytable)) => let
        val (_, idtable, tytable) = make_shared_type ty idtable tytable
      in (idtable, tytable) end) (idtable, tytable) tys
    val idtable = List.foldl (fn (s, tab) => #2 (make_shared_string s tab))
        idtable (Set.listItems ss)
  in (idtable, tytable, termtable) end

end; (* struct *)
