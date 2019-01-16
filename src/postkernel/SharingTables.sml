structure SharingTables :> SharingTables =
struct

open Term Type

local open Feedback
in val ERR = mk_HOL_ERR "SharingTables" end

structure Map = Binarymap

(* references into string/type/term vectors across theories. *)
type theory_ref = {ThyId : int, Id : int}

(* ----------------------------------------------------------------------
    Per-Theory stored vectors
   ---------------------------------------------------------------------- *)
type vectors = {ids : string Vector.vector,
                types : Type.hol_type Vector.vector,
                terms : Term.term Vector.vector}
type vv = vectors Vector.vector

val thy_vectors = ref (Map.mkDict String.compare : (string, vectors) Map.dict)
fun register_theory_vectors thy vs
  = (thy_vectors := Map.insert (! thy_vectors, thy, vs))

type thy_name = string
fun mk_vv (parents : thy_name Vector.vector) : vv = let
    val tv = ! thy_vectors
    fun find s = Map.find (tv, s) handle NotFound => raise ERR "mk_vv" s
  in Vector.map find parents end

fun lookup_vv (parents : vv) f (i : theory_ref) =
    Vector.sub (f (Vector.sub (parents, #ThyId i)), #Id i)

(* ----------------------------------------------------------------------
    IDs (strings)
   ---------------------------------------------------------------------- *)

datatype shared_id = IDStr of string | IDRef of theory_ref
type idtable = {idsize : int,
                idmap : (string, (int * int option)) Map.dict,
                idlist : shared_id list}

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
    | conv_id (IDRef i) = lookup_vv parents (#ids) i
  in Vector.fromList (map conv_id sh_ids) end

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

fun add_thy_id thy_id (idn, s, tab : idtable) = let
    val {idsize, idmap, idlist} = tab
    val sh_id = (idn, SOME thy_id)
  in
    {idsize = idsize, idmap = Map.insert (idmap, s, sh_id), idlist = idlist}
  end

fun add_thy_ids thy_id idv idtable = Vector.foldri (add_thy_id thy_id)
    idtable idv

(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

datatype shared_type = TYV of string
                     | TYOP of int list
                     | TYRef of theory_ref

type typetable = {tysize : int,
                  tymap : (hol_type, (int * int option)) Map.dict,
                  tylist : shared_type list}

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
        if is_vartype ty then (#tysize table, idtable,
            add_typetable ty (TYV (dest_vartype ty)) table)
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
  fun conv_ty (TYV s) = Type.mk_vartype s
    | conv_ty (TYOP (thy_id :: nm_id :: args)) = let
        val thy = Vector.sub (idv, thy_id)
        val nm = Vector.sub (idv, nm_id)
        val arg_tys = map (Lib.curry Array.sub ty_arr) args
      in Type.mk_thy_type {Thy = thy, Tyop = nm, Args = arg_tys} end
    | conv_ty (TYOP _) = raise ERR "conv_ty" "TYOP: not enough arguments"
    | conv_ty (TYRef i) = lookup_vv parents (#types) i
  val tys = Lib.mapi (fn n => fn x => let val ty = conv_ty x in
    Array.update (ty_arr, n, ty); ty end) sh_tys
  in Vector.fromList tys end

fun theoryout_typetable (tytable : typetable) = let
  fun output_shtype shty =
      case shty of
        TYV s => out ("TYV "^ Lib.mlquote s)
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

fun add_thy_ty thy_id (idn, ty, tab : typetable) = let
    val {tysize, tymap, tylist} = tab
    val sh_id = (idn, SOME thy_id)
  in
    {tysize = tysize, tymap = Map.insert (tymap, ty, sh_id), tylist = tylist}
  end

fun add_thy_tys thy_id tyv tab = Vector.foldri (add_thy_ty thy_id) tab tyv

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

datatype shared_term = TMV of string * int
                     | TMC of int * int * int
                     | TMAp of int * int
                     | TMAbs of int * int
                     | TMRef of theory_ref

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
            val (ty_i, idtable, tytable) =
                make_shared_type ty idtable tytable
          in
            (#termsize tmtable, (idtable, tytable,
                                 add_termtable tm (TMV (s, ty_i)) tmtable))
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
  fun conv_tm (TMV (s, ty_id)) = mk_var (s, Vector.sub (tyv, ty_id))
    | conv_tm (TMC (thy_id, nm_id, ty_id)) = let
        val thy = Vector.sub (idv, thy_id)
        val nm = Vector.sub (idv, nm_id)
        val ty = Vector.sub (tyv, ty_id)
      in mk_thy_const {Name = nm, Thy = thy, Ty = ty} end
    | conv_tm (TMAp (f_id, x_id)) = mk_comb (tm_sub f_id, tm_sub x_id)
    | conv_tm (TMAbs (v_id, b_id)) = mk_abs (tm_sub v_id, tm_sub b_id)
    | conv_tm (TMRef i) = lookup_vv parents (#terms) i
  val tms = Lib.mapi (fn n => fn x => let val tm = conv_tm x in
    Array.update (tm_arr, n, tm); tm end) sh_tms
  in Vector.fromList tms end

fun theoryout_termtable (tmtable: termtable) =
  let
    val pad_ints = String.concatWith " " o map Int.toString
    fun output_shtm shtm =
      case shtm of
          TMV (s, tyn) =>
            out ("TMV " ^ Lib.mlquote s ^" "^Int.toString tyn)
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

fun add_thy_tm thy_id (idn, tm, tab : termtable) = let
    val {termsize, termmap, termlist} = tab
    val sh_id = (idn, SOME thy_id)
  in
    {termsize = termsize, termmap = Map.insert (termmap, tm, sh_id),
     termlist = termlist}
  end

fun add_thy_tms thy_id tmv tab = Vector.foldri (add_thy_tm thy_id) tab tmv

fun shared_tables parent_thys = let
  val parents = mk_vv parent_thys
  val ids = Vector.foldri (fn (i, vs, ids) => add_thy_ids i (#ids vs) ids)
    empty_idtable parents
  val tys = Vector.foldri (fn (i, vs, tys) => add_thy_tys i (#types vs) tys)
    empty_tytable parents
  val terms = Vector.foldri (fn (i, vs, tms) => add_thy_tms i (#terms vs) tms)
    empty_termtable parents
  in (ids, tys, terms) end

end; (* struct *)
