

structure DataSet = struct

open boolSyntax pred_setSyntax

fun purge_extra ty = case TypeBase.fetch ty of
    NONE => ()
  | SOME tyinfo => TypeBase.write [TypeBasePure.put_extra [] tyinfo]

fun extra_type_consts ty nm = case TypeBase.fetch ty of
    NONE => []
  | SOME tyinfo => let
    fun matching (ThyDataSexp.List [ThyDataSexp.String n, ThyDataSexp.Term t]) =
        if n = nm then t else failwith "not matching"
      | matching _ = failwith "not matching"
  in mapfilter matching (TypeBasePure.extra_of tyinfo) end

fun get_sets tm = if is_vartype (type_of tm)
  then [mk_insert (tm, mk_empty (type_of tm))]
  else let
    val consts = extra_type_consts (type_of tm) "set_const"
    val const_apps = mapfilter (fn c => mk_icomb (c, tm)) consts
    val (leaf, compound) = partition (is_vartype o dest_set_type o type_of) const_apps
    fun eta_abs (v, tm) = eta_conv (mk_abs (v, tm))
        handle HOL_ERR _ => mk_abs (v, tm)
    fun image c = let
        val x = mk_var ("x", dest_set_type (type_of c))
        val ss = get_sets x
      in map (fn s => mk_bigunion (mk_image (eta_abs (x, s), c))) ss end
  in leaf @ List.concat (map image compound) end

fun add_set_fun ty tm = let
    val tyinfo = valOf (TypeBase.fetch ty)
    val sexp = [ThyDataSexp.List [ThyDataSexp.String "set_const", ThyDataSexp.Term tm]]
    val ext = TypeBasePure.add_extra sexp tyinfo
  in TypeBase.write [ext] end

fun mk_list_union ty ss = if null ss then mk_empty ty
    else list_mk_rbinop (curry mk_union) ss

fun type_conses_to_name ty = let
    fun f ty = if is_vartype ty then []
      else let
        val (cname, xs) = dest_type ty
      in [cname] @ List.concat (map f xs) end
  in concat (separate "_" (f ty)) end

fun build_set_fun ty ty_var nm_sfx = let
    val ax = TypeBase.axiom_of ty
    val eqs = concl ax |> strip_forall |> snd |> strip_exists |> snd |> strip_conj
    val lhss = map (lhs o snd o strip_forall) eqs
    val cons_apps = map rand lhss
    val tys = map type_of cons_apps |> HOLset.fromList Type.compare |> HOLset.listItems
    val fs = map (fn ty => (ty, mk_var (type_conses_to_name ty ^ "_set" ^ nm_sfx,
            ty --> ty_var --> bool))) tys
    fun get_sets2 v = case total (assoc (type_of v)) fs of
        SOME f => [mk_comb (f, v)]
      | NONE => get_sets v
    fun get_set_union vs = List.concat (map get_sets2 vs)
        |> filter (fn t => dest_set_type (type_of t) = ty_var)
        |> mk_list_union ty_var
    fun eq_of_app t = mk_eq (hd (get_sets2 t), get_set_union (snd (strip_comb t)))
    val eqs = map eq_of_app cons_apps
    val fs_nm = map (fst o dest_var o snd) fs |> separate "_" |> concat
    val def = new_recursive_definition {name = fs_nm ^ "_def",
        rec_axiom = ax, def = list_mk_conj eqs}
    val tms = concl def |> strip_conj
        |> map (fst o strip_comb o lhs o snd o strip_forall)
        |> HOLset.fromList Term.compare |> HOLset.listItems
  in (tms, def) end

fun build_set_funs ty = let
    val (ty_nm, vars) = dest_type ty
    fun mk_nm i = if length vars > 1 then Int.toString (i + 1) else ""
  in mapi (fn i => fn ty_var => build_set_fun ty ty_var (mk_nm i)) vars end

fun ensure_set_funs ty = if null (extra_type_consts ty "set_const")
  then List.app (List.app (add_set_fun ty) o fst) (build_set_funs ty)
  else ()

end

(* Tests. FIXME: move these to a selftest.sml or similar. *)

(* self recursion *)
Datatype:
  test1 = Leaf 'a | Split test1 test1
End

(* use of existing datatypes *)
Datatype:
  test2 = Test2 'a (('b # 'c) list) ('b list)
End

(* mutual recursion *)
Datatype:
  test3_a = Test3_a 'a 'a 'b test3_b
;
  test3_b = Test3_b_None | Test3_b_x test3_a
End

(* recursion via an existing datatype *)
Datatype:
  test4 = Leaf_4 'a | Split_4 (test4 list)
End


build_set_funs ``: 'a test1``;
ensure_set_funs ``: 'a test1``;

ensure_set_funs ``: 'a list``;
ensure_set_funs ``: 'a # 'b``;

build_set_funs ``: ('a, 'b, 'c) test2``;
ensure_set_funs ``: ('a, 'b, 'c) test2``;

build_set_funs ``: ('a, 'b) test3_a``;
ensure_set_funs ``: ('a, 'b) test3_a``;

build_set_funs ``: 'a test4``;
ensure_set_funs ``: 'a test4``;

(* Known issue: there are now two constructions of the set of "'a" in a
   "('a test4) list" tree/forest. This might not be as important as the
   equivalent issue about size constants. *)
get_sets ``x : 'a test4 list``;
Theorem list_test4_set_eq:
  (! x. (x = y \/ T) ==> test4_set x = test4_set x) /\
  (! x. (x = [y] \/ T) ==> list_test4_set x = BIGUNION (IMAGE test4_set (list_set x)))
Proof
  ho_match_mp_tac (fetch "-" "test4_induction")
  \\ simp [fetch "-" "list_test4_set_test4_set_def", fetch "-" "list_set_def"]
QED

(* Second problem: users may want to prefer to use standard list-set constant,
   defined in a totally different way. *)
Theorem list_set_eq_set:
  !x. list_set x = LIST_TO_SET x
Proof
  Induct \\ simp [fetch "-" "list_set_def", GSYM pred_setTheory.INSERT_SING_UNION]
QED


