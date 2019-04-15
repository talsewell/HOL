(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables

fun get_tm tmvector i = #1 (Vector.sub (tmvector, i))

fun temp_encoded_update tmvector thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      read = get_tm tmvector o Lib.string_to_int,
      data = data
    }

type depinfo = {head : string * int, deps : (string * int list) list}

fun read_thm tmvector {name,depinfo:depinfo,tagnames,encoded_hypscon} =
    let
      val dd = (#head depinfo, #deps depinfo)
      val terms = map (get_tm tmvector) encoded_hypscon
    in
      (name, Thm.disk_thm((dd,tagnames), terms))
    end

fun load_thydata thyname path =
  let
    val raw_data = TheoryDat_Parser.read_dat_file {filename=path}
    val {thyname = fullthy as (thyname, _, _), parents, new_types,
         ...} = raw_data
    val _ = Theory.link_parents fullthy parents
    val share_parents = filter (fn "min" => false | _ => true) (map #1 parents)
      |> get_share_parents
    val idvector = build_id_vector share_parents (#shared_ids raw_data)
    fun get_id i = #1 (Vector.sub (idvector, i))
    val _ = Theory.incorporate_types thyname (map (Lib.apfst get_id) new_types)
    val tyvector = build_type_vector share_parents idvector
                                     (#shared_types raw_data)
    val tyvector1 = Vector.map #1 tyvector
    val new_consts = map (Lib.apfst get_id) (#new_consts raw_data)
    val _ = Theory.incorporate_consts thyname tyvector1 new_consts
    val tmvector = build_term_vector share_parents idvector tyvector
                                     (#shared_terms raw_data)
    val named_thms = map (read_thm tmvector) (#theorems raw_data)

    val v = {ids = idvector, types = tyvector, terms = tmvector,
             sharing_parents = share_parents}
    val _ = register_theory_vectors thyname v

    val thmdict = Redblackmap.fromList String.compare named_thms
    val _ = DB.bindl thyname
                     (map (fn (n,c) => (n,Redblackmap.find (thmdict,n),c))
                          (#classinfo raw_data))
    val _ = app (temp_encoded_update tmvector thyname) (#thydata raw_data)
  in
    thmdict
  end

end;  (* TheoryReader *)
