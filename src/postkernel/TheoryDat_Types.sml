structure TheoryDat_Types =
struct

  exception ParseError of string
  type depinfo = {head : string * int, deps : (string * int list) list}
  type encoded_thm = {name : string, depinfo : depinfo, tagnames : string list,
                      encoded_hypscon : int list}
  type thyname = (string * Arbnum.num * Arbnum.num)
  type dat_info = {thyname: thyname,
                   parents: thyname list,
                   new_types : (int * int) list,
                   shared_ids : SharingTables.shared_id list,
                   shared_types : SharingTables.shared_type list,
                   new_consts : (int * int) list,
                   shared_terms : SharingTables.shared_term list,
                   theorems : encoded_thm list,
                   classinfo : (string * DB.class) list,
                   thydata : {ty: string, data:string} list}

end
