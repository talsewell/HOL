signature SharingTables =
sig

  structure Map : Redblackmap
  type theory_ref = {ThyId : int, Id : int}
  datatype shared_id = IDStr of string | IDRef of theory_ref
  datatype shared_type = TYV of int
                       | TYOP of int list
                       | TYRef of theory_ref
  datatype shared_term = TMV of int * int
                       | TMC of int * int * int
                       | TMAp of int * int
                       | TMAbs of int * int
                       | TMRef of theory_ref

  (* register the id/type/term vectors of a loaded theory. *)
  type idv = (string * shared_id) Vector.vector
  type typev = (Type.hol_type * shared_type) Vector.vector
  type termv = (Term.term * shared_term) Vector.vector
  type thy_name = string
  type vectors = {ids : idv, types : typev, terms : termv,
                  sharing_parents : thy_name Vector.vector}
  val register_theory_vectors : string -> vectors -> unit
  val peek_theory_vectors : string -> vectors

  (* set up tables to also share with previously loaded theories. *)
  val share_values : thy_name list -> string list ->
                     Type.hol_type list -> Term.term list ->
                     ((shared_id list * int list) *
                      (shared_type list * int list) *
                      (shared_term list * int list))

  (* canonical order of parent/ancestor theories for sharing *)
  val get_share_parents : thy_name list -> thy_name Vector.vector

  val build_id_vector : thy_name Vector.vector -> shared_id list -> idv

  val theoryout_idtable : shared_id list PP.pprinter

  val build_type_vector : thy_name Vector.vector -> idv ->
                          shared_type list -> typev

  val theoryout_typetable : shared_type list PP.pprinter

  val build_term_vector : thy_name Vector.vector -> idv -> typev ->
                          shared_term list -> termv

  val theoryout_termtable : shared_term list PP.pprinter

  val term_compare : Term.term Lib.cmp
end
