signature SharingTables =
sig

  structure Map : Binarymap
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

  type idtable = {idsize : int,
                  idmap : (string, (int * int option))Map.dict,
                  idlist : shared_id list}
  type typetable = {tysize : int,
                    tymap : (Type.hol_type, (int * int option))Map.dict,
                    tylist : shared_type list}
  type termtable = {termsize : int,
                    termmap : (Term.term, (int * int option))Map.dict,
                    termlist : shared_term list}

  val empty_idtable : idtable
  val empty_tytable : typetable
  val empty_termtable : termtable

  (* register the id/type/term vectors of a loaded theory. *)
  type idv = (string * shared_id) Vector.vector
  type typev = (Type.hol_type * shared_type) Vector.vector
  type termv = (Term.term * shared_term) Vector.vector
  type thy_name = string
  type vectors = {ids : idv, types : typev, terms : termv,
                  parents : thy_name Vector.vector}
  val register_theory_vectors : string -> vectors -> unit

  (* set up tables to also share with previously loaded theories. *)
  val setup_shared_tables : thy_name Vector.vector -> string list ->
                            Type.hol_type list -> Term.term list ->
                            (idtable * typetable * termtable)

  val make_shared_string : string -> idtable -> (int * idtable)

  val make_shared_type : Type.hol_type -> idtable -> typetable ->
                         (int * idtable * typetable)

  val make_shared_term : Term.term -> (idtable * typetable * termtable) ->
                         int * (idtable * typetable * termtable)

  val build_id_vector : thy_name Vector.vector -> shared_id list -> idv

  val theoryout_idtable : idtable PP.pprinter

  val build_type_vector : thy_name Vector.vector -> string Vector.vector ->
                          shared_type list -> typev

  val theoryout_typetable : typetable PP.pprinter

  val build_term_vector : thy_name Vector.vector -> string Vector.vector ->
                          Type.hol_type Vector.vector -> shared_term list ->
                          termv

  val theoryout_termtable : termtable PP.pprinter

end
