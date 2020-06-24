structure typecheck_error =
struct
  datatype tcheck_error =
           ConstrainFail of Term.term * Type.hol_type * string
         | AppFail of Term.term * Term.term * string
         | OvlNoType of string * Type.hol_type
         | OvlTooMany
         | OvlFail
         | Misc of string

  local
  val last_overload_ref = ref ("", Type.bool)
  in

  type error = tcheck_error * locn.locn
  fun errorMsg tc =
    case tc of
        ConstrainFail (_,_,msg) => msg
      | AppFail (_,_,msg) => msg
      | OvlNoType(s,t) =>
        (last_overload_ref := (s, t);
            "Couldn't infer type for overloaded name "^s^
            "  (try Parse.print_last_overload_error ())")
      | OvlFail => "Overloading constraints were unsatisfiable"
      | OvlTooMany =>
          "There was more than one resolution of overloaded constants"
      | Misc s => s

  fun last_impossible_overload () = (! last_overload_ref)

  end (* local *)

  local
    open Feedback
  in
  fun mkExn (tc, loc) =
    mk_HOL_ERRloc "Preterm" "type-analysis" loc (errorMsg tc)

  end (* local *)


end (* struct *)
