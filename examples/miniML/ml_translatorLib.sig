signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm   (* e.g. try translate listTheory.MAP *)
    val hol2deep   : term -> thm  (* e.g. try hol2deep ``\x.x`` *)

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm * thm
    val mltDefine  : string -> term quotation -> tactic -> thm * thm

    (* interface for teaching the translator about new types *)

    val add_type_inv   : term -> unit
    val store_eval_thm : thm -> thm
    val store_eq_thm   : thm -> thm

end
