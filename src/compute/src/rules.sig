signature rules =
sig

local open Term in

datatype ('a,'b,'c) stack =
    Ztop
  | Zrator of { Rand : 'a, Ctx : ('a,'b,'c) stack }
  | Zrand of { Rator : 'b, Ctx : ('a,'b,'c) stack }
  | Zabs of { Bvar : 'c, Ctx : ('a,'b,'c) stack }

exception DEAD_CODE of string

(* An abstraction of the Thm.thm type *)
type thm (*= Thm.thm*)

val rhs_concl : thm -> term
val evaluate  : thm -> Thm.thm

val push_in_stk :  ('a -> 'b) ->
      'a * (thm * ((thm->thm->thm) * (thm * 'b), 'c, 'd) stack) ->
            thm * ((thm->thm->thm) * (thm * 'b), 'c, 'd) stack
val push_lam_in_stk :
      thm * ('a, 'b, thm->thm) stack ->
      thm * ('a, 'b, thm->thm) stack

val refl_thm  : term -> thm
val trans_thm : thm -> Thm.thm -> thm
val beta_thm  : thm -> thm


val lazyfy_thm    : Thm.thm -> Thm.thm
val strictify_thm : Thm.thm -> Thm.thm

end;

end;
