(* ------------------------------------------------------------------------- *)
(* Some miscellaneous tools that come in useful in the probability           *)
(* development.                                                              *)
(* ------------------------------------------------------------------------- *)

structure probExtraTools :> probExtraTools = 
struct

open HolKernel Parse basicHol90Lib;
open Psyntax bossLib pred_setTheory probUtil probExtraTheory;

infixr 0 ++ || ORELSEC ## THENC;
infix 1 >>;
nonfix THEN ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Error handling.                                                           *)
(* ------------------------------------------------------------------------- *)

fun ERROR f s
  = Exception.HOL_ERR{origin_structure = "probExtraTools",
		      origin_function = f, message = s};
fun assert_false f s = raise ERROR f s;
fun assert b f s = if b then () else assert_false f s;

(* ------------------------------------------------------------------------- *)
(* Set simplification.                                                       *)
(* ------------------------------------------------------------------------- *)

val pred_set_rewrs
  = [IN_COMPL, IN_DIFF, IN_UNIV, IN_EMPTY, IN_UNION,
     IN_INTER, SET_EQ_EXT, SUBSET_DEF, IN_IMAGE, INTER_EMPTY,
     INTER_UNIV, UNION_EMPTY, UNION_UNIV, GSPECIFICATION];

val pred_set_ss = simpLib.++(std_ss, simpLib.SIMPSET {
  ac = [],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = pred_set_rewrs,
  congs = []});

fun PRED_SET_TAC ths
  = REPEAT (POP_ASSUM MP_TAC)
    ++ RW_TAC pred_set_ss ths
    ++ REPEAT (POP_ASSUM MP_TAC)
    ++ RW_TAC std_ss (SPECIFICATION::ths);

fun dest_binop tm
  = let val (tm', res2) = dest_comb tm
	val (tm'', res1) = dest_comb tm'
    in (dest_const tm'', (res1, res2))
    end;

fun IN_LAMBDA_CONV ty tm
  = let val ((c_n, c_ty), (a1, a2)) = dest_binop tm
    in if c_n = "IN" andalso is_abs a2 andalso type_of a1 = ty then
         (REWR_CONV SPECIFICATION THENC BETA_CONV) tm
       else assert_false "IN_LAMBDA_CONV" "not the right form"
    end;

fun pset_ss_ty ty = simpLib.++(std_ss, simpLib.SIMPSET {
  ac = [],
  convs = [{conv = (K o K) (IN_LAMBDA_CONV ty),
	    key = SOME ([], ``(x:'a) IN y``),
	    name = "IN_LAMBDA_CONV", trace = 2}],
  dprocs = [],
  filter = NONE,
  rewrs = map (INST_TYPE [(ty, ``:'a``)]) (GSYM SPECIFICATION::pred_set_rewrs),
  congs = []});

fun PSET_TAC_ty ty ths
  = REPEAT (POP_ASSUM MP_TAC)
    ++ RW_TAC (pset_ss_ty ty) ths
    ++ REPEAT (POP_ASSUM MP_TAC)
    ++ RW_TAC std_ss (INST_TYPE [(ty, ``:'a``)] SPECIFICATION::ths);

val pset_ss = pset_ss_ty ``:num->bool``;
val PSET_TAC = PSET_TAC_ty ``:num->bool``;

end;
