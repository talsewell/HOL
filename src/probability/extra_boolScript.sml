
open HolKernel Parse bossLib boolLib combinTheory;
val _ = new_theory "extra_bool";

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val xor_def = Define `xor (x:bool) y = ~(x = y)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val RAND_THM = store_thm
  ("RAND_THM",
   ``!f x y. (x = y) ==> (f x = f y)``,
   RW_TAC std_ss []);

val K_PARTIAL = store_thm
  ("K_PARTIAL",
   ``!x. K x = \z. x``,
   RW_TAC std_ss [K_DEF]);

val SELECT_EXISTS_UNIQUE = store_thm
  ("SELECT_EXISTS_UNIQUE",
   ``!P n. $? P /\ (!m. P m ==> (m = n)) ==> ($@ P = n)``,
   RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val CONJ_EQ_IMP = store_thm
  ("CONJ_EQ_IMP",
   ``!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)

val _ = export_theory ();