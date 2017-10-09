(* ========================================================================== *)
(* FILE          : TraceScript.sml                                            *)
(* DESCRIPTION   : Reach, STEP, and TRACE relations                           *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open relationTheory arithmeticTheory listTheory;
open CCSLib CCSTheory StrongEQTheory WeakEQTheory;

val _ = new_theory "Trace";

(******************************************************************************)
(*                                                                            *)
(*             The reachability relation (and finite-state CCS)               *)
(*                                                                            *)
(******************************************************************************)

val Reach_defn = ``(\E E'. ?u. TRANS E u E')``
val Reach_def = Define `Reach = RTC ^Reach_defn`;

val Reach_one = store_thm ((* NEW *)
   "Reach_one", ``!E E'. (?u. TRANS E u E') ==> Reach E E'``,
    REWRITE_TAC [Reach_def]
 >> REPEAT STRIP_TAC
 >> MATCH_MP_TAC RTC_SINGLE
 >> BETA_TAC
 >> Q.EXISTS_TAC `u`
 >> ASM_REWRITE_TAC []);

val Reach_self = store_thm ((* NEW *)
   "Reach_self", ``!E. Reach E E``,
    REWRITE_TAC [Reach_def, RTC_REFL]);

local
    val trans = (REWRITE_RULE [GSYM Reach_def]) o BETA_RULE o (ISPEC Reach_defn);
in
val Reach_trans = save_thm ((* NEW *)
   "Reach_trans", trans (REWRITE_RULE [transitive_def] RTC_TRANSITIVE));

val Reach_ind = save_thm ((* NEW *)
   "Reach_ind", trans RTC_INDUCT);

val Reach_strongind = save_thm ((* NEW *)
   "Reach_strongind", trans RTC_STRONG_INDUCT);

val Reach_ind_right = save_thm ((* NEW *)
   "Reach_ind_right", trans RTC_INDUCT_RIGHT1);

val Reach_strongind_right = save_thm ((* NEW *)
   "Reach_strongind_right", trans RTC_STRONG_INDUCT_RIGHT1);

val Reach_cases1 = save_thm ((* NEW *)
   "Reach_cases1", trans RTC_CASES1);

val Reach_cases2 = save_thm ((* NEW *)
   "Reach_cases2", trans RTC_CASES2);
end;

(* Define the set of states reachable from any CCS process *)
val NODES_def = Define `
    NODES (p :('a, 'b) CCS) = { q | Reach p q }`;

(* Finite-state CCS *)
val finite_state_def = Define `
    finite_state (p :('a, 'b) CCS) = FINITE (NODES p)`;

val Reach_NODES = store_thm (
   "Reach_NODES", ``!p q. Reach p q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> SRW_TAC [] [NODES_def]);

val SELF_NODES = store_thm (
   "SELF_NODES", ``!p. p IN (NODES p)``,
    REPEAT STRIP_TAC
 >> SRW_TAC [] [NODES_def]
 >> REWRITE_TAC [Reach_self]);

val MORE_NODES = store_thm (
   "MORE_NODES", ``!p q q'. q IN (NODES p) /\ Reach q q' ==> q' IN (NODES p)``,
    REPEAT GEN_TAC
 >> SRW_TAC [] [NODES_def]
 >> IMP_RES_TAC Reach_trans);

val TRANS_IN_NODES = store_thm (
   "TRANS_IN_NODES", ``!p q u. TRANS p u q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [NODES_def]
 >> SRW_TAC [] []
 >> MATCH_MP_TAC Reach_one
 >> Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC []);

val EPS_Reach = store_thm ((* NEW *)
   "EPS_Reach", ``!p q. EPS p q ==> Reach p q``,
    HO_MATCH_MP_TAC EPS_ind_right
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >- REWRITE_TAC [Reach_self]
 >> IMP_RES_TAC Reach_one
 >> IMP_RES_TAC Reach_trans);

val EPS_IN_NODES = store_thm ((* NEW *)
   "EPS_IN_NODES", ``!p q. EPS p q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC Reach_NODES
 >> IMP_RES_TAC EPS_Reach);

val WEAK_TRANS_Reach = store_thm ((* NEW *)
   "WEAK_TRANS_Reach", ``!p q u. WEAK_TRANS p u q ==> Reach p q``,
    REWRITE_TAC [WEAK_TRANS]
 >> REPEAT STRIP_TAC
 >> IMP_RES_TAC EPS_Reach
 >> IMP_RES_TAC Reach_one
 >> IMP_RES_TAC Reach_trans);

val WEAK_TRANS_IN_NODES = store_thm ((* NEW *)
   "WEAK_TRANS_IN_NODES", ``!p q u. WEAK_TRANS p u q ==> q IN (NODES p)``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC Reach_NODES
 >> IMP_RES_TAC WEAK_TRANS_Reach);

(******************************************************************************)
(*                                                                            *)
(*            N-steps transition of CCS, based on arithmetic.NRC              *)
(*                                                                            *)
(******************************************************************************)

val STEP_defn = ``\E E'. ?u. TRANS E u E'``;
val STEP_def = Define `STEP P n Q = NRC ^STEP_defn n P Q`;
val _ = overload_on ("Trans", ``STEP``);

local
    val trans = (REWRITE_RULE [GSYM STEP_def]) o BETA_RULE o (ISPEC STEP_defn);
in
(* |- ∀x y. x --0--> y ⇔ (x = y) *)
val STEP0 = save_thm ("STEP0", trans NRC_0);

(* |- x --1--> y ⇔ ∃u. x --u--> y *)
val STEP1 = save_thm ("STEP1", trans (Q.GEN `R` NRC_1));

(* |- ∀n x y. x --SUC n--> y ⇔ ∃z. (∃u. x --u--> z) ∧ z --n--> y *)
val STEP_SUC = save_thm (
   "STEP_SUC", trans (CONJUNCT2 NRC));

(* |- ∀n x y. x --SUC n--> y ⇔ ∃z. x --n--> z ∧ ∃u. z --u--> y *)
val STEP_SUC_LEFT = save_thm (
   "STEP_SUC_LEFT", trans (Q.GENL [`R`, `n`, `x`, `y`] NRC_SUC_RECURSE_LEFT));

(* |- ∀m n x z. x --m + n--> z ⇒ ∃y. x --m--> y ∧ y --n--> z *)
val STEP_ADD_E = save_thm (
   "STEP_ADD_E", trans (Q.GEN `R` NRC_ADD_E));

(* |- ∀m n x z. x --m + n--> z ⇔ ∃y. x --m--> y ∧ y --n--> z *)
val STEP_ADD_EQN = save_thm (
   "STEP_ADD_EQN", trans (Q.GENL [`R`, `m`, `n`, `x`, `z`] NRC_ADD_EQN));

(* |- ∀m n x y z. x --m--> y ∧ y --n--> z ⇒ x --m + n--> z *)
val STEP_ADD_I = save_thm (
   "STEP_ADD_I", trans (Q.GEN `R` NRC_ADD_I));
end;

val EPS_AND_STEP = store_thm (
   "EPS_AND_STEP", ``!E E'. EPS E E' ==> ?n. STEP E n E'``,
    HO_MATCH_MP_TAC EPS_ind
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `0` >> PROVE_TAC [STEP0],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `SUC n` \\
      ONCE_REWRITE_TAC [STEP_SUC] \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `tau` >> ASM_REWRITE_TAC [] ]);

val WEAK_TRANS_AND_STEP = store_thm (
   "WEAK_TRANS_AND_STEP", ``!E u E'. WEAK_TRANS E u E' ==> ?n. STEP E n E'``,
    REWRITE_TAC [WEAK_TRANS]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EPS_AND_STEP
 >> Q.EXISTS_TAC `n' + 1 + n`
 >> REWRITE_TAC [STEP_ADD_EQN]
 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC []
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []
 >> ONCE_REWRITE_TAC [STEP1]
 >> Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*               Reflexive Transitive Closure with a List (LRTC)              *)
(*                                                                            *)
(******************************************************************************)

val LRTC_DEF = new_definition ("LRTC_DEF",
  ``LRTC (R :'a -> 'b -> 'a -> bool) a l b =
      !P. (!x. P x [] x) /\
          (!x h y t z. R x h y /\ P y t z ==> P x (h :: t) z) ==> P a l b``);

val LRTC_INDUCT = store_thm (
   "LRTC_INDUCT",
  ``!R P. (!x. P x [] x) /\ (!x h y t z. R x h y /\ P y t z ==> P x (h :: t) z) ==>
          (!x l (y :'a). LRTC R x l y ==> P x l y)``,
    REWRITE_TAC [LRTC_DEF] >> PROVE_TAC []);

val LRTC_RULES = store_thm (
   "LRTC_RULES",
  ``!R. (!x. LRTC R (x :'a) [] x) /\
	(!x h y t z. R x h y /\ LRTC R y t z ==> LRTC R x (h :: t) z)``,
    REWRITE_TAC [LRTC_DEF] >> PROVE_TAC []);

val LRTC_REFL = store_thm (
   "LRTC_REFL", ``!R. LRTC R x [] x``,
    REWRITE_TAC [LRTC_RULES]);

val LRTC_SINGLE = store_thm (
   "LRTC_SINGLE",
  ``!R x t y. R x t y ==> LRTC R x [t] y``,
    rpt STRIP_TAC
 >> `~NULL [t]` by PROVE_TAC [NULL_DEF]
 >> POP_ASSUM (ASSUME_TAC o SYM o (MATCH_MP (Q.SPEC `[t]` CONS)))
 >> ONCE_ASM_REWRITE_TAC []
 >> MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES))
 >> PURE_ONCE_REWRITE_TAC [HD, TL]
 >> Q.EXISTS_TAC `y`
 >> ASM_REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)]);

val LRTC_STRONG_INDUCT = store_thm (
   "LRTC_STRONG_INDUCT",
  ``!R P. (!x. P x [] x) /\
	  (!x h y t z. R x h y /\ LRTC R y t z /\ P y t z ==> P x (h :: t) z) ==>
          (!x l (y :'a). LRTC R x l y ==> P x l y)``,
    REPEAT GEN_TAC
 >> STRIP_TAC
 >> MATCH_MP_TAC ((CONV_RULE (SIMP_CONV list_ss [LRTC_RULES]) o
                   Q.SPECL [`R`, `\u l v. LRTC R u l v /\ P u l v`]) LRTC_INDUCT)
 >> rpt STRIP_TAC
 >> PROVE_TAC [LRTC_RULES]);

val LRTC_LRTC = store_thm (
   "LRTC_LRTC",
  ``!R (x :'a) m y. LRTC R x m y ==> !n z. LRTC R y n z ==> LRTC R x (m ++ n) z``,
    GEN_TAC
 >> HO_MATCH_MP_TAC LRTC_STRONG_INDUCT
 >> FULL_SIMP_TAC list_ss []
 >> rpt STRIP_TAC
 >> RES_TAC
 >> MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES))
 >> Q.EXISTS_TAC `x'`
 >> ASM_REWRITE_TAC []);

val LRTC_TRANS = store_thm (
   "LRTC_TRANS",
  ``!R (x :'a) m y n z. LRTC R x m y /\ LRTC R y n z ==> LRTC R x (m ++ n) z``,
    rpt STRIP_TAC
 >> irule LRTC_LRTC
 >> Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC []);

val LRTC_CASES1 = store_thm (
   "LRTC_CASES1",
  ``!R (x :'a) l y. LRTC R x l y = if NULL l then (x = y)
					     else ?u. R x (HD l) u /\ LRTC R u (TL l) y``,
    SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM]
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      GEN_TAC >> HO_MATCH_MP_TAC LRTC_INDUCT \\
      SIMP_TAC list_ss [] \\
      rpt STRIP_TAC \\
      Q.EXISTS_TAC `x'` >> ASM_REWRITE_TAC [] \\
      Cases_on `NULL l` >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	POP_ASSUM (REWRITE_TAC o wrap o (REWRITE_RULE [NULL_EQ])) \\
	REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)],
	(* goal 1.2 (of 2) *)
	POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM o (MATCH_MP CONS)) \\
	MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES)) \\
	Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC \\
      Cases_on `NULL l` >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
	POP_ASSUM (REWRITE_TAC o wrap o (REWRITE_RULE [NULL_EQ])) \\
	REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)],
	(* goal 2.2 (of 2) *)
	POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM o (MATCH_MP CONS)) \\
	MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES)) \\
	Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] ] ]);

val LRTC_NIL = store_thm (
   "LRTC_NIL", ``!R (x :'a) y. LRTC R x [] y = (x = y)``,
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [LRTC_CASES1]
 >> SIMP_TAC list_ss []);

val LRTC_ONE = store_thm (
   "LRTC_ONE",
  ``!R x t y. LRTC R x [t] y = R x t y``,
    rpt GEN_TAC
 >> Rev EQ_TAC
 >- ( DISCH_TAC >> MATCH_MP_TAC LRTC_SINGLE >> ASM_REWRITE_TAC [] )
 >> ONCE_REWRITE_TAC [LRTC_CASES1]
 >> SIMP_TAC list_ss []
 >> rpt STRIP_TAC
 >> IMP_RES_TAC LRTC_NIL
 >> FULL_SIMP_TAC std_ss []);

val LRTC_CASES2 = store_thm (
   "LRTC_CASES2",
  ``!R (x :'a) l y. LRTC R x l y = if NULL l then (x = y)
					     else ?u. LRTC R x (FRONT l) u /\ R u (LAST l) y``,
    SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM]
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      GEN_TAC >> HO_MATCH_MP_TAC LRTC_INDUCT \\
      SIMP_TAC list_ss [] \\
      rpt STRIP_TAC \\
      Cases_on `l` >> FULL_SIMP_TAC list_ss [] >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)],
	(* goal 1.2 (of 2) *)
	Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] \\
	MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES)) \\
	Q.EXISTS_TAC `x'` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC \\
      Cases_on `l` >> FULL_SIMP_TAC list_ss []
	>- REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)] \\
      Cases_on `t = []` \\
      FULL_SIMP_TAC list_ss [FRONT_DEF, LAST_DEF] >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
	MATCH_MP_TAC LRTC_SINGLE \\
	IMP_RES_TAC (EQ_IMP_LR LRTC_NIL) >> ASM_REWRITE_TAC [],
	(* goal 2.2 (of 2) *)
	Know `h :: t = (h :: FRONT t) ++ [LAST t]`
	>- ( SIMP_TAC list_ss [] >> PROVE_TAC [APPEND_FRONT_LAST] ) \\
	Rewr \\
	MATCH_MP_TAC LRTC_TRANS \\
	Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] \\
	MATCH_MP_TAC LRTC_SINGLE >> ASM_REWRITE_TAC [] ] ]);

val LRTC_CASES_LRTC_TWICE = store_thm (
   "LRTC_CASES_LRTC_TWICE",
  ``!R (x :'a) l y. LRTC R x l y = ?u l1 l2. LRTC R x l1 u /\ LRTC R u l2 y /\ (l = l1 ++ l2)``,
    SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM]
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      GEN_TAC >> HO_MATCH_MP_TAC LRTC_INDUCT \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
	take [`x`, `[]`, `[]`] >> SIMP_TAC list_ss [] \\
	PROVE_TAC [LRTC_RULES],
	(* goal 1.2 (of 2) *)
	take [`u`, `h :: l1`, `l2`] >> ASM_SIMP_TAC list_ss [] \\
	MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES)) \\
	Q.EXISTS_TAC `x'` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC LRTC_TRANS \\
      Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] ]);

val LRTC_APPEND_CASES = store_thm (
   "LRTC_APPEND_CASES",
  ``!R l1 l2 (x :'a) y. LRTC R x (l1 ++ l2) y = ?u. LRTC R x l1 u /\ LRTC R u l2 y``,
    SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM]
 >> Rev CONJ_TAC
 >- ( rpt STRIP_TAC >> Q.ABBREV_TAC `l = l1 ++ l2` \\
      ONCE_REWRITE_TAC [LRTC_CASES_LRTC_TWICE] \\
      take [`u`, `l1`, `l2`] >> Q.UNABBREV_TAC `l` >> ASM_REWRITE_TAC [] )
 >> GEN_TAC
 >> Induct_on `l1`
 >| [ (* goal 1 (of 2) *)
      rpt STRIP_TAC >> FULL_SIMP_TAC list_ss [] \\
      Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC [CONJUNCT1 (Q.SPEC `R` LRTC_RULES)],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC \\
      IMP_RES_TAC LRTC_CASES1 \\
      FULL_SIMP_TAC list_ss [] \\
      RES_TAC \\
      Q.EXISTS_TAC `u'` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC (CONJUNCT2 (Q.SPEC `R` LRTC_RULES)) \\
      Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*                            The trace relation                              *)
(*                                                                            *)
(******************************************************************************)

val _ = overload_on ("epsilon", ``[] :'b Action list``);

val _ = Unicode.unicode_version { u = UTF8.chr 0x03B5, tmnm = "epsilon"};
val _ = TeX_notation { hol = UTF8.chr 0x03B5,
		       TeX = ("\\ensuremath{\\epsilon}", 1) };

val TRACE_def = Define `TRACE = LRTC TRANS`;

val _ = type_abbrev ("trace",
		    ``:('a, 'b) CCS -> 'b Action list -> ('a, 'b) CCS -> bool``);

local
    val trans = (REWRITE_RULE [SYM TRACE_def]) o (ISPEC ``TRANS``);
in

(* (∀x. x --ε--> x) ∧
    ∀x h y t z. x --h--> y ∧ y --t--> z ⇒ x --h::t--> z *)
val TRACE_rules = save_thm (
   "TRACE_rules", trans LRTC_RULES);

val TRACE_trans = save_thm (
   "TRACE_trans", trans LRTC_LRTC);

val TRACE_ind = save_thm (
   "TRACE_ind", trans LRTC_INDUCT);

val TRACE_strongind = save_thm (
   "TRACE_strongind", trans LRTC_STRONG_INDUCT);

val TRACE_cases1 = save_thm (
   "TRACE_cases1", trans LRTC_CASES1);

val TRACE_cases2 = save_thm (
   "TRACE_cases2", trans LRTC_CASES2);

val TRACE_cases_twice = save_thm (
   "TRACE_cases_twice", trans LRTC_CASES_LRTC_TWICE);

val TRACE_APPEND_cases = save_thm (
   "TRACE_APPEND_cases", trans LRTC_APPEND_CASES);

val TRACE_NIL = save_thm (
   "TRACE_NIL", trans LRTC_NIL);

val TRACE1 = save_thm (
   "TRACE1", trans LRTC_SINGLE);

val TRACE_ONE = save_thm (
   "TRACE_ONE", trans LRTC_ONE);
end;

val _ = overload_on ("Trans", ``TRACE``); (* share the pp with TRANS *)

(* The `transitivity` of TRACE relation *)
val TRACE_trans_applied = store_thm (
   "TRACE_trans_applied",
  ``!xs ys E E1 E'. TRACE E xs E1 /\ TRACE E1 ys E' ==> TRACE E (xs ++ ys) E'``,
    PROVE_TAC [TRACE_trans]);

val TRACE_REFL = store_thm ("TRACE_REFL", ``!E. TRACE E [] E``,
    PROVE_TAC [TRACE_def, LRTC_REFL]);

val TRACE2 = store_thm ("TRACE2",
  ``!E x E1 xs E'. TRANS E x E1 /\ TRACE E1 xs E' ==> TRACE E (x :: xs) E'``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC (CONJUNCT2 TRACE_rules)
 >> Q.EXISTS_TAC `E1`
 >> ASM_REWRITE_TAC []);

val EPS_TRACE = store_thm (
   "EPS_TRACE", ``!E E'. EPS E E' ==> ?xs. TRACE E xs E'``,
    HO_MATCH_MP_TAC EPS_ind
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `[]` >> REWRITE_TAC [TRACE_REFL],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `tau :: xs` \\
      MATCH_MP_TAC TRACE2 \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] ]);

val WEAK_TRANS_TRACE = store_thm (
   "WEAK_TRANS_TRACE", ``!E u E'. WEAK_TRANS E u E' ==> ?xs. TRACE E xs E'``,
    REWRITE_TAC [WEAK_TRANS]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EPS_TRACE
 >> IMP_RES_TAC TRACE1
 >> Q.EXISTS_TAC `xs' ++ [u] ++ xs`
 >> MATCH_MP_TAC TRACE_trans_applied
 >> Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC []
 >> MATCH_MP_TAC TRACE_trans_applied
 >> Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC []);

val NO_LABEL_def = Define `
    NO_LABEL (L :'b Action list) = ~?l. MEM (label l) L`;

val NO_LABEL_cases = store_thm (
   "NO_LABEL_cases",
  ``!(x :'b Action) xs. NO_LABEL (x :: xs) ==> (x = tau) /\ NO_LABEL xs``,
    REWRITE_TAC [NO_LABEL_def]
 >> rpt GEN_TAC >> REWRITE_TAC [MEM]
 >> Cases_on `x` >> SIMP_TAC list_ss [Action_distinct_label, IS_LABEL_def]
 >> Q.EXISTS_TAC `L` >> DISJ1_TAC
 >> ACCEPT_TAC (REFL ``label (L :'b Label)``));

val EPS_TRACE2 = Q.prove (
   `!E E'. EPS E E' ==> ?xs. TRACE E xs E' /\ NO_LABEL xs`,
    REWRITE_TAC [NO_LABEL_def]
 >> HO_MATCH_MP_TAC EPS_ind
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `[]` >> REWRITE_TAC [TRACE_REFL] \\
      REWRITE_TAC [MEM],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `tau :: xs` \\
      CONJ_TAC >| (* 2 sub-goal here *)
      [ (* goal 2.1 (of 2) *)
	MATCH_MP_TAC TRACE2 \\
	Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],
	(* goal 2.2 (of 2) *)
	REWRITE_TAC [MEM] \\
	ASM_REWRITE_TAC [Action_distinct_label] ] ]);

val EPS_AND_TRACE = store_thm (
   "EPS_AND_TRACE", ``!E E'. EPS E E' <=> ?xs. TRACE E xs E' /\ NO_LABEL xs``,
    rpt GEN_TAC >> EQ_TAC
 >- ( DISCH_TAC \\
      MATCH_MP_TAC EPS_TRACE2 >> ASM_REWRITE_TAC [] )
 >> REWRITE_TAC [NO_LABEL_def]
 >> rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`E`, `E`)
 >> Q.SPEC_TAC (`xs`, `xs`)
 >> Induct_on `xs` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      GEN_TAC >> REWRITE_TAC [TRACE_NIL] \\
      RW_TAC std_ss [EPS_REFL],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `TRACE E (h::xs) E'`
	(ASSUME_TAC o (ONCE_REWRITE_RULE [TRACE_cases1])) \\
      FULL_SIMP_TAC list_ss [] \\
      RES_TAC \\
      Cases_on `h` >- ( IMP_RES_TAC ONE_TAU >> IMP_RES_TAC EPS_TRANS ) \\
      FULL_SIMP_TAC std_ss [Action_11] \\
      PROVE_TAC [] ]);

(* u is the unique Label in L, learnt from Robert Beers *)
val UNIQUE_LABEL_def = Define `
    UNIQUE_LABEL u (L :'b Action list) =
	?L1 L2. (L1 ++ [u] ++ L2 = L) /\ ~?l. MEM (label l) L1 \/ MEM (label l) L2`;

val UNIQUE_LABEL_IMP_MEM = store_thm (
   "UNIQUE_LABEL_IMP_MEM",
  ``!u (L :'b Action list). UNIQUE_LABEL u L ==> MEM u L``,
    rpt GEN_TAC
 >> REWRITE_TAC [UNIQUE_LABEL_def]
 >> rpt STRIP_TAC
 >> POP_ASSUM K_TAC
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> SIMP_TAC list_ss []);

val UNIQUE_LABEL_NOT_NULL = store_thm (
   "UNIQUE_LABEL_NOT_NULL",
  ``!u (L :'b Action list). UNIQUE_LABEL u L ==> ~NULL L``,
    rpt GEN_TAC >> STRIP_TAC
 >> IMP_RES_TAC UNIQUE_LABEL_IMP_MEM
 >> POP_ASSUM MP_TAC
 >> KILL_TAC
 >> PROVE_TAC [NOT_NULL_MEM]);

val UNIQUE_LABEL_cases1 = store_thm (
   "UNIQUE_LABEL_cases1",
  ``!(l :'b Label) xs. UNIQUE_LABEL (label l) (tau :: xs) = UNIQUE_LABEL (label l) xs``,
    rpt GEN_TAC
 >> REWRITE_TAC [UNIQUE_LABEL_def]
 >> EQ_TAC >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Cases_on `L1` >- FULL_SIMP_TAC list_ss [Action_distinct_label] \\
      REV_FULL_SIMP_TAC list_ss [Action_distinct_label] \\
      take [`t`, `L2`] >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      take [`tau :: L1`, `L2`] \\
      FULL_SIMP_TAC list_ss [Action_distinct_label] ]);

val UNIQUE_LABEL_cases2 = store_thm (
   "UNIQUE_LABEL_cases2",
  ``!(l :'b Label) l' xs. UNIQUE_LABEL (label l) (label l' :: xs) = (l = l') /\ NO_LABEL xs``,
    rpt GEN_TAC
 >> REWRITE_TAC [UNIQUE_LABEL_def]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      Cases_on `L1` >- FULL_SIMP_TAC list_ss [Action_11] \\
      FULL_SIMP_TAC list_ss [],
      (* goal 2 (of 3) *)
      REWRITE_TAC [NO_LABEL_def] \\
      Cases_on `L1` >- REV_FULL_SIMP_TAC list_ss [Action_11] \\
      FULL_SIMP_TAC list_ss [],
      (* goal 3 (of 3) *)
      take [`[]`, `xs`] \\
      FULL_SIMP_TAC list_ss [Action_11, NO_LABEL_def] ]);

val WEAK_TRANS_TRACE2 = Q.prove (
   `!E u E'. WEAK_TRANS E u E' ==> ?us. TRACE E us E' /\ ~NULL us /\
					if (u = tau) then NO_LABEL us else UNIQUE_LABEL u us`,
    REWRITE_TAC [WEAK_TRANS]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC EPS_TRACE2
 >> IMP_RES_TAC TRACE1
 >> Q.EXISTS_TAC `xs' ++ [u] ++ xs`
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC TRACE_trans_applied \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC TRACE_trans_applied \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      FULL_SIMP_TAC list_ss [NO_LABEL_def, NULL_EQ, Action_distinct_label] \\
      Cases_on `u` >> RW_TAC std_ss [] \\
      REWRITE_TAC [UNIQUE_LABEL_def] \\
      take [`xs'`, `xs`] >> FULL_SIMP_TAC list_ss [] ]);

val WEAK_TRANS_AND_TRACE = store_thm (
   "WEAK_TRANS_AND_TRACE",
  ``!E u E'. WEAK_TRANS E u E' <=> ?us. TRACE E us E' /\ ~NULL us /\
					if (u = tau) then NO_LABEL us else UNIQUE_LABEL u us``,
    rpt GEN_TAC >> EQ_TAC (* 2 sub-goals here *)
 >- ( DISCH_TAC \\
      MATCH_MP_TAC WEAK_TRANS_TRACE2 >> ASM_REWRITE_TAC [] )
 >> rpt STRIP_TAC
 >> Cases_on `u`
 >> FULL_SIMP_TAC std_ss [Action_distinct_label, NO_LABEL_def] (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [WEAK_TRANS] \\
      Q.EXISTS_TAC `E` >> REWRITE_TAC [EPS_REFL] \\
      Q.PAT_X_ASSUM `TRACE E us E'` (ASSUME_TAC o (ONCE_REWRITE_RULE [TRACE_cases1])) \\
      REV_FULL_SIMP_TAC list_ss [] \\
      Know `HD us = tau`
      >- ( Cases_on `HD us` >- REWRITE_TAC [] \\
	   Q.PAT_X_ASSUM `!l. ~MEM (label l) us` (ASSUME_TAC o (Q.SPEC `L`)) \\
	   Q.PAT_X_ASSUM `HD us = label L` ((FULL_SIMP_TAC list_ss) o wrap o SYM) \\
	   PROVE_TAC [CONS, MEM] ) \\
      DISCH_TAC >> FULL_SIMP_TAC list_ss [] \\
      Q.EXISTS_TAC `u` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [EPS_AND_TRACE, NO_LABEL_def] \\
      Q.EXISTS_TAC `TL us` >> ASM_REWRITE_TAC [] \\
      CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
      Q.PAT_X_ASSUM `!l. ~MEM (label l) us` (MP_TAC o (Q.SPEC `l`)) \\
      Cases_on `us` >- FULL_SIMP_TAC list_ss [] \\
      REWRITE_TAC [MEM] \\
      FULL_SIMP_TAC list_ss [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [WEAK_TRANS] \\
      IMP_RES_TAC UNIQUE_LABEL_def \\
      Q.PAT_X_ASSUM `L1 ++ [label L] ++ L2 = us` ((FULL_SIMP_TAC std_ss) o wrap o SYM) \\
      Q.PAT_X_ASSUM `TRACE E (L1 ++ [label L] ++ L2) E'`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [TRACE_APPEND_cases])) \\
      take [`u'`, `u`] \\
      IMP_RES_TAC TRACE_ONE >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [EPS_AND_TRACE, NO_LABEL_def] \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
	Q.EXISTS_TAC `L1` >> ASM_REWRITE_TAC [],
	(* goal 2.2 (of 2) *)
	Q.EXISTS_TAC `L2` >> ASM_REWRITE_TAC [] ] ]);

val _ = export_theory ();
val _ = html_theory "Trace";

(* last updated: May 14, 2017 *)
