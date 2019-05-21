(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork mleArithData

val ERR = mk_HOL_ERR "mleCompute"

(* -------------------------------------------------------------------------
   Todo : move comments into structure.
   ------------------------------------------------------------------------- *)

fun compute_exout tml = map_assoc (bin_rep 4 o eval_numtm) tml

fun random_tnn_compute dim =
  let 
    val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)
    val nbit = 4
  in
    random_tnn (dim,nbit) operl
  end

(* single parameter experiment
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleArithData"; open mleArithData;
load "mleCompute"; open mleCompute;
open aiLib;

val traintml = mlTacticData.import_terml 
    (HOLDIR ^ "/src/AI/experiments/data200_train");
val trainex = compute_exout traintml;

val dim = 16;
val randtnn = random_tnn_compute dim;
val bsize = 64;
val schedule = [(10, 0.1 / (Real.fromInt bsize))];
val ncore = 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex,first_n 100 
trainex) schedule;

val r1 = accuracy_set tnn trainex;
*)

(* Compute external experiments 
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleArithData"; open mleArithData;
load "mleCompute"; open mleCompute;
load "mlTune"; open mlTune;
load "smlParallel"; open smlParallel;
load "mlTacticData"; open mlTacticData;
open aiLib;

val traintml = import_terml (HOLDIR ^ "/src/AI/experiments/data200_train");
val trainex = compute_exout traintml;
val validtml = import_terml(HOLDIR ^ "/src/AI/experiments/data200_valid");
val validex = compute_exout validtml;

val trainfile = (!parallel_dir) ^ "/train";
val testfile = (!parallel_dir) ^ "/test";
val operlfile = (!parallel_dir) ^ "/operl";
val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``);
fun init () =
  (
  write_tnnex trainfile trainex;
  write_tnnex testfile validex;
  write_operl operlfile operl
  )
;

val dl = [12,16];
val nl = [400];
val bl = [16,64];
val ll = [10,20,50];
val yl = [2,4];

fun codel_of wid = tune_codel_of (dl,nl,bl,ll,yl) 4 wid;
val paraml = grid_param (dl,nl,bl,ll,yl);
val ncore = 24;

val final = 
  parmap_queue_extern ncore codel_of (init,tune_collect_result) paraml;

write_param_results 
  (HOLDIR ^ "/src/AI/experiments/mleCompute_param_results3") final;
*)








end (* struct *)
