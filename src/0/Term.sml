(* ===================================================================== *)
(* FILE          : Term.sml                                              *)
(* DESCRIPTION   : ML-style typed lambda terms (no ML "let" though).     *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 22, 1997, Ken Larsen (functor removal)      *)
(* Rewritten     : 1999, Bruno Barras, to use explicit substitutions     *)
(* Modified      : July 2000, Konrad Slind, for Moscow ML 2.00           *)
(* ===================================================================== *)

structure Term : RawTerm =
struct

(*
In *scratch*, type
(hol-set-executable mosml-executable)
and type Ctrl-j.

loadPath := "/Users/palantir/hol/hol-omega/sigobj" :: !loadPath;
app load ["Feedback","Lib","Subst","KernelTypes","Type","Sig","Lexis",
          "Polyhash","Binarymap","combinTheory"];
*)

open Feedback Lib Subst KernelTypes Type;

type 'a set = 'a HOLset.set;

val ERR = mk_HOL_ERR "Term";
val WARN = HOL_WARNING "Term";

val ==> = Kind.==>;   infixr 3 ==>;
val --> = Type.-->;   infixr 3 -->;

infix |-> ##;

(*---------------------------------------------------------------------------
               Create the signature for HOL terms
 ---------------------------------------------------------------------------*)

structure TermSig =
  SIG(type ty = term
      fun key (Const(r,_)) = r
        | key _ = raise ERR "key" "not a constant"
      val ERR = ERR
      val table_size = 1999);


(*---------------------------------------------------------------------------*
 * Builtin constants. These are in every HOL signature, and it is            *
 * convenient to nail them down here.                                        *
 *---------------------------------------------------------------------------*)

local open TermSig Type
   val eq_const  = Const(mk_id("=",  "min"), POLY(alpha --> alpha --> bool))
   val hil_const = Const(mk_id("@",  "min"), POLY((alpha --> bool) --> alpha))
   val imp_const = Const(mk_id("==>","min"), GRND(bool --> bool --> bool))
in
val INITIAL {const=eqc,...} = TermSig.insert eq_const
val INITIAL {const=hil,...} = TermSig.insert hil_const
val INITIAL {const=imp,...} = TermSig.insert imp_const
end;

(*---------------------------------------------------------------------------*
    Useful functions to hide explicit substitutions
    Important invariant: never delay subst on atoms, and compose Clos.
    Therefore, in Clos{Env,Body}, Body is either a Comb, TComb, Abs, or TAbs.
    This invariant is enforced if we always use mk_clos instead of Clos.
 ---------------------------------------------------------------------------*)

fun pair_comp (atm,btm) = Subst.comp mk_clos (atm,btm)

and mk_clos (stm, Bv i) =
      (case (Subst.exp_rel(stm,i))
        of (0, SOME t) => mk_clos (Subst.id, t)
         | (k, SOME t) => mk_clos (Subst.shift(k,Subst.id), t)
         | (v, NONE)   => Bv v)
  | mk_clos (s, t as Fv _)     = t
  | mk_clos (s, t as Const _)  = t
  | mk_clos (s,Clos(Env,Body)) = Clos(pair_comp (s,Env), Body)
  | mk_clos (s,t)              = Clos(s, t)
;

(*---------------------------------------------------------------------------
    Propagate substitutions so that we are sure the head of the term is
    not a delayed substitution.
 ---------------------------------------------------------------------------*)

fun push_clos (Clos(E, Comb(f,x)))     = Comb(mk_clos(E,f), mk_clos(E,x))
  | push_clos (Clos(E, TComb(f,ty)))   = TComb(mk_clos(E,f), ty)
  | push_clos (Clos(E, Abs(v,M)))      = Abs(v, mk_clos(Subst.lift(1,E),M))
  | push_clos (Clos(E, TAbs(a,M)))     = TAbs(a, mk_clos(E,M))
  | push_clos _ = raise ERR "push_clos" "not a subst";


(*--------------------------------------------------------------------------*
 * Computing the type of a term.                                            *
 *--------------------------------------------------------------------------*)

local open Subst
      fun lookup 0 (ty::_)  = ty
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "type_of" "lookup"
      fun ty_of (Fv(_,Ty)) _           = Ty
        | ty_of (Const(_,GRND Ty)) _   = Ty
        | ty_of (Const(_,POLY Ty)) _   = Ty
        | ty_of (Bv i) E               = lookup i E
        | ty_of (Comb(Rator, _)) E     = snd(Type.dom_rng(ty_of Rator E))
        | ty_of (TComb(Tm, Ty)) E      =
                let val (Bty,TBody) = Type.dest_univ_type(ty_of Tm E)
                in Type.type_subst[Bty |-> Ty] TBody
                end
        | ty_of (Abs(Fv(_,Ty),Body)) E = Ty --> ty_of Body (Ty::E)
        | ty_of (TAbs(Btyvar,Body)) E  = TyAll(Btyvar, ty_of Body E)
	| ty_of (t as Clos _) E        = ty_of (push_clos t) E
        | ty_of _ _ = raise ERR "type_of" "term construction"
in
fun type_of tm = ty_of tm []
end;


(*---------------------------------------------------------------------------
                Discriminators
 ---------------------------------------------------------------------------*)

fun is_bvar  (Bv _)    = true | is_bvar _  = false;
fun is_var   (Fv _)    = true | is_var _   = false;
fun is_const (Const _) = true | is_const (t as Clos _) = is_const (push_clos t)
                              | is_const _ = false;
fun is_comb  (Comb _)  = true | is_comb  (Clos(_,Comb _)) = true
                              | is_comb _ = false
fun is_tycomb(TComb _) = true | is_tycomb (Clos(_,TComb _)) = true
                              | is_tycomb _ = false
fun is_abs   (Abs _)   = true | is_abs (Clos(_,Abs _)) = true
                              | is_abs _ = false
fun is_tyabs (TAbs _)  = true | is_tyabs (Clos(_,TAbs _)) = true
                              | is_tyabs _ = false;


(*-----------------------------------------------------------------------------*
 * The free type variables of a lambda term. Tail recursive (from Ken Larsen). *
 *-----------------------------------------------------------------------------*)

local fun tyV (Fv(_,Ty)) k         = k (Type.type_vars Ty)
        | tyV (Bv _) k             = k []
        | tyV (Const(_,GRND _)) k  = k []
        | tyV (Const(_,POLY Ty)) k = k (Type.type_vars Ty)
        | tyV (Comb(Rator,Rand)) k = tyV Rand (fn q1 =>
                                     tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (TComb(Rator,Ty)) k  = tyV Rator (fn q  =>
                                         k (union q (Type.type_vars Ty)))
        | tyV (Abs(Bvar,Body)) k   = tyV Body (fn q1 =>
                                     tyV Bvar (fn q2 => k (union q2 q1)))
        | tyV (TAbs(_,Body)) k     = tyV Body k
        | tyV (t as Clos _) k      = tyV (push_clos t) k
in
fun type_vars_in_term tm = tyV tm Lib.I
end;

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. Tail recursive (from Ken Larsen).    *
 *---------------------------------------------------------------------------*)

local fun FV (v as Fv _) A k    = k (Lib.insert v A)
        | FV (Comb(f,x)) A k    = FV f A (fn q => FV x q k)
        | FV (TComb(f,ty)) A k  = FV f A k
        | FV (Abs(_,Body)) A k  = FV Body A k
        | FV (TAbs(_,Body)) A k = FV Body A k
        | FV (t as Clos _) A k  = FV (push_clos t) A k
        | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end;

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term, in textual order.                    *
 *---------------------------------------------------------------------------*)

fun free_vars_lr tm =
  let fun FV ((v as Fv _)::t) A   = FV t (Lib.insert v A)
        | FV (Bv _::t) A          = FV t A
        | FV (Const _::t) A       = FV t A
        | FV (Comb(M,N)::t) A     = FV (M::N::t) A
        | FV (TComb(M,ty)::t) A   = FV (M::t) A
        | FV (Abs(_,M)::t) A      = FV (M::t) A
        | FV (TAbs(_,M)::t) A     = FV (M::t) A
	| FV ((M as Clos _)::t) A = FV (push_clos M::t) A
        | FV [] A = rev A
  in 
     FV [tm] []
  end;

(*---------------------------------------------------------------------------*
 * The set of all variables in a term, represented as a list.                *
 *---------------------------------------------------------------------------*)

local fun vars (v as Fv _) A        = Lib.insert v A
        | vars (Comb(Rator,Rand)) A = vars Rand (vars Rator A)
        | vars (TComb(Rator,Ty)) A  = vars Rator A
        | vars (Abs(Bvar,Body)) A   = vars Body (vars Bvar A)
        | vars (TAbs(_,Body)) A     = vars Body A
	| vars (t as Clos _) A      = vars (push_clos t) A
        | vars _ A = A
in
fun all_vars tm = vars tm []
end;

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list  = itlist (union o all_vars) tm_list [];

(*---------------------------------------------------------------------------
     Support for efficient sets of variables
 ---------------------------------------------------------------------------*)

fun var_compare (Fv(s1,ty1), Fv(s2,ty2)) =
       (case String.compare (s1,s2)
         of EQUAL => Type.compare (ty1,ty2)
          | x => x)
  | var_compare _ = raise ERR "var_compare" "variables required";

val empty_varset = HOLset.empty var_compare

(* ----------------------------------------------------------------------
    A total ordering on terms that respects alpha equivalence.
    Fv < Bv < Const < Comb < TComb < Abs < TAbs
   ---------------------------------------------------------------------- *)

fun compare p =
    if Portable.pointer_eq p then EQUAL else
    case p of
      (t1 as Clos _, t2)     => compare (push_clos t1, t2)
    | (t1, t2 as Clos _)     => compare (t1, push_clos t2)
    | (u as Fv _, v as Fv _) => var_compare (u,v)
    | (Fv _, _)              => LESS
    | (Bv _, Fv _)           => GREATER
    | (Bv i, Bv j)           => Int.compare (i,j)
    | (Bv _, _)              => LESS
    | (Const _, Fv _)        => GREATER
    | (Const _, Bv _)        => GREATER
    | (Const(c1,ty1),
       Const(c2,ty2))        => (case KernelTypes.compare (c1,c2)
                                  of EQUAL => Type.compare (to_hol_type ty1,
                                                            to_hol_type ty2)
                                   | x => x)
    | (Const _, _)           => LESS
    | (Comb(M,N),Comb(P,Q))  => (case compare (M,P)
                                  of EQUAL => compare (N,Q)
                                   | x => x)
    | (Comb _, TComb _)      => LESS
    | (Comb _, Abs _)        => LESS
    | (Comb _, TAbs _)       => LESS
    | (Comb _, _)            => GREATER
    | (TComb(M,a),TComb(N,b))=> (case compare (M,N)
                                  of EQUAL => Type.compare (a,b)
                                   | x => x)
    | (TComb _, Abs _)       => LESS
    | (TComb _, TAbs _)      => LESS
    | (TComb _, _)           => GREATER
    | (Abs(Fv(_, ty1),M),
       Abs(Fv(_, ty2),N))    => (case Type.compare(ty1,ty2)
                                  of EQUAL => compare (M,N)
                                   | x => x)
    | (Abs _, TAbs _)        => LESS
    | (Abs _, _)             => GREATER
    | (TAbs((_,k1,r1),M),
       TAbs((_,k2,r2),N))    => (case Type.kind_rank_compare((k1,r1),(k2,r2))
                                  of EQUAL => compare (M,N)
                                   | x => x)
    | (TAbs _, _)            => GREATER;

val empty_tmset = HOLset.empty compare
fun term_eq t1 t2 = compare(t1,t2) = EQUAL

(*---------------------------------------------------------------------------
        Free variables of a term. Tail recursive. Returns a set.
 ---------------------------------------------------------------------------*)

fun FVL [] A = A
  | FVL ((v as Fv _)::rst) A      = FVL rst (HOLset.add(A,v))
  | FVL (Comb(Rator,Rand)::rst) A = FVL (Rator::Rand::rst) A
  | FVL (TComb(Rator,Ty)::rst) A  = FVL (Rator::rst) A
  | FVL (Abs(_,Body)::rst) A      = FVL (Body::rst) A
  | FVL (TAbs(_,Body)::rst) A     = FVL (Body::rst) A
  | FVL ((t as Clos _)::rst) A    = FVL (push_clos t::rst) A
  | FVL (_::rst) A                = FVL rst A


(* ----------------------------------------------------------------------
    free_in tm M : does tm occur free in M?
   ---------------------------------------------------------------------- *)

fun free_in tm =
   let fun f1 (Comb(Rator,Rand)) = (f2 Rator) orelse (f2 Rand)
         | f1 (TComb(Rator,Ty)) = f2 Rator
         | f1 (Abs(_,Body)) = f2 Body
         | f1 (TAbs(_,Body)) = f2 Body
	 | f1 (t as Clos _) = f2 (push_clos t)
         | f1 _ = false
       and f2 t = term_eq t tm orelse f1 t
   in f2
   end;

(*---------------------------------------------------------------------------
     The following are used in Thm to check side conditions (e.g.,
     does variable v occur free in the assumptions).
 ---------------------------------------------------------------------------*)

fun var_occurs M =
  let val v = (case M of Fv v => v | _ => raise ERR "" "")
      fun occ (Fv u)             = (v=u)
        | occ (Bv _)             = false
        | occ (Const _)          = false
        | occ (Comb(Rator,Rand)) = occ Rand orelse occ Rator
        | occ (TComb(Rator,Ty))  = occ Rator
        | occ (Abs(_,Body))      = occ Body
        | occ (TAbs(_,Body))     = occ Body
        | occ (t as Clos _)      = occ (push_clos t)
   in occ end
   handle HOL_ERR _ => raise ERR "var_occurs" "not a variable";


(*---------------------------------------------------------------------------*
 * Making variables                                                          *
 *---------------------------------------------------------------------------*)

val mk_var = Fv

fun inST s = not(null(TermSig.resolve s));

fun mk_primed_var (Name,Ty) =
  let val next = Lexis.nameStrm Name
      fun spin s = if inST s then spin (next()) else s
  in mk_var(spin Name, Ty)
  end;

(*---------------------------------------------------------------------------*
 *   "genvars" are a Lisp-style "gensym" for HOL variables.                  *
 *---------------------------------------------------------------------------*)

local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar ty = Fv(state(next nameStrm), ty)

fun genvars ty =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar ty::acc) (n-1)
 in gen []
 end

fun is_genvar (Fv(Name,_)) = String.isPrefix genvar_prefix Name
  | is_genvar _ = false;
end;


(*---------------------------------------------------------------------------*
 * Given a variable and a list of variables, if the variable does not exist  *
 * on the list, then return the variable. Otherwise, rename the variable and *
 * try again. Note well that the variant uses only the name of the variable  *
 * as a basis for testing equality. Experience has shown that basing the     *
 * comparison on both the name and the type of the variable resulted in      *
 * needlessly confusing formulas occasionally being displayed in interactive *
 * sessions.                                                                 *
 *---------------------------------------------------------------------------*)

fun gen_variant P caller =
  let fun var_name _ (Fv(Name,_)) = Name
        | var_name caller _ = raise ERR caller "not a variable"
      fun vary vlist (Fv(Name,Ty)) =
          let val next = Lexis.nameStrm Name
              val L = map (var_name caller) vlist
              fun away s = if mem s L then away (next()) else s
              fun loop name =
                 let val s = away name
                 in if P s then loop (next()) else s
                 end
          in mk_var(loop Name, Ty)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

val variant      = gen_variant inST "variant"
val prim_variant = gen_variant (K false) "prim_variant";


(*---------------------------------------------------------------------------*
 *             Making constants.                                             *
 *                                                                           *
 * We grab the constant scheme from the signature. If it is ground, then     *
 * we just return the scheme. Thus there will only be one copy of any        *
 * ground constant. If it is polymorphic, we match its type against the      *
 * given type. If the match is the identity substitution, we just return     *
 * the constant. If the match moves some variables, then we check that the   *
 * instance is ground (and then return GRND); otherwise the type is still    *
 * polymorphic.                                                              *
 *---------------------------------------------------------------------------*)

val decls = map #const o TermSig.resolve;

fun prim_mk_const {Name,Thy} =
 case TermSig.lookup (Name,Thy)
  of SOME{const,...} => const
   | NONE => raise ERR "prim_mk_const"
               (Lib.quote Name^" not found in theory "^Lib.quote Thy)

fun ground x = Lib.all (fn {redex,residue} => not(Type.polymorphic residue)) x;

fun create_const errstr (const as Const(_,GRND pat)) Ty =
      if Ty=pat then const else raise ERR "create_const" "not a type match"
  | create_const errstr (const as Const(r,POLY pat)) Ty =
     ((case Type.raw_match_type pat Ty ([],[])
        of ([],_) => const
         | (S,[]) => Const(r, if ground S then GRND Ty else POLY Ty)
         | (S, _) => Const(r,POLY Ty))
        handle HOL_ERR _ => raise ERR errstr
             (String.concat["Not a type instance: ", id_to_string r]))
  | create_const errstr _ _ = raise ERR errstr "non-constant in signature";


fun mk_thy_const {Thy,Name,Ty} =
  case TermSig.lookup (Name,Thy)
   of NONE => raise ERR "mk_thy_const" (fullname(Name,Thy)^" not found")
    | SOME {const, ...} => create_const "mk_thy_const" const Ty

fun first_decl fname Name =
  case TermSig.resolve Name
   of []             => raise ERR fname (Name^" not found")
    | [{const,...}]  => const
    | {const,...}::_ =>
        (WARN fname (Lib.quote Name^": more than one possibility");
         const)

val current_const = first_decl "current_const";
fun mk_const(Name,Ty) = create_const"mk_const" (first_decl"mk_const" Name) Ty;

val all_consts = map #const o TermSig.all_entries;
val thy_consts = map #const o TermSig.slice;

fun same_const (Const(id1,_)) (Const(id2,_)) = same_id (id1,id2)
  | same_const _ _ = false

(*---------------------------------------------------------------------------*
 *        Making applications                                                *
 *---------------------------------------------------------------------------*)

local val INCOMPAT_TYPES  = Lib.C ERR "incompatible types"
      fun lmk_comb err =
        let fun loop (A,_) [] = A
              | loop (A,typ) (tm::rst) =
                 let val (ty1,ty2) = with_exn Type.dom_rng typ err
                 in if type_of tm = ty1
                    then loop(Comb(A,tm),ty2) rst
                    else raise err
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
      val mk_comb0 = lmk_comb (INCOMPAT_TYPES "mk_comb")
in

fun mk_comb(r as (Abs(Fv(_,Ty),_), Rand)) =
      if type_of Rand = Ty then Comb r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(r as (Clos(_,Abs(Fv(_,Ty),_)), Rand)) =
      if type_of Rand = Ty then Comb r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(Rator,Rand) = mk_comb0 (Rator,[Rand])

val list_mk_comb = lmk_comb (INCOMPAT_TYPES "list_mk_comb")
end;

fun dest_comb (Comb r) = r
  | dest_comb (t as Clos _) = dest_comb (push_clos t)
  | dest_comb _ = raise ERR "dest_comb" "not a comb"

(*---------------------------------------------------------------------------*
 *        Making type applications                                           *
 *---------------------------------------------------------------------------*)

local val err  = Lib.C ERR "operator on type does not have universal type"
      fun check_rank caller (TyFv (_,_,rank)) ty =
          if Type.rank_of ty > rank
          then raise ERR caller "universal type variable has insufficient rank"
          else ()
        | check_rank caller _ _ = raise ERR caller "not a type variable"
      fun lmk_tcomb caller =
        let val err = err caller
            fun loop (A,_) [] = A
              | loop (A,typ) (ty::rst) =
                 let val (bty,ty2) = with_exn Type.dest_univ_type typ err
                     val _ = check_rank caller bty ty
                     val ty2' = Type.type_subst[bty |-> ty] ty2
                 in loop(TComb(A,ty), ty2') rst
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
      val mk_tcomb0 = lmk_tcomb "mk_tcomb"
in

fun mk_tycomb(r as (TAbs(btyvar,_), Ty)) =
     (check_rank "mk_tycomb" (TyFv btyvar) Ty; TComb r)
  | mk_tycomb(r as (Clos(_,TAbs(btyvar,_)), Ty)) =
     (check_rank "mk_tycomb" (TyFv btyvar) Ty; TComb r)
  | mk_tycomb(Rator,Ty) = mk_tcomb0 (Rator,[Ty])

val list_mk_tycomb = lmk_tcomb "list_mk_tycomb"
end;

fun dest_tycomb (TComb r) = r
  | dest_tycomb (t as Clos _) = dest_tycomb (push_clos t)
  | dest_tycomb _ = raise ERR "dest_tycomb" "not a type comb"


fun dest_var (Fv v) = v
  | dest_var _ = raise ERR "dest_var" "not a var"


(*---------------------------------------------------------------------------*
 *                  Alpha conversion                                         *
 *---------------------------------------------------------------------------*)

fun rename_bvar s t =
    case t of
      Abs(Fv(_, Ty), Body) => Abs(Fv(s,Ty), Body)
    | Clos(_, Abs _) => rename_bvar s (push_clos t)
    | _ => raise ERR "rename_bvar" "not an abstraction";


local val EQ = Portable.pointer_eq
in
fun aconv t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (Fv(M,ty1),Fv(N,ty2)) => M=N andalso aconv_ty ty1 ty2
   | (Const(M,GRND ty1),Const(N,GRND ty2)) => M=N andalso aconv_ty ty1 ty2
   | (Const(M,POLY ty1),Const(N,POLY ty2)) => M=N andalso aconv_ty ty1 ty2
   | (Const _,Const _) => false
   | (Comb(M,N),Comb(P,Q)) => aconv N Q andalso aconv M P
   | (TComb(M,ty1),TComb(P,ty2)) => Type.aconv_ty ty1 ty2 andalso aconv M P
   | (Abs(Fv(_,ty1),M),
      Abs(Fv(_,ty2),N)) => aconv_ty ty1 ty2 andalso aconv M N
   | (TAbs((_,k1,r1),M),
      TAbs((_,k2,r2),N)) => k1=k2 andalso r1=r2 andalso aconv M N
   | (Clos(e1,b1),
      Clos(e2,b2)) => (EQ(e1,e2) andalso EQ(b1,b2))
                       orelse aconv (push_clos t1) (push_clos t2)
   | (Clos _, _) => aconv (push_clos t1) t2
   | (_, Clos _) => aconv t1 (push_clos t2)
   | (M,N)       => (M=N)
end;


(*---------------------------------------------------------------------------*
 *        Beta-reduction. Non-renaming.                                      *
 *---------------------------------------------------------------------------*)

fun beta_conv (Comb(Abs(_,Body), Bv 0)) = Body
  | beta_conv (Comb(Abs(_,Body), Rand)) =
     let fun subs((tm as Bv j),i)     = if i=j then Rand else tm
           | subs(Comb(Rator,Rand),i) = Comb(subs(Rator,i),subs(Rand,i))
           | subs(TComb(Rator,Ty),i)  = TComb(subs(Rator,i),Ty)
           | subs(Abs(v,Body),i)      = Abs(v,subs(Body,i+1))
           | subs(TAbs(a,Body),i)     = TAbs(a,subs(Body,i))
           | subs (tm as Clos _,i)    = subs(push_clos tm,i)
           | subs (tm,_) = tm
     in
       subs (Body,0)
     end
  | beta_conv (Comb(x as Clos _, Rand)) = beta_conv (Comb(push_clos x, Rand))
  | beta_conv (x as Clos _) = beta_conv (push_clos x)
  | beta_conv _ = raise ERR "beta_conv" "not a beta-redex";


(*---------------------------------------------------------------------------*
 *   Beta-reduction without propagation of the explicit substitution         *
 *   until the next abstraction.                                             *
 *---------------------------------------------------------------------------*)

fun lazy_beta_conv (Comb(Abs(_,Body),Rand)) =
      mk_clos(Subst.cons(Subst.id,Rand), Body)
  | lazy_beta_conv (Comb(Clos(Env, Abs(_,Body)),Rand)) =
      mk_clos(Subst.cons(Env,Rand), Body)
  | lazy_beta_conv (t as Clos _) = lazy_beta_conv (push_clos t)
  | lazy_beta_conv _ = raise ERR "lazy_beta_conv" "not a beta-redex";


(*---------------------------------------------------------------------------*
 *       Eta-conversion                                                      *
 *---------------------------------------------------------------------------*)

local fun pop (tm as Bv i, k) =
           if i=k then raise ERR "eta_conv" "not an eta-redex" else tm
        | pop (Comb(Rator,Rand),k) = Comb(pop(Rator,k), pop(Rand,k))
        | pop (TComb(Rator,Ty),k)  = TComb(pop(Rator,k), Ty)
        | pop (Abs(v,Body), k)     = Abs(v,pop(Body, k+1))
        | pop (TAbs(a,Body), k)    = TAbs(a,pop(Body, k))
        | pop (tm as Clos _, k)    = pop (push_clos tm, k)
        | pop (tm,k) = tm
      fun eta_body (Comb(Rator,Bv 0)) = pop (Rator,0)
        | eta_body (tm as Clos _)     = eta_body (push_clos tm)
        | eta_body _ = raise ERR "eta_conv" "not an eta-redex"
in
fun eta_conv (Abs(_,Body))  = eta_body Body
  | eta_conv (tm as Clos _) = eta_conv (push_clos tm)
  | eta_conv _ = raise ERR "eta_conv" "not an eta-redex"
end;


(*---------------------------------------------------------------------------*
 *        Type Beta-reduction. Non-renaming.                                 *
 *---------------------------------------------------------------------------*)

fun ty_beta_conv (TComb(TAbs(Bvar as (Name,Kind,Rank),Body), Rand)) =
     let fun subs(Fv(s,ty),i)         = Fv(s,subs_ty(ty,i))
           | subs(Const(Name,Ty),i)   = Const(Name,subs_pty(Ty,i))
           | subs(Comb(Rator,Rand),i) = Comb(subs(Rator,i),subs(Rand,i))
           | subs(TComb(Rator,Ty),i)  = TComb(subs(Rator,i),subs_ty(Ty,i))
           | subs(Abs(v,Body),i)      = Abs(subs(v,i),subs(Body,i))
           | subs(TAbs(a,Body),i)     = TAbs(a,subs(Body,i+1))
           | subs (tm as Clos _,i)    = subs(push_clos tm,i)
           | subs (tm,_) = tm (* e.g., bound variables *)
         and subs_pty (GRND ty,i)     = GRND (subs_ty(ty,i))
           | subs_pty (POLY ty,i)     = POLY (subs_ty(ty,i))
         and subs_ty (v as TyBv j,i)      = if i=j then Rand else v
           | subs_ty (TyApp(opr,arg),i)   = TyApp(subs_ty(opr,i), subs_ty(arg,i))
           | subs_ty (TyAll(bv,Body),i)   = TyAll(bv, subs_ty(Body,i+1))
           | subs_ty (TyAbs(bv,Body),i)   = TyAbs(bv, subs_ty(Body,i+1))
           | subs_ty (ty,_) = ty (* e.g., free type variables *)
     in
       subs (Body,0)
     end
  | ty_beta_conv (Comb(x as Clos _, Rand)) = ty_beta_conv (Comb(push_clos x, Rand))
  | ty_beta_conv (x as Clos _) = ty_beta_conv (push_clos x)
  | ty_beta_conv _ = raise ERR "ty_beta_conv" "not a type beta-redex";


(*---------------------------------------------------------------------------*
 *       Type Eta-conversion                                                 *
 *---------------------------------------------------------------------------*)

local fun pop (tm as Fv(s,ty),k)    = Fv(s,pop_ty(ty,k))
        | pop (Const(Name,Ty),k)    = Const(Name,pop_pty(Ty,k))
        | pop (Comb(Rator,Rand),k)  = Comb(pop(Rator,k), pop(Rand,k))
        | pop (TComb(Rator,Ty),k)   = TComb(pop(Rator,k), pop_ty(Ty,k))
        | pop (Abs(v,Body), k)      = Abs(pop(v,k), pop(Body, k+1))
        | pop (TAbs(a,Body), k)     = TAbs(a,pop(Body, k))
        | pop (tm as Clos _, k)     = pop (push_clos tm, k)
        | pop (tm,k) = tm (* e.g., bound variables *)
      and pop_pty (GRND ty,k)       = GRND (pop_ty(ty,k))
        | pop_pty (POLY ty,k)       = POLY (pop_ty(ty,k))
      and pop_ty (v as TyBv i,k)    =
           if i=k then raise ERR "ty_eta_conv" "not a type eta-redex" else v
        | pop_ty (TyApp(opr,arg),k) = TyApp(pop_ty(opr,k), pop_ty(arg,k))
        | pop_ty (TyAll(bv,Body),k) = TyAll(bv, pop_ty(Body,k+1))
        | pop_ty (TyAbs(bv,Body),k) = TyAbs(bv, pop_ty(Body,k+1))
        | pop_ty (ty,_) = ty (* e.g., free type variables *)
      fun ty_eta_body (TComb(Rator,TyBv 0)) = pop (Rator,0)
        | ty_eta_body (tm as Clos _)        = ty_eta_body (push_clos tm)
        | ty_eta_body _ = raise ERR "ty_eta_conv" "not a type eta-redex"
in
fun ty_eta_conv (TAbs(_,Body)) = ty_eta_body Body
  | ty_eta_conv (tm as Clos _) = ty_eta_conv (push_clos tm)
  | ty_eta_conv _ = raise ERR "ty_eta_conv" "not a type eta-redex"
end;


(*---------------------------------------------------------------------------*
 *    Replace arbitrary subterms in a term. Non-renaming.                    *
 *---------------------------------------------------------------------------*)

val emptysubst:(term,term)Binarymap.dict = Binarymap.mkDict compare
local
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (if type_of redex = type_of residue
              then (insert(A,redex,residue),
                    is_var redex andalso b)
              else raise ERR "subst" "redex has different type than residue")
in
fun subst [] = I
  | subst theta =
    let val (fmap,b) = addb theta (emptysubst, true)
        fun vsubs (v as Fv _) = (case peek(fmap,v) of NONE => v | SOME y => y)
          | vsubs (Comb(Rator,Rand)) = Comb(vsubs Rator, vsubs Rand)
          | vsubs (TComb(Rator,Ty))  = TComb(vsubs Rator, Ty)
          | vsubs (Abs(Bvar,Body))   = Abs(Bvar,vsubs Body)
          | vsubs (TAbs(Bvar,Body))  = TAbs(Bvar,vsubs Body)
          | vsubs (c as Clos _) = vsubs (push_clos c)
          | vsubs tm = tm
        fun subs tm =
          case peek(fmap,tm)
           of SOME residue => residue
	    | NONE =>
              (case tm
                of Comb(Rator,Rand) => Comb(subs Rator, subs Rand)
                 | TComb(Rator,Ty)  => TComb(subs Rator, Ty)
                 | Abs(Bvar,Body)   => Abs(Bvar,subs Body)
                 | TAbs(Bvar,Body)  => TAbs(Bvar,subs Body)
	         | Clos _           => subs(push_clos tm)
                 |   _              => tm)
    in
      (if b then vsubs else subs)
    end
end

(*---------------------------------------------------------------------------*
 *     Instantiate type variables in a term                                  *
 *---------------------------------------------------------------------------*)

fun inst [] tm = tm
  | inst theta tm =
    let fun
       inst1 (bv as Bv _) = bv
     | inst1 (c as Const(_, GRND _)) = c
     | inst1 (c as Const(r, POLY Ty)) =
       (case Type.ty_sub theta Ty
         of SAME => c
          | DIFF ty => Const(r,(if Type.polymorphic ty then POLY else GRND)ty))
     | inst1 (v as Fv(Name,Ty)) =
         (case Type.ty_sub theta Ty of SAME => v | DIFF ty => Fv(Name, ty))
     | inst1 (Comb(Rator,Rand)) = Comb(inst1 Rator, inst1 Rand)
     | inst1 (TComb(Rator,Ty))  = TComb(inst1 Rator, Type.type_subst theta Ty)
     | inst1 (Abs(Bvar,Body))   = Abs(inst1 Bvar, inst1 Body)
     | inst1 (TAbs(Bvar,Body))  = TAbs(Bvar, inst1 Body)
     | inst1 (t as Clos _)      = inst1(push_clos t)
    in
      inst1 tm
    end;


(*---------------------------------------------------------------------------
       Making abstractions. list_mk_binder is a relatively
       efficient version for making terms with many consecutive
       abstractions.
  ---------------------------------------------------------------------------*)

local val FORMAT = ERR "list_mk_binder"
   "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
   fun check_opt NONE = Lib.I
     | check_opt (SOME c) =
        if not(is_const c) then raise FORMAT
        else case total (fst o Type.dom_rng o fst o Type.dom_rng o type_of) c
              of NONE => raise FORMAT
               | SOME ty => (fn abs =>
                   let val dom = fst(Type.dom_rng(type_of abs))
                   in mk_comb (inst[ty |-> dom] c, abs)
                   end)
in
fun list_mk_binder opt =
 let val f = check_opt opt
 in fn (vlist,tm)
 => if not (all is_var vlist) then raise ERR "list_mk_binder" ""
    else
  let open Polyhash
     val varmap = mkPolyTable(length vlist, Fail "varmap")
     fun enum [] _ A = A
       | enum (h::t) i A = (insert varmap (h,i); enum t (i-1) (h::A))
     val rvlist = enum vlist (length vlist - 1) []
     fun lookup v vmap = case peek vmap v of NONE => v | SOME i => Bv i
     fun increment vmap = transform (fn x => x+1) vmap
     fun bind (v as Fv _) vmap k   = k (lookup v vmap)
       | bind (Comb(M,N)) vmap k   = bind M vmap (fn m =>
                                     bind N vmap (fn n => k (Comb(m,n))))
       | bind (TComb(M,Ty)) vmap k = bind M vmap (fn m => k (TComb(m,Ty)))
       | bind (Abs(v,M)) vmap k    = bind M (increment vmap)
                                            (fn q => k (Abs(v,q)))
       | bind (TAbs(v,M)) vmap k   = bind M vmap (fn q => k (TAbs(v,q)))
       | bind (t as Clos _) vmap k = bind (push_clos t) vmap k
       | bind tm vmap k = k tm
  in
     rev_itlist (fn v => fn M => f(Abs(v,M))) rvlist (bind tm varmap I)
  end
  handle e => raise wrap_exn "Term" "list_mk_binder" e
 end
end;

val list_mk_abs = list_mk_binder NONE;

fun mk_abs(Bvar as Fv _, Body) =
    let fun bind (v as Fv _) i        = if v=Bvar then Bv i else v
          | bind (Comb(Rator,Rand)) i = Comb(bind Rator i, bind Rand i)
          | bind (TComb(Rator,Ty)) i  = TComb(bind Rator i, Ty)
          | bind (Abs(Bvar,Body)) i   = Abs(Bvar, bind Body (i+1))
          | bind (TAbs(Bvar,Body)) i  = TAbs(Bvar, bind Body i)
          | bind (t as Clos _) i      = bind (push_clos t) i
          | bind tm _ = tm (* constant *)
    in
      Abs(Bvar, bind Body 0)
    end
  | mk_abs _ = raise ERR "mk_abs" "Bvar not a variable"



(*---------------------------------------------------------------------------
       Making type abstractions. list_mk_tybinder is a relatively
       efficient version for making terms with many consecutive
       type abstractions.
  ---------------------------------------------------------------------------*)


local val FORMAT = ERR "list_mk_tybinder"
   "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
   fun check_opt NONE = Lib.I
     | check_opt (SOME c) =
        if not(is_const c) then raise FORMAT
        else case total (fst o Type.dom_rng o fst o Type.dom_rng o type_of) c
              of NONE => raise FORMAT
               | SOME ty => (fn abs =>
                   let val dom = fst(Type.dom_rng(type_of abs))
                   in mk_comb (inst[ty |-> dom] c, abs)
                   end)
in
fun list_mk_tybinder opt =
 let val f = check_opt opt
 in fn (vlist,tm) => 
    if not (null (Lib.intersect vlist (type_varsl (map type_of (free_vars tm)))))
    then raise ERR "list_mk_tyabs"
         "bound variable occurs free in the type of a free variable of the body"
    else
    let open Polyhash
     val varmap = mkPolyTable(length vlist, Fail "varmap")
     fun enum [] _ A = A
       | enum (h::t) i A = (insert varmap (h,i); enum t (i-1) (h::A))
     val rvlist = enum vlist (length vlist - 1) []
     fun lookup v vmap = case peek vmap v of NONE => v | SOME i => TyBv i
     fun increment vmap = transform (fn x => x+1) vmap
     fun bind (Fv(Name,Ty)) vmap k = bindty Ty vmap (fn ty => k (Fv(Name,ty)))
       | bind (Const(N,Ty)) vmap k = bindpty Ty vmap (fn ty => k (Const(N,ty)))
       | bind (Comb(M,N)) vmap k   = bind M vmap (fn m =>
                                     bind N vmap (fn n => k (Comb(m,n))))
       | bind (TComb(M,Ty)) vmap k = bind M vmap (fn m =>
                                     bindty Ty vmap (fn ty => k (TComb(m,ty))))
       | bind (Abs(v,M)) vmap k    = bind M vmap (fn q => k (Abs(v,q)))
       | bind (TAbs(v,M)) vmap k   = bind M (increment vmap)
                                            (fn q => k (TAbs(v,q)))
       | bind (t as Clos _) vmap k = bind (push_clos t) vmap k
       | bind tm vmap k = k tm (* constant *)
     and bindpty (GRND Ty) vmap k  = bindty Ty vmap (fn ty => k (GRND ty))
       | bindpty (POLY Ty) vmap k  = bindty Ty vmap (fn ty => k (POLY ty))
     and bindty (v as TyFv _) vmap k    = k (lookup v vmap)
       | bindty (TyApp(Opr,Arg)) vmap k = bindty Opr vmap (fn opr =>
                                          bindty Arg vmap (fn arg =>
                                            k (TyApp(opr,arg))))
       | bindty (TyAll(bv,Body)) vmap k = bindty Body (increment vmap)
                                            (fn body => k (TyAll(bv,body)))
       | bindty (TyAbs(bv,Body)) vmap k = bindty Body (increment vmap)
                                            (fn body => k (TyAbs(bv,body)))
       | bindty ty _ k = k ty (* constant *)
  in
     rev_itlist (fn TyFv a => fn M => f(TAbs(a,M))) rvlist (bind tm varmap I)
  end
  handle e => raise wrap_exn "Term" "list_mk_binder" e
 end
end;

val list_mk_tyabs = list_mk_tybinder NONE;


fun mk_tyabs(Bvar as TyFv Bvarty, Body) =
    if mem Bvar (type_varsl (map type_of (free_vars Body)))
    then raise ERR "mk_tyabs"
         "bound variable occurs free in the type of a free variable of the body"
    else
    let fun bind (Fv(Name,Ty)) i      = Fv(Name, bindty Ty i)
          | bind (Const(Name,Ty)) i   = Const(Name, bindpty Ty i)
          | bind (Comb(Rator,Rand)) i = Comb(bind Rator i, bind Rand i)
          | bind (TComb(Rator,Ty)) i  = TComb(bind Rator i, bindty Ty i)
          | bind (Abs(Bvar,Body)) i   = Abs(bind Bvar i, bind Body i)
          | bind (TAbs(Bvar,Body)) i  = TAbs(Bvar, bind Body (i+1))
          | bind (t as Clos _) i      = bind (push_clos t) i
          | bind tm _ = tm (* constant *)
        and bindpty (GRND ty) i         = GRND (bindty ty i)
          | bindpty (POLY ty) i         = POLY (bindty ty i)
        and bindty (v as TyFv _) i    = if v=Bvar then TyBv i else v
          | bindty (TyApp(opr,arg)) i = TyApp(bindty opr i, bindty arg i)
          | bindty (TyAll(bv,Body)) i = TyAll(bv, bindty Body (i+1))
          | bindty (TyAbs(bv,Body)) i = TyAbs(bv, bindty Body (i+1))
          | bindty ty _ = ty (* constant *)
    in
      TAbs(Bvarty, bind Body 0)
    end
  | mk_tyabs _ = raise ERR "mk_tyabs" "not a type variable";

(*---------------------------------------------------------------------------
            Taking terms apart

    These operations are all easy, except for taking apart multiple
    abstractions. It can happen, via beta-conversion or substitution,
    or instantiation, that a free variable is bound by the scope. One
    of the tasks of strip_abs is to sort the resulting mess out.
    strip_abs works by first classifying all the free variables in the
    body as being captured by the prefix bindings or not. Each capturing
    prefix binder is then renamed until it doesn't capture. Then we go
    through the body and replace the dB indices of the prefix with the
    corresponding free variables. These may in fact fall under another
    binder; the renaming of that will, if necessary, get done if that
    binder is taken apart (by a subsequent dest/strip_binder).
 ---------------------------------------------------------------------------*)

local fun peel f (t as Clos _) A = peel f (push_clos t) A
        | peel f tm A =
            case f tm of
              SOME(Abs(v,M)) => peel f M (v::A)
            | otherwise => (A,tm)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => var_compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
      fun trypush_clos (x as Clos _) = push_clos x
        | trypush_clos t = t
in
fun strip_binder opt =
 let val f =
         case opt of
           NONE => (fn (t as Abs _) => SOME t
                     | (t as Clos(_, Abs _)) => SOME (push_clos t)
                     | other => NONE)
               | SOME c => (fn t => let val (rator,rand) = dest_comb t
                                    in if same_const rator c
                                       then SOME (trypush_clos rand)
                                       else NONE
                                    end handle HOL_ERR _ => NONE)
 in fn tm =>
   let val (prefixl,body) = peel f tm []
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Polyhash  (* AV is hashtable  of (var,occtype) elems *)
            val AV = mkPolyTable(Array.length prefix, Fail"AV")
            fun insertl [] _ dupls = dupls
              | insertl (x::rst) i dupls =
                  let val n = fst(dest_var x)
                  in case peekInsert AV (n,PREFIX i)
                      of NONE => insertl rst (i+1) dupls
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls)
                  end
            val dupls = insertl prefixl 0 []
        in ((fn s => insert AV (s,BODY)),         (* insertAVbody *)
            (fn (s,i) => insert AV (s,PREFIX i)), (* insertAVprefix *)
            peek AV,                              (* lookAV *)
            dupls)
        end
     fun variantAV n =
       let val next = Lexis.nameStrm n
           fun loop s = case lookAV s of NONE => s | SOME _ => loop (next())
       in loop n
       end
     fun CVs (v as Fv(n,_)) capt k =
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
       | CVs(Comb(M,N)) capt k   = CVs N capt (fn c => CVs M c k)
       | CVs(TComb(M,Ty)) capt k = CVs M capt k
       | CVs(Abs(_,M)) capt k    = CVs M capt k
       | CVs(TAbs(_,M)) capt k   = CVs M capt k
       | CVs(t as Clos _) capt k = CVs (push_clos t) capt k
       | CVs tm capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v,i)::rst) =
           let val (n,ty) = dest_var v
               val n' = variantAV n
               val v' = mk_var(n',ty)
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     fun unbind (v as Bv i) j k = k (vmap(i-j) handle Subscript => v)
       | unbind (Comb(M,N)) j k = unbind M j (fn m =>
                                  unbind N j (fn n => k(Comb(m,n))))
       | unbind (TComb(M,Ty)) j k = unbind M j (fn m => k(TComb(m,Ty)))
       | unbind (Abs(v,M)) j k  = unbind M (j+1) (fn q => k(Abs(v,q)))
       | unbind (TAbs(a,M)) j k  = unbind M j (fn q => k(TAbs(a,q)))
       | unbind (t as Clos _) j k = unbind (push_clos t) j k
       | unbind tm j k = k tm
 in
     unclash insertAVprefix (List.rev dupls)
   ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
   ; (array_to_revlist prefix, unbind body 0 I)
 end
 end
end;

val strip_abs = strip_binder NONE;

local exception CLASH
in
fun dest_abs(Abs(Bvar as Fv(Name,Ty), Body)) =
    let fun dest (v as (Bv j), i)     = if i=j then Bvar else v
          | dest (v as Fv(s,_), _)    = if Name=s then raise CLASH else v
          | dest (Comb(Rator,Rand),i) = Comb(dest(Rator,i),dest(Rand,i))
          | dest (TComb(Rator,Ty),i)  = TComb(dest(Rator,i),Ty)
          | dest (Abs(Bvar,Body),i)   = Abs(Bvar, dest(Body,i+1))
          | dest (TAbs(Bvar,Body),i)  = TAbs(Bvar, dest(Body,i))
          | dest (t as Clos _, i)     = dest (push_clos t, i)
          | dest (tm,_) = tm
    in (Bvar, dest(Body,0))
       handle CLASH =>
              dest_abs(Abs(variant (free_vars Body) Bvar, Body))
    end
  | dest_abs (t as Clos _) = dest_abs (push_clos t)
  | dest_abs _ = raise ERR "dest_abs" "not a lambda abstraction"
end;


(* Now for stripping binders of type abstractions of terms. *)

local fun peel f (t as Clos _) A = peel f (push_clos t) A
        | peel f tm A =
            case f tm of
              SOME(TAbs(v,M)) => peel f M (TyFv v::A)
            | otherwise => (A,tm)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => Type.compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
      fun trypush_clos (x as Clos _) = push_clos x
        | trypush_clos t = t
in
fun strip_tybinder opt =
 let val f =
         case opt of
           NONE => (fn (t as TAbs _) => SOME t
                     | (t as Clos(_, TAbs _)) => SOME (push_clos t)
                     | other => NONE)
               | SOME c => (fn t => let val (rator,rand) = dest_comb t
                                    in if same_const rator c
                                       then SOME (trypush_clos rand)
                                       else NONE
                                    end handle HOL_ERR _ => NONE)
 in fn tm =>
   let val (prefixl,body) = peel f tm []
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Polyhash  (* AV is hashtable  of (var,occtype) elems *)
            val AV = mkPolyTable(Array.length prefix, Fail"AV")
            fun insertl [] _ dupls = dupls
              | insertl (x::rst) i dupls =
                  let val n = #1(dest_vartype_opr x)
                  in case peekInsert AV (n,PREFIX i)
                      of NONE => insertl rst (i+1) dupls
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls)
                  end
            val dupls = insertl prefixl 0 []
        in ((fn s => insert AV (s,BODY)),         (* insertAVbody *)
            (fn (s,i) => insert AV (s,PREFIX i)), (* insertAVprefix *)
            peek AV,                              (* lookAV *)
            dupls)
        end
     fun variantAV n =
       let val next = Lexis.tyvar_vary
           fun loop s = case lookAV s of NONE => s | SOME _ => loop (next s)
       in loop n
       end
     fun CVs (Fv(n,Ty)) capt k   = CVts Ty capt k
       | CVs(Const(_,Ty)) capt k = CVps Ty capt k
       | CVs(Comb(M,N)) capt k   = CVs N capt (fn c => CVs M c k)
       | CVs(TComb(M,Ty)) capt k = CVs M capt (fn c => CVts Ty c k)
       | CVs(Abs(x,M)) capt k    = CVs x capt (fn c => CVs M c k)
       | CVs(TAbs(a,M)) capt k   = CVts (TyFv a) capt (fn c => CVs M c k)
       | CVs(t as Clos _) capt k = CVs (push_clos t) capt k
       | CVs tm capt k = k capt
     and CVps (GRND ty) capt k = CVts ty capt k
       | CVps (POLY ty) capt k = CVts ty capt k
     and CVts (v as TyFv (n,_,_)) capt k =
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
       | CVts (TyApp(Opr,A)) capt k = CVts Opr capt (fn c => CVts A c k)
       | CVts (TyAll(bv,B)) capt k  = CVts B capt k
       | CVts (TyAbs(bv,B)) capt k  = CVts B capt k
       | CVts ty capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v,i)::rst) =
           let val (n,kd,rk) = dest_vartype_opr v
               val n' = variantAV n
               val v' = mk_vartype_opr(n',kd,rk)
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     fun unbind (Fv(n,Ty)) j k        = unbindt Ty j (fn ty => k(Fv(n,ty)))
       | unbind (Const(n,Ty)) j k     = unbindp Ty j (fn ty => k(Const(n,ty)))
       | unbind (Comb(M,N)) j k       = unbind M j (fn m =>
                                        unbind N j (fn n => k(Comb(m,n))))
       | unbind (TComb(M,Ty)) j k     = unbind M j (fn m =>
                                        unbindt Ty j (fn ty => k(TComb(m,ty))))
       | unbind (Abs(V,M)) j k        = unbind V j (fn v =>
                                        unbind M j (fn m => k(Abs(v,m))))
       | unbind (TAbs(a,M)) j k       = unbind M (j+1) (fn q => k(TAbs(a,q)))
       | unbind (t as Clos _) j k     = unbind (push_clos t) j k
       | unbind tm j k = k tm
     and unbindp (GRND ty) j k        = unbindt ty j (fn q => k(GRND q))
       | unbindp (POLY ty) j k        = unbindt ty j (fn q => k(POLY q))
     and unbindt (v as TyBv i) j k   = k (vmap(i-j) handle Subscript => v)
       | unbindt (TyApp(Opr,A))j k   = unbindt Opr j (fn opr =>
                                       unbindt A j (fn a => k(TyApp(opr,a))))
       | unbindt (TyAll(a,B)) j k    = unbindt B (j+1) (fn q => k(TyAll(a,q)))
       | unbindt (TyAbs(a,B)) j k    = unbindt B (j+1) (fn q => k(TyAll(a,q)))
       | unbindt ty j k = k ty
 in
     unclash insertAVprefix (List.rev dupls)
   ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
   ; (array_to_revlist prefix, unbind body 0 I)
 end
 end
end;

val strip_tyabs = strip_tybinder NONE;

local exception CLASH
val variant_tyvar = Type.variant_tyvar
val type_vars = Type.type_vars
in
fun dest_tyabs(TAbs(Bvar as (Name,Arity,Rank), Body)) =
    let fun dest (Fv(Name,Ty)) i        = Fv(Name, destty Ty i)
          | dest (Const(Name,Ty)) i     = Const(Name, destpty Ty i)
          | dest (Comb(Rator,Rand)) i   = Comb(dest Rator i, dest Rand i)
          | dest (TComb(Rator,Ty)) i    = TComb(dest Rator i, destty Ty i)
          | dest (Abs(Bvar,Body)) i     = Abs(dest Bvar i, dest Body i)
          | dest (TAbs(Bvar,Body)) i    = TAbs(Bvar, dest Body (i+1))
          | dest (t as Clos _) i        = dest (push_clos t) i
          | dest tm _ = tm
        and destpty (GRND ty) i         = GRND (destty ty i)
          | destpty (POLY ty) i         = POLY (destty ty i)
        and destty (v as TyBv j) i      = if i=j then TyFv Bvar else v
          | destty (v as TyFv(s,_,_)) i = if Name=s then raise CLASH else v
          | destty (TyApp(opr,arg)) i   = TyApp(destty opr i, destty arg i)
          | destty (TyAll(bv,Body)) i   = TyAll(bv, destty Body (i+1))
          | destty (TyAbs(bv,Body)) i   = TyAbs(bv, destty Body (i+1))
          | destty opr _ = opr (* constant *)
    in (TyFv Bvar, dest Body 0)
       handle CLASH =>
              dest_tyabs(TAbs(variant_tyvar (type_vars (type_of Body)) Bvar,
                              Body))
    end
  | dest_tyabs (t as Clos _) = dest_tyabs (push_clos t)
  | dest_tyabs _ = raise ERR "dest_tyabs" "not a type abstraction"
end;

fun break_abs(Abs(_,Body)) = Body
  | break_abs(t as Clos _) = break_abs (push_clos t)
  | break_abs _ = raise ERR "break_abs" "not an abstraction";

fun break_tyabs(TAbs(_,Body)) = Body
  | break_tyabs(t as Clos _) = break_abs (push_clos t)
  | break_tyabs _ = raise ERR "break_tyabs" "not a type abstraction";



fun dest_thy_const (Const(id,ty)) =
      let val (name,thy) = dest_id id
      in {Thy=thy, Name=name, Ty=to_hol_type ty}
      end
  | dest_thy_const _ = raise ERR"dest_thy_const" "not a const"

fun break_const (Const p) = (I##to_hol_type) p
  | break_const _ = raise ERR "break_const" "not a const"

fun dest_const (Const(id,ty)) = (name_of id, to_hol_type ty)
  | dest_const _ = raise ERR "dest_const" "not a const"

(*---------------------------------------------------------------------------
               Derived destructors
 ---------------------------------------------------------------------------*)

fun rator (Comb(Rator,_)) = Rator
  | rator (Clos(Env, Comb(Rator,_))) = mk_clos(Env,Rator)
  | rator _ = raise ERR "rator" "not a comb"

fun rand (Comb(_,Rand)) = Rand
  | rand (Clos(Env, Comb(_,Rand))) = mk_clos(Env,Rand)
  | rand _ = raise ERR "rand" "not a comb"

val bvar = fst o dest_abs;
val body = snd o dest_abs;


(*---------------------------------------------------------------------------
    Matching (first order, modulo alpha conversion) of terms, including
    sets of variables and type variables to avoid binding.
 ---------------------------------------------------------------------------*)

local
  fun MERR s = raise ERR "raw_match_term error" s
  fun free (Bv i) n             = i<n
    | free (Comb(Rator,Rand)) n = free Rand n andalso free Rator n
    | free (TComb(Rator,Ty)) n  = free Rator n
    | free (Abs(_,Body)) n      = free Body (n+1)
    | free (TAbs(_,Body)) n     = free Body n
    | free (t as Clos _) n      = free (push_clos t) n
    | free _ _ = true
  fun lookup x ids =
   let fun look [] = if HOLset.member(ids,x) then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
  fun bound_by_scope scoped M = if scoped then not (free M 0) else false
  val tymatch = Type.raw_match_type
in
fun RM [] theta = theta
  | RM (((v as Fv(_,Ty)),tm,scoped)::rst) ((S1 as (tmS,Id)),tyS)
     = if bound_by_scope scoped tm
       then MERR "variable bound by scope"
       else RM rst
            ((case lookup v Id tmS
               of NONE => if aconv v tm (* can't use = because of aconv_ty *)
                                  then (tmS,HOLset.add(Id,v))
                                  else ((v |-> tm)::tmS,Id)
                | SOME tm' => if aconv tm' tm then S1
                              else MERR "double bind on variable"),
             tymatch Ty (type_of tm) tyS)
  | RM ((Const(c1,ty1),Const(c2,ty2),_)::rst) (tmS,tyS)
      = RM rst
        (if c1 <> c2 then MERR "different constants" else
         case (ty1,ty2)
          of (GRND _,  POLY _)   => MERR"ground const vs. polymorphic const"
           | (GRND pat,GRND obj) => if aconv_ty pat obj then (tmS,tyS)
                       else MERR"const-const with different (ground) types"
           | (POLY pat,GRND obj) => (tmS, tymatch pat obj tyS)
           | (POLY pat,POLY obj) => (tmS, tymatch pat obj tyS))
  | RM ((Abs(Fv(_,ty1),M),Abs(Fv(_,ty2),N),_)::rst) (tmS,tyS)
      = RM ((M,N,true)::rst) (tmS, tymatch ty1 ty2 tyS)
  | RM ((TAbs((_,k1,r1),M), TAbs((_,k2,r2),N), s)::rst) S
      = if k1=k2 andalso r1=r2 then RM ((M,N,true)::rst) S
        else MERR "different type abstractions"
  | RM ((Comb(M,N),Comb(P,Q),s)::rst) S = RM ((M,P,s)::(N,Q,s)::rst) S
  | RM ((TComb(M,ty1),TComb(N,ty2),s)::rst) (tmS,tyS)
      = RM ((M,N,s)::rst) (tmS, tymatch ty1 ty2 tyS)
  | RM ((Bv i,Bv j,_)::rst) S  = if i=j then RM rst S
                                 else MERR "Bound var. depth"
  | RM (((pat as Clos _),ob,s)::t) S = RM ((push_clos pat,ob,s)::t) S
  | RM ((pat,(ob as Clos _),s)::t) S = RM ((pat,push_clos ob,s)::t) S
  | RM all others                    = MERR "different constructors"
end

fun raw_match tyfixed tmfixed pat ob (tmS,tyS)
   = RM [(pat,ob,false)] ((tmS,tmfixed), (tyS,tyfixed));

fun norm_subst ((tmS,_),(tyS,_)) =
 let val Theta = inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if residue=redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS,tyS)
 end

fun match_terml tyfixed tmfixed pat ob =
 norm_subst (raw_match tyfixed tmfixed pat ob ([],[]))

val match_term = match_terml [] empty_varset;

(*---------------------------------------------------------------------------
       Must know that ty is the type of tm1 and tm2.
 ---------------------------------------------------------------------------*)

fun prim_mk_eq ty tm1 tm2 = Comb(Comb(inst [Type.alpha |-> ty] eqc, tm1), tm2)

(*---------------------------------------------------------------------------
      Must know that tm1 and tm2 both have type "bool"
 ---------------------------------------------------------------------------*)

fun prim_mk_imp tm1 tm2  = Comb(Comb(imp, tm1),tm2);

(*---------------------------------------------------------------------------
      Take an equality apart, and return the type of the operands
 ---------------------------------------------------------------------------*)

local val err = ERR "dest_eq_ty" ""
in
fun dest_eq_ty t =
 let val ((c,M),N) = with_exn ((dest_comb##I) o dest_comb) t err
 in if same_const c eqc
       then (M,N,fst(Type.dom_rng (type_of c)))
       else raise err
 end
end;

(*---------------------------------------------------------------------------
   Full propagation of substitutions.
 ---------------------------------------------------------------------------*)

local val subs_comp = pair_comp
  fun vars_sigma_norm (s, t) =
    case t of
      Comb(Rator,Rand) => Comb(vars_sigma_norm(s, Rator),
                               vars_sigma_norm(s, Rand))
    | TComb(Rator,Ty) => TComb(vars_sigma_norm(s, Rator), Ty)
    | Bv i =>
        (case Subst.exp_rel(s,i) of
           (0, SOME v)   => vars_sigma_norm (Subst.id, v)
         | (lams,SOME v) => vars_sigma_norm (Subst.shift(lams,Subst.id),v)
         | (lams,NONE)   => Bv lams)
    | Fv _ => t
    | Const _ => t
    | Abs(Bvar,Body) => Abs(Bvar, vars_sigma_norm (Subst.lift(1,s),
                                                   Body))
    | TAbs(Bvar,Body) => TAbs(Bvar,
                        vars_sigma_norm (s, Body))
    | Clos(Env,Body) => vars_sigma_norm (subs_comp(s,Env), Body)
in
fun norm_clos tm = vars_sigma_norm(Subst.id,tm)
end

(*---------------------------------------------------------------------------*
 * Traverse a term, performing a given (side-effecting) operation at the     *
 * leaves. For our purposes, bound variables can be ignored.                 *
 *---------------------------------------------------------------------------*)

fun trav f =
  let fun trv (a as Fv _) = f a
        | trv (a as Const _) = f a
        | trv (Comb(Rator,Rand)) = (trv Rator; trv Rand)
        | trv (TComb(Rator,Ty))  =  trv Rator
        | trv (Abs(Bvar,Body))   = (trv Bvar; trv Body)
        | trv (TAbs(Bvar,Body))  =  trv Body
        | trv (t as Clos _)      =  trv (push_clos t)
        | trv _ = ()
  in
    trv o norm_clos
  end;

(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for terms.                                      *
 *---------------------------------------------------------------------------*)

val dot     = "."
val dollar  = "$"
val percent = "%";

fun pp_raw_term index pps tm =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pp (Abs(Bvar,Body)) =
          ( add_string "(\\";
            pp Bvar; add_string dot; add_break(1,0);
            pp Body; add_string ")" )
      | pp (TAbs((name,kind,rank),Body)) =
         ( add_string "(\\:";
           add_string name; add_string dot; add_break(1,0);
           pp Body; add_string ")" )
      | pp (Comb(Rator,Rand)) =
         ( add_string "("; pp Rator; add_break(1,0);
                           pp Rand; add_string ")")
      | pp (TComb(Rator,Ty)) =
         ( add_string "("; pp Rator; add_break(1,0);
                           add_string "[type]";
                           add_string ")" )
      | pp (Bv i) = add_string (dollar^Lib.int_to_string i)
      | pp a      = add_string (percent^Lib.int_to_string (index a))
 in
   begin_block INCONSISTENT 0;
   add_string "`";
   pp (norm_clos tm);
   add_string "`";
   end_block()
 end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to a string                            *)
(*---------------------------------------------------------------------------*)

fun sprint pp x = PP.pp_to_string 72 pp x

val term_to_string = sprint (pp_raw_term (fn t => ~1));

(*
val _ = installPP Kind.pp_kind;
val _ = installPP pp_raw_type;
val _ = installPP (pp_raw_term (fn t => ~1));
*)

(* Tests:

val tm0 = mk_var("x", alpha);
val tm1 = mk_abs(tm0, tm0);
val tm2 = mk_tyabs(alpha, tm1);
val (ty1,tm3) = dest_tyabs tm2;
val tm4 = mk_tyabs(alpha, tm2);
val (tys, tm5) = strip_tyabs tm4;

*)

end (* Term *)
