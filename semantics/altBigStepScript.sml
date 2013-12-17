(*Generated by Lem from altBigStep.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasives_extraTheory libTheory astTheory semanticPrimitivesTheory bigStepTheory;

val _ = numLib.prefer_num();



val _ = new_theory "altBigStep"

(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ast*) 
(*open import SemanticPrimitives*)
(*import BigStep*)

(* A version of the big-step expression semantics that does not store module
and constructor environments in closures.  It is equivalent to the normal one
for well-typed programs. *)

(*
type v' =
  | Litv' of lit
  (* Constructor application. *)
  | Conv' of maybe (id conN) * list v' 
  (* Function closures
     The environment is used for the free variables in the function *)
  | Closure' of env varN v' * varN * exp
  (* Function closure for recursive functions
   * See Closure and Letrec above
   * The last variable name indicates which function from the mutually
   * recursive bundle this closure value represents *)
  | Recclosure' of list (varN * varN * exp) * varN
  | Loc' of nat

type envE' = env varN v'

(* The bindings of a module *)
type envM' = env modN envE'

indreln [evaluate' : bool -> envM -> envC -> BigStep.count_store -> envE -> exp -> BigStep.count_store * result v' -> bool]
and [evaluate_list' : bool -> envM -> envC -> BigStep.count_store -> envE -> list exp -> BigStep.count_store * result (list v') -> bool]
and [evaluate_match' : bool -> envM -> envC -> BigStep.count_store -> envE -> v' -> list (pat * exp) -> v' -> BigStep.count_store * result v' -> bool]

lit : forall ck menv cenv env l s.
true
==>
evaluate' ck menv cenv s env (Lit l) (s, Rval (Litv l))

and

raise1 : forall ck menv cenv env e s1 s2 v.
evaluate' ck menv cenv s1 env e (s2, Rval v)
==>
evaluate' ck menv cenv s1 env (Raise e) (s2, Rerr (Rraise v))

and

raise2 : forall ck menv cenv env e s1 s2 err.
evaluate' ck menv cenv s1 env e (s2, Rerr err)
==>
evaluate' ck menv cenv s1 env (Raise e) (s2, Rerr err)

and

handle1 : forall ck menv cenv s1 s2 env e v pes.
evaluate' ck menv cenv s1 env e (s2, Rval v)
==>
evaluate' ck menv cenv s1 env (Handle e pes) (s2, Rval v)

and

handle2 : forall ck menv cenv s1 s2 env e pes v bv.
evaluate' ck menv cenv s1 env e (s2, Rerr (Rraise v)) &&
evaluate_match' ck menv cenv s2 env v pes v bv
==>
evaluate' ck menv cenv s1 env (Handle e pes) bv

and

handle3 : forall ck menv cenv s1 s2 env e pes err.
evaluate' ck menv cenv s1 env e (s2, Rerr err) &&
(err = Rtimeout_error || (err = Rtype_error))
==>
evaluate' ck menv cenv s1 env (Handle e pes) (s2, Rerr err)

and

con1 : forall ck menv cenv env cn es vs s s'.
do_con_check cenv cn (List.length es) &&
evaluate_list' ck menv cenv s env es (s', Rval vs)
==>
evaluate' ck menv cenv s env (Con cn es) (s', Rval (Conv cn vs))

and

con2 : forall ck menv cenv env cn es s.
not (do_con_check cenv cn (List.length es))
==>
evaluate' ck menv cenv s env (Con cn es) (s, Rerr Rtype_error)

and

con3 : forall ck menv cenv env cn es err s s'.
do_con_check cenv cn (List.length es) &&
evaluate_list' ck menv cenv s env es (s', Rerr err)
==>
evaluate' ck menv cenv s env (Con cn es) (s', Rerr err)

and

var1 : forall ck menv cenv env n v s.
(lookup_var_id n menv env = Just v)
==>
evaluate' ck menv cenv s env (Var n) (s, Rval v)

and

var2 : forall ck menv cenv env n s.
(lookup_var_id n menv env = Nothing)
==>
evaluate' ck menv cenv s env (Var n) (s, Rerr Rtype_error)

and

fn : forall ck menv cenv env n e s.
true
==>
evaluate' ck menv cenv s env (Fun n e) (s, Rval (Closure env n e))

and

uapp1 : forall ck menv cenv env uop e v v' s1 s2 count s3.
evaluate' ck menv cenv s1 env e ((count,s2), Rval v) &&
(do_uapp s2 uop v = Just (s3,v'))
==>
evaluate' ck menv cenv s1 env (Uapp uop e) ((count,s3), Rval v')

and

uapp2 : forall ck menv cenv env uop e v s1 s2 count.
evaluate' ck menv cenv s1 env e ((count,s2), Rval v) &&
(do_uapp s2 uop v = Nothing)
==>
evaluate' ck menv cenv s1 env (Uapp uop e) ((count,s2), Rerr Rtype_error)

and

uapp3 : forall ck menv cenv env uop e err s s'.
evaluate' ck menv cenv s env e (s', Rerr err)
==>
evaluate' ck menv cenv s env (Uapp uop e) (s', Rerr err)

and

app1 : forall ck menv cenv env op e1 e2 v1 v2 env' e3 bv s1 s2 s3 count s4.
evaluate' ck menv cenv s1 env e1 (s2, Rval v1) &&
evaluate' ck menv cenv s2 env e2 ((count,s3), Rval v2) &&
do_app' s3 env op v1 v2 = Just (s4, env', e3) &&
((ck && (op = Opapp)) --> count <> 0) &&
evaluate' ck menv cenv ((if ck then BigStep.dec_count op count else count),s4) env' e3 bv
==>
evaluate' ck menv cenv s1 env (App op e1 e2) bv

and

app2 : forall ck menv cenv env op e1 e2 v1 v2 env' e3 s1 s2 s3 count s4.
evaluate' ck menv cenv s1 env e1 (s2, Rval v1) &&
evaluate' ck menv cenv s2 env e2 ((count,s3), Rval v2) &&
do_app' s3 env op v1 v2 = Just (s4, env', e3) &&
count = 0 &&
op = Opapp &&
ck
==>
evaluate' ck menv cenv s1 env (App op e1 e2) ((0,s4), Rerr Rtimeout_error)

and

app3 : forall ck menv cenv env op e1 e2 v1 v2 s1 s2 s3 count.
evaluate' ck menv cenv s1 env e1 (s2, Rval v1) &&
evaluate' ck menv cenv s2 env e2 ((count,s3), Rval v2) &&
do_app' s3 env op v1 v2 = Nothing
==>
evaluate' ck menv cenv s1 env (App op e1 e2) ((count,s3), Rerr Rtype_error)

and

app4 : forall ck menv cenv env op e1 e2 v1 err s1 s2 s3.
evaluate' ck menv cenv s1 env e1 (s2, Rval v1) &&
evaluate' ck menv cenv s2 env e2 (s3, Rerr err)
==>
evaluate' ck menv cenv s1 env (App op e1 e2) (s3, Rerr err)

and

app5 : forall ck menv cenv env op e1 e2 err s s'.
evaluate' ck menv cenv s env e1 (s', Rerr err)
==>
evaluate' ck menv cenv s env (App op e1 e2) (s', Rerr err)

and

log1 : forall ck menv cenv env op e1 e2 v e' bv s1 s2.
evaluate' ck menv cenv s1 env e1 (s2, Rval v) &&
do_log op v e2 = Just e' &&
evaluate' ck menv cenv s2 env e' bv
==>
evaluate' ck menv cenv s1 env (Log op e1 e2) bv

and

log2 : forall ck menv cenv env op e1 e2 v s1 s2.
evaluate' ck menv cenv s1 env e1 (s2, Rval v) &&
(do_log op v e2 = Nothing)
==>
evaluate' ck menv cenv s1 env (Log op e1 e2) (s2, Rerr Rtype_error)

and

log3 : forall ck menv cenv env op e1 e2 err s s'.
evaluate' ck menv cenv s env e1 (s', Rerr err)
==>
evaluate' ck menv cenv s env (Log op e1 e2) (s', Rerr err)

and

if1 : forall ck menv cenv env e1 e2 e3 v e' bv s1 s2.
evaluate' ck menv cenv s1 env e1 (s2, Rval v) &&
do_if v e2 e3 = Just e' &&
evaluate' ck menv cenv s2 env e' bv
==>
evaluate' ck menv cenv s1 env (If e1 e2 e3) bv

and

if2 : forall ck menv cenv env e1 e2 e3 v s1 s2.
evaluate' ck menv cenv s1 env e1 (s2, Rval v) &&
(do_if v e2 e3 = Nothing)
==>
evaluate' ck menv cenv s1 env (If e1 e2 e3) (s2, Rerr Rtype_error)

and

if3 : forall ck menv cenv env e1 e2 e3 err s s'.
evaluate' ck menv cenv s env e1 (s', Rerr err)
==>
evaluate' ck menv cenv s env (If e1 e2 e3) (s', Rerr err)

and

mat1 : forall ck menv cenv env e pes v bv s1 s2.
evaluate' ck menv cenv s1 env e (s2, Rval v) &&
evaluate_match' ck menv cenv s2 env v pes (Conv (Just (Short "Bind")) []) bv
==>
evaluate' ck menv cenv s1 env (Mat e pes) bv

and

mat2 : forall ck menv cenv env e pes err s s'.
evaluate' ck menv cenv s env e (s', Rerr err)
==>
evaluate' ck menv cenv s env (Mat e pes) (s', Rerr err)

and

let1 : forall ck menv cenv env n e1 e2 v bv s1 s2.
evaluate' ck menv cenv s1 env e1 (s2, Rval v) &&
evaluate' ck menv cenv s2 (bind n v env) e2 bv
==>
evaluate' ck menv cenv s1 env (Let n e1 e2) bv

and

let2 : forall ck menv cenv env n e1 e2 err s s'.
evaluate' ck menv cenv s env e1 (s', Rerr err)
==>
evaluate' ck menv cenv s env (Let n e1 e2) (s', Rerr err)

and

letrec1 : forall ck menv cenv env funs e bv s.
all_distinct (List.map (fun (x,y,z) -> x) funs) &&
evaluate' ck menv cenv s (build_rec_env funs env env) e bv
==>
evaluate' ck menv cenv s env (Letrec funs e) bv

and

letrec2 : forall ck menv cenv env funs e s.
not (all_distinct (List.map (fun (x,y,z) -> x) funs))
==>
evaluate' ck menv cenv s env (Letrec funs e) (s, Rerr Rtype_error)

and

empty : forall ck menv cenv env s.
true
==>
evaluate_list' ck menv cenv s env [] (s, Rval [])

and

cons1 : forall ck menv cenv env e es v vs s1 s2 s3.
evaluate' ck menv cenv s1 env e (s2, Rval v) &&
evaluate_list' ck menv cenv s2 env es (s3, Rval vs)
==>
evaluate_list' ck menv cenv s1 env (e::es) (s3, Rval (v::vs))

and

cons2 : forall ck menv cenv env e es err s s'.
evaluate' ck menv cenv s env e (s', Rerr err)
==>
evaluate_list' ck menv cenv s env (e::es) (s', Rerr err)

and

cons3 : forall ck menv cenv env e es v err s1 s2 s3.
evaluate' ck menv cenv s1 env e (s2, Rval v) &&
evaluate_list' ck menv cenv s2 env es (s3, Rerr err)
==>
evaluate_list' ck menv cenv s1 env (e::es) (s3, Rerr err)

and

mat_empty : forall ck menv cenv env v err_v s.
true
==>
evaluate_match' ck menv cenv s env v [] err_v (s, Rerr (Rraise err_v))

and

mat_cons1 : forall ck menv cenv env v p e pes env' bv err_v s count.
all_distinct (pat_bindings p []) &&
(pmatch cenv s p v env = Match env') &&
evaluate' ck menv cenv (count,s) env' e bv
==>
evaluate_match' ck menv cenv (count,s) env v ((p,e)::pes) err_v bv

and

mat_cons2 : forall ck menv cenv env v p e pes bv s count err_v.
all_distinct (pat_bindings p []) &&
(pmatch cenv s p v env = No_match) &&
evaluate_match' ck menv cenv (count,s) env v pes err_v bv
==>
evaluate_match' ck menv cenv (count,s) env v ((p,e)::pes) err_v bv

and

mat_cons3 : forall ck menv cenv env v p e pes s count err_v.
(pmatch cenv s p v env = Match_type_error)
==>
evaluate_match' ck menv cenv (count,s) env v ((p,e)::pes) err_v ((count,s), Rerr Rtype_error)

and

mat_cons4 : forall ck menv cenv env v p e pes s err_v.
not (all_distinct (pat_bindings p []))
==>
evaluate_match' ck menv cenv s env v ((p,e)::pes) err_v (s, Rerr Rtype_error)


indreln [evaluate_dec' : maybe modN -> envM -> envC -> store -> envE -> dec -> store * result (envC * envE) -> bool]

dlet1 : forall mn menv cenv env p e v env' s1 s2 count.
evaluate' false menv cenv (0,s1) env e ((count,s2), Rval v) &&
all_distinct (pat_bindings p []) &&
(pmatch cenv s2 p v emp = Match env')
==>
evaluate_dec' mn menv cenv s1 env (Dlet p e) (s2, Rval (emp, env'))

and

dlet2 : forall mn menv cenv env p e v s1 s2 count.
evaluate' false menv cenv (0,s1) env e ((count,s2), Rval v) &&
all_distinct (pat_bindings p []) &&
(pmatch cenv s2 p v emp = No_match)
==>
evaluate_dec' mn menv cenv s1 env (Dlet p e) (s2, Rerr (Rraise (Conv (Just (Short "Bind")) [])))

and

dlet3 : forall mn menv cenv env p e v s1 s2 count.
evaluate' false menv cenv (0,s1) env e ((count,s2), Rval v) &&
all_distinct (pat_bindings p []) &&
(pmatch cenv s2 p v emp = Match_type_error)
==>
evaluate_dec' mn menv cenv s1 env (Dlet p e) (s2, Rerr Rtype_error)

and

dlet4 : forall mn menv cenv env p e s.
not (all_distinct (pat_bindings p []))
==>
evaluate_dec' mn menv cenv s env (Dlet p e) (s, Rerr Rtype_error)

and

dlet5 : forall mn menv cenv env p e err s count s'.
evaluate' false menv cenv (0,s) env e ((count,s'), Rerr err) &&
all_distinct (pat_bindings p [])
==>
evaluate_dec' mn menv cenv s env (Dlet p e) (s', Rerr err)

and

dletrec1 : forall mn menv cenv env funs s.
all_distinct (List.map (fun (x,y,z) -> x) funs)
==>
evaluate_dec' mn menv cenv s env (Dletrec funs) (s, Rval (emp, build_rec_env funs env emp))

and

dletrec2 : forall mn menv cenv env funs s.
not (all_distinct (List.map (fun (x,y,z) -> x) funs))
==>
evaluate_dec' mn menv cenv s env (Dletrec funs) (s, Rerr Rtype_error)

and

dtype1 : forall mn menv cenv env tds s.
check_dup_ctors mn cenv tds
==>
evaluate_dec' mn menv cenv s env (Dtype tds) (s, Rval (build_tdefs mn tds, emp))

and

dtype2 : forall mn menv cenv env tds s.
not (check_dup_ctors mn cenv tds)
==>
evaluate_dec' mn menv cenv s env (Dtype tds) (s, Rerr Rtype_error)

and

dexn1 : forall mn menv cenv env cn ts s.
(lookup (mk_id mn cn) cenv = Nothing)
==>
evaluate_dec' mn menv cenv s env (Dexn cn ts) (s, Rval (bind (mk_id mn cn) (List.length ts, TypeExn) emp, emp))

and

dexn2 : forall mn menv cenv env cn ts s.
(lookup (mk_id mn cn) cenv <> Nothing)
==>
evaluate_dec' mn menv cenv s env (Dexn cn ts) (s, Rerr Rtype_error)

indreln [evaluate_decs' : maybe modN -> envM -> envC -> store -> envE -> list dec -> store * envC * result envE -> bool]

empty : forall mn menv cenv s env.
true
==>
evaluate_decs' mn menv cenv s env [] (s, emp, Rval emp)

and

cons1 : forall mn menv cenv s1 s2 env d ds e.
evaluate_dec' mn menv cenv s1 env d (s2, Rerr e)
==>
evaluate_decs' mn menv cenv s1 env (d::ds) (s2, emp, Rerr e)

and

cons2 : forall mn menv cenv s1 s2 s3 env d ds new_tds' new_tds new_env r.
evaluate_dec' mn menv cenv s1 env d (s2, Rval (new_tds,new_env)) &&
evaluate_decs' mn menv (merge new_tds cenv) s2 (merge new_env env) ds (s3, new_tds', r)
==>
evaluate_decs' mn menv cenv s1 env (d::ds) (s3, merge new_tds' new_tds, combine_dec_result new_env r)

indreln [evaluate_top' : envM -> envC -> store -> envE -> top -> store * envC * result (envM * envE) -> bool]


tdec1 : forall menv cenv s1 s2 env d new_tds new_env.
evaluate_dec' Nothing menv cenv s1 env d (s2, Rval (new_tds, new_env))
==>
evaluate_top' menv cenv s1 env (Tdec d) (s2, new_tds, Rval (emp, new_env))

and

tdec2 : forall menv cenv s1 s2 env d err.
evaluate_dec' Nothing menv cenv s1 env d (s2, Rerr err)
==>
evaluate_top' menv cenv s1 env (Tdec d) (s2, emp, Rerr err)

and

tmod1 : forall menv cenv s1 s2 env ds mn specs new_tds new_env. 
not (elem mn (List.map fst menv)) &&
evaluate_decs' (Just mn) menv cenv s1 env ds (s2, new_tds, Rval new_env)
==>
evaluate_top' menv cenv s1 env (Tmod mn specs ds) (s2, new_tds, Rval ([(mn,new_env)], emp))

and

tmod2 : forall menv cenv s1 s2 env ds mn specs new_tds err. 
not (elem mn (List.map fst menv)) &&
evaluate_decs' (Just mn) menv cenv s1 env ds (s2, new_tds, Rerr err)
==>
evaluate_top' menv cenv s1 env (Tmod mn specs ds) (s2, new_tds, Rerr err)

and

tmod3 : forall menv cenv s env mn specs ds.
elem mn (List.map fst menv)
==>
evaluate_top' menv cenv s env (Tmod mn specs ds) (s, emp, Rerr Rtype_error)

indreln [evaluate_prog' : envM -> envC -> store -> envE -> prog -> store * envC * result (envM * envE) -> bool]

empty : forall menv cenv s env.
true
==>
evaluate_prog' menv cenv s env [] (s, emp, Rval (emp, emp))

and

cons1 : forall menv cenv s1 s2 s3 env top tops new_mods new_tds new_tds' new_env r.
evaluate_top' menv cenv s1 env top (s2, new_tds, Rval (new_mods,new_env)) &&
evaluate_prog' (merge new_mods menv) (merge new_tds cenv) s2 (merge new_env env) tops (s3, new_tds', r)
==>
evaluate_prog' menv cenv s1 env (top::tops) (s3, merge new_tds' new_tds, combine_mod_result new_mods new_env r)

and

cons2 : forall menv cenv s1 s2 env top tops err new_tds.
evaluate_top' menv cenv s1 env top (s2, new_tds, Rerr err)
==>
evaluate_prog' menv cenv s1 env (top::tops) (s2, new_tds, Rerr err)
*)
val _ = export_theory()
