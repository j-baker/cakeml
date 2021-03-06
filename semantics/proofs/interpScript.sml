open preamble;
open monadsyntax;
open semanticPrimitivesTheory bigStepTheory;
open terminationTheory;
open evalPropsTheory determTheory bigClockTheory;

val _ = new_theory "interp";

val run_eval_spec_lem = Q.prove (
`?run_eval run_eval_list run_eval_match.
  (!env e st. 
    evaluate T env st e (run_eval env e st)) ∧
  (!env es st.
    evaluate_list T env st es (run_eval_list env es st)) ∧
  (!env v pes err_v st.
    evaluate_match T env st v pes err_v (run_eval_match env v pes err_v st))`,
 simp [METIS_PROVE [] ``(?x y z. P x ∧ Q y ∧ R z) = ((?x. P x) ∧ (?y. Q y) ∧ (?z. R z))``,
       GSYM SKOLEM_THM] >>
 strip_tac
 >- metis_tac [big_clocked_total, pair_CASES] >> 
 strip_tac 
 >- (induct_on `es` >>
     rw [Once evaluate_cases] >>
     `?count' s' r. evaluate T env st h ((count',s'),r)` by metis_tac [big_clocked_total, pair_CASES] >>
     metis_tac [pair_CASES, result_nchotomy]) >>
 strip_tac
 >- (induct_on `pes` >>
     rw [Once evaluate_cases] >>
     `(?count s. st = (count,s)) ∧ (?p e. h = (p,e))` by metis_tac [pair_CASES] >>
     rw [] >>
     `?menv cenv env'. env = (menv,cenv,env')` by (PairCases_on `env` >> metis_tac [])>>
     rw [] >>
     cases_on `pmatch cenv s p v env'` >>
     rw []
     >- metis_tac []
     >- metis_tac []
     >- (`?count'' s' r. evaluate T (menv,cenv,a) (count',s) e ((count'',s'),r)` by metis_tac [big_clocked_total, pair_CASES] >>
         metis_tac [])));

val run_eval_spec = 
 new_specification ("run_eval", ["run_eval", "run_eval_list", "run_eval_match"], run_eval_spec_lem);

val evaluate_run_eval = Q.store_thm ("evaluate_run_eval",
`!env e r st. 
  evaluate T env st e r 
  = 
  (run_eval env e st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val evaluate_run_eval_list = Q.store_thm ("evaluate_run_eval_list",
`!env es r st. 
  evaluate_list T env st es r 
  = 
  (run_eval_list env es st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val evaluate_run_eval_match = Q.store_thm ("evaluate_run_eval_match",
`!env v pes r err_v st. 
  evaluate_match T env st v pes err_v r 
  = 
  (run_eval_match env v pes err_v st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val _ = type_abbrev("M", ``:v count_store -> v count_store # ('a, v) result``);

val result_bind_def = Define `
(result_bind : α M -> (α -> β M) -> β M) x f =
  λs.
    case x s of
      (s, Rval v) => f v s
    | (s, Rerr err) => (s, Rerr err)`;

val result_return_def = Define `
(result_return (*: α -> (β, α, γ) M*)) x = 
  λs. (s, Rval x)`;

val result_raise_def = Define `
result_raise err = \s. (s, Rerr err)`;

val get_store_def = Define `
(get_store : v store M) = \(count,s). ((count,s), Rval s)`;

val set_store_def = Define `
(set_store : v store -> unit M) s = \(count,s'). ((count,s), Rval ())`;

val dec_clock_def = Define `
(dec_clock : unit M) = (\(count,s). if count = 0 then ((0,s), Rerr Rtimeout_error) else ((count - 1, s), Rval ()))`;

val _ = temp_overload_on ("monad_bind", ``result_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. result_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. result_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``result_return``);
val _ = temp_overload_on ("raise", ``result_raise``);

val remove_lambda_pair = Q.prove (
`((\(x,y). f x y) z) = f (FST z) (SND z)`,
PairCases_on `z` >>
rw []);

val fst_lem = Q.prove (
`FST = (\(x,y, z).x)`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
fs []);

val run_eval_def = Q.store_thm ("run_eval_def",
`(!st env l.
  run_eval env (Lit l)
  =
  return (Litv l)) ∧
 (!st env e.
  run_eval env (Raise e)
  =
  do v1 <- run_eval env e;
     raise (Rraise v1)
  od) ∧
 (!env e1 pes.
  run_eval env (Handle e1 pes)
  =
  (\st.
    case run_eval env e1 st of
        (st', Rerr (Rraise v)) =>
          run_eval_match env v pes v st'
      | (st', r) => (st',r))) ∧
 (!env cn es.
  run_eval env (Con cn es)
  =
  case cn of
      NONE =>
        do vs <- run_eval_list env es;
           return (Conv NONE vs)
        od
    | SOME n =>
       (case lookup_alist_mod_env n (all_env_to_cenv env) of
          | NONE => raise Rtype_error
          | SOME (l,t) =>
              if l = LENGTH es then
                do vs <- run_eval_list env es;
                   return (Conv (SOME (id_to_n n,t)) vs)
                od
              else
                raise Rtype_error)) ∧
 (!env n.
  run_eval env (Var n)
  =
  case lookup_var_id n env of
       NONE => raise Rtype_error
     | SOME v => return v) ∧
 (!env n e.
   run_eval env (Fun n e)
   =
   return (Closure env n e)) ∧
 (!env op e1 e2.
   run_eval env (App op es)
   =
   do vs <- run_eval_list env es;
      st <- get_store;
      if op = Opapp then
        case do_opapp vs of
        | NONE => raise Rtype_error
        | SOME (env', e3) =>
            do () <- dec_clock;
               run_eval env' e3
            od
      else
        case do_app st op vs of
        | NONE => raise Rtype_error
        | SOME (st',res) =>
          do () <- set_store st';
             combin$C return res
          od
   od) ∧
 (!env lop e1 e2.
   run_eval env (Log lop e1 e2)
   =
   do v1 <- run_eval env e1;
      case do_log lop v1 e2 of
           NONE => raise Rtype_error
         | SOME e' => run_eval env e'
   od) ∧
 (!env e1 e2 e3.
   run_eval env (If e1 e2 e3)
   =
   do v1 <- run_eval env e1;
      case do_if v1 e2 e3 of
           NONE => raise Rtype_error
         | SOME e' => run_eval env e'
   od) ∧
 (!env e pes.
   run_eval env (Mat e pes)
   =
   do v <- run_eval env e;
      run_eval_match env v pes (Conv (SOME ("Bind",TypeExn (Short "Bind"))) [])
   od) ∧
 (!env x e1 e2.
   run_eval env (Let x e1 e2)
   =
   do v1 <- run_eval env e1;
      run_eval (all_env_to_menv env, all_env_to_cenv env, opt_bind x v1 (all_env_to_env env)) e2
   od) ∧
 (!env funs e.
   run_eval env (Letrec funs e)
   =
   if ALL_DISTINCT (MAP FST funs) then
     run_eval (all_env_to_menv env, all_env_to_cenv env, build_rec_env funs env (all_env_to_env env)) e
   else
     raise Rtype_error) ∧
 (!env.
   run_eval_list env []
   =
   return []) ∧
 (!env e es.
   run_eval_list env (e::es)
   =
   do v <- run_eval env e;
      vs <- run_eval_list env es;
      return (v::vs)
   od) ∧
 (!env v err_v.
   run_eval_match env v [] err_v
   =
   raise (Rraise err_v)) ∧
 (!env v p e pes err_v.
   run_eval_match env v ((p,e)::pes) err_v
   =
   do st <- get_store;
      if ALL_DISTINCT (pat_bindings p []) then
        case pmatch (all_env_to_cenv env) st p v (all_env_to_env env) of
             Match_type_error => raise Rtype_error
           | No_match => run_eval_match env v pes err_v
           | Match env' => run_eval (all_env_to_menv env, all_env_to_cenv env, env') e
      else
        raise Rtype_error
   od)`,
 rw [GSYM evaluate_run_eval, FUN_EQ_THM, result_raise_def, result_return_def,
     result_bind_def, get_store_def, set_store_def] >>
 rw [Once evaluate_cases]
 >- (every_case_tac >>
     fs [GSYM evaluate_run_eval] >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     fs [do_con_check_def, build_conv_def] >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     PairCases_on `q` >>
     fs [] >>
     rw [] >>
     fs [GSYM evaluate_run_eval] >>
     metis_tac [])
 >- (rw [dec_clock_def] >>
     every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair] >>
     rw [] >>
     every_case_tac >>
     fs [GSYM evaluate_run_eval] >>
     rw [] >>
     fs [do_app_cases,do_opapp_cases] >>
     rw [] >> fs[state_transformerTheory.UNIT_DEF] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec,
                all_env_to_menv_def, all_env_to_cenv_def, all_env_to_env_def])
 >- metis_tac [fst_lem, run_eval_spec, all_env_to_menv_def, all_env_to_cenv_def,
               all_env_to_env_def, pair_CASES]
 >- metis_tac [fst_lem, run_eval_spec]
 >- (rw [GSYM evaluate_run_eval_list] >>
     rw [Once evaluate_cases])
 >- (every_case_tac >>
     rw [] >>
     fs [GSYM evaluate_run_eval_list, GSYM evaluate_run_eval] >>
     rw [Once evaluate_cases] >>
     metis_tac [])
 >- (rw [GSYM evaluate_run_eval_match] >>
     rw [Once evaluate_cases])
 >- (every_case_tac >>
     rw [] >>
     fs [GSYM evaluate_run_eval_match, GSYM evaluate_run_eval] >>
     rw [Once evaluate_cases] >>
     fs [] >>
     PairCases_on `x` >>
     fs [] >>
     metis_tac [fst_lem, run_eval_spec, all_env_to_menv_def, all_env_to_cenv_def,
               all_env_to_env_def, pair_CASES]));

val run_eval_dec_def = Define `
(run_eval_dec mn env (st,tdecs) (Dlet p e) =
  if ALL_DISTINCT (pat_bindings p []) then
    case run_eval env e st of
       | (st', Rval v) =>
           (case pmatch (all_env_to_cenv env) (SND st') p v [] of
              | Match env' => ((st',tdecs), Rval ([], env'))
              | No_match => ((st',tdecs), Rerr (Rraise (Conv (SOME ("Bind",TypeExn (Short "Bind"))) [])))
              | Match_type_error => ((st',tdecs), Rerr Rtype_error))
       | (st', Rerr e) => ((st',tdecs), Rerr e)
  else
    ((st,tdecs), Rerr Rtype_error)) ∧
(run_eval_dec mn env st (Dletrec funs) =
  if ALL_DISTINCT (MAP FST funs) then
    (st, Rval ([], build_rec_env funs env []))
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn env (st,tdecs) (Dtype tds) =
  let new_tdecs = set (MAP (\(tvs,tn,ctors). TypeId (mk_id mn tn)) tds) in
    if check_dup_ctors tds ∧ DISJOINT new_tdecs tdecs ∧ ALL_DISTINCT (MAP (\(tvs,tn,ctors). tn) tds) then
      ((st, new_tdecs ∪ tdecs), Rval (build_tdefs mn tds, []))
    else
      ((st,tdecs), Rerr Rtype_error)) ∧
(run_eval_dec mn env (st,tdecs) (Dtabbrev tvs tn t) =
  ((st,tdecs), Rval ([], []))) ∧
(run_eval_dec mn env (st,tdecs) (Dexn cn ts) =
  if TypeExn (mk_id mn cn) ∉ tdecs  then
    ((st, {TypeExn (mk_id mn cn)} ∪ tdecs), Rval ([(cn,(LENGTH ts, TypeExn (mk_id mn cn)))], []))
  else
    ((st,tdecs), Rerr Rtype_error))`;

val run_eval_decs_def = Define `
(run_eval_decs mn env st [] = (st, [], Rval [])) ∧
(run_eval_decs mn env st (d::ds) =
  case run_eval_dec mn env st d of
      (st', Rval (cenv',env')) =>
         (case run_eval_decs mn (all_env_to_menv env, merge_alist_mod_env ([],cenv') (all_env_to_cenv env), env' ++ all_env_to_env env) st' ds of
               (st'', cenv'', r) =>
                 (st'', cenv'' ++ cenv', combine_dec_result env' r))
    | (st',Rerr err) => (st',[],Rerr err))`;

val run_eval_top_def = Define `
(run_eval_top env (st,tdecls,mdecls) (Tdec d) = 
  case run_eval_dec NONE env (st,tdecls) d of
       ((st',tdecls'), Rval (cenv', env')) => ((st',tdecls',mdecls), ([],cenv'), Rval ([], env'))
     | ((st',tdecls'), Rerr err) => ((st',tdecls',mdecls), ([],[]), Rerr err)) ∧
(run_eval_top env (st,tdecls,mdecls) (Tmod mn specs ds) =
  if mn ∉ mdecls ∧ no_dup_types ds then
    case run_eval_decs (SOME mn) env (st,tdecls) ds of
         ((st',tdecls'), cenv', Rval env') => ((st',tdecls',{mn} ∪ mdecls),
         ([(mn,cenv')],[]), (Rval ([(mn, env')], [])))
       | ((st',tdecls'), cenv', Rerr err) => 
           ((st',tdecls',{mn} ∪ mdecls), ([(mn,cenv')],[]), Rerr err)
  else
    ((st,tdecls,mdecls), ([],[]), Rerr Rtype_error))`;

val run_eval_prog_def = Define `
(run_eval_prog env st [] = (st, ([],[]), Rval ([], []))) ∧
(run_eval_prog env st (top::prog) =
  case run_eval_top env st top of
       (st', cenv', Rval (menv', env')) =>
          (case run_eval_prog (menv' ++ all_env_to_menv env, merge_alist_mod_env cenv' (all_env_to_cenv env), env' ++ all_env_to_env env) st' prog of
              | (st'', cenv'', Rval (menv'', env'')) =>
                  (st'', merge_alist_mod_env cenv'' cenv', Rval (menv'' ++ menv', env'' ++ env'))
              | (st'', cenv'', Rerr err) => (st'', merge_alist_mod_env cenv'' cenv', Rerr err))
     | (st', cenv', Rerr err) => (st', cenv', Rerr err))`;

val run_eval_whole_prog_def = Define `
run_eval_whole_prog env st prog = 
  if no_dup_mods prog st ∧ no_dup_top_types prog st then
    run_eval_prog env st prog
  else
    (st,([],[]),Rerr Rtype_error)`;

val run_eval_dec_spec = Q.store_thm ("run_eval_dec_spec",
`!mn st tdecs env d st' tdecs' r.
  (run_eval_dec mn env (st,tdecs) d = ((st',tdecs'), r)) ⇒
  evaluate_dec T mn env (st,tdecs) d ((st',tdecs'), r)`,
 cases_on `d` >>
 rw [evaluate_dec_cases, run_eval_dec_def, fst_lem, LET_THM] >>
 every_case_tac >>
 fs [GSYM evaluate_run_eval] >>
 rw [type_defs_to_new_tdecs_def] >>
 metis_tac [big_clocked_unclocked_equiv, clocked_min_counter, SND, pair_CASES, result_distinct, result_11]);

val run_eval_decs_spec = Q.store_thm ("run_eval_decs_spec",
`!mn env st tdecs ds st' tdecs' cenv' r.
  (run_eval_decs mn env (st,tdecs) ds = ((st',tdecs'),cenv', r)) ⇒
  evaluate_decs T mn env (st,tdecs) ds ((st',tdecs'),cenv', r)`,
 induct_on `ds` >>
 rw [Once evaluate_decs_cases] >>
 fs [run_eval_decs_def] >>
 every_case_tac >>
 `?s tdecs. q = (s,tdecs)` by metis_tac [pair_CASES] >>
 rw [] >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] >>
 cases_on `r'''` >>
 fs [combine_dec_result_def] >>
 every_case_tac >>
 fs [] >>
 PairCases_on `env` >>
 fs [all_env_to_cenv_def, all_env_to_menv_def, all_env_to_env_def] >>
 rw []
 >- (MAP_EVERY qexists_tac [`s,tdecs''`, `q'''`, `q'`, `r'`, `Rval a`] >>
     rw [])
 >- (disj2_tac >>
     MAP_EVERY qexists_tac [`s,tdecs''`, `q'''`, `q'`, `r'`, `Rerr e`] >>
     rw []));

val run_eval_top_spec = Q.store_thm ("run_eval_top_spec",
`!st tdecs mdecs env top st' tdecs' mdecs' cenv' r.
  (run_eval_top env (st,tdecs,mdecs) top = ((st',tdecs',mdecs'),cenv', r)) ⇒
  evaluate_top T env (st,tdecs,mdecs) top ((st',tdecs',mdecs'), cenv', r)`,
 cases_on `top` >>
 rw [evaluate_top_cases, run_eval_top_def]  >>
 every_case_tac >>
 `?s tdecs. q = (s,tdecs)` by metis_tac [pair_CASES] >>
 rw [] >>
 imp_res_tac run_eval_decs_spec >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] >>
 metis_tac []);

val run_eval_prog_spec = Q.store_thm ("run_eval_prog_spec",
`!env st tdecs mdecs prog st' tdecs' mdecs' cenv' r.
  run_eval_prog env (st,tdecs,mdecs) prog = ((st',tdecs',mdecs'),cenv', r) ⇒
  evaluate_prog T env (st,tdecs,mdecs) prog ((st',tdecs',mdecs'),cenv', r)`,
 induct_on `prog` >>
 rw [run_eval_prog_def, Once evaluate_prog_cases] >>
 every_case_tac >>
 `?s tdecs mdecs. q = (s,tdecs,mdecs)` by metis_tac [pair_CASES] >>
 rw [] >>
 imp_res_tac run_eval_top_spec >>
 fs [] >>
 rw [] >>
 PairCases_on `env` >>
 fs [all_env_to_cenv_def, all_env_to_menv_def, all_env_to_env_def]
 >- (MAP_EVERY qexists_tac [`s,tdecs'',mdecs''`, `q''`, `q'`, `q''''`, `r'`, `Rval (q''''', r'')`] >>
     rw [combine_mod_result_def])
 >- (disj1_tac >>
     MAP_EVERY qexists_tac [`s,tdecs'',mdecs''`, `q''`, `q'`, `q''''`, `r'`, `Rerr e`] >>
     rw [combine_mod_result_def]));

val run_eval_whole_prog_spec = Q.store_thm ("run_eval_whole_prog_spec",
`!env st tdecs mdecs prog st' tdecs' mdecs' cenv' r.
  run_eval_whole_prog env (st,tdecs,mdecs) prog = ((st',tdecs',mdecs'),cenv', r) ⇒
  evaluate_whole_prog T env (st,tdecs,mdecs) prog ((st',tdecs',mdecs'),cenv', r)`,
 rw [run_eval_whole_prog_def, evaluate_whole_prog_def] >>
 metis_tac [run_eval_prog_spec]);

val _ = export_theory ();
