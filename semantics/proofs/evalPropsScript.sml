(* Various basic properties of the big and small step semantics, and their
 * semantic primitives. *)

open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory;

val _ = new_theory "evalProps";

val pmatch_append = Q.store_thm ("pmatch_append",
`(!(cenv : envC) (st : v store) p v env env' env''.
    (pmatch cenv st p v env = Match env') ⇒
    (pmatch cenv st p v (env++env'') = Match (env'++env''))) ∧
 (!(cenv : envC) (st : v store) ps v env env' env''.
    (pmatch_list cenv st ps v env = Match env') ⇒
    (pmatch_list cenv st ps v (env++env'') = Match (env'++env'')))`,
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, bind_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val do_app_cases = Q.store_thm ("do_app_cases",
`!st env op v1 v2 st' env' v3.
  (do_app env st op v1 v2 = SOME (env',st',v3))
  =
  ((?op' n1 n2. 
    (op = Opn op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    ((((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧ 
     (st' = st) ∧ (env' = exn_env) ∧ (v3 = Raise (Con (SOME (Short "Div")) [])) ∨
     ~(((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (env' = env) ∧ (v3 = Lit (IntLit (opn_lookup op' n1 n2))))) ∨
  (?op' n1 n2.
    (op = Opb op') ∧ (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
    (st = st') ∧ (env = env') ∧ (v3 = Lit (Bool (opb_lookup op' n1 n2)))) ∨
  ((op = Equality) ∧ (st = st') ∧
      ((?b. (do_eq v1 v2 = Eq_val b) ∧ (v3 = Lit (Bool b)) ∧ (env = env')) ∨
       ((do_eq v1 v2 = Eq_closure) ∧ (v3 = Raise (Con (SOME (Short "Eq")) []) ∧
       (env' = exn_env))))) ∨
  (∃menv'' cenv'' env'' n e.
    (op = Opapp) ∧ (v1 = Closure (menv'',cenv'',env'') n e) ∧
    (st' = st) ∧ (env' = (menv'',cenv'',bind n v2 env'')) ∧ (v3 = e)) ∨
  (?menv'' cenv'' env'' funs n' n'' e.
    (op = Opapp) ∧ (v1 = Recclosure (menv'',cenv'',env'') funs n') ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (st = st') ∧ (env' = (menv'',cenv'', bind n'' v2 (build_rec_env funs (menv'',cenv'',env'') env''))) ∧ (v3 = e)) ∨
  (?lnum.
    (op = Opassign) ∧ (v1 = Loc lnum) ∧ (store_assign lnum v2 st = SOME st') ∧
    (env' = env) ∧ (v3 = Lit Unit)))`,
 SIMP_TAC (srw_ss()) [do_app_def] >>
 cases_on `op` >>
 rw [] 
 >- (cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     cases_on `v2` >>
     rw [] >>
     cases_on `l` >> 
     rw [] >>
     cases_on `l'` >> 
     rw [] >>
     metis_tac [])
 >- (cases_on `do_eq v1 v2` >>
     rw [] >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     PairCases_on `p` >>
     rw [] >-
     metis_tac [] >>
     every_case_tac >>
     metis_tac [])
 >- (cases_on `v1` >>
     rw [] >>
     every_case_tac >>
     metis_tac []));

val build_rec_env_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure env funs' f) env') env' funs =
merge (MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs) env'`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
`∀funs funs' env env'.
  build_rec_env funs env env' =
  merge (MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs) env'`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val do_con_check_build_conv = Q.store_thm ("do_con_check_build_conv",
`!tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v`,
rw [do_con_check_def, build_conv_def] >>
every_case_tac >>
fs []);

val merge_envC_empty_assoc = Q.store_thm ("merge_envC_empty_assoc",
`!envC1 envC2 envC3.
  merge_envC ([],envC1) (merge_envC ([],envC2) envC3)
  =
  merge_envC ([],envC1++envC2) envC3`,
 rw [] >>
 PairCases_on `envC3` >>
 rw [merge_envC_def, merge_def]);

val same_ctor_and_same_tid = Q.store_thm ("same_ctor_and_same_tid",
`!cn1 tn1 cn2 tn2.
  same_tid tn1 tn2 ∧
  same_ctor (cn1,tn1) (cn2,tn2)
  ⇒
  tn1 = tn2 ∧ cn1 = cn2`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 fs [same_tid_def, same_ctor_def]);

val same_tid_sym = Q.store_thm ("same_tid_sym",
`!tn1 tn2. same_tid tn1 tn2 = same_tid tn2 tn1`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 rw [same_tid_def] >>
 metis_tac []);


val _ = export_theory ();