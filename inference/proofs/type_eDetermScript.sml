open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib;
open infer_eSoundTheory;
open infer_eCompleteTheory;

val _ = new_theory "type_eDeterm";

val _ = temp_tight_equality ();

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 rw [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

val infer_pe_complete = Q.store_thm ("infer_pe_complete",
  `check_menv menv ∧
    tenvC_ok cenv ∧
    num_tvs tenv = tvs ∧
    check_env {} env ∧
    tenv_invC FEMPTY env tenv ∧
    type_p tvs cenv p t1 tenv1 ∧
    type_e (convert_menv menv) cenv tenv e t1
    ⇒
    ?t t' tenv' st st' s constrs s'.
      infer_e menv cenv env e init_infer_state = (Success t, st) ∧
      infer_p cenv p st = (Success (t', tenv'), st') ∧
      t_unify st'.subst t t' = SOME s ∧
      sub_completion (num_tvs tenv) st.next_uvar s constrs s' ∧
      t1 = convert_t (t_walkstar s' t') ∧
      t1 = convert_t (t_walkstar s' t) ∧
      t_wfs s ∧
      simp_tenv_invC s' (num_tvs tenv) tenv' tenv1`,
  rw [] >>
  (infer_e_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  (infer_p_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  rw [] >>
  `t_wfs init_infer_state.subst` by rw [t_wfs_def, init_infer_state_def] >>
  first_x_assum (qspecl_then [`FEMPTY`, `menv`, `env`, `init_infer_state`, `[]`] mp_tac) >>
  rw [sub_completion_empty, init_infer_state_def] >>
  `t_wfs st'.subst`
          by (imp_res_tac (CONJUNCT1 infer_e_wfs) >>
              fs [init_infer_state_def]) >>
  first_x_assum (qspecl_then [`s'`, `st'`, `constraints'`] mp_tac) >>
  rw [] >>
  MAP_EVERY qexists_tac [`t''`, `tenv'`, `st''`] >>
  rw [] >>
  `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
  `check_t (num_tvs tenv) {} (t_walkstar s' t') ∧ check_t (num_tvs tenv) {} (t_walkstar s'' t'')`
              by (conj_tac >>
                  match_mp_tac (GEN_ALL sub_completion_completes) >>
                  rw []
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_e_check_t) >>
                      fs [])
                  >- fs [sub_completion_def]
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_p_check_t) >>
                      fs [])
                  >- fs [sub_completion_def]) >>
  `t_walkstar s'' (t_walkstar s' t') = t_walkstar s'' (t_walkstar s'' t'')` by metis_tac [convert_bi_remove] >>
  `t_walkstar s'' t' = t_walkstar s'' t''`
            by metis_tac [t_walkstar_SUBMAP, SUBMAP_REFL, t_compat_def] >>
  `t_compat st''.subst s''`
               by metis_tac [pure_add_constraints_success, sub_completion_def, t_compat_def] >>
  `?si. t_unify st''.subst t' t'' = SOME si ∧ t_compat si s''` by metis_tac [t_compat_eqs_t_unify] >>
  qexists_tac `si` >>
  `t_wfs si` by metis_tac [t_unify_wfs] >>
  rw [] >>
  fs[sub_completion_def] >>
  `pure_add_constraints st''.subst [t',t''] si` by (
    simp[pure_add_constraints_def] ) >>
  `t_wfs s''` by metis_tac[pure_add_constraints_wfs] >>
  `pure_add_constraints s'' [t',t''] s''` by
    (match_mp_tac pure_add_constraints_ignore >>
     fs[t_walkstar_eqn,t_walk_eqn]) >>
  `pure_add_constraints st''.subst (constraints''++[(t',t'')]) s''` by (
    metis_tac[pure_add_constraints_append]) >>
  pop_assum(fn th =>
    mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
                       (ONCE_REWRITE_RULE[CONJ_COMM]
                         (GEN_ALL pure_add_constraints_swap))) th)) >>
  simp[] >> disch_then(qx_choose_then`si2`strip_assume_tac) >>
  `pure_add_constraints si constraints'' si2` by (
    metis_tac[pure_add_constraints_append,
              pure_add_constraints_functional,
              CONS_APPEND]) >>
  imp_res_tac infer_p_next_uvar_mono >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qspecl_then[`num_tvs tenv`,`si2`,`s''`]mp_tac(GEN_ALL t_compat_bi_ground) >>
  discharge_hyps >- simp[] >> strip_tac >> simp[] >>
  conj_tac >- (
    fs[SUBSET_DEF,EXTENSION] >> rw[] >> res_tac >> DECIDE_TAC ) >>
  fs[simp_tenv_invC_def] >>
  metis_tac[]);

val unconvert_11 = Q.prove (
`!t1 t2. check_freevars 0 [] t1 ∧ check_freevars 0 [] t2 ⇒ 
  (unconvert_t t1 = unconvert_t t2 ⇔ t1 = t2)`,
 ho_match_mp_tac unconvert_t_ind >>
 rw [unconvert_t_def] >>
 Cases_on `t2` >>
 fs [unconvert_t_def, check_freevars_def] >>
 fs [EVERY_MEM] >>
 eq_tac >>
 rw [] >>
 match_mp_tac LIST_EQ >>
 rw []
 >- metis_tac [LENGTH_MAP] >>
 `x < LENGTH l` by metis_tac [LENGTH_MAP] >>
 `EL x (MAP (λa. unconvert_t a) ts) = EL x (MAP (λa. unconvert_t a) l)` by metis_tac [] >>
 rfs [EL_MAP] >>
 metis_tac [EL_MEM]);

val type_p_pat_bindings = Q.store_thm ("type_p_pat_bindings",
`(∀tvs cenv p t tenv.
  type_p tvs cenv p t tenv ⇒ MAP FST tenv = pat_bindings p []) ∧
 (∀tvs cenv ps ts tenv.
  type_ps tvs cenv ps ts tenv ⇒ MAP FST tenv = pats_bindings ps [])`,
 ho_match_mp_tac type_p_ind >>
 rw [pat_bindings_def] >>
 metis_tac [evalPropsTheory.pat_bindings_accum]);

val infer_e_type_pe_determ = Q.store_thm ("infer_e_type_pe_determ",
`!menv cenv env tenv p e st st' t t' tenv' s.
  ALL_DISTINCT (MAP FST tenv') ∧
  check_menv menv ∧
  tenvC_ok cenv ∧
  check_env {} env ∧
  num_tvs tenv = 0 ∧
  tenv_invC FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  infer_p cenv p st = (Success (t', tenv'), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) tenv'
  ⇒
  type_pe_determ (convert_menv menv) cenv tenv p e`,
 rw [type_pe_determ_def] >>
 mp_tac (Q.INST [`tvs`|->`0`] infer_pe_complete) >>
 rw [] >>
 mp_tac (Q.INST [`t1`|->`t2`, `tenv1` |-> `tenv2`,`tvs`|->`0`] infer_pe_complete) >>
 rw [] >>
 match_mp_tac LIST_EQ >>
 imp_res_tac type_p_pat_bindings >>
 imp_res_tac infer_p_bindings >>
 pop_assum (qspecl_then [`[]`] mp_tac) >>
 rw []
 >- metis_tac [LENGTH_MAP] >>
 fs [simp_tenv_invC_def] >>
 first_x_assum (qspecl_then [`FST (EL x tenv2)`, `SND (EL x tenv2)`] mp_tac) >>
 first_x_assum (qspecl_then [`FST (EL x tenv1)`, `SND (EL x tenv1)`] mp_tac) >>
 `ALL_DISTINCT (MAP FST tenv2) ∧ x < LENGTH tenv2` by metis_tac [LENGTH_MAP] >>
 rw [ALOOKUP_ALL_DISTINCT_EL, LENGTH_MAP] >>
 `?k1 t1 k2 t2. EL x tenv1 = (k1,t1) ∧ EL x tenv2 = (k2, t2)` by metis_tac [pair_CASES] >> 
 fs [] >>
 conj_asm1_tac
 >- (`EL x (MAP FST tenv1) = EL x (MAP FST tenv2)` by metis_tac [] >>
     rfs [EL_MAP]) >>
 rw [GSYM unconvert_11] >>
 fs [EVERY_MEM] >>
 imp_res_tac ALOOKUP_MEM >>
 res_tac >>
 fs [sub_completion_def] >>
 imp_res_tac pure_add_constraints_success >>
 fs [t_compat_def] >>
 metis_tac [t_walkstar_no_vars]);

val generalise_complete_lem = Q.prove (
`∀n s t tvs s' t' tvs next_uvar.
  t_wfs s ∧ check_s 0 (count next_uvar) s ∧
  check_t 0 (count next_uvar) t ∧
  generalise 0 n FEMPTY (t_walkstar s t) = (tvs,s',t') ⇒
  ∃ec1 last_sub.
    t' = t_walkstar last_sub t ∧ t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub`,
 rw [] >>
 mp_tac (Q.SPECL [`n`, `s`, `[t]`] generalise_complete) >>
 rw [generalise_def, LET_THM]);

val t_vars_check_t = prove(``
  (∀t.
  ¬check_t 0 {} t ∧ 
  check_t 0 s t ⇒
  ∃n'. n' ∈ s ∧ n' ∈ t_vars t) ∧ 
  (∀ts.
  ∀x.MEM x ts ⇒ 
    ¬check_t 0 {} x ∧ 
    check_t 0 s x ⇒ 
    ∃n'. n' ∈ s ∧ n' ∈ t_vars x)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,t_vars_eqn]>>
  fs[EXISTS_MEM,EVERY_MEM]>>res_tac>>
  qexists_tac `n'`>>
  fs[MEM_MAP]>>
  metis_tac[])

val t_walkstar_diff = prove(``
  t_wfs s1 ∧ t_wfs s2 ∧ 
  (t_walkstar s1 (Infer_Tuvar n) ≠ t_walkstar s2 (Infer_Tuvar n))
  ⇒ 
  (∀t.(n ∈ t_vars t) ⇒ t_walkstar s1 t ≠ t_walkstar s2 t) ∧
  (∀ts. 
  ∀x. MEM x ts ⇒ 
    n ∈ t_vars x ⇒ t_walkstar s1 x ≠ t_walkstar s2 x)``,
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[t_vars_eqn]>>fs[]>>
  fs[t_walkstar_eqn,t_walk_eqn,MEM_MAP]>>
  res_tac>>rfs[]>>
  SPOSE_NOT_THEN assume_tac>>
  imp_res_tac MAP_EQ_f>>
  metis_tac[])

val type_pe_determ_infer_e = Q.store_thm ("type_pe_determ_infer_e",
`!menv cenv env tenv p e st st' t t' tenv' s.
  ALL_DISTINCT (MAP FST tenv') ∧
  check_menv menv ∧
  tenvC_ok cenv ∧
  check_env {} env ∧
  num_tvs tenv = 0 ∧
  tenv_inv FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  infer_p cenv p st = (Success (t', tenv'), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  type_pe_determ (convert_menv menv) cenv tenv p e
  ⇒
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) tenv'`,
 rw [type_pe_determ_def, check_cenv_tenvC_ok] >>
 `t_wfs init_infer_state.subst` by rw [t_wfs_def, init_infer_state_def] >>
 `t_wfs st.subst` by metis_tac [infer_e_wfs] >>
 `t_wfs st'.subst` by metis_tac [infer_p_wfs] >>
 `t_wfs s` by metis_tac [t_unify_wfs] >>
 `check_t 0 (count st.next_uvar) t`
          by (imp_res_tac infer_e_check_t >>
              fs [init_infer_state_def]) >>
 `check_s 0 (count st.next_uvar) st.subst`
           by (match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`menv`, `cenv`, `env`, `e`, `init_infer_state`] >>
               rw [init_infer_state_def, check_s_def]) >>
 `?l. set l = count st'.next_uvar DIFF FDOM s ∧ ALL_DISTINCT l`
          by metis_tac [FINITE_COUNT, FINITE_DIFF, SET_TO_LIST_INV, ALL_DISTINCT_SET_TO_LIST] >>
 qabbrev_tac `inst1 = MAP (\n. (Infer_Tuvar n, Infer_Tbool)) l` >>
 qabbrev_tac `inst2 = MAP (\n. (Infer_Tuvar n, Infer_Tint)) l` >>
(* Because we're instantiating exactly the unconstrained variables *)
 let
   fun tac q q1 =
     simp[sub_completion_def] >>
     qexists_tac`s |++ (MAP (λn. (n, ^q)) l)` >>
     conj_asm1_tac >- (
       qunabbrev_tac q1 >>
       qpat_assum`t_wfs s`mp_tac >>
       qpat_assum`set l = X`mp_tac >>
       qpat_assum`ALL_DISTINCT l`mp_tac >>
       qspec_tac(`st'.next_uvar`,`n`) >>
       map_every qid_spec_tac[`s`,`l`] >>
       Induct >>
       simp[pure_add_constraints_def,FUPDATE_LIST_THM] >> rw[] >>
       qho_match_abbrev_tac`∃s2. P s2 ∧ Q s2` >>
       qsuff_tac`∃s2. P s2 ∧ (t_wfs s2 ⇒ Q s2)`>-metis_tac[t_unify_wfs] >>
       simp[Abbr`P`,t_unify_eqn,t_walk_eqn,Infer_Tbool_def,Infer_Tint_def,Once t_vwalk_eqn] >>
       simp[FLOOKUP_DEF] >> rw[] >- (
         fs[EXTENSION] >> metis_tac[] ) >>
       simp[t_ext_s_check_eqn,Once t_oc_eqn,t_walk_eqn] >>
       simp[GSYM Infer_Tbool_def,GSYM Infer_Tint_def,Abbr`Q`] >> strip_tac >>
       first_x_assum (match_mp_tac o MP_CANON) >>
       simp[FDOM_FUPDATE] >> fs[EXTENSION] >> metis_tac[] ) >>
     conj_tac >- (
       fs[EXTENSION,SUBSET_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] ) >>
     simp[FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
     imp_res_tac pure_add_constraints_wfs >>
     ntac 3 (pop_assum kall_tac) >>
     reverse(rw[]) >- (
       rw[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn,flookup_fupdate_list] >>
       BasicProvers.CASE_TAC >- (
         imp_res_tac ALOOKUP_FAILS >>
         fs[MEM_MAP,EXTENSION] >> metis_tac[] ) >>
       imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >>
       rw[Infer_Tbool_def,Infer_Tint_def] >> rw[check_t_def] ) >>
     first_assum(fn th=> mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] (CONJUNCT1 infer_p_check_s)) th)) >>
     simp[] >> disch_then(qspec_then`0`mp_tac) >> simp[] >> strip_tac >>
     match_mp_tac t_walkstar_check >>
     simp[check_t_def,FDOM_FUPDATE_LIST] >>
     (t_unify_check_s
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))))
      |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     imp_res_tac infer_p_next_uvar_mono >>
     first_assum(fn th => mp_tac (MATCH_MP (CONJUNCT1 check_t_more5) th)) >>
     disch_then(qspec_then`count st'.next_uvar`mp_tac) >>
     simp[SUBSET_DEF] >> strip_tac >>
     imp_res_tac (CONJUNCT1 infer_p_check_t) >>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
     strip_tac >>
     (pure_add_constraints_check_s
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``pure_add_constraints`` o fst o strip_comb))))
      |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     disch_then(qspecl_then[`0`,`st'.next_uvar`]mp_tac) >> simp[] >>
     discharge_hyps >- (
       simp[Abbr q1,EVERY_MEM,MEM_MAP,PULL_EXISTS,check_t_def,Infer_Tbool_def,Infer_Tint_def] ) >>
     strip_tac >>
     match_mp_tac (MP_CANON check_s_more3) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     simp[SUBSET_DEF,MEM_MAP,PULL_EXISTS]
 in
   `?s1. sub_completion 0 st'.next_uvar s inst1 s1` by (tac ``Infer_Tbool`` `inst1`) >>
   `?s2. sub_completion 0 st'.next_uvar s inst2 s2` by (tac ``Infer_Tint`` `inst2`)
 end >>
  `t_wfs s1 ∧ t_wfs s2` by metis_tac[sub_completion_wfs] >>
 imp_res_tac sub_completion_unify2 >>
 imp_res_tac infer_p_constraints >>
 (sub_completion_add_constraints |> REWRITE_RULE[GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 disch_then imp_res_tac >>
 (infer_e_sound |> CONJUNCT1 |> REWRITE_RULE[GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 simp[init_infer_state_def] >>
 disch_then(qspec_then`tenv`mp_tac) >> simp[] >>
 fs[sub_completion_def,GSYM AND_IMP_INTRO] >>
 disch_then(fn th =>
   first_x_assum(mp_tac o MATCH_MP th) >>
   first_x_assum(mp_tac o MATCH_MP th)) >>
 imp_res_tac infer_p_next_uvar_mono >>
 `count st.next_uvar ⊆ count st'.next_uvar` by simp[SUBSET_DEF] >>
 discharge_hyps >- metis_tac[SUBSET_TRANS] >> simp[] >>
 discharge_hyps >- metis_tac[tenv_inv_empty_to] >> strip_tac >>
 discharge_hyps >- metis_tac[SUBSET_TRANS] >> simp[] >>
 discharge_hyps >- metis_tac[tenv_inv_empty_to] >> strip_tac >>
 imp_res_tac infer_p_check_t>>
 assume_tac (infer_p_sound |> CONJUNCT1)>>
 first_assum (qspecl_then
   [`cenv`,`p`,`st`,`t'`,`tenv'`,`st'`,`0`,`(t,t')::inst1`,`s1`]assume_tac)>>
 first_x_assum (qspecl_then
   [`cenv`,`p`,`st`,`t'`,`tenv'`,`st'`,`0`,`(t,t')::inst2`,`s2`]assume_tac)>>
 rfs[sub_completion_def]>>
 res_tac>>pop_assum kall_tac>>
 (*Because t,t' is part of the unifications that yielded s1 and s2*)
 `t_compat s s1 ∧ t_compat s s2` by (
   imp_res_tac pure_add_constraints_success >> rw[] ) >>
 `t_walkstar s t = t_walkstar s t'` by (
   imp_res_tac t_unify_unifier ) >>
 `convert_t (t_walkstar s2 t') = convert_t (t_walkstar s2 t)` by (
   fs[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rfs[]>>
 res_tac>>pop_assum kall_tac>>
 `convert_t (t_walkstar s1 t') = convert_t (t_walkstar s1 t)` by (
   fs[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rfs[]>>
 fs[convert_env_def]>>
 spose_not_then strip_assume_tac >>
 fs[EXISTS_MEM,EXISTS_PROD] >>
 qpat_assum`MAP X Y = Z`mp_tac >> simp[] >>
 simp[LIST_EQ_REWRITE,EL_MAP,UNCURRY] >>
 qpat_assum`MEM X Y`mp_tac >> simp[MEM_EL] >> strip_tac >>
 qexists_tac`n` >>
 pop_assum(assume_tac o SYM) >> simp[] >>
 fs[EVERY_MEM] >>
 first_x_assum(qspec_then`EL n tenv'`mp_tac) >>
 discharge_hyps >- metis_tac[MEM_EL] >> simp[] >> strip_tac >>
 qmatch_assum_rename_tac`check_t 0 (count st'.next_uvar) tt` >>
 `t_vars tt ⊆ count (st'.next_uvar)` by imp_res_tac check_t_t_vars >>
 imp_res_tac infer_p_check_s>> ntac 7 (pop_assum kall_tac)>>
 `check_s 0 (count st'.next_uvar) s` by 
   (match_mp_tac t_unify_check_s>>
   Q.LIST_EXISTS_TAC [`st'.subst`,`t`,`t'`]>>fs[]>>
   `count st.next_uvar ⊆ count st'.next_uvar` by
     (imp_res_tac infer_p_next_uvar_mono>>
     rw[count_def,SUBSET_DEF]>>DECIDE_TAC)>>
   metis_tac[check_t_more5,infer_p_check_t])>>
 `check_t 0 (count st'.next_uvar) (t_walkstar s tt)` by
   (match_mp_tac t_walkstar_check>>fs[]>>
   `count st'.next_uvar ⊆ count st'.next_uvar ∪ FDOM s` by fs[]>>
   metis_tac[check_t_more5,check_s_more3])>>
  imp_res_tac t_vars_check_t>>
  ntac 5 (pop_assum kall_tac)>>
  imp_res_tac t_walkstar_vars_notin>>
  `t_walkstar s1 tt ≠ t_walkstar s2 tt` by
    (Q.ISPECL_THEN [`s2`,`s1`,`n'`]mp_tac (GEN_ALL t_walkstar_diff)>>
    discharge_hyps>-
      (rfs[]>>
      `MEM n' l` by fs[]>>
      `t_walkstar s1 (Infer_Tuvar n') = Infer_Tbool ∧
       t_walkstar s2 (Infer_Tuvar n') = Infer_Tint ` by
        (imp_res_tac pure_add_constraints_apply>>
        unabbrev_all_tac>>
        fs[MAP_EQ_f,FORALL_PROD,MEM_MAP]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum (qspecl_then [`Infer_Tuvar n'`,`Infer_Tint`] mp_tac)>>
        pop_assum (qspecl_then [`Infer_Tuvar n'`,`Infer_Tbool`] mp_tac)>>
        ntac 4 (pop_assum kall_tac)>>
        fs[t_walkstar_eqn,t_walk_eqn,Infer_Tint_def,Infer_Tbool_def])>>
      fs[Infer_Tint_def,Infer_Tbool_def])>>
    rw[]>>pop_assum kall_tac>>
    pop_assum (qspec_then `t_walkstar s tt` assume_tac)>>rfs[]>>
    metis_tac[t_compat_def])>>
  assume_tac (GEN_ALL (CONJUNCT1 check_t_less))>>
  first_assum(qspecl_then [`count st'.next_uvar`,`s1`,`0`,`tt`] assume_tac)>>
  first_x_assum(qspecl_then [`count st'.next_uvar`,`s2`,`0`,`tt`]assume_tac)>>
  `count st'.next_uvar ∩ COMPL (FDOM s1) = {} ∧
   count st'.next_uvar ∩ COMPL (FDOM s2) = {}` by
    (fs[EXTENSION,SUBSET_DEF]>>metis_tac[])>>
  fs[]>>rfs[]>>
  metis_tac[check_t_empty_unconvert_convert_id]);

 
 (*From ¬check_t 0 {} (t_walkstar s tt) it should follow that
   t_walkstar s tt must contain some unification variables.
   (*
   first_assum(
     mp_tac o (MATCH_MP (GEN_ALL(CONTRAPOS(SPEC_ALL(CONJUNCT1 check_t_walkstar)))))) >>
   *)
   But we know that s is completed by s1 and s2 therefore those
   unification variables are exactly bound in s1 and s2 to 
   Infer_Tbool and Infer_Tint, hence the walkstars must differ *)

val _ = export_theory ();

