open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory pairTheory;
open optionTheory alistTheory finite_mapTheory; 
open holSyntaxLibTheory;
open holSyntaxTheory holSyntaxExtraTheory;

val _ = temp_tight_equality();
val every_case_tac = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "holConservative";

val CLOSED_INST = Q.prove (
`!tm tysubst. CLOSED tm ⇒ CLOSED (INST tysubst tm)`,
 cheat);

val type_ok_subst = Q.prove (
`!tys i ty.
  type_ok tys (TYPE_SUBST i ty)
  ⇒
  ?i'. EVERY (type_ok tys) (MAP FST i') ∧ TYPE_SUBST i' ty = TYPE_SUBST i ty`,
 cheat);

val updates_disjoint = Q.prove (
`!upd ctxt.
  upd updates ctxt
  ⇒
  DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd))) (FDOM (tmsof ctxt))`,
 rw [Once updates_cases, DISJOINT_DEF, EXTENSION] >>
 rw [consts_of_upd_def] >>
 rw []
 >- metis_tac []
 >- (rw [PROVE [] ``a ∨ b ⇔ ~a ⇒ b``] >>
     first_x_assum match_mp_tac >>
     fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     metis_tac [])
 >- metis_tac []);

val update_extension = Q.prove (
`!lhs tm.
  lhs |- tm
  ⇒
  !ctxt tms upd.
    lhs = (thyof ctxt,tms) ∧
    upd updates ctxt
    ⇒
    (thyof (upd::ctxt),tms) |- tm`,
 ho_match_mp_tac proves_ind >>
 rw []
 >- (rw [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`l`, `r`, `ty`, `x`] >>
     rw [] >>
     match_mp_tac type_ok_extend >>
     qexists_tac `tysof (sigof (thyof ctxt))` >>
     rw [] >>
     match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
     fs [Once updates_cases])
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     ntac 2 disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`t`, `ty`, `x`] >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac type_ok_extend >>
         qexists_tac `tysof ctxt` >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (Cases_on `ctxt` >>
             fs []))
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     ntac 3 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 4 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 5 disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`tm`, `h`, `ilist`] >>
     rw [] >>
     res_tac  >>
     fs [] >>
     rw [] >>
     match_mp_tac term_ok_extend >>
     MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
     rw []
     >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
         fs [Once updates_cases])
     >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
         metis_tac [updates_disjoint]))
 >- (rw [Once proves_cases] >>
     ntac 6 disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`tm`, `h`, `tyin`] >>
     rw [] >>
     fs [EVERY_MAP, EVERY_MEM] >>
     rw [] >>
     match_mp_tac type_ok_extend >>
     qexists_tac `tysof ctxt` >>
     rw [] >>
     match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
     fs [Once updates_cases])
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 8 disj2_tac >>
     disj1_tac >>
     rw [] >>
     qexists_tac `t` >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     ntac 9 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 10 disj2_tac >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (Cases_on `ctxt` >>
         fs [])));

val const_subst_ok_def = Define `
const_subst_ok s = EVERY (\(c,tm). welltyped tm ∧ CLOSED tm) s`;

val remove_const_def = Define `
(remove_const thy subst (Var v ty) = Var v ty) ∧
(remove_const thy subst (Const c ty) =
  case ALOOKUP subst c of
     | NONE => Const c ty
     | SOME tm =>
         case some tysubst. EVERY (type_ok thy) (MAP FST tysubst) ∧ TYPE_SUBST tysubst (typeof tm) = ty of
            | NONE => Const c ty (* Can't happen *)
            | SOME tysubst => INST tysubst tm) ∧
(remove_const thy subst (Comb tm1 tm2) =
  Comb (remove_const thy subst tm1) (remove_const thy subst tm2)) ∧
(remove_const thy subst (Abs v tm) =
  Abs v (remove_const thy subst tm))`;

val upd_to_subst_def = Define `
(upd_to_subst (ConstSpec consts p) =
  consts) ∧
(upd_to_subst _ = [])`;

val updates_to_subst = Q.prove (
`!upd ctxt.
  upd updates ctxt 
  ⇒
  const_subst_ok (upd_to_subst upd) ∧
  ALOOKUP (upd_to_subst upd) "=" = NONE`,
 rw [updates_cases] >>
 rw [upd_to_subst_def, const_subst_ok_def] >>
 imp_res_tac proves_theory_ok >>
 imp_res_tac theory_ok_sig
 >- (imp_res_tac proves_term_ok >>
     fs [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     res_tac >>
     PairCases_on `e` >>
     fs [] >>
     rfs [term_ok_equation] >>
     cheat >>
     metis_tac [term_ok_welltyped])
 >- (fs [is_std_sig_def] >>
     CCONTR_TAC >>
     fs [ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     res_tac >>
     fs [MEM_MAP] >>
     metis_tac [pair_CASES, FST, SND]));

val typeof_remove_const = Q.prove (
`!tm thy s. const_subst_ok s ⇒ typeof (remove_const thy s tm) = typeof tm`,
 Induct_on `tm` >>
 rw [remove_const_def] >>
 every_case_tac >>
 rw [] >>
 match_mp_tac WELLTYPED_LEMMA >>
 match_mp_tac INST_HAS_TYPE >>
 qexists_tac `typeof x` >>
 rw [GSYM WELLTYPED]
 >- (fs [const_subst_ok_def] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [EVERY_MEM] >>
     res_tac >>
     fs []) >>
 Cases_on `?tysubst. TYPE_SUBST tysubst (typeof x) = t` >>
 fs [some_def] >>
 rw [] >>
 metis_tac [SELECT_THM]);

val remove_const_eq = Q.prove (
`const_subst_ok s ∧ ALOOKUP s "=" = NONE ⇒ 
  remove_const thy s (tm1 === tm2) = remove_const thy s tm1 === remove_const thy s tm2`,
 rw [equation_def, remove_const_def, typeof_remove_const]);

val has_type_remove_const = Q.prove (
`!tm ty. tm has_type ty ⇒ !s. const_subst_ok s ⇒ remove_const thy s tm has_type ty`,
 ho_match_mp_tac has_type_ind >>
 rw [remove_const_def]
 >- rw [Once has_type_cases]
 >- (every_case_tac >>
     fs []
     >- rw [Once has_type_cases]
     >- rw [Once has_type_cases] >>
     match_mp_tac INST_HAS_TYPE >>
     qexists_tac `typeof x` >>
     rw [GSYM WELLTYPED]
     >- (fs [const_subst_ok_def, EVERY_MEM] >>
         imp_res_tac ALOOKUP_MEM >>
         res_tac >>
         fs [])
     >- (Cases_on `?tysubst. TYPE_SUBST tysubst (typeof x) = t` >>
         fs [some_def] >>
         rw [] >>
         metis_tac [SELECT_THM]))
 >- metis_tac [has_type_cases]
 >- rw [Once has_type_cases]);

val vfree_in_remove_const = Q.prove (
`const_subst_ok s ∧ VFREE_IN (Var x ty) (remove_const thy s tm) ⇒ VFREE_IN (Var x ty) tm`,
 Induct_on `tm` >>
 rw [VFREE_IN_def, remove_const_def] >>
 rw [VFREE_IN_def] >>
 every_case_tac >>
 fs [] >>
 CCONTR_TAC >>
 fs [] >>
 `CLOSED x'`
       by (fs [const_subst_ok_def, EVERY_MEM] >>
           imp_res_tac ALOOKUP_MEM >>
           res_tac >>
           fs []) >>
 metis_tac [CLOSED_INST, CLOSED_def]);

val type_ok_remove_upd = Q.prove (
`!sig ty.
  type_ok sig ty
  ⇒
  !ctxt upd.
    (!name arity. upd ≠ NewType name arity) ∧
    (!name pred v2 v3. upd ≠ TypeDefn name pred v2 v3) ∧
    sig = alist_to_fmap (types_of_upd upd) ⊌ tysof ctxt
    ⇒
    type_ok (tysof ctxt) ty`,
 ho_match_mp_tac type_ok_ind >>
 rw [type_ok_def]
 >- (Cases_on `upd` >>
     fs [FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
     every_case_tac >>
     fs []) >>
 fs [EVERY_MEM] >>
 rw [] >>
 metis_tac []);

val term_ok_remove_upd = Q.prove (
`!upd ctxt tm thy.
  term_ok (alist_to_fmap (types_of_upd upd) ⊌ tysof ctxt, alist_to_fmap (consts_of_upd upd) ⊌ tmsof ctxt) tm ∧
  upd updates ctxt ∧
  (?consts p. upd = ConstSpec consts p)
  ⇒
  term_ok (sigof ctxt) (remove_const (tysof ctxt) (upd_to_subst upd) tm)`,
 Induct_on `tm` >>
 rw [term_ok_def, remove_const_def] >>
 rw [upd_to_subst_def]
 >- metis_tac [type_ok_remove_upd, update_distinct]
 >- (fs [updates_cases] >>
     rw [] >>
     every_case_tac >>
     fs [term_ok_def, FLOOKUP_FUNION] >>
     every_case_tac >>
     fs []
     >- metis_tac []
     >- (imp_res_tac ALOOKUP_MEM >>
         fs [ALOOKUP_NONE, MEM_MAP] >>
         PairCases_on `y` >>
         fs [] >>
         metis_tac [FST])
     >- metis_tac []
     >- (`typeof x = ty0` 
                by (fs [ALOOKUP_MAP] >>
                    metis_tac [SOME_11]) >>
         rw [] >>
         fs [some_def] >>
         metis_tac [type_ok_subst, EVERY_NOT_EXISTS])
     >- (imp_res_tac ALOOKUP_MEM >>
         fs [ALOOKUP_NONE, MEM_MAP] >>
         fs [] >>
         metis_tac [FST])
     >- (match_mp_tac term_ok_INST >>
         `typeof x = ty0` 
                by (fs [ALOOKUP_MAP] >>
                    metis_tac [SOME_11]) >>
         simp [] >>
         imp_res_tac proves_term_ok >>
         imp_res_tac proves_theory_ok >>
         fs [theory_ok_def] >>
         fs [EVERY_MAP, term_ok_equation, LAMBDA_PROD] >>
         fs [EVERY_MEM] >>
         rw []
         >- (imp_res_tac ALOOKUP_MEM >>
             fs [MEM_MAP] >>
             PairCases_on `y` >>
             fs [] >>
             res_tac >>
             fs [] >>
             cheat)
         >- (PairCases_on `e` >>
             fs [some_def] >>
             rw [] >>
             qabbrev_tac `tysubst = (@tysubst.  (∀e. MEM e tysubst ⇒ (λ(p1,p2).  type_ok (tysof ctxt) p1) e) ∧ TYPE_SUBST tysubst (typeof x) = TYPE_SUBST i (typeof x))` >>
             `(∀e. MEM e tysubst' ⇒ (λ(p1,p2). type_ok (tysof ctxt) p1) e) ∧
              TYPE_SUBST tysubst' (typeof x) = TYPE_SUBST i (typeof x)`
                   by metis_tac [SELECT_THM] >>
             res_tac >>
             fs [])))
 >- (fs [welltyped_def] >>
     qexists_tac `ty` >>
     match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] has_type_remove_const) >>
     rw [] >>
     metis_tac [updates_to_subst, upd_to_subst_def])
 >- (fs [welltyped_def] >>
     qexists_tac `ty'` >>
     match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] has_type_remove_const) >>
     rw [] >>
     metis_tac [updates_to_subst, upd_to_subst_def])
 >- (imp_res_tac updates_to_subst >>
     fs [upd_to_subst_def] >>
     rw [typeof_remove_const])
 >- metis_tac [type_ok_remove_upd, update_distinct]);

val theory_ok_remove_upd = Q.prove (
`!sig ty.
  (?consts p. upd = ConstSpec consts p) ∧
  upd updates ctxt
  ⇒
  theory_ok (thyof ctxt)`,
 rw [updates_cases] >>
 imp_res_tac proves_theory_ok >>
 fs []);

val remove_const_inst = Q.prove (
`!tys consts tyin tm.
  remove_const tys consts (INST tyin tm) = INST tyin (remove_const tys consts tm)`,
 Induct_on `tm` >>
 rw [remove_const_def] >>
 cheat);

val remove_const_aconv = Q.prove (
`!tm1 tm2. ACONV tm1 tm2 ⇒ ACONV (remove_const tys consts tm1) (remove_const tys consts tm2)`,
 cheat);

val remove_const_vsubst = Q.prove (
`!tys consts tm.
  remove_const tys consts (VSUBST ilist tm) = 
  VSUBST (MAP (λ(x,y). (remove_const tys consts x, y)) ilist) (remove_const tys consts tm)`,
 cheat);

val welltyped_remove_const = Q.prove (
`!tys consts tm.
  const_subst_ok consts ∧ welltyped tm ⇒ welltyped (remove_const tys consts tm)`,
 rw [WELLTYPED] >>
 imp_res_tac has_type_remove_const >>
 rw [typeof_remove_const]);

val use_const_spec = Q.prove (
`!ctxt consts p.
  (thyof ctxt,fromList alphaorder (MAP (λ(s,t). (Var s (typeof t) === t, ())) consts)) |- p
  ⇒
  (thyof ctxt,empty) |-
  remove_const (tysof ctxt) consts (VSUBST (MAP (λ(s,t). (Const s (typeof t),Var s (typeof t))) consts) p)`,
 cheat);

val remove_const_old_axiom = Q.prove (
`!ctxt consts tm.
  term_ok (sigof ctxt) tm ∧
  (∀s. MEM s (MAP FST consts) ⇒ ¬MEM s (MAP FST (const_list ctxt)))
  ⇒
  remove_const (tysof ctxt) consts tm = tm`,
 Induct_on `tm` >>
 rw [remove_const_def] >>
 every_case_tac >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP, term_ok_def] >>
 res_tac >>
 fs [FORALL_PROD] >>
 imp_res_tac ALOOKUP_MEM >>
 metis_tac []);

 (*
val update_conservative = Q.prove (
`!lhs tm.
  lhs |- tm
  ⇒
  !ctxt tms upd.
    lhs = (thyof (upd::ctxt),tms) ∧
    upd updates ctxt ∧
    (?consts p. upd = ConstSpec consts p)
    ⇒
    (thyof ctxt,map_keys alphaorder (remove_const (tysof (upd::ctxt)) (upd_to_subst upd)) tms) |- remove_const (tysof (upd::ctxt)) (upd_to_subst upd) tm`,
 ho_match_mp_tac proves_ind >>
 rw [] >>
 imp_res_tac updates_to_subst >>
 qabbrev_tac `s = upd_to_subst upd`
 >- (rw [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const (tysof ctxt) consts l`, `remove_const (tysof ctxt) consts r`, `ty`, `x`] >>
     rw []
     >- rw [remove_const_eq, remove_const_def, upd_to_subst_def]
     >- (fs [EVERY_MEM] >>
         rw [] >>
         fs [MEM_MAP] >>
         rw [] >>
         res_tac >>
         cheat >>
         metis_tac [vfree_in_remove_const])
     >- (match_mp_tac type_ok_extend >>
         qexists_tac `tysof (sigof (thyof ctxt))` >>
         rw [] >>
         fs [] >>
         metis_tac [type_ok_remove_upd, update_distinct])
     >- (unabbrev_all_tac >>
         first_x_assum (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
         rw [remove_const_eq, remove_const_def, upd_to_subst_def]))
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     rw [] >>
     fs []
     >- cheat
     >- metis_tac [theory_ok_remove_upd]
     >- metis_tac [has_type_remove_const]
     >- (match_mp_tac term_ok_remove_upd >>
         fs []))
 >- (rw [Once proves_cases] >>
     ntac 2 disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const (tysof ctxt) consts t`, `ty`, `x`] >>
     rw [remove_const_eq, remove_const_def] >>
     fs []
     >- cheat
     >- rw [upd_to_subst_def]
     >- metis_tac [theory_ok_remove_upd]
     >- (match_mp_tac (SIMP_RULE (srw_ss()) [PULL_EXISTS, upd_to_subst_def] term_ok_remove_upd) >>
         metis_tac []))
 >- (rw [Once proves_cases] >>
     ntac 3 disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const (tysof ctxt) consts tm`, `remove_const (tysof ctxt) consts tm'`, 
                            `map_keys alphaorder (remove_const (tysof ctxt) consts) h1`, 
                            `map_keys alphaorder (remove_const (tysof ctxt) consts) h2`] >>
     rw [remove_const_eq, remove_const_def] >>
     fs [upd_to_subst_def, rich_listTheory.FILTER_MAP]
     >> cheat
     >- cheat (* TODO: not true as stated, need an extra weakening step? *)
     >- (LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
         rw [upd_to_subst_def])
     >- (FIRST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
         rw [upd_to_subst_def]))
 >- (rw [Once proves_cases] >>
     ntac 4 disj2_tac >>
     disj1_tac >>
     rw [] >>
     fs [upd_to_subst_def] >>
     MAP_EVERY qexists_tac [`map_keys alphaorder (remove_const (tysof ctxt) consts) h1`,
                            `map_keys alphaorder (remove_const (tysof ctxt) consts) h2`,
                            `remove_const (tysof ctxt) consts p`,
                            `remove_const (tysof ctxt) consts tm`] >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p'`] mp_tac) >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p'`] mp_tac) >>
     rw [upd_to_subst_def] >>
     rfs [upd_to_subst_def, remove_const_eq] >>
     metis_tac [remove_const_aconv])
 >- (rw [Once proves_cases] >>
     ntac 5 disj2_tac >>
     disj1_tac >>
     fs [upd_to_subst_def] >>
     MAP_EVERY qexists_tac [`remove_const (tysof ctxt) consts tm`,
                            `MAP (remove_const (tysof ctxt) consts) h`,
                            `MAP (\(x,y). remove_const (tysof ctxt) consts x, y) ilist`] >>
     simp [MAP_MAP_o, combinTheory.o_DEF, remove_const_vsubst] >>
     first_x_assum (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
     rw [upd_to_subst_def, remove_const_vsubst] >>
     fs [MEM_MAP] >>
     PairCases_on `y` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [has_type_remove_const] >>
     match_mp_tac (SIMP_RULE (srw_ss()) [PULL_EXISTS, upd_to_subst_def] term_ok_remove_upd) >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 6 disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const (tysof ctxt) consts tm`, `MAP (remove_const (tysof ctxt) consts) h`, `tyin`] >>
     rw [] >>
     fs [upd_to_subst_def]
     >- (rw [MAP_MAP_o, combinTheory.o_DEF] >>
         rw [remove_const_inst])
     >- rw [remove_const_inst]
     >- (LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
         rw [upd_to_subst_def]))
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     fs [upd_to_subst_def, remove_const_term_union, remove_const_eq] >>
     MAP_EVERY qexists_tac [`MAP (remove_const (tysof ctxt) consts) h1`,
                            `MAP (remove_const (tysof ctxt) consts) h2`,
                            `remove_const (tysof ctxt) consts l1`,
                            `remove_const (tysof ctxt) consts l2`,
                            `remove_const (tysof ctxt) consts r1`,
                            `remove_const (tysof ctxt) consts r2`] >>
     rw [remove_const_def] >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
     rw [] >>
     rfs [remove_const_eq, upd_to_subst_def, typeof_remove_const, welltyped_remove_const])
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     qexists_tac `remove_const (tysof ctxt) consts t` >>
     rw [remove_const_eq] >>
     fs [upd_to_subst_def]
     >- metis_tac [theory_ok_remove_upd]
     >- (imp_res_tac theory_ok_sig >>
         match_mp_tac (SIMP_RULE (srw_ss()) [PULL_EXISTS, upd_to_subst_def] term_ok_remove_upd) >>
         metis_tac []))
 >- (rw [Once proves_cases] >>
     ntac 9 disj2_tac >>
     disj1_tac >>
     fs [upd_to_subst_def, remove_const_term_union, remove_const_eq] >>
     MAP_EVERY qexists_tac [`MAP (remove_const (tysof ctxt) consts) h1`,
                            `MAP (remove_const (tysof ctxt) consts) h2`,
                            `remove_const (tysof ctxt) consts l`,
                            `remove_const (tysof ctxt) consts m1`,
                            `remove_const (tysof ctxt) consts m2`,
                            `remove_const (tysof ctxt) consts r`] >>
     rw [remove_const_def] >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
     LAST_X_ASSUM (qspecl_then [`ctxt`, `ConstSpec consts p`] mp_tac) >>
     rw [] >>
     rfs [remove_const_eq, upd_to_subst_def] >>
     metis_tac [remove_const_aconv])
 >- (fs [updates_cases, upd_to_subst_def, conexts_of_upd_def, LET_THM] 
     >- metis_tac [use_const_spec]
     >- (rw [Once proves_cases] >>
         ntac 9 disj2_tac >>
         imp_res_tac proves_theory_ok >>
         fs [] >>
         fs [theory_ok_def] >>
         res_tac >>
         metis_tac [remove_const_old_axiom])));
         *)

val _ = export_theory ();