open HolKernel boolLib boolSimps bossLib lcsymtacs pairTheory listTheory pred_setTheory sortingTheory stringTheory holSyntaxLibTheory
val _ = temp_tight_equality()
val _ = new_theory "holSyntax"

val _ = Parse.temp_type_abbrev("stype",``:type``)
val _ = Hol_datatype`type
  = Tyvar of string
  | Tyapp of string => type list`

val _ = Parse.overload_on("Bool",``Tyapp "bool" []``)
val _ = Parse.overload_on("Ind",``Tyapp "ind" []``)
val _ = Parse.overload_on("Fun",``λs t. Tyapp "fun" [s;t]``)

val domain_def = Define`domain (Fun s t) = s`
val codomain_def = Define`codomain (Fun s t) = t`
val domain_def = save_thm("domain_def",SIMP_RULE(srw_ss())[]domain_def)
val codomain_def = save_thm("codomain_def",SIMP_RULE(srw_ss())[]codomain_def)
val _ = export_rewrites["domain_def","codomain_def"]

val _ = Parse.temp_type_abbrev("sterm",``:term``)
val _ = Hol_datatype`term
  = Var of string => holSyntax$type
  | Const of string => holSyntax$type
  | Comb of term => term
  | Abs of string => holSyntax$type => term`

val _ = Parse.overload_on("Equal",``λty. Const "=" (Fun ty (Fun ty Bool))``)
val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty)``)

val _ = Parse.add_infix("has_type",450,Parse.NONASSOC)

val (has_type_rules,has_type_ind,has_type_cases) = Hol_reln`
  ((Var   n ty) has_type ty) ∧
  ((Const n ty) has_type ty) ∧
  (s has_type (Fun dty rty) ∧
   t has_type dty
   ⇒
   (Comb s t) has_type rty) ∧
  (t has_type rty ⇒
   (Abs n dty t) has_type (Fun dty rty))`

val welltyped_def = Define`
  welltyped tm = ∃ty. tm has_type ty`

val typeof_def = Define`
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs n ty t) = Fun ty (typeof t))`
val _ = export_rewrites["typeof_def"]

val WELLTYPED_LEMMA = store_thm("WELLTYPED_LEMMA",
  ``∀tm ty. tm has_type ty ⇒ (typeof tm = ty)``,
  ho_match_mp_tac has_type_ind >>
  simp[typeof_def,has_type_rules,codomain_def])

val WELLTYPED = store_thm("WELLTYPED",
  ``∀tm. welltyped tm ⇔ tm has_type (typeof tm)``,
  simp[welltyped_def] >> metis_tac[WELLTYPED_LEMMA])

val WELLTYPED_CLAUSES = store_thm("WELLTYPED_CLAUSES",
 ``(!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!n ty t. welltyped (Abs n ty t) = welltyped t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped_def] THEN
  rw[Once has_type_cases] >>
  metis_tac[WELLTYPED,WELLTYPED_LEMMA])
val _ = export_rewrites["WELLTYPED_CLAUSES"]

val _ = Parse.add_infix("===",460,Parse.RIGHT)

val equation_def = xDefine "equation"`
  (s === t) = Comb (Comb (Equal(typeof s)) s) t`

val EQUATION_HAS_TYPE_BOOL = store_thm("EQUATION_HAS_TYPE_BOOL",
  ``∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t)``,
  rw[equation_def] >> rw[Ntimes has_type_cases 3] >>
  metis_tac[WELLTYPED_LEMMA,WELLTYPED])

val (RACONV_rules,RACONV_ind,RACONV_cases) = Hol_reln`
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  ((ty1 = ty2) ∧ RACONV ((Var x1 ty1,Var x2 ty2)::env) (t1,t2)
    ⇒ RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`

val RACONV = store_thm("RACONV",
 ``(RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2) <=>
        (ty1 = ty2) /\ RACONV (CONS (Var x1 ty1,Var x2 ty2) env) (t1,t2))``,
  REPEAT CONJ_TAC THEN simp[Once RACONV_cases] >> metis_tac[])

val ACONV_def = Define`
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)`

val RACONV_REFL = store_thm("RACONV_REFL",
  ``∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t)``,
  Induct >> simp[RACONV,ALPHAVARS_REFL])

val ACONV_REFL = store_thm("ACONV_REFL",
  ``∀t. ACONV t t``,
  simp[ACONV_def,RACONV_REFL])
val _ = export_rewrites["ACONV_REFL"]

val ALPHAVARS_TYPE = store_thm("ALPHAVARS_TYPE",
  ``∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t``,
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> rw[])

val RACONV_TYPE = store_thm("RACONV_TYPE",
  ``∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p)``,
  ho_match_mp_tac RACONV_ind >>
  simp[FORALL_PROD,typeof_def,WELLTYPED_CLAUSES] >>
  rw[] >> imp_res_tac ALPHAVARS_TYPE >>
  fs[typeof_def,WELLTYPED_CLAUSES])

val ACONV_TYPE = store_thm("ACONV_TYPE",
  ``∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)``,
  rw[ACONV_def] >> imp_res_tac RACONV_TYPE >> fs[])

val TERM_UNION_def = Define`
  TERM_UNION [] l2 = l2 ∧
  TERM_UNION (h::t) l2 =
    let subun = TERM_UNION t l2 in
    if EXISTS (ACONV h) subun then subun else h::subun`

val TERM_UNION_NONEW = store_thm("TERM_UNION_NONEW",
  ``∀l1 l2 x. MEM x (TERM_UNION l1 l2) ⇒ MEM x l1 ∨ MEM x l2``,
  Induct >> simp[TERM_UNION_def] >> rw[] >> metis_tac[])

val TERM_UNION_THM = store_thm("TERM_UNION_THM",
  ``∀l1 l2 x. MEM x l1 ∨ MEM x l2
              ⇒ ∃y. MEM y (TERM_UNION l1 l2) ∧ ACONV x y``,
  Induct >> simp[TERM_UNION_def] >> rw[EXISTS_MEM] >> metis_tac[ACONV_REFL])

val ALL_BOOL_TERM_UNION = store_thm("ALL_BOOL_TERM_UNION",
  ``EVERY (λa. a has_type Bool) l1 ∧ EVERY (λa. a has_type Bool) l2
    ⇒ EVERY (λa. a has_type Bool) (TERM_UNION l1 l2)``,
  rw[EVERY_MEM] >> metis_tac[TERM_UNION_NONEW])

val VFREE_IN_def = Define`
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs x ty t) ⇔ (Var x ty ≠ v) ∧ VFREE_IN v t)`
val _ = export_rewrites["VFREE_IN_def"]

val VFREE_IN_RACONV = store_thm("VFREE_IN_RACONV",
  ``∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env)``,
  ho_match_mp_tac RACONV_ind >> simp[VFREE_IN_def] >>
  reverse conj_tac >- metis_tac[] >>
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> metis_tac[])

val VFREE_IN_ACONV = store_thm("VFREE_IN_ACONV",
  ``∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t)``,
  rw[ACONV_def] >> imp_res_tac VFREE_IN_RACONV >> fs[])

val CLOSED_def = Define`
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)`

val TYPE_SUBST_def = tDefine"TYPE_SUBST"`
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))`
(WF_REL_TAC`measure (type_size o SND)` >> simp[] >>
 gen_tac >> Induct >> simp[definition"type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])
val _ = export_rewrites["TYPE_SUBST_def"]

val VFREE_IN_FINITE = store_thm("VFREE_IN_FINITE",
  ``∀t. FINITE {x | VFREE_IN x t}``,
  Induct >> simp[VFREE_IN_def] >- (
    qmatch_abbrev_tac`FINITE z` >>
    qmatch_assum_abbrev_tac`FINITE x` >>
    qpat_assum`FINITE x`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE y` >>
    qsuff_tac`z = x ∪ y`>-metis_tac[FINITE_UNION] >>
    simp[Abbr`x`,Abbr`y`,Abbr`z`,EXTENSION] >> metis_tac[]) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE x` >>
  qmatch_abbrev_tac`FINITE z` >>
  qsuff_tac`∃y. z = x DIFF y`>-metis_tac[FINITE_DIFF] >>
  simp[Abbr`z`,Abbr`x`,EXTENSION] >>
  metis_tac[IN_SING])

val VFREE_IN_FINITE_ALT = store_thm("VFREE_IN_FINITE_ALT",
  ``∀t ty. FINITE {x | VFREE_IN (Var x ty) t}``,
  rw[] >> match_mp_tac (MP_CANON SUBSET_FINITE) >>
  qexists_tac`IMAGE (λt. case t of Var x y => x) {x | VFREE_IN x t}` >>
  simp[VFREE_IN_FINITE,IMAGE_FINITE] >>
  simp[SUBSET_DEF] >> rw[] >>
  HINT_EXISTS_TAC >> simp[])

val PRIMED_NAME_EXISTS = store_thm("PRIMED_NAME_EXISTS",
  ``∃n. ¬(VFREE_IN (Var (APPEND x (GENLIST (K #"'") n)) ty) t)``,
  qspecl_then[`t`,`ty`]mp_tac VFREE_IN_FINITE_ALT >>
  disch_then(mp_tac o CONJ PRIMED_INFINITE) >>
  disch_then(mp_tac o MATCH_MP INFINITE_DIFF_FINITE) >>
  simp[GSYM MEMBER_NOT_EMPTY] >> rw[] >> metis_tac[])

val LEAST_EXISTS = prove(
  ``(∃n. P n) ⇒ ∃k. P k ∧ ∀m. m < k ⇒ ¬(P m)``,
  metis_tac[whileTheory.LEAST_EXISTS])

val VARIANT_PRIMES_def = new_specification
  ("VARIANT_PRIMES_def"
  ,["VARIANT_PRIMES"]
  ,(PRIMED_NAME_EXISTS
   |> HO_MATCH_MP LEAST_EXISTS
   |> Q.GENL[`ty`,`x`,`t`]
   |> SIMP_RULE std_ss [SKOLEM_THM]))

val VARIANT_def = Define`
  VARIANT t x ty = APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty))`

val VARIANT_THM = store_thm("VARIANT_THM",
  ``∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t``,
  metis_tac[VARIANT_def,VARIANT_PRIMES_def])

val VSUBST_def = Define`
  (VSUBST ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (VSUBST ilist (Const x ty) = Const x ty) ∧
  (VSUBST ilist (Comb s t) = Comb (VSUBST ilist s) (VSUBST ilist t)) ∧
  (VSUBST ilist (Abs x ty t) =
    let ilist' = FILTER (λ(s',s). ¬(s = Var x ty)) ilist in
    let t' = VSUBST ilist' t in
    if EXISTS (λ(s',s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s t) ilist'
    then let z = VARIANT t' x ty in
         let ilist'' = CONS (Var z ty,Var x ty) ilist' in
         Abs z ty (VSUBST ilist'' t)
    else Abs x ty t')`

val VSUBST_HAS_TYPE = store_thm("VSUBST_HAS_TYPE",
  ``∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty``,
  Induct >> simp[VSUBST_def]
  >- (
    map_every qx_gen_tac[`x`,`ty`,`tty`] >>
    Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> rw[] >> fs[] >>
    qpat_assum`X has_type tty`mp_tac >>
    simp[Once has_type_cases]>>rw[]>>rw[])
  >- (
    simp[Once has_type_cases] >> rw[] >>
    rw[Once has_type_cases] >> metis_tac[] )
  >- (
    map_every qx_gen_tac[`ty`,`x`,`fty`,`ilist`] >>
    simp[Once has_type_cases] >> rw[] >>
    simp[Once has_type_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    simp[MEM_FILTER] >> rw[] >> TRY(metis_tac[]) >>
    simp[Once has_type_cases]))

val VSUBST_WELLTYPED = store_thm("VSUBST_WELLTYPED",
  ``∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm)``,
  metis_tac[VSUBST_HAS_TYPE,welltyped_def])

val VFREE_IN_VSUBST = store_thm("VFREE_IN_VSUBST",
  ``∀tm u uty ilist.
      VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
        ∃y ty. VFREE_IN (Var y ty) tm ∧
               VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))``,
  Induct >> simp[VFREE_IN_def,VSUBST_def] >- metis_tac[] >>
  map_every qx_gen_tac[`xty`,`x`,`u`,`uty`,`ilist`] >>
  qmatch_abbrev_tac`VFREE_IN vu (if p then Abs vx xty (VSUBST l1 tm) else Abs x xty (VSUBST l2 tm)) ⇔ q` >>
  qsuff_tac`VFREE_IN vu (Abs (if p then vx else x) xty (VSUBST (if p then l1 else l2) tm)) ⇔ q` >- metis_tac[] >>
  simp[VFREE_IN_def,Abbr`vu`] >>
  rw[] >- (
    simp[Abbr`q`,Abbr`l1`,REV_ASSOCD,Abbr`l2`,REV_ASSOCD_FILTER] >>
    EQ_TAC >- (
      rw[] >>
      pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
      metis_tac[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(vx = VARIANT t x xty)` >>
    qspecl_then[`t`,`x`,`xty`]mp_tac VARIANT_THM >> strip_tac >>
    qmatch_assum_abbrev_tac`Abbrev(t = VSUBST ll tm)` >>
    rfs[Abbr`t`] >>
    fs[Abbr`vx`] >> strip_tac >>
    (conj_tac >- (
      spose_not_then strip_assume_tac >>
      first_x_assum(qspecl_then[`y`,`ty`]mp_tac) >>
      simp[Abbr`ll`,REV_ASSOCD_FILTER])) >>
    map_every qexists_tac[`y`,`ty`] >> simp[]) >>
  simp[Abbr`q`,Abbr`l2`,REV_ASSOCD_FILTER,Abbr`l1`,Abbr`vx`] >>
  EQ_TAC >- (
    rw[] >>
    pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
    metis_tac[] ) >>
  fs[EXISTS_MEM,EVERY_MEM,markerTheory.Abbrev_def,MEM_FILTER,FORALL_PROD] >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  rpt gen_tac >>
  Cases_on`∃a. MEM (a,Var y ty) ilist ∧ VFREE_IN (Var x xty) a` >- (
    fs[] >> first_x_assum(qspecl_then[`a`,`Var y ty`]mp_tac) >>
    simp[] >> rw[] >> fs[] >> fs[VFREE_IN_def] >>
    metis_tac[] ) >> fs[] >>
  Cases_on`VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`>>simp[] >>
  Cases_on`Var u uty = Var y ty`>- (
    fs[] >> metis_tac[] ) >>
  Q.ISPECL_THEN[`ilist`,`Var y ty`,`Var y ty`]mp_tac REV_ASSOCD_MEM >>
  strip_tac >> fs[] >>
  fs[VFREE_IN_def] >>
  metis_tac[])

val sizeof_def = Define`
  sizeof (Var x ty) = 1 ∧
  sizeof (Const x ty) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs x ty t) = 2 + sizeof t`
val _ = export_rewrites["sizeof_def"]

val SIZEOF_VSUBST = store_thm("SIZEOF_VSUBST",
  ``∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t``,
  Induct >> simp[VSUBST_def] >> rw[VSUBST_def] >> simp[] >- (
    Q.ISPECL_THEN[`ilist`,`Var s t`,`Var s t`]mp_tac REV_ASSOCD_MEM >>
    rw[] >> res_tac >> pop_assum SUBST1_TAC >> simp[] )
  >- metis_tac[] >>
  first_x_assum match_mp_tac >>
  simp[MEM_FILTER] >>
  rw[] >> res_tac >> fs[] )

val sizeof_positive = store_thm("sizeof_positive",
  ``∀t. 0 < sizeof t``,
  Induct >> simp[])

val INST_CORE_def = tDefine"INST_CORE"`
  (INST_CORE env tyin (Var x ty) =
     let tm = Var x ty in
     let tm' = Var x (TYPE_SUBST tyin ty) in
     if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') ∧
  (INST_CORE env tyin (Const x ty) =
    Result(Const x (TYPE_SUBST tyin ty))) ∧
  (INST_CORE env tyin (Comb s t) =
    let sres = INST_CORE env tyin s in
    if IS_CLASH sres then sres else
    let tres = INST_CORE env tyin t in
    if IS_CLASH tres then tres else
    let s' = RESULT sres and t' = RESULT tres in
    Result (Comb s' t')) ∧
  (INST_CORE env tyin (Abs x ty t) =
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x ty,Var x ty')::env in
    let tres = INST_CORE env' tyin t in
    if IS_RESULT tres then Result(Abs x ty' (RESULT tres)) else
    let w = CLASH tres in
    if (w ≠ Var x ty') then tres else
    let x' = VARIANT (RESULT(INST_CORE [] tyin t)) x ty' in
    let t' = VSUBST [Var x' ty,Var x ty] t in
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x' ty,Var x' ty')::env in
    let tres = INST_CORE env' tyin t' in
    if IS_RESULT tres then Result(Abs x' ty' (RESULT tres)) else tres)`
(WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST])

val INST_CORE_HAS_TYPE = store_thm("INST_CORE_HAS_TYPE",
  ``∀n tm env tyin.
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀s s'. MEM (s,s') env ⇒
              ∃x ty. (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      ⇒ (∃x ty. (INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃tm'. INST_CORE env tyin tm = Result tm' ∧
               tm' has_type (TYPE_SUBST tyin (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                        ∃oty. VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty))``,
  gen_tac >> completeInduct_on`n` >>
  Induct >> simp[Once INST_CORE_def] >>
  TRY (
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    NO_TAC )
  >- (
    pop_assum kall_tac >> rw[] >>
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][] >>
    simp[Once INST_CORE_def] >>
    first_assum(qspec_then`sizeof tm`mp_tac) >>
    first_x_assum(qspec_then`sizeof tm'`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tm'`,`env`,`tyin`]mp_tac) >> simp[] >>
    qmatch_abbrev_tac`P ⇒ Q` >> strip_tac >>
    qunabbrev_tac`Q` >>
    disch_then(qspecl_then[`tm`,`env`,`tyin`]mp_tac) >>
    simp[] >>
    qunabbrev_tac`P` >>
    reverse (strip_tac >> fs[]) >- (
      simp[Once has_type_cases] >>
      metis_tac[] ) >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][] >>
    Q.PAT_ABBREV_TAC`env' = X::env` >>
    Q.PAT_ABBREV_TAC`tm' = VSUBST X tm` >>
    Q.PAT_ABBREV_TAC`env'' = X::env` >>
    `sizeof tm' = sizeof tm` by (
      simp[Abbr`tm'`,SIZEOF_VSUBST] ) >>
    `welltyped tm'` by (
      simp[Abbr`tm'`] >>
      match_mp_tac VSUBST_WELLTYPED >>
      simp[] >> simp[Once has_type_cases] ) >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    simp[Once INST_CORE_def] >>
    disch_then(fn th =>
      qspecl_then[`tm`,`env'`,`tyin`]mp_tac th >>
      qspecl_then[`tm'`,`env''`,`tyin`]mp_tac th >>
      qspecl_then[`tm`,`[]`,`tyin`]mp_tac th) >> simp[] >>
    qmatch_abbrev_tac`a ⇒ b` >> strip_tac >> qunabbrev_tac`b` >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`p`,`q`,`r`] >> pop_assum kall_tac >>
    qmatch_abbrev_tac`x ⇒ (p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`x`,`p`,`q`,`r`] >> pop_assum kall_tac >>
    qunabbrev_tac`a` >>
    fs[] >- (
      rw[] >> fs[] >> fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD] ) >>
    strip_tac >> fs[] >- (
      strip_tac >> fs[] >- (
        fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        metis_tac[VARIANT_THM] ) >>
      fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      simp[Once has_type_cases] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      rw[] >> fs[] >>
      metis_tac[VARIANT_THM,theorem"term_11"]) >>
    strip_tac >> fs[] >- (
      rw[] >> fs[] >>
      fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      simp[Once has_type_cases] >>
      TRY (
        qmatch_assum_abbrev_tac`tz has_type TYPE_SUBST tyin (typeof (VSUBST ez tm))` >>
        `typeof (VSUBST ez tm) = typeof tm` by (
          match_mp_tac WELLTYPED_LEMMA >>
          match_mp_tac VSUBST_HAS_TYPE >>
          conj_tac >- metis_tac[WELLTYPED] >>
          simp[Abbr`ez`] >>
          simp[Once has_type_cases] ) >>
        unabbrev_all_tac >> fs[] >>
        fs[GSYM LEFT_FORALL_IMP_THM] >>
        first_x_assum(qspecl_then[`x'`,`ty'`,`x'`,`ty'`]mp_tac) >>
        simp[] >> BasicProvers.CASE_TAC >> simp[] >> strip_tac >> fs[] >>
        `VFREE_IN (Var x' (TYPE_SUBST tyin ty')) tm''` by metis_tac[] >>
        metis_tac[VARIANT_THM]) >>
      TRY (
        EQ_TAC >> rw[] >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        pop_assum mp_tac >> rw[] >> fs[] >>
        TRY (
          qexists_tac`oty`>>simp[] >>
          map_every qexists_tac[`u`,`oty`] >>
          simp[] >> NO_TAC) >>
        metis_tac[VARIANT_THM,theorem"term_11",VSUBST_HAS_TYPE,WELLTYPED] ) >>
      metis_tac[VARIANT_THM,theorem"term_11",VSUBST_HAS_TYPE,WELLTYPED] ) >>
    rw[] >> fs[] >>
    fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp[Once has_type_cases] >>
    metis_tac[VARIANT_THM,theorem"term_11"]))

val INST_def = Define`INST tyin tm = RESULT(INST_CORE [] tyin tm)`

val tyvars_def = tDefine"tyvars"`
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys`
(WF_REL_TAC`measure type_size` >> simp[] >>
 gen_tac >> Induct >>
 simp[definition"type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val tvars_def = Define`
  (tvars (Var n ty) = tyvars ty) /\
  (tvars (Const n ty) = tyvars ty) /\
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) /\
  (tvars (Abs n ty t) = LIST_UNION (tyvars ty) (tvars t))`

val _ = Hol_datatype`def
  = Constdef of (string # holSyntax$term) list => holSyntax$term
  | Typedef of string => holSyntax$term => string => string`

val types_aux_def = Define`
  (types_aux (Constdef eqs p) = []) /\
  (types_aux (Typedef tyname t a r) = [(tyname,LENGTH (tvars t))])`

val types_def = Define
 `types defs = FLAT (MAP types_aux defs)++[("ind",0);("bool",0);("fun",2)]`

val consts_aux_def = Define
 `(consts_aux (Constdef eqs p) = MAP (\(s,t). (s, typeof t)) eqs) /\
  (consts_aux (Typedef tyname t a r) =
     let rep_type = domain (typeof t) in
     let abs_type = Tyapp tyname (MAP Tyvar (STRING_SORT (tvars t))) in
       [(a,Fun rep_type abs_type);
        (r,Fun abs_type rep_type)])`

val consts_def = Define
 `consts defs = FLAT (MAP consts_aux defs)++[("@",typeof(Select(Tyvar"A")));("=",typeof(Equal(Tyvar"A")))]`

val _ = Parse.add_infix("|-",450,Parse.NONASSOC)

val _ = Parse.overload_on("Exists",``λx ty p. Comb (Const "?" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Forall",``λx ty p. Comb (Const "!" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("And",``λp1 p2. Comb (Comb (Const "/\\" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Truth",``Const "T" Bool``)
val _ = Parse.overload_on("Falsity",``Const "F" Bool``)
val _ = Parse.overload_on("Implies",``λp1 p2. Comb (Comb (Const "==>" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Not",``λp. Comb (Const "~" (Fun Bool Bool)) p``)
val _ = Parse.overload_on("One_One",``λa b f. Comb (Const "ONE_ONE" (Fun (Fun a b) Bool)) f``)
val _ = Parse.overload_on("Onto",``λa b f. Comb (Const "ONTO" (Fun (Fun a b) Bool)) f``)

val _ = Parse.overload_on("CD1",``λn t. Constdef [(n,t)] (Var n (typeof t) === t)``)

val (proves_rules,proves_ind,proves_cases) = xHol_reln"proves"
 `(!n defs. context_ok defs ==> type_ok defs (Tyvar n)) /\
  (!defs. context_ok defs ==> type_ok defs Ind) /\
  (!defs tm ty. term_ok defs tm /\ tm has_type ty ==> type_ok defs ty) /\
  (!defs n ls ty. type_ok defs (Tyapp n ls) /\ MEM ty ls ==> type_ok defs ty) /\

  (!defs x ty. type_ok defs ty ==> term_ok defs (Var x ty)) /\
  (!defs t1 t2. term_ok defs t1 /\ term_ok defs t2 /\ welltyped (Comb t1 t2) ==> term_ok defs (Comb t1 t2)) /\
  (!defs x ty tm. term_ok defs tm /\ type_ok defs ty ==> term_ok defs (Abs x ty tm)) /\
  (!defs t1 t2. term_ok defs (Comb t1 t2) ==> term_ok defs t1) /\
  (!defs t1 t2. term_ok defs (Comb t1 t2) ==> term_ok defs t2) /\
  (!defs x ty tm. term_ok defs (Abs x ty tm) ==> term_ok defs tm) /\
  (!defs x t eqs p. context_ok defs /\ MEM (Constdef eqs p) defs /\ MEM (x,t) eqs
                     ==> term_ok defs (Const x (typeof t))) /\
  (!defs h c t. (defs,h) |- c /\ MEM t (c::h) ==> term_ok defs t) /\

  (context_ok []) /\
  (!defs h c. (defs,h) |- c ==> context_ok defs) /\

  (!t defs.
        context_ok defs /\ term_ok defs t
        ==> (defs, []) |- t === t) /\
  (!asl1 asl2 l m1 m2 r defs.
        (defs, asl1) |- l === m1 /\ (defs, asl2) |- m2 === r /\ ACONV m1 m2
        ==> (defs, TERM_UNION asl1 asl2) |- l === r) /\
  (!asl1 l1 r1 asl2 l2 r2 defs.
        (defs, asl1) |- l1 === r1 /\
        (defs, asl2) |- l2 === r2 /\ welltyped(Comb l1 l2)
        ==> (defs, TERM_UNION asl1 asl2) |- Comb l1 l2 === Comb r1 r2) /\
  (!asl x ty l r defs.
        ~(EXISTS (VFREE_IN (Var x ty)) asl) /\ type_ok defs ty /\
        (defs, asl) |- l === r
        ==> (defs, asl) |- (Abs x ty l) === (Abs x ty r)) /\
  (!x ty t defs.
        context_ok defs /\ term_ok defs t /\ type_ok defs ty
        ==> (defs, []) |- Comb (Abs x ty t) (Var x ty) === t) /\
  (!p defs.
        context_ok defs /\ p has_type Bool /\ term_ok defs p
        ==> (defs, [p]) |- p) /\
  (!asl1 asl2 p q p' defs.
        (defs, asl1) |- p === q /\ (defs, asl2) |- p' /\ ACONV p p'
        ==> (defs, TERM_UNION asl1 asl2) |- q) /\
  (!asl1 asl2 c1 c2 defs.
        (defs, asl1) |- c1 /\ (defs, asl2) |- c2
        ==> (defs, TERM_UNION (FILTER((~) o ACONV c2) asl1)
                              (FILTER((~) o ACONV c1) asl2))
               |- c1 === c2) /\
  (!tyin asl p defs.
        (!s s'. MEM (s',s) tyin ==> type_ok defs s') /\
        (defs, asl) |- p
        ==> (defs, MAP (INST tyin) asl) |- INST tyin p) /\
  (!ilist asl p defs.
        (!s s'. MEM (s',s) ilist ==> ?x ty. (s = Var x ty) /\ s' has_type ty /\
                                            term_ok defs s') /\
        (defs, asl) |- p
        ==> (defs, MAP (VSUBST ilist) asl) |- VSUBST ilist p) /\
  (!asl p eqs c defs.
        (defs, asl) |- p /\
        (defs, MAP (\(s,t). Var s (typeof t) === t) eqs) |- c /\
        EVERY
          (\t. CLOSED t /\
               (!v. MEM v (tvars t) ==> MEM v (tyvars (typeof t))))
          (MAP SND eqs) /\
        (!x ty. VFREE_IN (Var x ty) c ==> MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
        ALL_DISTINCT (MAP FST eqs ++ MAP FST (consts defs))
        ==> (CONS (Constdef eqs c) defs, asl) |- p) /\
  (!eqs p ilist defs.
        context_ok defs /\ MEM (Constdef eqs p) defs /\
        (ilist = MAP (\(s,t). (Const s (typeof t),Var s (typeof t))) eqs)
        ==> (defs, []) |- VSUBST ilist p) /\
  (!asl p tyname t a r defs x rep_type abs_type y d.
        (d = Typedef tyname t a r) /\
        (abs_type = Tyapp tyname (MAP Tyvar (STRING_SORT (tvars t)))) /\
        (defs, []) |- Comb t y /\
        CLOSED t /\ t has_type (Fun rep_type Bool) /\
        ~(MEM tyname (MAP FST (types defs))) /\
        ~(MEM a (MAP FST (consts defs))) /\
        ~(MEM r (MAP FST (consts defs))) /\
        ~(a = r) /\
        ( (defs, asl) |- p  \/
          ((asl,p) = ([],
             Comb (Const a (Fun rep_type abs_type))
                    (Comb (Const r (Fun abs_type rep_type))
                          (Var x abs_type)) === Var x abs_type)) \/
          ((asl,p) = ([],
             Comb t (Var x rep_type) ===
                Comb (Const r (Fun abs_type rep_type))
                     (Comb (Const a (Fun rep_type abs_type))
                           (Var x rep_type)) === Var x rep_type)) )
        ==> (CONS d defs, asl) |- p) /\
  (!ty1 ty2 defs.
    context_ok defs /\ type_ok defs ty1 /\ type_ok defs ty2
    ==> (defs,[]) |- Abs x ty1 (Comb (Var f (Fun ty1 ty2)) (Var x ty1)) === Var f (Fun ty1 ty2)) /\
  (!asl p w ty defs.
     p has_type (Fun ty Bool) /\ (defs,asl) |- Comb p w
     ==> (defs,asl) |- Comb p (Comb (Select ty) p)) /\
  (!defs.
    context_ok defs ∧
    MEM (CD1 "T" (Abs "p" Bool (Var "p" Bool) === Abs "p" Bool (Var "p" Bool))) defs ∧
    MEM (CD1 "/\\" (Abs "p" Bool
                          (Abs "q" Bool
                            (Abs "f" (Fun Bool (Fun Bool Bool))
                              (Comb (Comb (Var "f" (Fun Bool (Fun Bool Bool))) (Var "p" Bool)) (Var "q" Bool))
                             ===
                             Abs "f" (Fun Bool (Fun Bool Bool))
                               (Comb (Comb (Var "f" (Fun Bool (Fun Bool Bool))) Truth) Truth))))) defs ∧
    MEM (CD1 "==>" (Abs "p" Bool
                          (Abs "q" Bool
                            (And (Var "p" Bool) (Var "q" Bool) === Var "p" Bool)))) defs ∧
    MEM (CD1 "!" (Abs "P" (Fun (Tyvar "A") Bool)
                        (Var "P" (Fun (Tyvar "A") Bool) === Abs "x" (Tyvar "A") Truth))) defs ∧
    MEM (CD1 "?" (Abs "P" (Fun (Tyvar "A") Bool)
                        (Forall "q" Bool
                          (Implies
                            (Forall "x" (Tyvar "A")
                              (Implies (Comb (Var "P" (Fun (Tyvar "A") Bool)) (Var "x" (Tyvar "A")))
                                       (Var "q" Bool)))
                            (Var "q" Bool))))) defs ∧
    MEM (CD1 "F" (Forall "p" Bool (Var "p" Bool))) defs ∧
    MEM (CD1 "~" (Abs "p" Bool (Implies (Var "p" Bool) Falsity))) defs ∧
    MEM (CD1 "ONE_ONE"
          (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
            (Forall "x1" (Tyvar "A")
              (Forall "x2" (Tyvar "A")
                (Implies
                  (Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B"))) (Var "x1" (Tyvar "A"))
                   ===
                   Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B"))) (Var "x2" (Tyvar "A")))
                  (Var "x1" (Tyvar "A")
                   ===
                   Var "x2" (Tyvar "A"))))))) defs ∧
    MEM (CD1 "ONTO"
          (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
            (Forall "y" (Tyvar "B")
              (Exists "x" (Tyvar "A")
                (Var "y" (Tyvar "B")
                 ===
                 Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B")))
                      (Var "x" (Tyvar "A"))))))) defs
    ==> (defs,[]) |- Exists "f" (Fun Ind Ind)
                       (And (One_One Ind Ind (Var "f" (Fun Ind Ind)))
                            (Not (Onto Ind Ind (Var "f" (Fun Ind Ind))))))`

val RACONV_TRANS = store_thm("RACONV_TRANS",
  ``∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)``,
  ho_match_mp_tac RACONV_ind >> simp[RACONV] >>
  conj_tac >- (
    Induct >- simp[ALPHAVARS_def] >>
    Cases >> simp[ALPHAVARS_def] >>
    rw[] >> Cases_on`vs`>>fs[] >>
    Cases_on`t`>>fs[RACONV]>>
    fs[ALPHAVARS_def] >> rw[] >>
    metis_tac[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  rw[] >>
  Cases_on`t`>>fs[RACONV]>>rw[]>>
  metis_tac[LENGTH,ZIP])

val ACONV_TRANS = store_thm("ACONV_TRANS",
  ``∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3``,
  rw[ACONV_def] >> imp_res_tac RACONV_TRANS >> fs[LENGTH_NIL])

val RACONV_SYM = store_thm("RACONV_SYM",
  ``∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)``,
  ho_match_mp_tac RACONV_ind >> simp[] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >>
    rw[] >> res_tac >> fs[RACONV]) >>
  simp[RACONV])

val ACONV_SYM = store_thm("ACONV_SYM",
  ``∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1``,
  rw[ACONV_def] >> imp_res_tac RACONV_SYM >> fs[])

val type_ind = save_thm("type_ind",
  TypeBase.induction_of``:holSyntax$type``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`)

val tyvars_ALL_DISTINCT = store_thm("tyvars_ALL_DISTINCT",
  ``∀ty. ALL_DISTINCT (tyvars ty)``,
  ho_match_mp_tac type_ind >>
  rw[tyvars_def] >>
  Induct_on`l` >> simp[] >>
  rw[ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tyvars_ALL_DISTINCT"]

val tvars_ALL_DISTINCT = store_thm("tvars_ALL_DISTINCT",
  ``∀tm. ALL_DISTINCT (tvars tm)``,
  Induct >> simp[tvars_def,ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tvars_ALL_DISTINCT"]

val _ = export_theory()
