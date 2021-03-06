open HolKernel boolLib boolSimps bossLib lcsymtacs pairTheory listTheory pred_setTheory holSyntaxLibTheory
val _ = temp_tight_equality()
val _ = new_theory "sholSyntax"

val _ = Hol_datatype`
    term
    = Var of string => type
    | Const of string => type => const_tag
    | Comb of term => term
    | Abs of string => type => term
  ; type
    = Tyvar of string
    | Tyapp of type_op => type list
  ; type_op
    = Typrim of string => num
    | Tydefined of string => term
  ; const_tag
    = Prim
    | Defined of num => (string#term) list => term
    | Tyabs of string => term
    | Tyrep of string => term`

val _ = Parse.overload_on("Fun",``λs t. Tyapp (Typrim "fun" 2) [s;t]``)
val _ = Parse.overload_on("Bool",``Tyapp (Typrim "bool" 0) []``)
val _ = Parse.overload_on("Ind",``Tyapp (Typrim "ind" 0) []``)
val _ = Parse.overload_on("Equal" ,``λty. Const "=" (Fun ty (Fun ty Bool)) Prim``)
val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty) Prim``)

val domain_def = Define`domain (Tyapp op args) = if op = (Typrim "fun" 2) then EL 0 args else ARB`
val domain_rwt = store_thm("domain_rwt", ``domain (Fun s t) = s``, rw[domain_def])
val codomain_def = Define`codomain (Tyapp op args) = if op = (Typrim "fun" 2) then EL 1 args else ARB`
val codomain_rwt = store_thm("codomain_rwt", ``codomain (Fun s t) = t``, rw[codomain_def])
val _ = export_rewrites["domain_rwt","codomain_rwt"]

val _ = Parse.add_infix("has_type",450,Parse.NONASSOC)

val (has_type_rules,has_type_ind,has_type_cases) = Hol_reln`
  ((Var   n ty)   has_type ty) ∧
  ((Const n ty g) has_type ty) ∧
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
  (typeof (Const n ty _) = ty) ∧
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
   (!n ty g. welltyped(Const n ty g)) /\
   (!ty. welltyped(Equal ty)) /\
   (!ty. welltyped(Select ty)) /\
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
  (RACONV env (Const x ty g,Const x ty g)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  ((ty1 = ty2) ∧ RACONV ((Var x1 ty1,Var x2 ty2)::env) (t1,t2)
    ⇒ RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`

val RACONV = store_thm("RACONV",
 ``(RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2 g2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Const x1 ty1 g1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1 g1,Const x2 ty2 g2) <=>
     (x1 = x2) /\ (ty1 = ty2) /\ (g1 = g2)) /\
   (RACONV env (Const x1 ty1 g1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1 g1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2 g2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Const x2 ty2 g2) <=> F) /\
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
  (VFREE_IN v (Const x ty g) ⇔ (Const x ty g = v)) ∧
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
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys))`
(WF_REL_TAC`measure (type_size o SND)` >> simp[] >>
 gen_tac >> Induct >> simp[definition"term_size_def"] >> rw[] >>
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
  (VSUBST ilist (Const x ty g) = Const x ty g) ∧
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
    map_every qx_gen_tac[`x`,`ty`] >>
    Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> rw[] >> fs[] >>
    qpat_assum`X has_type ty`mp_tac >>
    simp[Once has_type_cases]>>rw[]>>rw[])
  >- (
    simp[Once has_type_cases] >> rw[] >>
    rw[Once has_type_cases] >> metis_tac[] )
  >- (
    map_every qx_gen_tac[`x`,`fty`,`ilist`] >>
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
  map_every qx_gen_tac[`x`,`u`,`uty`,`ilist`] >>
  qmatch_abbrev_tac`VFREE_IN vu (if p then Abs vx xty (VSUBST l1 tm) else Abs x xty (VSUBST l2 tm)) ⇔ q` >>
  qsuff_tac`VFREE_IN vu (Abs (if p then vx else x) xty (VSUBST (if p then l1 else l2) tm)) ⇔ q` >- metis_tac[] >>
  simp[VFREE_IN_def,Abbr`vu`] >>
  rw[] >- (
    simp[Abbr`q`,Abbr`l1`,REV_ASSOCD,Abbr`l2`,REV_ASSOCD_FILTER] >>
    EQ_TAC >- (
      rw[] >>
      pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
      metis_tac[] ) >>
    pop_assum kall_tac >>
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
  sizeof (Var _ _) = 1 ∧
  sizeof (Const _ _ _) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs _ _ t) = 2 + sizeof t`
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
  (INST_CORE env tyin (Const x ty g) =
    Result(Const x (TYPE_SUBST tyin ty) g)) ∧
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
 simp[definition"term_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val tvars_def = Define`
  (tvars (Var _ ty) = tyvars ty) /\
  (tvars (Const _ ty _) = tyvars ty) /\
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) /\
  (tvars (Abs _ ty t) = LIST_UNION (tyvars ty) (tvars t))`

val _ = Parse.add_infix("|-",450,Parse.NONASSOC)

val _ = Parse.overload_on("closed",``λt. ∀n ty. ¬VFREE_IN (Var n ty) t``)

val typeof_shadow_def = Define`typeof_shadow = typeof`
val _ = Parse.overload_on("Const1",``λname ty rhs.
  Const name ty (Defined 0 [(name,rhs)] (Var name (typeof_shadow rhs) === rhs))``)

val pid = ``Abs "p" Bool (Var "p" Bool)``
val TT_def = Define `TT = Const1 "T" Bool (^pid === ^pid)`

val AN_ty = ``Fun Bool (Fun Bool Bool)``
val AN_tm = ``Const1 "/\\" ^AN_ty
    (Abs "p" Bool
      (Abs "q" Bool
        (Abs "f" ^AN_ty
           (Comb (Comb (Var "f" ^AN_ty) (Var "p" Bool)) (Var "q" Bool))
         ===
         Abs "f" ^AN_ty
           (Comb (Comb (Var "f" ^AN_ty) TT) TT))))``
val AN_def = Define `AN p = Comb (Comb ^AN_tm p)`

val IM_tm = ``Const1 "==>" ^AN_ty
    (Abs "p" Bool
      (Abs "q" Bool
        (AN (Var "p" Bool) (Var "q" Bool) === (Var "p" Bool))))``
val IM_def = Define `IM p = Comb (Comb ^IM_tm p)`

val P_ty = ``Fun (Tyvar "A") Bool``
val FA_def_tm = ``Abs "P" ^P_ty (Var "P" ^P_ty === Abs "x" (Tyvar "A") TT)``
val FA_def = Define `FA x ty b =
  Comb (Const1 "!" (Fun (Fun ty Bool) Bool) ^FA_def_tm)
       (Abs x ty b)`

val EX_def_tm = ``
  (Abs "P" ^P_ty
    (FA "q" Bool
      (IM
        (FA "x" (Tyvar "A") (IM (Comb (Var "P" ^P_ty) (Var "x" (Tyvar "A")))
                                (Var "q" Bool)))
        (Var "q" Bool))))``
val EX_def = Define`EX x ty b =
  Comb (Const1 "?" (Fun (Fun ty Bool) Bool) ^EX_def_tm)
       (Abs x ty b)`

val FF_def = Define`FF = Const1 "F" Bool (FA "p" Bool (Var "p" Bool))`

val NO_def = Define`NO = Comb (Const1 "~" (Fun Bool Bool)
  (Abs "p" Bool (IM (Var "p" Bool) FF)))`

val O1_def = Define`O1 a b =
  Comb (Const1 "ONE_ONE" (Fun (Fun a b) Bool)
                (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
                  (FA "x1" (Tyvar "A")
                    (FA "x2" (Tyvar "A")
                      (IM (Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B")))
                                (Var "x1" (Tyvar "A"))
                           ===
                           Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B")))
                                (Var "x2" (Tyvar "A")))
                          (Var "x1" (Tyvar "A")
                           ===
                           Var "x2" (Tyvar "A")))))))`

val OT_def = Define`OT a b =
  Comb (Const1 "ONTO" (Fun (Fun a b) Bool)
                (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
                  (FA "y" (Tyvar "B")
                    (EX "x" (Tyvar "A")
                       (Var "y" (Tyvar "B")
                        ===
                        Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B")))
                             (Var "x" (Tyvar "A")))))))`

val (proves_rules,proves_ind,proves_cases) = xHol_reln"proves"`
 (type_ok (Tyvar a)) ∧ (type_ok Bool) ∧ (type_ok Ind) ∧
 (type_ok ty1 ∧ type_ok ty2 ⇒ type_ok (Fun ty1 ty2)) ∧
 (type_ok (Tyapp op args) ∧ MEM ty args ⇒ type_ok ty) ∧
 (type_ok ty ⇒ term_ok (Var x ty)) ∧
 (type_ok ty ⇒ term_ok (Equal ty)) ∧
 (type_ok ty ⇒ term_ok (Select ty)) ∧
 (term_ok t1 ∧ term_ok t2 ∧ welltyped (Comb t1 t2) ⇒ term_ok (Comb t1 t2)) ∧
 (type_ok ty ∧ term_ok tm ⇒ term_ok (Abs x ty tm)) ∧
 (term_ok (Comb t1 t2) ⇒ term_ok t1) ∧
 (term_ok (Comb t1 t2) ⇒ term_ok t2) ∧
 (term_ok (Abs x ty tm) ⇒ term_ok tm) ∧
 (term_ok tm ∧ tm has_type ty ⇒ type_ok ty) ∧
 (h |- c ∧ MEM t (c::h) ⇒ term_ok t) ∧

  (* REFL *)
  (term_ok t
   ⇒
   [] |- t === t)
∧ (* TRANS *)
  (h1 |- l === m1 ∧ h2 |- m2 === r ∧ ACONV m1 m2
   ⇒
   (TERM_UNION h1 h2) |- l === r)
∧ (* MK_COMB *)
  (h1 |- l1 === r1 ∧
   h2 |- l2 === r2 ∧ welltyped (Comb l1 l2)
   ⇒
   (TERM_UNION h1 h2) |- Comb l1 l2 === Comb r1 r2)
∧ (* ABS *)
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧
   h |- l === r ∧ type_ok ty
   ⇒
   h |- (Abs x ty l) === (Abs x ty r))
∧ (* BETA *)
  (type_ok ty ∧ term_ok t
   ⇒
   [] |- Comb (Abs x ty t) (Var x ty) === t)
∧ (* ASSUME *)
  (term_ok p ∧ p has_type Bool
   ⇒
   [p] |- p)
∧ (* EQ_MP *)
  (h1 |- p === q ∧ h2 |- p' ∧ ACONV p p'
   ⇒
   (TERM_UNION h1 h2) |- q)
∧ (* DEDUCT_ANTISYM *)
  (h1 |- c1 ∧ h2 |- c2
   ⇒
   (TERM_UNION (FILTER((~) o ACONV c2) h1)
               (FILTER((~) o ACONV c1) h2))
     |- c1 === c2)
∧ (* INST_TYPE *)
  (h |- c ∧ EVERY type_ok (MAP FST tyin)
   ⇒
   (MAP (INST tyin) h) |- INST tyin c)
∧ (* INST *)
  ((∀s s'. MEM (s',s) ilist ⇒ term_ok s' ∧ ∃x ty. (s = Var x ty) ∧ s' has_type ty) ∧
   h |- c
   ⇒
   (MAP (VSUBST ilist) h) |- VSUBST ilist c)
∧ (* new_specification *)
  (MAP (λ(s,t). Var s (typeof t) === t) eqs |- p ∧
   EVERY
     (λt. closed t ∧ welltyped t ∧ set (tvars t) ⊆ set (tyvars (typeof t)))
     (MAP SND eqs) ∧
   vars = MAP (λ(s,t). (s,typeof t)) eqs ∧ ALL_DISTINCT vars ∧
   (∀x ty. VFREE_IN (Var x ty) p ⇒ MEM (x,ty) vars) ∧
   (ilist = GENLIST (λn. let (x,ty) = EL n vars in (Const x ty (Defined n eqs p), Var x ty)) (LENGTH eqs))
   ⇒
   [] |- VSUBST ilist p)
∧ (MAP (λ(s,t). Var s (typeof t) === t) eqs |- p ∧
   EVERY
     (λt. closed t ∧ welltyped t ∧ set (tvars t) ⊆ set (tyvars (typeof t)))
     (MAP SND eqs) ∧
   vars = MAP (λ(s,t). (s,typeof t)) eqs ∧ ALL_DISTINCT vars ∧
   (∀x ty. VFREE_IN (Var x ty) p ⇒ MEM (x,ty) vars) ∧
   i < LENGTH eqs ∧ (s,ty) = EL i vars
   ⇒
   term_ok (Const s ty (Defined i eqs p)))
∧ (* new_basic_type_definition |- abs (rep x) = x *)
  (closed p ∧
   [] |- Comb p w ∧
   rty = domain (typeof p) ∧
   aty = Tyapp (Tydefined n p) (MAP Tyvar (STRING_SORT (tvars p)))
   ⇒
   [] |-
     Comb (Const abs (Fun rty aty) (Tyabs n p))
          (Comb (Const rep (Fun aty rty) (Tyrep n p))
                (Var x aty)) === Var x aty)
∧ (* new_basic_type_definition |- p x = (rep (abs x) = x) *)
  (closed p ∧
   [] |- Comb p w ∧
   rty = domain (typeof p) ∧
   aty = Tyapp (Tydefined n p) (MAP Tyvar (STRING_SORT (tvars p)))
   ⇒
   [] |-
     Comb p (Var x rty) ===
     Comb (Const rep (Fun aty rty) (Tyrep n p))
          (Comb (Const abs (Fun rty aty) (Tyabs n p))
                (Var x rty)) === Var x rty)
∧ (* ETA_AX *)
  (type_ok ty1 ∧ type_ok ty2
   ⇒
   [] |- Abs x ty1 (Comb (Var f (Fun ty1 ty2)) (Var x ty1)) === Var f (Fun ty1 ty2))
∧ (* SELECT_AX *)
  (p has_type (Fun ty Bool) ∧
   h |- Comb p w
   ⇒
   h |- Comb p (Comb (Select ty) p))
∧ (* INFINITY_AX *)
  ([] |- EX "f" (Fun Ind Ind) (AN (O1 Ind Ind (Var "f" (Fun Ind Ind)))
                                  (NO (OT Ind Ind (Var "f" (Fun Ind Ind))))))`

val _ = export_theory()
