open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_const";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs bvlTheory bvpTheory;
open bvp_lemmasTheory bvp_simpTheory alistTheory;

infix \\ val op \\ = op THEN;

(* This file defines an optimisation that pushes constant assignments
   as far forward as possible. It pushes them through GC points so
   that known constants aren't stored on the stack past subroutine
   calls. The variables are removed from the live sets by the pLive
   optimisation that must come after the pConst optimisation defined
   in this file. *)

val pSeq2_def = Define `
  pSeq2 c1 c2 =
    if isSkip c1 then c2 else
    if isSkip c2 then c1 else Seq c1 c2`;

val ConstAssign_def = Define `
  ConstAssign v i = Assign v (Const i) [] NONE`;

val pConst_def = Define `
  (pConst Skip env = (Skip,env)) /\
  (pConst (Return n) env =
    case lookup n env of
    | NONE => (Return n, LN)
    | SOME i => (Seq (ConstAssign n i) (Return n), LN)) /\
  (pConst (Raise n) env =
    case lookup n env of
    | NONE => (Raise n, LN)
    | SOME i => (Seq (ConstAssign n i) (Raise n), LN)) /\
  (pConst (Move n1 n2) env =
    case lookup n2 env of
    | NONE => (Move n1 n2, delete n1 env)
    | SOME i => (ConstAssign n1 i, delete n1 env)) /\
  (pConst (Seq c1 c2) env =
     let (d1,e1) = pConst c1 env in
     let (d2,e2) = pConst c2 e1 in
       (Seq d1 d2, e2)) /\
  (pConst Tick env = (Tick,env)) /\
  (pConst (MakeSpace k names) env =
     (MakeSpace k names,inter env names)) /\
  (* case below need to be improved *)
  (pConst (Assign v op vs opt_names) env =
     (Assign v op vs opt_names,LN)) /\
  (pConst (x) env =
     (x,LN))`

val pEval_ConstAssign = prove(
  ``small_enough_int i ==>
    (pEval (ConstAssign v i,s) = (NONE,set_var v (Number i) s))``,
  EVAL_TAC \\ fs [] \\ fs [bvp_state_component_equality]);

val ignore_insert = store_thm("ignore_insert",
  ``!n t x. (lookup n t = SOME x) ==> (insert n x t = t)``,
  HO_MATCH_MP_TAC lookup_ind
  \\ REPEAT STRIP_TAC
  \\ fs [lookup_def]
  \\ SIMP_TAC std_ss [Once insert_def] \\ fs []
  \\ Cases_on `EVEN n` \\ fs []
  \\ Cases_on `n = 0` \\ fs []);

val get_var_set_var = prove(
  ``(get_var n s = SOME (Number x)) ==>
    (set_var n (Number x) s = s)``,
  fs [get_var_def,set_var_def,bvp_state_component_equality]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC ignore_insert \\ fs []);

val pConst_correct_lemma = prove(
  ``!c s env.
      (!n i. (lookup n env = SOME i) ==>
             small_enough_int i /\
             (get_var n s = SOME (Number i))) /\
      FST (pEval (c,s)) <> SOME Error ==>
      let (d1,e1) = pConst c env in
        (pEval (d1,s) = pEval (c,s)) /\
        (!n i. (lookup n e1 = SOME i) /\ (FST (pEval (c,s)) = NONE) ==>
               small_enough_int i /\
               (get_var n (SND (pEval (c,s))) = SOME (Number i)))``,
  Induct \\ fs [pConst_def] \\ REPEAT STRIP_TAC
  \\ TRY (fs [LET_DEF,lookup_def,pEval_def] \\ REPEAT STRIP_TAC
          \\ RES_TAC \\ fs [] \\ NO_TAC)
  THEN1 (* Move *)
   (Cases_on `lookup n0 env` \\ fs [] \\ RES_TAC
    \\ fs [pEval_ConstAssign,pEval_def,LET_DEF]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs []
    \\ fs [lookup_delete] \\ RES_TAC
    \\ REPEAT BasicProvers.CASE_TAC \\ fs []
    \\ fs [get_var_def,set_var_def,lookup_insert])
  THEN1 (* Seq *)
   (Cases_on `pConst c env`
    \\ Q.MATCH_ASSUM_RENAME_TAC `pConst c1 env = (d1,e1)` []
    \\ Cases_on `pConst c' e1`
    \\ Q.MATCH_ASSUM_RENAME_TAC `pConst c2 e1 = (d2,e2)` []
    \\ fs [LET_DEF,pEval_def]
    \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` MP_TAC
    \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` (MP_TAC o Q.SPECL [`s`,`env`])
    \\ fs [] \\ Cases_on `pEval (c1,s)` \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (Cases_on `q` \\ fs [] \\ METIS_TAC [])
    \\ STRIP_TAC \\ STRIP_TAC \\ fs []
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`r`,`e1`]) \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 METIS_TAC []
    \\ REPEAT STRIP_TAC \\ fs [] \\ RES_TAC)
  THEN1 (* MakeSpace *)
   (fs [LET_DEF,pEval_def]
    \\ Cases_on `cut_env s s'.locals` \\ fs []
    \\ fs [lookup_inter,get_var_def]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `lookup n' env` \\ fs []
    \\ Cases_on `lookup n' s` \\ fs [cut_env_def]
    \\ RES_TAC \\ SRW_TAC [] []
    \\ fs [SUBSET_DEF,domain_lookup]
    \\ RES_TAC \\ fs [] \\ SRW_TAC [] []
    \\ fs [lookup_inter])
  THEN1 (* Raise *)
   (Cases_on `lookup n env` \\ fs [LET_DEF,lookup_def] \\ RES_TAC
    \\ fs [pEval_def,pEval_ConstAssign,LET_DEF,get_var_set_var])
  THEN1 (* Return *)
   (Cases_on `lookup n env` \\ fs [LET_DEF,lookup_def] \\ RES_TAC
    \\ fs [pEval_def,pEval_ConstAssign,LET_DEF,get_var_set_var])
  THEN1 (* Tick *)
   (fs [LET_DEF,lookup_def,pEval_def]
    \\ SRW_TAC [] [] \\ fs [] \\ RES_TAC
    \\ fs [get_var_def,bvpTheory.dec_clock_def]));

val pConst_correct = store_thm("pConst_correct",
  ``!c s env.
      FST (pEval (c,s)) <> SOME Error /\
      FST (pEval (c,s)) <> NONE ==>
      (pEval (FST (pConst c LN),s) = pEval (c,s))``,
  REPEAT STRIP_TAC
  \\ (SPEC_ALL pConst_correct_lemma |> Q.INST [`env`|->`LN`]
      |> SIMP_RULE std_ss [lookup_def] |> MP_TAC)
  \\ fs [] \\ Cases_on `pConst c LN` \\ fs [LET_DEF]);

val _ = export_theory();
