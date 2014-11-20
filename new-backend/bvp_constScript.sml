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
   optimisation that must come after the pConst optimisation function
   defined in this file. *)

val pSeq2_def = Define `
  pSeq2 c1 c2 =
    if isSkip c1 then c2 else
    if isSkip c2 then c1 else Seq c1 c2`;

val ConstAssign_def = Define `
  ConstAssign v i = Assign v (Const i) [] NONE`;

val ConstAssigns_def = Define `
  (ConstAssigns [] env x = x) /\
  (ConstAssigns (v::vs) env x =
     case lookup v env of
     | NONE => ConstAssigns vs env x
     | SOME i => ConstAssigns vs env (Seq (ConstAssign v i) x))`

val destConstAssign_def = Define `
  destConstAssign op =
    case op of
    | Const i => SOME i
    | _ => NONE`;

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
    | SOME i => (ConstAssign n1 i, insert n1 i env)) /\
  (pConst (Seq c1 c2) env =
     let (d1,e1) = pConst c1 env in
     let (d2,e2) = pConst c2 e1 in
       (Seq d1 d2, e2)) /\
  (pConst Tick env = (Tick,env)) /\
  (pConst (MakeSpace k names) env =
     (MakeSpace k names,inter env names)) /\
  (pConst (Assign v op vs opt_names) env =
     let env' = (case opt_names of
                 | NONE => env
                 | SOME ns => inter env ns) in
       case destConstAssign op of
       | SOME i =>
           (Assign v op vs opt_names,insert v i env')
       | NONE =>
           (ConstAssigns vs env (Assign v op vs opt_names),delete v env')) /\
  (pConst (If c1 v c2 c3) env =
     let (d1,e1) = pConst c1 env in
     let (d2,e2) = pConst c2 e1 in
     let (d3,e3) = pConst c3 e1 in
       (If d1 v d2 d3, inter_eq e2 e3)) /\
  (pConst (Call ret dest vs handler) env =
     (ConstAssigns vs env (Call ret dest vs handler),
      if IS_SOME handler then LN
      else case ret of
           | NONE => LN
           | SOME (v,ns) => inter (delete v env) ns))`;

val pEval_ConstAssign = prove(
  ``small_enough_int i ==>
    (pEval (ConstAssign v i,s) = (NONE,set_var v (Number i) s))``,
  EVAL_TAC \\ fs [] \\ fs [bvp_state_component_equality]);

val ignore_insert = store_thm("ignore_insert",
  ``!n t x. (lookup n t = SOME x) ==> (insert n x t = t)``,
  HO_MATCH_MP_TAC lookup_ind \\ REPEAT STRIP_TAC
  \\ fs [lookup_def] \\ SIMP_TAC std_ss [Once insert_def] \\ fs []
  \\ Cases_on `EVEN n` \\ fs [] \\ Cases_on `n = 0` \\ fs []);

val get_var_set_var = prove(
  ``(get_var n s = SOME (Number x)) ==>
    (set_var n (Number x) s = s)``,
  fs [get_var_def,set_var_def,bvp_state_component_equality]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC ignore_insert \\ fs []);

val pEval_ConstAssigns = prove(
  ``!vs x env s.
      (!n i. (lookup n env = SOME i) ==>
           small_enough_int i /\
           (get_var n s = SOME (Number i))) ==>
      (pEval (ConstAssigns vs env x,s) = pEval (x,s))``,
  Induct \\ fs [ConstAssigns_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ Cases_on `lookup h env` \\ fs[pEval_def]
  \\ fs [] \\ RES_TAC \\ fs [pEval_ConstAssign,LET_DEF]
  \\ IMP_RES_TAC get_var_set_var \\ fs []);

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
    \\ fs [get_var_def,set_var_def,lookup_insert]
    \\ Cases_on `n' = n` \\ fs [] \\ RES_TAC)
  THEN1 (* Call *)
   (fs [LET_DEF] \\ STRIP_TAC
    THEN1 (MATCH_MP_TAC pEval_ConstAssigns \\ fs [])
    \\ Cases_on `o1` \\ fs [lookup_def] \\ Cases_on `x` \\ fs []
    \\ fs [lookup_inter_alt,lookup_delete]
    \\ NTAC 3 STRIP_TAC \\ RES_TAC \\ fs []
    \\ fs [pEval_def]
    \\ Cases_on `s.clock = 0` \\ fs []
    \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
    \\ Q.MATCH_ASSUM_RENAME_TAC
          `find_code dest args s.code = SOME (vs1,prog)` []
    \\ fs [lookup_def,lookup_inter_alt,lookup_delete] \\ RES_TAC \\ fs []
    \\ MP_TAC (Q.SPECL [`prog`,`call_env vs1 (push_env x F (dec_clock s))`]
         pEval_stack_swap) \\ fs [call_env_def] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPEC `(push_env x F (dec_clock s)).stack`)
    \\ fs [] \\ fs [GSYM call_env_def]
    \\ `call_env vs1
           (push_env x F (dec_clock s) with
            stack := (push_env x F (dec_clock s)).stack) =
          call_env vs1 (push_env x F (dec_clock s))` by ALL_TAC THEN1
        (fs [bvp_state_component_equality,call_env_def])
    \\ REPEAT STRIP_TAC \\ rfs []
    \\ Q.PAT_ASSUM `pop_env r'' = SOME x''` MP_TAC
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ fs [pop_env_def,push_env_def]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ fs [set_var_def,get_var_def,lookup_insert]
    \\ RES_TAC \\ fs [cut_env_def] \\ SRW_TAC [] []
    \\ fs [lookup_inter_alt])
  THEN1 (* Assign *)
   (REVERSE (Cases_on `destConstAssign b` \\ fs []) THEN1
     (fs [LET_DEF] \\ fs []
      \\ Cases_on `b` \\ fs [destConstAssign_def]
      \\ fs [pEval_def,op_space_reset_def]
      \\ Cases_on `cut_state_opt o' s` \\ fs []
      \\ Cases_on `get_vars l x'` \\ fs []
      \\ Cases_on `pEvalOp (Const x) x'' x'` \\ fs []
      \\ Cases_on `x'''`
      \\ IMP_RES_TAC pEvalOp_IMP
      \\ fs [pEvalOp_def]
      \\ Cases_on `pEvalOpSpace (Const x) x'` \\ fs []
      \\ fs [bviTheory.iEvalOp_def,bEvalOp_def,bviTheory.iEvalOpAux_def]
      \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
      \\ fs [lookup_insert,get_var_def,set_var_def]
      \\ SRW_TAC [] [] \\ fs [] \\ RES_TAC
      \\ Q.PAT_ASSUM `x'.locals = xxx` (ASSUME_TAC o GSYM)
      \\ fs [cut_state_opt_def,lookup_inter_alt] \\ RES_TAC
      \\ fs [cut_state_def,cut_env_def]
      \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
      \\ SRW_TAC [] [lookup_inter_alt])
    \\ fs [LET_DEF] \\ STRIP_TAC
    THEN1 (MATCH_MP_TAC pEval_ConstAssigns \\ METIS_TAC [])
    \\ Q.MATCH_ASSUM_RENAME_TAC
         `FST (pEval (Assign n b l opt,s)) <> SOME Error` []
    \\ Cases_on `opt` \\ fs [lookup_delete,lookup_inter]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ fs [pEval_def,cut_state_opt_def]
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ fs [get_var_def,set_var_def,lookup_insert]
    \\ IMP_RES_TAC pEvalOp_IMP \\ fs [] \\ SRW_TAC [] [] \\ RES_TAC
    \\ fs [cut_state_def,cut_env_def]
    \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ Q.PAT_ASSUM `inter s.locals x = r.locals` (MP_TAC o GSYM)
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs [lookup_inter])
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
  THEN1 (* If *)
   (Cases_on `pConst c env`
    \\ Q.MATCH_ASSUM_RENAME_TAC `pConst c1 env = (d1,e1)` []
    \\ Cases_on `pConst c' e1`
    \\ Q.MATCH_ASSUM_RENAME_TAC `pConst c2 e1 = (d2,e2)` []
    \\ Cases_on `pConst c'' e1`
    \\ Q.MATCH_ASSUM_RENAME_TAC `pConst c3 e1 = (d3,e3)` []
    \\ fs [LET_DEF,pEval_def]
    \\ `?res1 t1. pEval (c1,s) = (res1,t1)` by METIS_TAC [PAIR] \\ fs []
    \\ REVERSE (Cases_on `res1`) \\ fs [] THEN1
     (Q.PAT_ASSUM `!(s:bvp_state).bbb` MP_TAC
      \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` MP_TAC
      \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` (MP_TAC o Q.SPECL [`s`,`env`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (fs [] \\ METIS_TAC [])
      \\ fs [])
    \\ Cases_on `get_var n t1` \\ fs []
    \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` MP_TAC
    \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` MP_TAC
    \\ Q.PAT_ASSUM `!(s:bvp_state).bbb` (MP_TAC o Q.SPECL [`s`,`env`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (fs [] \\ METIS_TAC [])
    \\ NTAC 3 STRIP_TAC \\ fs [] \\ rfs []
    \\ NTAC 2
     (Q.PAT_ASSUM `!(s:bvp_state).bbb` (MP_TAC o Q.SPECL [`t1`,`e1`])
      \\ fs [GSYM AND_IMP_INTRO] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ TRY (REPEAT STRIP_TAC \\ RES_TAC \\ fs [] \\ NO_TAC))
    \\ Cases_on `x = Block 1 []` \\ fs [] THEN1
     (REPEAT STRIP_TAC
      \\ fs [lookup_inter_eq]
      \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
      \\ RES_TAC \\ SRW_TAC [] [] \\ fs [])
    \\ Cases_on `x = Block 0 []` \\ fs [] THEN1
     (REPEAT STRIP_TAC
      \\ fs [lookup_inter_eq]
      \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
      \\ RES_TAC \\ SRW_TAC [] [] \\ fs []))
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
