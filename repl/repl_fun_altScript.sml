
open HolKernel Parse boolLib bossLib;

val _ = new_theory "repl_fun_alt";

open listTheory arithmeticTheory relationTheory;
open repl_funTheory bytecodeLabelsTheory bytecodeTheory;

(*

   This file rephrases repl_fun (as repl_fun_alt) so that it fits
   better with the machine-code implementation. In particular:

    - all functions that are to be bootstrapped are collected into
      one function called repl_step, and

    - all labels are expanded away before code installation.

*)

val num_bc_bc_num = store_thm("num_bc_bc_num",
  ``!x. num_bc (bc_num x) = x``,
  Cases THEN TRY (Cases_on `b`) THEN TRY (Cases_on `l`) THEN EVAL_TAC
  THEN SIMP_TAC std_ss [stringTheory.ORD_BOUND]
  THEN Cases_on `i < 0` THEN FULL_SIMP_TAC std_ss []
  THEN intLib.COOPER_TAC);

val bc_num_lists_def = Define `
  bc_num_lists xs ys = MAP bc_num xs ++ [(18,0,0)] ++ MAP bc_num ys`;

val empty_bc_state_def = Define `
  empty_bc_state = <| stack := []; code := []; pc := 0; refs := FEMPTY;
                      handler := 0; clock := NONE; output := "";
                      cons_names := []; inst_length := real_inst_length |>`;

val repl_step_def = Define `
  repl_step state =
    case state of
    | NONE => (* first time around *)
       let len = 0 in
       let code = PrintE ++ [Stop] in
       let labs = collect_labels code len real_inst_length in
       let len = code_length real_inst_length code in
       let code1 = inst_labels labs code in
       let code = SND (SND compile_primitives) in
       let code = REVERSE code in
       let labs = FUNION labs (collect_labels code len real_inst_length) in
       let len = len + code_length real_inst_length code in
       let code = inst_labels labs code in
         INL ([],bc_num_lists code1 code,len,labs,
                 initial_repl_fun_state,initial_repl_fun_state)
    | SOME (tokens,new_s,len,labs,s',s_exc) => (* received some input *)
        let s = if new_s then s' else s_exc in
        case parse_elaborate_infertype_compile (MAP token_of_sym tokens) s of
        | Success (code,s',s_exc) =>
            let code = REVERSE code in
            let labs = FUNION labs (collect_labels code len real_inst_length) in
            let len = len + code_length real_inst_length code in
            let code = inst_labels labs code in
              INL (cpam s'.rcompiler_state,bc_num_lists [] code,len,labs,s_exc,s')
        | Failure error_msg => INR (error_msg,(F,len,labs,s,s))`

val set_cons_names_def = Define `
  set_cons_names m bs =
    bs with <| cons_names := m; output := "" |>`;

val install_bc_lists_def = Define `
  (install_bc_lists [] bs = bs) /\
  (install_bc_lists (x::xs) bs =
     if FST x = 18 then
       install_bc_lists xs (bs with
         pc := next_addr bs.inst_length bs.code)
     else
       install_bc_lists xs (bs with
         code := bs.code ++ [num_bc x]))`;

val tac = (WF_REL_TAC `measure (LENGTH o FST o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lexer_implTheory.lex_until_top_semicolon_alt_LESS);

val main_loop_alt_def = tDefine "main_loop_alt" `
  main_loop_alt bs input state init =
    case repl_step state of
      | INR (error_msg,x) =>
            Result error_msg
             (case lex_until_top_semicolon_alt input of
              | NONE => Terminate
              | SOME (ts,rest) =>
                  (main_loop_alt bs rest (SOME (ts,x)) F))
      | INL (m,code,new_state) =>
        case bc_eval (set_cons_names m (install_bc_lists code bs)) of
        | NONE => Diverge
        | SOME new_bs =>
            let new_bs = (if init then new_bs with stack := TL new_bs.stack
                                  else new_bs) in
            let new_s = (bc_fetch new_bs = SOME Stop) in
              (if init then I else Result (REVERSE new_bs.output))
                (case lex_until_top_semicolon_alt input of
                 | NONE => Terminate
                 | SOME (ts,rest) =>
                     (main_loop_alt new_bs rest (SOME (ts,new_s,new_state)) F)) ` tac

val repl_fun_alt_def = Define `
  repl_fun_alt input = main_loop_alt empty_bc_state input NONE T`;

val _ = export_theory();
