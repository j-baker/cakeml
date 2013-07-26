open HolKernel bossLib repl_computeLib replDecsTheory compileReplDecsTheory
val _ = new_theory"compileCallReplStepDec"

val _ = Globals.max_print_depth := 15

val internal_code_def = new_definition("internal_code_def",
  mk_eq(``internal_code:bc_inst list``,rand(rand(rator(rand(rand(rand(rand(rhs(concl(repl_decs_compiled)))))))))))

val internal_contab_def = new_definition("internal_contab_def",
  mk_eq(``internal_contab:contab``, rand(rator(rhs(concl(repl_decs_compiled))))))

val _ = computeLib.add_funs[call_repl_step_dec_def,
  CONV_RULE(LAND_CONV(REWRITE_CONV[SYM compile_repl_decs_def]))
    (REWRITE_RULE[SYM internal_code_def, SYM internal_contab_def]repl_decs_compiled)]

val call_repl_step_dec_compiled = save_thm("call_repl_step_dec_compiled",
  EVAL``
    let m = FST(SND(compile_repl_decs)) in
    let env = FST(SND(SND(compile_repl_decs))) in
    let rsz = FST(SND(SND(SND(compile_repl_decs)))) in
    let cs = SND(SND(SND(SND(compile_repl_decs)))) in
  compile_dec FEMPTY m env rsz <|out:=[];next_label:=cs.next_label|> call_repl_step_dec``);

val _ = export_theory()