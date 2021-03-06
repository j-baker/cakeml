structure cakeml_computeLib = struct local
open HolKernel boolLib bossLib lcsymtacs
open miscLib optionLib stringLib listLib listTheory pairTheory finite_mapTheory stringTheory
open miscTheory cmlParseTheory cmlPEGTheory initialEnvTheory 
open lexer_funTheory elabTheory astTheory modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory compilerTheory
open lexer_implTheory inferTheory intLangTheory toIntLangTheory toBytecodeTheory printingTheory compilerProofTheory
open bytecodeLabelsTheory labels_computeLib bytecodeEncodeTheory bytecodeEvalTheory free_varsTheory progToBytecodeTheory
open initialProgramTheory
open terminationTheory compilerTerminationTheory
open x64_code_evalTheory x64_heapTheory

val encode_bc_insts_thm = prove(
  ``∀bcs. encode_bc_insts bcs =
    let ls = MAP encode_bc_inst bcs in
    if EXISTS IS_NONE ls then NONE else
    SOME (FLAT (MAP THE ls))``,
  Induct >> simp[encode_bc_insts_def] >>
  fs[LET_THM] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[])

val SUC_TO_NUMERAL_RULE = CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)

val eval_real_inst_length =
  let
    val compset = reduceLib.num_compset()
    val () = intReduce.add_int_compset compset
    val () = computeLib.add_thms [bytecodeExtraTheory.real_inst_length_compute] compset
  in
    computeLib.CBV_CONV compset
  end

val compile_top_code_ok =
  prove(``∀types rs top ss sf code.
          (compile_top types rs top = (ss,sf,code)) ⇒
          (FV_top top ⊆ global_dom rs.globals_env) ⇒
          code_labels_ok code``,
  metis_tac[compile_top_labels,pair_CASES,SND])

fun cakeml_compset() = let
(*
val () =
  let
    fun compile_Cexp_conv eval tm =
      let
        val th = (REWR_CONV compile_Cexp_def THENC eval) tm
        val th1 = MATCH_MP compile_Cexp_code_ok_thm th
        val th2 = MP (CONV_RULE(LAND_CONV eval) th1) TRUTH
        val th3 = CONV_RULE (RAND_CONV eval) th2
        val () = labels_computeLib.add_code_labels_ok_thm th3
      in
        th
      end
  in
    computeLib.add_conv(``compile_Cexp``,4,(compile_Cexp_conv (computeLib.CBV_CONV compset))) compset
  end
*)
(* labels removal *)
val () = labels_computeLib.reset_code_labels_ok_db()
val () = computeLib.add_conv (``code_labels``,2,code_labels_conv eval_real_inst_length) compset
val () =
  let
    fun code_labels_ok_conv tm =
      EQT_INTRO
        (labels_computeLib.get_code_labels_ok_thm
          (rand tm))
  in
    computeLib.add_conv(``code_labels_ok``,1,code_labels_ok_conv) compset ;
    add_datatype ``:bc_inst``;
    computeLib.add_thms [uses_label_def] compset
  end
(* compile_top *)
val () =
  let
    fun compile_top_conv eval tm =
      let
        val th = (REWR_CONV compile_top_def THENC eval) tm
        val th1 = MATCH_MP compile_top_code_ok th
        val th2 = MP (CONV_RULE(LAND_CONV eval) th1) TRUTH
        val () = labels_computeLib.add_code_labels_ok_thm th2
      in
        th
      end
  in
    computeLib.add_conv(``compile_top``,3,(compile_top_conv (computeLib.CBV_CONV compset))) compset
  end
(* compile_prog *)
val () =
  let
    val compile_prog_code_ok = compile_prog_code_labels_ok |> REWRITE_RULE[GSYM AND_IMP_INTRO]
    fun compile_prog_conv eval tm =
      let
        val th = (REWR_CONV compile_prog_def THENC eval) tm
        val th1 = MATCH_MP compile_prog_code_ok th
        val th2 = MP (CONV_RULE(LAND_CONV eval) th1) TRUTH
        val () = labels_computeLib.add_code_labels_ok_thm th2
      in
        th
      end
  in
    computeLib.add_conv(``compile_prog``,1,(compile_prog_conv (computeLib.CBV_CONV compset))) compset
  end
(* prog to bytecode *)
val () = computeLib.add_thms
  [prog_to_bytecode_def
  ,prog_to_bytecode_string_def
  ,prog_to_bytecode_encoded_def
  ,bc_inst_to_string_def
  ,bc_loc_to_string_def
  ,int_to_string2_def
  ,encode_bc_insts_thm
  ,encode_bc_inst_def
  ,CONV_RULE(computeLib.CBV_CONV(wordsLib.words_compset()))
    (INST_TYPE[alpha|->``:64``]encode_num_def)
  ,encode_loc_def
  ,encode_char_def
  ,initial_program_def
  ,init_compiler_state_def
  ] compset
val () = computeLib.add_thms
  [get_all_asts_def
  ,elab_all_asts_def
  ,infer_all_asts_def
  ,compile_all_asts_def
  ,all_asts_to_string_def
  ,all_asts_to_encoded_def
  ,remove_labels_all_asts_def
  ] compset

(*Bytecode to asm*)
val () = computeLib.add_thms 
  [prog_x64_extraTheory.IMM32_def,
   small_offset_def,
   small_offset6_def,
   small_offset12_def,
   small_offset16_def,
   x64_def,
   x64_length_def,
   x64_code_def] compset

in compset end

val bc_fetch_aux_0_thm = prove(
  ``∀code pc. bc_fetch_aux code (K 0) pc =
    if no_labels code then el_check pc code
    else FAIL (bc_fetch_aux code (K 0) pc) "code has labels"``,
  REWRITE_TAC[no_labels_def] >>
  Induct >> simp[bytecodeTheory.bc_fetch_aux_def,libTheory.el_check_def] >>
  rw[] >> fs[combinTheory.FAIL_DEF,libTheory.el_check_def] >>
  simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

val remove_labels_all_asts_no_labels = prove(
  ``(remove_labels_all_asts len x = Success ls) ⇒ no_labels ls``,
  Cases_on`x`>>rw[remove_labels_all_asts_def]
  >> rw[code_labels_no_labels])

in
  val cakeml_compset = cakeml_compset

  val eval_real_inst_length = eval_real_inst_length

  val eval = computeLib.CBV_CONV (cakeml_compset())

  fun add_bc_eval_compset compset = let
    val () = computeLib.add_thms
      [bytecodeEvalTheory.bc_eval_compute
      ,bytecodeEvalTheory.bc_eval1_def
      ,bytecodeEvalTheory.bc_eval_stack_def
      ,bytecodeTheory.bump_pc_def
      ,bytecodeTheory.bc_fetch_def
      ,bc_fetch_aux_0_thm
      ,bytecodeTheory.bc_equality_result_to_val_def
      ,bytecodeTheory.bool_to_val_def
      ,bytecodeTheory.bool_to_tag_def
      ,bytecodeTheory.bc_find_loc_def
      ,bytecodeTerminationTheory.bc_equal_def
      ,bytecodeTheory.bv_to_string_def
      ,bytecodeTheory.bvs_to_chars_def
      ,semanticPrimitivesTheory.int_to_string_def
      ,semanticPrimitivesTheory.string_to_string_def
      ,semanticPrimitivesTheory.string_escape_def
      ,SUC_TO_NUMERAL_RULE bc_evaln_def
      ,LEAST_thm
      ,least_from_thm
      ,libTheory.el_check_def
      ,listTheory.LUPDATE_compute
      ] compset
    val () = computeLib.add_datatype_info compset (valOf(TypeBase.fetch``:bc_state``))
    val () = computeLib.add_datatype_info compset (valOf(TypeBase.fetch``:bc_value``))
  in () end

  local
    open TextIO;
    (* Specialised for 64-bit little endian *)
    local
      open IntInf;
      infix ~>>
    in
      fun encode (i:int) =
        Word8Vector.fromList
          (List.map Word8.fromInt [i, (i ~>> 0w8), (i ~>> 0w16), (i ~>> 0w24),
                                   (i ~>> 0w32), (i ~>> 0w40), (i ~>> 0w48), (i ~>> 0w56)])
    end
    fun do_textio istr outfile f =
      let
        val s = inputAll istr
        val _ = closeIn istr
        val r = f s
        val ostr = openOut outfile
        val _ = output (ostr, r)
        val _ = closeOut ostr
      in
        ()
      end
    fun do_binio istr outfile f =
      let
        val s = inputAll istr
        val _ = closeIn istr
        val r = f s
        val ostr = BinIO.openOut outfile
        val _ = List.app (curry BinIO.output ostr) r
        val _ = BinIO.closeOut ostr
      in
        ()
      end
    fun compile_string s =
      let
        val thm = eval ``case prog_to_bytecode_string (\x. 0) ^(fromMLstring s) of Failure x => "<compile error>" ++ x | Success s => s``
        val _ = assert (fn x => hyp x = []) thm;
      in
        fromHOLstring (rhs (concl thm))
      end
    fun compile_binary s =
      let
        val thm = eval ``case prog_to_bytecode_encoded (\x. 0) ^(fromMLstring s)
                         of Failure x =>
                           encode_bc_insts (MAP PrintC ("compile error: " ++ x ++ "\n"))
                         | Success s => s``
        val _ = assert (fn x => hyp x = []) thm;
      in
        thm |> concl |> rhs |> dest_some
            |> listSyntax.dest_list |> fst
            |> List.map wordsSyntax.uint_of_word
            |> List.map encode
      end
  in
    fun do_compile_string_istr istr outfile = do_textio istr outfile compile_string
    fun do_compile_binary_istr istr outfile = do_binio istr outfile compile_binary
    fun do_compile_string infile = do_compile_string_istr (openIn infile)
    fun do_compile_binary infile = do_compile_binary_istr (openIn infile)
    fun do_compile_string_str s = do_compile_string_istr (openString s)
    fun do_compile_binary_str s = do_compile_binary_istr (openString s)
  end

end

(*
val _ = Globals.max_print_depth := 30

val input = ``"datatype foo = A;"``
val input = ``"val x = \"str\";"``
val input = ``"structure Nat = struct val zero = 0 end;"``
val input = ``"val x = 1; val y = x; val it = x+y;"``
val input = ``"val x = 1;"``
val input = ``"structure Nat = struct val zero = 0 fun succ x = x+1 end; val x = Nat.zero;"``;
val x1 = eval ``get_all_asts ^(input)``
val x2 = eval ``elab_all_asts ^(x1 |> concl |> rhs)``
val x3 = eval ``infer_all_asts ^(x2 |> concl |> rhs)``

val y1 = eval
  ``let prog = ^(x3 |> concl |> rhs |> rand) in
    let n = init_compiler_state.next_global in
    let (m1,m2) = init_compiler_state.globals_env in
    let (v,v2,m2,p) = prog_to_i1 init_compiler_state.next_global m1 m2 prog in
    let (v,exh,p) = prog_to_i2 init_compiler_state.contags_env p in
    let (v,e) = prog_to_i3 (none_tag,SOME(TypeId(Short"option"))) (some_tag,SOME(TypeId(Short"option"))) n p in
    let e = exp_to_exh exh e in
    let e = exp_to_pat [] e in
    let e = exp_to_Cexp e in
    FLOOKUP m2 "it" ``
compile_prog_def

val () = computeLib.add_thms [compile_all_asts_no_init_def] compset
val x4 = eval ``compile_all_asts_no_init ^(x3 |> concl |> rhs)``

val x4 = eval ``compile_all_asts ^(x3 |> concl |> rhs)``

val x5 = eval ``remove_labels_all_asts (\x. 0) ^(x4 |> concl |> rhs)``

val th1 = MATCH_MP remove_labels_all_asts_no_labels x5
val th2 = eval(th1|>concl|>rand|>listSyntax.mk_length)
val () = computeLib.add_thms [EQT_INTRO th1,th2] compset
val res = x5

val x6 = eval ``all_asts_to_encoded ^(x5 |> concl |> rhs)``

val code = rand(rhs(concl x5))
eval ``REVERSE ^code``

val res = eval ``prog_to_bytecode_encoded (\x. 0) ^input``
val res = eval ``prog_to_bytecode_string (\x. 0) ^input``
val res = eval ``prog_to_bytecode (\x. 0) ^input``

val input = ``"fun fact n = if n <= 0 then 1 else n * fact (n-1); fact 5;"``
time (do_compile_binary_str (fromHOLstring input)) "tests/fact5.byte"

val input = ``"val it = 1;"``
time (do_compile_binary_str (fromHOLstring input)) "tests/it1.byte"

val th1 = eval ``bc_evaln 42 (^initial_bc_state with code := ^(res |> concl |> rhs |> rand))``
val th2 = eval ``bc_evaln 100 ^(th1 |> concl |> rhs)``
val th3 = eval ``bc_evaln 100 ^(th2 |> concl |> rhs)``
val thn = th3
val thn = eval ``bc_evaln 100 ^(thn |> concl |> rhs)``
val th4 = eval ``bc_eval1 ^(thn |> concl |> rhs)``
val th4 = eval ``bc_eval1 ^(th1 |> concl |> rhs)``
bytecodeEvalTheory.bc_eval1_def


time (do_compile_binary "tests/test1.ml") "tests/test1.byte"

do_compile_string "tests/test1.ml" "tests/test1.byte"

    val i = openIn "tests/test1.ml";
    val s = inputAll i;
    val _ = closeIn i;
    val asts1 = computeLib.CBV_CONV compset ``get_all_asts ^(fromMLstring s)``;
    val asts1 = computeLib.CBV_CONV compset ``get_all_asts "val x = 1;"``;



    val asts2 = computeLib.CBV_CONV compset ``elab_all_asts ^(asts1 |> concl |> rhs)``;
    val asts3 = computeLib.CBV_CONV compset ``infer_all_asts ^(asts2 |> concl |> rhs)``;
    val asts4 = computeLib.CBV_CONV compset ``compile_all_asts ^(asts3 |> concl |> rhs)``;
    val asts5 = computeLib.CBV_CONV compset ``remove_labels_all_asts (\x. 0) ^(asts4 |> concl |> rhs)``;
    val asts6 = computeLib.CBV_CONV compset ``all_asts_to_string ^(asts5 |> concl |> rhs)``;


    val thm = computeLib.CBV_CONV compset ``prog_to_bytecode_string (\x. 0) ^(fromMLstring s)``

*)
end
