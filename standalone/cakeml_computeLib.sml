structure cakeml_computeLib = struct local
open HolKernel boolLib bossLib lcsymtacs
open miscLib optionLib stringLib listLib listTheory pairTheory finite_mapTheory stringTheory
open miscTheory cmlParseTheory cmlPEGTheory initialEnvTheory 
open lexer_funTheory elabTheory astTheory modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory compilerTheory
open lexer_implTheory inferTheory intLangTheory toIntLangTheory toBytecodeTheory printingTheory compilerProofTheory
open bytecodeLabelsTheory labels_computeLib bytecodeEncodeTheory bytecodeEvalTheory free_varsTheory progToBytecodeTheory
open terminationTheory compilerTerminationTheory

val () = Parse.bring_to_front_overload"Num"{Name="Num",Thy="integer"}

(* computeLib only adds datatype support for the_compset :(. this code is copied
   and modified slightly to allow building custom compsets with datatype support. *)
local
   val get_f =
      fst o boolSyntax.strip_comb o boolSyntax.lhs o
      snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o
      Thm.concl
in
   fun add_datatype_info ty =
    let open Drule
        val size_opt =
          case TypeBase.size_of0 ty
           of SOME (_, TypeBasePure.ORIG def) => [def]
            | otherwise => []
        val boolify_opt =
          case TypeBase.encode_of0 ty
           of SOME (_, TypeBasePure.ORIG def) => [def]
            | otherwise => []
        val case_const = Lib.total TypeBase.case_const_of ty
        val simpls = #rewrs (TypeBase.simpls_of ty)
        val (case_thm, simpls) =
           List.partition (fn thm => Lib.total get_f thm = case_const) simpls
        val case_thm = List.map computeLib.lazyfy_thm case_thm
    in
       fn cs =>
       (computeLib.add_thms (size_opt @ boolify_opt @ case_thm @ simpls) cs;
        Option.app (fn t => computeLib.set_skip cs t (SOME 1)) case_const)
    end
end

val encode_bc_insts_thm = prove(
  ``∀bcs. encode_bc_insts bcs =
    let ls = MAP encode_bc_inst bcs in
    if EXISTS IS_NONE ls then NONE else
    SOME (FLAT (MAP THE ls))``,
  Induct >> simp[encode_bc_insts_def] >>
  fs[LET_THM] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[])

fun cakeml_compset() = let
val compset = wordsLib.words_compset()
(* good libraries which provide compsets :) *)
val () = intReduce.add_int_compset compset
(* included in words_compset
val () = listLib.list_rws compset
val () = numposrepLib.add_numposrep_compset compset
val () = ASCIInumbersLib.add_ASCIInumbers_compset compset
*)
val () = stringLib.add_string_compset compset
val () = sumSimps.SUM_rws compset
val () = optionLib.OPTION_rws compset
val () = pred_setLib.add_pred_set_compset compset
(* combin doesn't provide a compset :( *)
val () = let open combinTheory computeLib
  val K_tm = Term.prim_mk_const{Name="K",Thy="combin"} in
    add_thms
        [K_THM,S_DEF,I_THM,C_DEF,W_DEF,o_THM,K_o_THM,
         APP_DEF,APPLY_UPDATE_THM] compset;
    set_skip compset K_tm (SOME 1)
  end
(* pairLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  (map computeLib.lazyfy_thm
      [CLOSED_PAIR_EQ,FST,SND,pair_case_thm,SWAP_def,
       CURRY_DEF,UNCURRY_DEF,PAIR_MAP_THM])
  compset
(* finite_mapLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  [o_f_FEMPTY
  ,FLOOKUP_EMPTY
  ,FLOOKUP_UPDATE
  ,FLOOKUP_FUNION
  ,DOMSUB_FLOOKUP_THM
  ,FUNION_FEMPTY_1
  ,FUNION_FEMPTY_2
  ,FUPDATE_LIST_THM
  ,FDOM_FUPDATE
  ,FDOM_FEMPTY
  ] compset
(* examples/parsing doesn't provide a compset :( *)
val () = computeLib.add_thms
  [grammarTheory.isTOK_def
  ,grammarTheory.language_def
  ,grammarTheory.derive_def
  ,grammarTheory.ptree_fringe_def
  ,grammarTheory.complete_ptree_def
  ,grammarTheory.ptree_head_def
  ,grammarTheory.ptree_size_def
  ,pegTheory.subexprs_def
  ,pegTheory.wfG_def
  ,pegTheory.Gexprs_def
  ,pegexecTheory.poplist_aux_def
  ,pegexecTheory.poplistval_def
  ,pegexecTheory.pegparse_def
  ,pegexecTheory.destResult_def
  ,pegexecTheory.applykont_thm
  ,pegexecTheory.peg_exec_thm
  ] compset
val () = add_datatype_info ``:('a,'b)grammar$symbol`` compset
val () = add_datatype_info ``:('a,'b)grammar`` compset
val () = add_datatype_info ``:('a,'b)parsetree`` compset
val () = add_datatype_info ``:('a,'b,'c)pegsym`` compset
val () = add_datatype_info ``:('a,'b,'c)peg`` compset
val () = add_datatype_info ``:('a,'b,'c)kont`` compset
val () = add_datatype_info ``:('a,'b,'c)evalcase`` compset
(* misc :( *)
val () = computeLib.add_thms
  [miscTheory.find_index_def
  ,compilerLibTheory.lunion_def
  ,compilerLibTheory.lshift_def
  ,compilerLibTheory.el_check_def
  ,compilerLibTheory.the_def
  ,compilerLibTheory.num_fold_def
  ,listTheory.MAP2_def
  ] compset
(* semantics *)
val () = computeLib.add_thms
  [gramTheory.nt_distinct_ths
  ,libTheory.merge_def
  ,libTheory.bind_def
  ,terminationTheory.is_value_def
  ,pat_bindings_def
  ,typeSystemTheory.merge_tenvC_def
  ,bytecodeTheory.bool_to_tag_def
  ,bytecodeTheory.unit_tag_def
  ,bytecodeTheory.closure_tag_def
  ,bytecodeTheory.string_tag_def
  ,bytecodeTheory.block_tag_def
  ,conLangTheory.tuple_tag_def
  ,conLangTheory.div_tag_def
  ,conLangTheory.bind_tag_def
  ,conLangTheory.eq_tag_def
  ,conLangTheory.cons_tag_def
  ,conLangTheory.nil_tag_def
  ,conLangTheory.some_tag_def
  ,conLangTheory.none_tag_def
  ] compset
val () = add_datatype_info ``:MMLnonT`` compset
val () = add_datatype_info ``:top`` compset
val () = add_datatype_info ``:dec`` compset
val () = add_datatype_info ``:pat`` compset
val () = add_datatype_info ``:exp`` compset
val () = add_datatype_info ``:tid_or_exn`` compset
val () = add_datatype_info ``:uop`` compset
val () = add_datatype_info ``:op`` compset
val () = add_datatype_info ``:lop`` compset
val () = add_datatype_info ``:lit`` compset
val () = add_datatype_info ``:opb`` compset
val () = add_datatype_info ``:opn`` compset
val () = add_datatype_info ``:'a id`` compset
val () = add_datatype_info ``:eq_result`` compset
(* lexer *)
val () = computeLib.add_thms
  [lex_until_toplevel_semicolon_def
  ,lex_aux_def
  ,next_token_def
  ,next_sym_def
  ,token_of_sym_def
  ,read_while_def
  ,skip_comment_def
  ,isSymbol_def
  ,isAlphaNumPrime_def
  ,isAlphaNum_def
  ,is_single_char_symbol_def
  ,get_token_def
  ,processIdent_def
  ,tokenUtilsTheory.isInt_def
  ,tokenUtilsTheory.isTyvarT_def
  ,tokenUtilsTheory.destStringT_def
  ,tokenUtilsTheory.destIntT_def
  ,tokenUtilsTheory.destSymbolT_def
  ,tokenUtilsTheory.destAlphaT_def
  ,tokenUtilsTheory.destTOK_def
  ,tokenUtilsTheory.destLf_def
  ,tokenUtilsTheory.destTyvarPT_def
  ,tokenUtilsTheory.destLongidT_def
  ,tokenUtilsTheory.isLongidT_def
  ,tokenUtilsTheory.isWhitespaceT_def
  ,tokenUtilsTheory.isString_def
  ,tokenUtilsTheory.isAlphaSym_def
  ,tokenUtilsTheory.isSymbolT_def
  ,tokenUtilsTheory.isAlphaT_def
  ] compset
val () = add_datatype_info ``:symbol`` compset
val () = add_datatype_info ``:token`` compset
(* parser *)
val () = computeLib.add_thms
  [destResult_def
  ,parse_REPLphrase_def
  ,parse_def
  ,parse_top_def
  ,cmlParseREPLTop_def
  ,cmlParseExpr_def
  ,cmlParseREPLPhrase_def
  ,sumID_def
  ,tokeq_def
  ,cmlPEG_exec_thm
  ,peg_StructName_def
  ,peg_EbaseParen_def
  ,peg_EbaseParenFn_def
  ,peg_longV_def
  ,peg_V_def
  ,peg_TypeDec_def
  ,peg_UQConstructorName_def
  ,pnt_def
  ,try_def
  ,peg_nonfix_def
  ,pegf_def
  ,seql_def
  ,choicel_def
  ,mktokLf_def
  ,bindNT_def
  ,peg_linfix_def
  ,mk_linfix_def
  ,mk_rinfix_def
  ,cmlPtreeConversionTheory.tuplify_def
  ,cmlPtreeConversionTheory.ptree_REPLTop_def
  ,cmlPtreeConversionTheory.ptree_REPLPhrase_def
  ,cmlPtreeConversionTheory.ptree_TopLevelDecs_def
  ,cmlPtreeConversionTheory.ptree_TopLevelDec_def
  ,cmlPtreeConversionTheory.ptree_Structure_def
  ,cmlPtreeConversionTheory.ptree_StructName_def
  ,cmlPtreeConversionTheory.ptree_SignatureValue_def
  ,cmlPtreeConversionTheory.ptree_SpeclineList_def
  ,cmlPtreeConversionTheory.ptree_SpecLine_def
  ,cmlPtreeConversionTheory.ptree_Decls_def
  ,cmlPtreeConversionTheory.ptree_Decl_def
  ,cmlPtreeConversionTheory.ptree_Expr_def
  ,cmlPtreeConversionTheory.mkAst_App_def
  ,cmlPtreeConversionTheory.Eseq_encode_def
  ,cmlPtreeConversionTheory.ptree_Pattern_def
  ,cmlPtreeConversionTheory.mkPatApp_def
  ,cmlPtreeConversionTheory.ptree_FQV_def
  ,cmlPtreeConversionTheory.ptree_Vlist1_def
  ,cmlPtreeConversionTheory.ptree_V_def
  ,cmlPtreeConversionTheory.ptree_Op_def
  ,cmlPtreeConversionTheory.ptree_TypeDec_def
  ,cmlPtreeConversionTheory.ptree_DtypeDecl_def
  ,cmlPtreeConversionTheory.ptree_Dconstructor_def
  ,cmlPtreeConversionTheory.detuplify_def
  ,cmlPtreeConversionTheory.ptree_ConstructorName_def
  ,cmlPtreeConversionTheory.ptree_UQConstructorName_def
  ,cmlPtreeConversionTheory.ptree_TypeName_def
  ,cmlPtreeConversionTheory.ptree_Type_def
  ,cmlPtreeConversionTheory.ptree_linfix_def
  ,cmlPtreeConversionTheory.ptree_Tyop_def
  ,cmlPtreeConversionTheory.ptree_TyvarN_def
  ,cmlPtreeConversionTheory.ptree_UQTyop_def
  ,cmlPtreeConversionTheory.safeTL_def
  ,cmlPtreeConversionTheory.oHD_def
  ] compset
val () = add_datatype_info ``:repl_parse_result`` compset
(* elaborator *)
val () = computeLib.add_thms
  [elab_prog_def
  ,elab_top_def
  ,elab_dec_def
  ,elab_t_def
  ,init_type_bindings_def
  ] compset
(* inferencer *)
val () = unifyLib.reset_wfs_thms()
val () = unifyLib.add_unify_compset compset
val () = computeLib.add_thms
  [infer_prog_def
  ,infer_top_def
  ,infer_d_def
  ,infer_e_def
  ,infer_p_def
  ,st_ex_bind_def
  ,st_ex_return_def
  ,libTheory.lookup_def
  ,libTheory.opt_bind_def
  ,libTheory.emp_def
  ,lookup_tenvC_st_ex_def
  ,typeSystemTheory.merge_tenvC_def
  ,init_tenvC_def
  ,lookup_st_ex_def
  ,init_state_def
  ,get_next_uvar_def
  ,fresh_uvar_def
  ,n_fresh_uvar_def
  ,guard_def
  ,add_constraint_def
  ,add_constraints_def
  ,read_def
  ,generalise_def
  ,apply_subst_list_def
  ,append_decls_def
  ,constrain_op_def
  ,infer_deBruijn_subst_def
  ,Infer_Tfn_def
  ,Infer_Tint_def
  ,Infer_Tbool_def
  ,Infer_Tref_def
  ,Infer_Tunit_def
  ,init_infer_decls_def
  ,init_infer_state_def
  ,init_type_env_def
  ,typeSystemTheory.check_exn_tenv_def
  ,check_freevars_def
  ,mk_id_def
  ,infer_type_subst_def
  ,typeSystemTheory.tid_exn_to_tc_def
  ] compset
val () = add_datatype_info ``:infer_t`` compset
val () = add_datatype_info ``:atom`` compset
val () = add_datatype_info ``:('a,'b)exc`` compset
val () = add_datatype_info ``:'a infer_st`` compset
(* modLang compiler *)
val () = computeLib.add_thms
  [prog_to_i1_def
  ,top_to_i1_def
  ,decs_to_i1_def
  ,dec_to_i1_def
  ,exp_to_i1_def
  ,alloc_defs_def
  ] compset
val () = add_datatype_info ``:prompt_i1`` compset
val () = add_datatype_info ``:dec_i1`` compset
(* conLang compiler *)
val () = computeLib.add_thms
  [prog_to_i2_def
  ,prompt_to_i2_def
  ,decs_to_i2_def
  ,exp_to_i2_def
  ,pat_to_i2_def
  ,uop_to_i2_def
  ,init_tagenv_state_def
  ,get_tagenv_def
  ,lookup_tag_env_def
  ,lookup_tag_flat_def
  ,num_defs_def
  ,mod_tagenv_def
  ,insert_tag_env_def
  ,alloc_tag_def
  ] compset
val () = add_datatype_info ``:prompt_i2`` compset
val () = add_datatype_info ``:dec_i2`` compset
val () = add_datatype_info ``:pat_i2`` compset
val () = add_datatype_info ``:exp_i2`` compset
(* decLang compiler *)
val () = computeLib.add_thms
  [prog_to_i3_def
  ,prompt_to_i3_def
  ,init_globals_def
  ,init_global_funs_def
  ,decs_to_i3_def
  ] compset
(* exhLang compiler *)
val () = computeLib.add_thms
  [exp_to_exh_def
  ,pat_to_exh_def
  ,add_default_def
  ,exhaustive_match_def
  ,is_var_def
  ,get_tags_def
  ] compset
(* patLang compiler *)
val () = computeLib.add_thms
  [exp_to_pat_def
  ,row_to_pat_def
  ,pat_to_pat_def
  ,sLet_pat_def
  ,sIf_pat_def
  ,ground_pat_def
  ,uop_to_pat_def
  ,pure_pat_def
  ,(CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)) Let_Els_pat_def
  ,pure_uop_pat_def
  ] compset
val () = add_datatype_info ``:exp_pat`` compset
val () = add_datatype_info ``:uop_pat`` compset
(* intLang compiler *)
val () = computeLib.add_thms
  [exp_to_Cexp_def
  ,opn_to_prim2_def
  ,free_labs_def
  ,free_vars_def
  ,no_labs_def
  ] compset
val () = add_datatype_info ``:Cprim1`` compset
val () = add_datatype_info ``:Cprim2`` compset
(* bytecode compiler *)
val () =
  let
    val nameof = fst o dest_const o fst o strip_comb o lhs o snd o strip_forall o concl
    val (l1,l2) = List.partition(equal"compile" o nameof)(CONJUNCTS compile_def)
    val (l2,l3) = List.partition(equal"compile_bindings" o nameof) l2
  in
    computeLib.add_thms
      [label_closures_def
      ,bind_fv_def
      ,shift_def
      ,mkshift_def
      ,compile_code_env_def
      ,cce_aux_def
      ,get_label_def
      ,emit_def
      ,pushret_def
      ,push_lab_def
      ,cons_closure_def
      ,emit_ceenv_def
      ,emit_ceref_def
      ,update_refptr_def
      ,compile_closures_def
      ,compile_envref_def
      ,compile_varref_def
      ,stackshift_def
      ,stackshiftaux_def
      ,prim1_to_bc_def
      ,prim2_to_bc_def
      ,LIST_CONJ l1
      ,(CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)) (LIST_CONJ l2)
      ,LIST_CONJ l3
      ] compset
  end
val () = computeLib.add_thms
  [compile_Cexp_def
  ] compset
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
val () = add_datatype_info ``:compiler_result`` compset
val () = add_datatype_info ``:call_context`` compset
(* labels removal *)
val () = labels_computeLib.reset_code_labels_ok_db()
val () = computeLib.add_conv (``code_labels``,2,code_labels_conv (computeLib.CBV_CONV compset)) compset
(* free vars and closed (for discharging labels hypothesis) *)
val () = computeLib.add_thms
  [closed_prog_def
  ,FV_prog_def
  ,new_top_vs_def
  ,new_dec_vs_def
  ,FV_top_def
  ,FV_decs_def
  ,FV_dec_def
  ,FV_def
  ] compset
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
    fun code_labels_ok_conv tm =
      EQT_INTRO
        (labels_computeLib.get_code_labels_ok_thm
          (rand tm))
  in
    computeLib.add_thms
      [uses_label_def
      ,compile_print_err_def
      ] compset ;
    add_datatype_info ``:bc_inst`` compset ;
    computeLib.add_conv(``code_labels_ok``,1,code_labels_ok_conv) compset ;
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
val () = add_datatype_info ``:compiler_state`` compset
in compset end

val bc_fetch_aux_0_thm = prove(
  ``∀code pc. bc_fetch_aux code (K 0) pc =
    if no_labels code then el_check pc code
    else FAIL (bc_fetch_aux code (K 0) pc) "code has labels"``,
  REWRITE_TAC[no_labels_def] >>
  Induct >> simp[bytecodeTheory.bc_fetch_aux_def,compilerLibTheory.el_check_def] >>
  rw[] >> fs[combinTheory.FAIL_DEF,compilerLibTheory.el_check_def] >>
  simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

val remove_labels_all_asts_no_labels = prove(
  ``(remove_labels_all_asts x = Success ls) ⇒ no_labels ls``,
  Cases_on`x`>>rw[remove_labels_all_asts_def]
  >> rw[code_labels_no_labels])

in
  val cakeml_compset = cakeml_compset

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
      ,bytecodeTheory.can_Print_def
      ,printerTheory.ov_to_string_def
      ,bytecodeTheory.bv_to_ov_def
      ,semanticPrimitivesTheory.int_to_string_def
      ,CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook) bc_evaln_def
      ,LEAST_thm
      ,least_from_thm
      ,compilerLibTheory.el_check_def
      ,listTheory.LUPDATE_compute
      ] compset
    val () = add_datatype_info ``:bc_state`` compset
    val () = add_datatype_info ``:bc_value`` compset
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
        val thm = eval ``case prog_to_bytecode_string ^(fromMLstring s) of Failure x => "<compile error>" ++ x | Success s => s``
        val _ = assert (fn x => hyp x = []) thm;
      in
        fromHOLstring (rhs (concl thm))
      end
    fun compile_binary s =
      let
        val thm = eval ``case prog_to_bytecode_encoded ^(fromMLstring s)
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
val _ = Globals.max_print_depth := 50

val input = ``"val x = 1; val y = x; val it = x+y;"``
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

val x5 = eval ``remove_labels_all_asts ^(x4 |> concl |> rhs)``

val th1 = MATCH_MP remove_labels_all_asts_no_labels x5
val th2 = eval(th1|>concl|>rand|>listSyntax.mk_length)
val () = computeLib.add_thms [EQT_INTRO th1,th2] compset
val res = x5

val x6 = eval ``all_asts_to_encoded ^(x5 |> concl |> rhs)``

val code = rand(rhs(concl x5))
eval ``REVERSE ^code``

val res = eval ``prog_to_bytecode_encoded ^input``
val res = eval ``prog_to_bytecode_string ^input``
val res = eval ``prog_to_bytecode ^input``

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
    val asts5 = computeLib.CBV_CONV compset ``remove_labels_all_asts ^(asts4 |> concl |> rhs)``;
    val asts6 = computeLib.CBV_CONV compset ``all_asts_to_string ^(asts5 |> concl |> rhs)``;


    val thm = computeLib.CBV_CONV compset ``prog_to_bytecode_string ^(fromMLstring s)``

*)
end