open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open alistTheory BasicProvers sortingTheory miscTheory
open word_langTheory word_lemmasTheory word_procTheory word_liveTheory
open rich_listTheory

val _ = new_theory "word_ssa";

(*Define a ssa + calling conventions pass
  The strategy is the keep an sptree mapping of variables -> their latest names
  Whenever we get a new "write", we assign a new fresh name to it

  Alloc and Call will be special cases which instead generate alloc variables for cutsets
   
  The overall proof should be:

  prog (starts with 0,2,4,6... in locals)
  --> Add moves for each argument in the locals e.g. Move(2,2);Move(4,4);prog
  --> SSA pass changes these uniformly to Move(4n+3,2);Move...;prog

  Properties that should be proved:
  1) Every Alloc/Call cutsets only contain stack variables
  2) Every Call uses args [0;2;4...]
  3) Correctness theorem 
*)

(*If it's in the map then lookup the map else dont remap*)
val option_lookup_def = Define`
  option_lookup t v = case lookup v t of NONE => v | SOME x => x`

(*Consistently sets up the next alloc variable rename for v*)
val next_var_rename_def = Define`
  next_var_rename v ssa (na:num) = (na,insert v na ssa,na+4)`

val list_next_var_rename_def = Define`
  (list_next_var_rename [] ssa (na:num) = ([],ssa,na)) ∧
  (list_next_var_rename (x::xs) ssa na =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ssa',na') = next_var_rename x ssa na in
    let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
      (y::ys,ssa'',na''))`

val list_next_stack_rename_def = Define`
  (list_next_stack_rename [] (ns:num) = ([],ns)) ∧
  (list_next_stack_rename (x::xs) ns =
    (*Write this way to make it ascending, can also use acc passing*)
    let (y,ns') = (ns,ns+4) in
    let (ys,ns'') = list_next_stack_rename xs ns' in
      (y::ys,ns''))`

(*Whenever we have 2 branches, we need to make them consistent at their join positions
  This is an approximation of phi functions
  Current idea:
  Our proof will have an assumption like:
  ∀v. v ∈ domain ssa_map ∧  v ∈ st.locals ⇒ ssa_map v ∈ cst.locals
  therefore, we really want to take a special union of the 2 branches:

  If a variable exists in one branch but not the other, then merge it in
  Else,
    if they clash (i.e. both branches assigned to it, giving it different names) then add a move to undo the 
    renames
    Otherwise do nothing*)

(*For each entry that is in
  1) Ldiff = in R but not L --> Add moves to LHS
  2) Rdiff = in L but not R --> Add moves to RHS
  3) clash = in both --> For any inconsistencies, combine them
*)

(*This is slightly less efficient for fake moves
  but probably makes the proof easier*)
val fake_move_def = Define`
  fake_move v = Assign v (Const 0w)`

val merge_moves_def = Define`
  (merge_moves [] ssa_L ssa_R na = (Skip:'a word_prog,Skip:'a word_prog,
                                    na,ssa_L,ssa_R)) ∧ 
  (merge_moves (x::xs) ssa_L ssa_R na = 
    let (seqL,seqR,na',ssa_L',ssa_R') = 
      merge_moves xs ssa_L ssa_R na in
    let optLx = lookup x ssa_L' in
    let optLy = lookup x ssa_R' in
    case (optLx,optLy) of 
      (NONE,NONE) => (seqL,seqR,na',ssa_L',ssa_R')
    | (NONE,SOME Ly) =>
        let Lmove = Seq seqL (fake_move na') in
        let Rmove = Seq seqR (Move [(na',Ly)]) in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | (SOME Lx,NONE) =>
        let Lmove = Seq seqL (Move [(na',Lx)]) in
        let Rmove = Seq seqR (fake_move na') in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R')
    | (SOME Lx,SOME Ly) =>
      if Lx = Ly then
        (seqL,seqR,na',ssa_L',ssa_R')
      else
        let Lmove = Seq seqL (Move [(na',Lx)]) in
        let Rmove = Seq seqR (Move [(na',Ly)]) in
        (Lmove, Rmove,na'+4, insert x na' ssa_L', insert x na' ssa_R'))`

val fix_inconsistencies_def = Define`
  fix_inconsistencies ssa_L ssa_R na =
  let var_union = MAP FST (toAList (union ssa_L ssa_R)) in
  let (Lmov,Rmov,na',ssa_L',ssa_R') = 
    merge_moves var_union ssa_L ssa_R na in
    (Lmov,Rmov,na',ssa_L')`

(*ssa_cc_trans_inst does not need to interact with stack*)
val ssa_cc_trans_inst_def = Define`
  (ssa_cc_trans_inst Skip ssa na = (Skip,ssa,na)) ∧ 
  (ssa_cc_trans_inst (Const reg w) ssa na = 
    let (reg',ssa',na') = next_var_rename reg ssa na in
      ((Const reg' w),ssa',na')) ∧ 
  (ssa_cc_trans_inst (Arith (Binop bop r1 r2 ri)) ssa na =
    case ri of
      Reg r3 => 
      let r3' = option_lookup ssa r3 in
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Arith (Binop bop r1' r2' (Reg r3')),ssa',na')
    | _ => 
      let r2' = option_lookup ssa r2 in
      let (r1',ssa',na') = next_var_rename r1 ssa na in
        (Arith (Binop bop r1' r2' ri),ssa',na')) ∧ 
  (ssa_cc_trans_inst (Arith (Shift shift r1 r2 n)) ssa na =
    let r2' = option_lookup ssa r2 in
    let (r1',ssa',na') = next_var_rename r1 ssa na in
      (Arith (Shift shift r1' r2' n),ssa',na')) ∧ 
  (ssa_cc_trans_inst (Mem Load r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let (r',ssa',na') = next_var_rename r ssa na in
      (Mem Load r' (Addr a' w),ssa',na')) ∧ 
  (ssa_cc_trans_inst (Mem Store r (Addr a w)) ssa na =
    let a' = option_lookup ssa a in
    let r' = option_lookup ssa r in
      (Mem Store r' (Addr a' w),ssa,na)) ∧ 
  (*Catchall -- for future instructions to be added*)
  (ssa_cc_trans_inst x ssa na = (x,ssa,na))`

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
val ssa_cc_trans_exp_def = tDefine "ssa_cc_trans_exp" `
  (ssa_cc_trans_exp t (Var num) =
    Var (case lookup num t of NONE => num | SOME x => x)) ∧ 
  (ssa_cc_trans_exp t (Load exp) = Load (ssa_cc_trans_exp t exp)) ∧
  (ssa_cc_trans_exp t (Op wop ls) =
    Op wop (MAP (ssa_cc_trans_exp t) ls)) ∧ 
  (ssa_cc_trans_exp t (Shift sh exp nexp) = 
    Shift sh (ssa_cc_trans_exp t exp) nexp) ∧
  (ssa_cc_trans_exp t expr = expr)`
  (WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*TODO: delete option_lookups?*)
val ssa_cc_trans_def = Define`
  (ssa_cc_trans Skip ssa na ns = (Skip,ssa,na,ns)) ∧ 
  (ssa_cc_trans (Move ls) ssa na ns =
    let ls_1 = MAP FST ls in
    let ls_2 = MAP SND ls in 
    let ren_ls2 = MAP (option_lookup ssa) ls_2 in
    let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
      (Move(ZIP(ren_ls1,ren_ls2)),ssa',na',ns)) ∧ 
  (ssa_cc_trans (Inst i) ssa na ns =
    let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
      (Inst i',ssa',na',ns)) ∧ 
  (ssa_cc_trans (Assign num exp) ssa na ns =
    let exp' = ssa_cc_trans_exp ssa exp in
    let (num',ssa',na') = next_var_rename num ssa na in
      (Assign num' exp',ssa',na',ns)) ∧ 
  (ssa_cc_trans (Get num store) ssa na ns = 
    let (num',ssa',na') = next_var_rename num ssa na in
      (Get num' store,ssa',na',ns)) ∧ 
  (ssa_cc_trans (Store exp num) ssa na ns =
    let exp' = ssa_cc_trans_exp ssa exp in
    let num' = option_lookup ssa num in
      (Store exp' num',ssa,na,ns)) ∧ 
  (ssa_cc_trans (Seq s1 s2) ssa na ns =
    let (s1',ssa',na',ns') = ssa_cc_trans s1 ssa na ns in
    let (s2',ssa'',na'',ns'') = ssa_cc_trans s2 ssa' na' ns' in 
      (Seq s1' s2',ssa'',na'',ns'')) ∧ 
  (*Tricky case 1: we need to merge the ssa results from both branches by
    unSSA-ing the phi functions
  *)
  (ssa_cc_trans (If e1 num e2 e3) ssa na ns = 
    let (e1',ssa1,na1,ns1) = ssa_cc_trans e1 ssa na ns in
    let num' = option_lookup ssa1 num in
    (*ssa1 is the copy for both branches,
      however, we can use new na2 and ns2
    *)
    let (e2',ssa2,na2,ns2) = ssa_cc_trans e2 ssa1 na1 ns1 in
    (*ssa2 is the ssa map for the first branch*)
    let (e3',ssa3,na3,ns3) = ssa_cc_trans e3 ssa1 na2 ns2 in
    (*ssa3 is the ssa map for the second branch, notice we
      continued using na2 and ns2 here though!*)
    let (e2_cons,e3_cons,na_fin,ssa_fin) = 
      fix_inconsistencies ssa2 ssa3 na3 in
    (If e1' num' (Seq e2' e2_cons) (Seq e3' e3_cons),ssa_fin,na_fin,ns3)) ∧
  (*For cutsets, we must restart the ssa mapping to maintain consistency*) 
  (ssa_cc_trans (Alloc num numset) ssa na ns = 
    let num' = option_lookup ssa num in 
    let ls = MAP FST (toAList numset) in
    let cur_ls = MAP (option_lookup ssa) ls in
    let (stack_ls,ns') = list_next_stack_rename cur_ls ns in 
    let stack_set = numset_list_insert stack_ls LN in
    (*Cutdown to only those in numset, maybe shift later*)
    let ssa' = inter ssa numset in  
    let (ren_ls,ssa'',na') = list_next_var_rename ls ssa' na in
    let prog = (Seq (Move (ZIP (stack_ls,cur_ls))) 
               (Seq (Alloc num' stack_set)
               (Move (ZIP (ren_ls,stack_ls))))) in
    (prog,ssa',na',ns')) ∧ 
  (ssa_cc_trans (Raise num) ssa na ns =
    let num' = option_lookup ssa num in
    (Raise num',ssa,na,ns)) ∧ 
  (ssa_cc_trans (Return num) ssa na ns =
    let num' = option_lookup ssa num in
    (Return num',ssa,na,ns)) ∧ 
  (ssa_cc_trans Tick ssa na ns = (Tick,ssa,na,ns)) ∧ 
  (ssa_cc_trans (Set n exp) ssa na ns = 
    let exp' = ssa_cc_trans_exp ssa exp in
    (Set n exp',ssa,na,ns)) ∧ 
  (*I think it may be easier to split Calls at the top level into 3 different cases
    because they have different control flow properties:
    1) Tail calls ⇒ just need to rename args, handler should be NONE..
    2) No handler ⇒ add a renamer to the returning handler to fixup the cutsets
    3) Handler ⇒ most complex, we will need renamers in both cases and THEN a consistency rename after
  *)
  (ssa_cc_trans (Call ret dest args h) ssa na ns =
    let names = MAP (option_lookup ssa) args in 
    let conv_args = even_list (LENGTH names) in
    let move_args = (Move (ZIP (conv_args,args))) in
      (case ret of 
        NONE =>
          (Seq move_args (Call NONE dest conv_args h),ssa,na,ns)
      | SOME (ret,numset,ret_handler) => 
          let ls = MAP FST (toAList numset) in
          let cur_ls = MAP (option_lookup ssa) ls in
          let (stack_ls,ns_1) = list_next_stack_rename cur_ls ns in 
          let stack_set = numset_list_insert stack_ls LN in
          let (ren_ls,ssa_0,na_1) = list_next_var_rename ls ssa na in
          (*Cut down the ssa set*)
          let ssa_1 = inter ssa_0 numset in  
          let move_cutset = Move (ZIP (stack_ls,cur_ls)) in
          let restore_cutset = Move (ZIP (ren_ls,stack_ls)) in
          (*ssa_1 is before branching*)
          let (ret',ssa_2_p,na_2_p) = next_var_rename ret ssa_1 na_1 in
          let (ren_ret_handler,ssa_2,na_2,ns_2) = 
            (ssa_cc_trans ret_handler ssa_2_p na_2_p ns_1) in
          let mov_ret_handler = 
            (Seq restore_cutset (Seq (Move[ret',0]) (ren_ret_handler))) in
          (case h of
            NONE =>
            let prog = 
              (Seq move_args (Seq move_cutset
              (Call (SOME(0,stack_set,mov_ret_handler)) 
                dest conv_args NONE))) in
            (prog,ssa_2,na_2,ns_2)
          | SOME(n,h) => 
            let (n',ssa_3_p,na_3_p) = next_var_rename n ssa_1 na_2 in
            let (ren_exc_handler,ssa_3,na_3,ns_3) =
              (ssa_cc_trans h ssa_3_p na_3_p ns_2) in
            let mov_exc_handler = 
              (Seq restore_cutset (Seq(Move[n',0]) (ren_exc_handler))) in
            let (ret_cons,exc_cons,na_fin,ssa_fin) = 
              fix_inconsistencies ssa_2 ssa_3 na_3 in
            let cons_ret_handler = Seq mov_ret_handler ret_cons in
            let cons_exc_handler = Seq mov_exc_handler exc_cons in
            let prog = 
              (Seq move_args (Seq move_cutset
              (Call (SOME(0,stack_set,cons_ret_handler))
               dest conv_args (SOME(0,cons_exc_handler))))) in
            (prog,ssa_fin,na_fin,ns_3))))` 

val size_tac = discharge_hyps>- (fs[word_prog_size_def]>>DECIDE_TAC)

(*
val fake_moves_conventions = prove(``
  ∀ls.
  let mov = fake_moves ls in 
  call_arg_convention mov ∧ 
  every_stack_var is_stack_var mov``,
  Induct>>rw[]>>unabbrev_all_tac>>
  fs[call_arg_convention_def,every_stack_var_def,fake_moves_def,LET_THM])

val merge_moves_conventions = prove(``
  ∀ls ssaL ssaR na ssaU.
  let (a:'a word_prog,b:'a word_prog,c,d) = 
    merge_moves ssaL ssaR ls na ssaU in
  every_stack_var is_stack_var a ∧ 
  every_stack_var is_stack_var b ∧ 
  call_arg_convention a ∧
  call_arg_convention b``,
  Induct>>rw[merge_moves_def]>>
  fs[call_arg_convention_def,every_stack_var_def]>>
  Cases_on`Lx=Ly`>>fs[]>>
  first_x_assum(qspecl_then[`ssaL`,`ssaR`,`na`,`ssaU`] assume_tac)>>
  rfs[LET_THM]>>
  unabbrev_all_tac>>
  fs[EQ_SYM_EQ,every_stack_var_def,call_arg_convention_def])

val fix_inconsistencies_conventions = prove(``
  ∀ssaL ssaR na.
  let (a:'a word_prog,b:'a word_prog,c,d) = 
    fix_inconsistencies ssaL ssaR na in 
  every_stack_var is_stack_var a ∧ 
  every_stack_var is_stack_var b ∧ 
  call_arg_convention a ∧
  call_arg_convention b``,
  fs[fix_inconsistencies_def,call_arg_convention_def,every_stack_var_def,UNCURRY]>>
  rpt strip_tac>>
  rw[]>>
  unabbrev_all_tac>>
  qabbrev_tac `ls = MAP FST (toAList (inter ssaL ssaR))` >>
  Q.SPECL_THEN [`ls`,`ssaL`,`ssaR`,`na`,`union ssaL ssaR`] 
    assume_tac merge_moves_conventions>>rfs[LET_THM]>>
  fs[every_stack_var_def,call_arg_convention_def]>>
  metis_tac[fake_moves_conventions])
  
val list_next_stack_rename_stack_vars = prove(``
  ∀(ls:num list) ns.
  is_stack_var ns ⇒ 
  let (ls',ns') = list_next_stack_rename ls ns in
  is_stack_var ns' ∧
  (*TODO:
  ns ≤ ns' ∧
  ALL_DISTINCT ls' probably need to prove these for correctness later*)  
  EVERY is_stack_var ls'``,
  Induct>>fs[list_next_stack_rename_def,LET_THM]>>rw[]>>
  `is_stack_var (ns+4)` by 
    (fs[is_stack_var_def]>>
    cheat)>>
  res_tac>>
  Cases_on`list_next_stack_rename ls (ns+4)`>>fs[])
 
val ssa_cc_trans_pre_alloc_conventions = store_thm("ssa_cc_trans_pre_alloc_conventions",
``∀prog ssa na ns.
  is_stack_var ns ⇒  
  let (prog',ssa',na',ns') = ssa_cc_trans prog ssa na ns in
  pre_alloc_conventions prog' ∧ 
  is_stack_var ns'``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,LET_THM,LAMBDA_PROD]>>
  Cases_on`prog`>>
  TRY(fs[ssa_cc_trans_def,pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,LET_THM,UNCURRY]>>rw[]>>NO_TAC)>>
  fs[ssa_cc_trans_def,pre_alloc_conventions_def]>>rw[]>>
  fs[call_arg_convention_def,every_stack_var_def]
  >-
  (EVERY_CASE_TAC>>
  TRY(fs[every_stack_var_def,Abbr`move_args`,call_arg_convention_def
      ,Abbr`conv_args`]>>NO_TAC)>>
  rw[]>>
  imp_res_tac list_next_stack_rename_stack_vars>>
  pop_assum(qspec_then`cur_ls` assume_tac)>>
  unabbrev_all_tac>>
  rfs[LET_THM,call_arg_convention_def,every_stack_var_def,even_list_def]
  >-
    (first_x_assum(qspecl_then[`r'`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    size_tac>>
    discharge_hyps>-fs[]>>rw[]>>
    fs[domain_numset_list_insert,EVERY_MEM])
  >>
    unabbrev_all_tac>>fs[call_arg_convention_def,every_stack_var_def]>>
    first_assum(qspecl_then[`r''`,`ssa_2_p`,`na_2_p`,`ns_1`] mp_tac)>>
    size_tac>>
    discharge_hyps>-fs[]>>strip_tac>>
    first_assum(qspecl_then[`r`,`ssa_3_p`,`na_3_p`,`ns_2`] mp_tac)>>
    size_tac>>
    discharge_hyps>-rfs[]>>
    strip_tac>>rfs[]>>
    fs[domain_numset_list_insert,EVERY_MEM]>>
    rw[]>>
    Q.SPECL_THEN [`ssa_2`,`ssa_3`,`na_3`] assume_tac fix_inconsistencies_conventions>>
    rfs[LET_THM])
  >-
  (*Seq*)
  (first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_x_assum(qspecl_then[`w0`,`ssa'`,`na'`,`ns'`] assume_tac)>>
  ntac 2 (pop_assum mp_tac >> size_tac)>>
  rw[])
  >-
  (*If*)
  (fs[]>>
  first_assum(qspecl_then[`w`,`ssa`,`na`,`ns`] assume_tac)>>
  first_assum(qspecl_then[`w0`,`ssa1`,`na1`,`ns1`] assume_tac)>>
  first_x_assum(qspecl_then[`w1`,`ssa1`,`na2`,`ns2`] assume_tac)>>
  ntac 3 (pop_assum mp_tac >> size_tac)>>
  rw[]>>
   Q.SPECL_THEN [`ssa2`,`ssa3`,`na3`] assume_tac fix_inconsistencies_conventions>>
  rfs[LET_THM])
  >>
  (*Alloc*)
  fs[Abbr`prog`,every_stack_var_def,call_arg_convention_def]>>
  imp_res_tac list_next_stack_rename_stack_vars>>
  pop_assum(qspec_then`cur_ls` assume_tac)>>
  rfs[LET_THM]>>rw[Abbr`stack_set`]>>
  fs[domain_numset_list_insert,EVERY_MEM])
*)

(*
EVAL ``ssa_cc_trans 
(Seq
(If (Move [(1,2)]) 0 
  (If (Move [(1,2)]) 0 (Move [(42,3)]) Skip) 
  (Seq (Move [(42,5)]) Skip))
(Seq (Move[(5,42)]) (Move [(6,4)]))) LN 101 103`` 

Skip)

Seq (Alloc 5 (numset_list_insert [1;2;3;4;5;6] LN)) (
Seq (Move [(1,5)]) Skip)))) init_ssa_state``

(Move([(1,2);(3,4)])) init_ssa_state``

Move 1,2
Move 3,1
Move 3,4
Move 1,5

*)
 
(*TODO: decide whether to prove this with or without permutation oracle machinery
  It is probably easier without, since we can force the key-vals pushed onto the stack to have
  the monotonicity properties wherever required

*)

val ssa_locals_rel_def = Define`
  ssa_locals_rel na ssa st_locs cst_locs =
  ((∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
  (∀x y. lookup x st_locs = SOME y ⇒ 
    x ∈ domain ssa ∧
    lookup (THE (lookup x ssa)) cst_locs = SOME y ∧ 
    (is_alloc_var x ⇒ x < na)))`    

val ssa_map_bounded_def = Define`
  ssa_map_bounded na ssa =
  (∀x y. lookup x ssa = SOME y ⇒ is_alloc_var y ∧ y < na)`

val list_next_var_rename_lemma_1 = prove(``
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒ 
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧ 
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧ 
  na' = na + 4* len``,
  Induct>>
  fs[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  rw[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>fs[]>>
  res_tac>>cheat) (*Should be easy with some decision tacs*)
 
val list_next_var_rename_lemma_2 = prove(``
  ∀ls ssa na.
  ALL_DISTINCT ls ⇒ 
  let (ls',ssa',na') = list_next_var_rename ls ssa na in 
  ls' = MAP (λx. THE(lookup x ssa')) ls ∧ 
  domain ssa' = domain ssa ∪ set ls ∧ 
  ∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa``,
  Induct>>fs[list_next_var_rename_def,LET_THM,next_var_rename_def]>>
  rw[]>>
  first_x_assum(qspecl_then[`insert h na ssa`,`na+4`] assume_tac)>>
  rfs[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>Cases_on`r`>>
  fs[lookup_insert,EXTENSION]>>rw[]>>
  metis_tac[])

(*Try proof with oracle
  The proof of na,ns maintainance should be pulled out
*)

val exists_tac = qexists_tac`cst.permute`>>
    fs[wEval_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];

val ssa_locals_rel_get_var = prove(``
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x``,
  fs[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  rw[]>>
  FULL_CASE_TAC>>fs[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rfs[])

val ssa_locals_rel_get_vars = prove(``
  ∀ls y na ssa st cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y``,
  Induct>>fs[get_vars_def]>>rw[]>>
  Cases_on`get_var h st`>>fs[]>>
  imp_res_tac ssa_locals_rel_get_var>>fs[]>>
  Cases_on`get_vars ls st`>>fs[]>>
  res_tac>>fs[])

val ALOOKUP_ZIP_FAIL = prove(``
  ∀A B x.
  LENGTH A = LENGTH B ⇒  
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)``,
  rw[]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  fs[MAP_ZIP])

val ssa_map_bounded_extend = prove(``
  ssa_map_bounded na ssa ∧ 
  is_alloc_var na ⇒  
  ssa_map_bounded (na+4) (insert h na ssa)``,
  fs[ssa_map_bounded_def]>>
  rw[]>>fs[lookup_insert]>>
  Cases_on`x=h`>>fs[]>>
  res_tac>>
  DECIDE_TAC)

val merge_moves_frame = prove(``
  ∀ls na ssaL ssaR.
  is_alloc_var na 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧  
  (ssa_map_bounded na ssaL ⇒ ssa_map_bounded na' ssaL') ∧ 
  (ssa_map_bounded na ssaR ⇒ ssa_map_bounded na' ssaR')``,
  Induct>>fs[merge_moves_def]>-
    (rw[]>>fs[])
  >>
  rpt strip_tac>>
  fs[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rfs[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rfs[]>>
  EVERY_CASE_TAC>>fs[]>>
  (CONJ_TAC>-
    (fs[is_alloc_var_def]>>
    (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>fs[]>>
    pop_assum (qspecl_then [`r1`,`4`] assume_tac)>>
    rfs[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_bounded_extend])

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the 3 cases are basically copy pasted... *)

val merge_moves_correctL = prove(``
  ∀ls na ssaL ssaR stL cstL.
  is_alloc_var na ∧ 
  ssa_map_bounded na ssaL 
  ⇒ 
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒ 
  let (resL,rcstL) = wEval(moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧ 
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧ 
    word_state_eq_rel cstL rcstL)``,
  Induct>>fs[merge_moves_def]>-
  (rw[]>>
  fs[wEval_def,word_state_eq_rel_def]>>
  rfs[])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`]mp_tac)>>
  discharge_hyps>-
    (rfs[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rfs[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  strip_tac>>fs[]>>
  Cases_on`wEval(q,cstL)`>>fs[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  rfs[LET_THM]
  >-
    (fs[wEval_def,get_vars_def,LET_THM]>>
    fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,get_var_def,set_vars_def,list_insert_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h r2 = SOME v''` SUBST_ALL_TAC>>
      fs[]>>
      rfs[])
      >>
      res_tac>>fs[]>>
      `v'' < r1` by 
        (fs[ssa_map_bounded_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def])
  >-
    (fs[wEval_def,get_vars_def,LET_THM,fake_move_def,word_exp_def]>>
    fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,get_var_def,set_var_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x'=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h r2 = SOME v''` SUBST_ALL_TAC>>
      fs[]>>
      rfs[])
      >>
      res_tac>>fs[]>>
      `v' < r1` by 
        (fs[ssa_map_bounded_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def])
  >>
    (fs[wEval_def,get_vars_def,LET_THM,fake_move_def,word_exp_def]>>
    fs[ssa_locals_rel_def]>>
    res_tac>>
    fs[domain_lookup,get_var_def,set_vars_def,list_insert_def]>>
    rw[]>>fs[lookup_insert]
    >-
      (`x'' ≠ r1` by DECIDE_TAC>>
      fs[lookup_insert])
    >-
      (IF_CASES_TAC>>fs[]>>
      Cases_on`x''=h`>>fs[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>fs[]>-
      (res_tac>>fs[]>>
      qpat_assum`lookup h r2 = SOME v''` SUBST_ALL_TAC>>
      fs[]>>
      rfs[])
      >>
      res_tac>>fs[]>>
      `v'' < r1` by 
        (fs[ssa_map_bounded_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      fs[])
    >-
      (res_tac>> 
      DECIDE_TAC)
    >>
      fs[word_state_eq_rel_def]))

val ssa_locals_rel_more = prove(``
  ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒ 
  ssa_locals_rel na' ssa stlocs cstlocs``,
  rw[ssa_locals_rel_def]>>fs[]
  >- metis_tac[]>>
  res_tac>>fs[]>>
  DECIDE_TAC)

val ssa_cc_trans_correct = store_thm("ssa_cc_trans_correct",
``∀prog st cst ssa na ns.
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  (*The following 3 assumptions have to be proved to hold
    separately for the conclusion
    also, na ≤ na' for the every_var to hold  
  *)
  is_alloc_var na ∧
  every_var (λx. x < na) prog ∧
  (*This might be a bit strong*)
  (∀x y. lookup x ssa = SOME y ⇒ is_alloc_var y ∧ y < na) 
  (*is_stack_var ns  -- probably not needed*)
  ⇒
  ∃perm'.
  let (res,rst) = wEval(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (prog',ssa',na',ns') = ssa_cc_trans prog ssa na ns in
  let (res',rcst) = wEval(prog',cst) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧ 
    (case res of
      NONE => 
        ssa_locals_rel na' ssa' rst.locals rcst.locals 
    | _    => T )``,
  completeInduct_on`word_prog_size (K 0) prog`>>
  rpt strip_tac>>
  fs[PULL_FORALL,wEval_def]>>
  Cases_on`prog`
  >-
    exists_tac
  >-
    (exists_tac>>EVERY_CASE_TAC>>fs[set_vars_def]>>
    Cases_on`list_next_var_rename (MAP FST l) ssa na`>>
    Cases_on`r`>>
    fs[wEval_def]>>
    imp_res_tac list_next_var_rename_lemma_1>>
    imp_res_tac list_next_var_rename_lemma_2>>
    fs[LET_THM]>>
    fs[MAP_ZIP,LENGTH_COUNT_LIST]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    pop_assum(qspecl_then[`ssa`,`na`,`cst`] assume_tac)>>
    rfs[set_vars_def]>>
    fs[ssa_locals_rel_def]>>
    first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
    rfs[]>>
    imp_res_tac get_vars_length_lemma>>
    CONJ_ASM1_TAC
    >-
      (rw[domain_lookup]>>
      fs[lookup_list_insert]>>
      EVERY_CASE_TAC>>
      rfs[ALOOKUP_NONE,MAP_ZIP]>>
      `¬ (MEM x' (MAP FST l))` by
        (CCONTR_TAC>>
        fs[MEM_MAP]>>
        first_x_assum(qspec_then`x'` assume_tac)>>
        rfs[]>>
        metis_tac[])>>
      `x' ∈ domain q' ∧ x' ∈ domain ssa` by
        (CONJ_ASM1_TAC>-
          fs[domain_lookup]
        >>
        fs[EXTENSION]>>metis_tac[])>>
      metis_tac[domain_lookup])
    >> 
    fs[strong_locals_rel_def]>>rw[]>>rfs[lookup_list_insert]
    >-
      (Cases_on`MEM x' (MAP FST l)`>>
      fs[]>>
      Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
      rfs[]>>fs[])
    >-
      (Cases_on`MEM x' (MAP FST l)`>>
      fs[]
      >-
        cheat (*via some ALOOKUP ALL_DISTINCT and key remap
                reasoning on 25*)
      >>
      Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
      rfs[]>>fs[]>>
      res_tac>>
      fs[domain_lookup]>>res_tac>>
      cheat) (*v cannot be in the first part of the ZIP*)
    >>
      EVERY_CASE_TAC>>rfs[every_var_def]
      >-
        metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
      >>
        `MEM x' (MAP FST l)` by cheat>>
        fs[EVERY_MEM]>>
        metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``])
  >-(*Inst*) cheat
  >-(*Assign*)
    (exists_tac>>cheat)
  >-(*Get -- Useful for illustrating the need for
    the various assumptions on na*) 
    (exists_tac>>EVERY_CASE_TAC>>
    fs[next_var_rename_def,wEval_def]>>
    fs[set_var_def,ssa_locals_rel_def]>>
    rw[]>>fs[lookup_insert]>>Cases_on`x'=n`>>fs[]
    >-
      metis_tac[]
    >-
      (res_tac>>
      fs[domain_lookup]>>
      first_x_assum(qspecl_then[`x'`,`v`]assume_tac)>>
      (*Next part is a key reasoning step --
        We only have alloc_vars < na in the range of ssa
        Otherwise, the new one may overwrite an old mapping
      *)
      rfs[]>>
      `v ≠ na` by DECIDE_TAC >>
      fs[])
    >-
      (*This illustrates need for every_var assumption*)
      (fs[every_var_def]>>DECIDE_TAC)
    >>
      (*Finally, this illustrates need for <na assumption on st.locals*)
      res_tac>>fs[]>>DECIDE_TAC)
  >-(*Set*)
    (exists_tac>>cheat)
  >- (*Store*)
    cheat
  >- (*Call*)
    cheat
  >- (*Seq*)
    (rw[]>>fs[wEval_def,ssa_cc_trans_def,LET_THM]>>
    last_assum(qspecl_then[`w`,`st`,`cst`,`ssa`,`na`,`ns`] mp_tac)>>
    rfs[every_var_def]>>
    size_tac>>discharge_hyps>>fs[]>>rw[]>>
    Cases_on`ssa_cc_trans w ssa na ns`>>Cases_on`r`>>fs[]>>
    Cases_on`r'`>>Cases_on`ssa_cc_trans w0 q' q'' r`>>fs[]>>
    PairCases_on`r'`>>fs[wEval_def,LET_THM]>>
    Cases_on`wEval(w,st with permute:=perm')`>>fs[]
    >- (qexists_tac`perm'`>>fs[]) >>
    Cases_on`wEval(q,cst)`>>fs[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>rw[]>>fs[])
    >>
    fs[]>>
    first_assum(qspecl_then[`w0`,`r'`,`r''`,`q'`,`q''`,`r`] mp_tac)>>
    size_tac>>
    discharge_hyps>-
      (rfs[]>>cheat)>> (*prove this separately I think*)
    rw[]>>
    qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[])
  >- (*If -- hard*)
   (fs[wEval_def,coloring_ok_def,LET_THM,ssa_cc_trans_def]>>
    last_assum(qspecl_then[`w`,`st`,`cst`,`ssa`,`na`,`ns`] mp_tac)>>
    size_tac>>discharge_hyps>>fs[every_var_def]>>
    fs[]>>rw[]>>
    Cases_on`ssa_cc_trans w ssa na ns`>>PairCases_on`r`>>fs[]>>
    Cases_on`ssa_cc_trans w0 r0 r1 r2`>>PairCases_on`r`>>fs[]>>
    Cases_on`ssa_cc_trans w1 r0 r1' r2'`>>PairCases_on`r`>>fs[]>>
    Cases_on`fix_inconsistencies r0' r0'' r1''`>>PairCases_on`r`>>fs[]>>
    Cases_on`wEval(w,st with permute:=perm')`>>fs[wEval_def]
    >- (qexists_tac`perm'`>>fs[])>>
    Cases_on`wEval(q,cst)`>>fs[]>>
    reverse (Cases_on`q'''''`)>>fs[]
    >-
      (qexists_tac`perm'`>>rw[])
    >>
    Cases_on`get_var n r`>>fs[]
    >-
      (qexists_tac`perm'`>>rw[])
    >>
    rfs[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    reverse (Cases_on`x`)
    >-
      (qexists_tac`perm'`>>rw[])
    >>
    reverse (Cases_on`c = 0w`)>>fs[]
    >-
      (first_assum(qspecl_then[`w0`,`r`,`r'`,`r0`,`r1`,`r2`] mp_tac)>>
      size_tac>>
      discharge_hyps>-
        (rfs[]>>
        `na ≤ r1 ∧ r1 ≤ r1' ∧ is_alloc_var r1' ∧ is_alloc_var r1` by cheat>>
        fs[ssa_locals_rel_def]>>rw[]>>
        TRY( res_tac>>DECIDE_TAC)
        >-
          (match_mp_tac every_var_mono>>
          qexists_tac`λx.x<na`>>fs[]>>
          DECIDE_TAC)
        >>
          cheat) (*should be proven as side conditions*)
      >>
      rw[]>>
      qspecl_then[`w`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      qexists_tac`perm'''`>>rw[get_var_perm]>>fs[]>>
      (*Start reasoning about fix_inconsistencies*)
      Cases_on`wEval(w0,r with permute:= perm'')`>>rw[]>>
      reverse (Cases_on`q''''`)>-
        (Cases_on`x`>>fs[]>>
        qpat_assum`A = res'` (SUBST_ALL_TAC o SYM)>>fs[])>>
      fs[]>>
      fs[fix_inconsistencies_def,LET_THM]>>
      qabbrev_tac`ls = MAP FST (toAList (union r0' r0''))`>>
      Cases_on`merge_moves ls r0' r0'' r1''`>>
      PairCases_on`r'''`>>
      rfs[]>>
      Q.SPECL_THEN [`ls`,`r1''`,`r0'`,`r0''`,`r''`,`s1`] mp_tac 
        merge_moves_correctL>>
      discharge_hyps>-
        cheat (*separate proof*)
      >>
      fs[LET_THM]>>
      discharge_hyps>-
        (`r1' ≤ r1''` by cheat>>
        metis_tac[ssa_locals_rel_more])
      >>
      Cases_on`wEval(q''',s1)`>>fs[word_state_eq_rel_def])
    >>
    cheat)
   (* *) 
 
  >- (*Alloc*)
    (fs[ssa_cc_trans_def,LET_THM]>>cheat)
  >>
    cheat)

val _ = export_theory();