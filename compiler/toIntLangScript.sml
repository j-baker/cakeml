(*Generated by Lem from toIntLang.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory intLangTheory astTheory conLangTheory patLangTheory;

val _ = numLib.prefer_num();



val _ = new_theory "toIntLang"

(* Translation from IL4 to Intermediate Language *)
(*open import Pervasives*)

(*open import Lib*)
(*open import IntLang*)
(*open import Ast*)
(*open import ConLang*)
(*open import PatLang*)

 val free_vars_defn = Hol_defn "free_vars" `

(free_vars (CRaise e) = (free_vars e))
/\
(free_vars (CHandle e1 e2) = (lunion (free_vars e1) (lshift( 1) (free_vars e2))))
/\
(free_vars (CVar n) = ([n]))
/\
(free_vars (CGvar _) = ([]))
/\
(free_vars (CLit _) = ([]))
/\
(free_vars (CCon _ es) = (free_vars_list es))
/\
(free_vars (CLet bd e eb) = (lunion (free_vars e) (if bd then lshift( 1) (free_vars eb) else free_vars eb)))
/\
(free_vars (CLetrec defs e) =  
(let n = (LENGTH defs) in
  lunion (free_vars_defs n defs) (lshift n (free_vars e))))
/\
(free_vars (CCall _ e es) = (lunion (free_vars e) (free_vars_list es)))
/\
(free_vars (CPrim1 _ e) = (free_vars e))
/\
(free_vars (CPrim2 _ e1 e2) = (lunion (free_vars e1) (free_vars e2)))
/\
(free_vars (CUpd _ e1 e2 e3) = (lunion (free_vars e1) (lunion (free_vars e2) (free_vars e3))))
/\
(free_vars (CIf e1 e2 e3) = (lunion (free_vars e1) (lunion (free_vars e2) (free_vars e3))))
/\
(free_vars (CExtG _) = ([]))
/\
(free_vars_list [] = ([]))
/\
(free_vars_list (e::es) = (lunion (free_vars e) (free_vars_list es)))
/\
(free_vars_defs _ [] = ([]))
/\
(free_vars_defs n (d::ds) = (lunion (free_vars_def n d) (free_vars_defs n ds)))
/\
(free_vars_def n (NONE,(k,e)) = (lshift (n+k) (free_vars e)))
/\
(free_vars_def _ (SOME _,_) = ([]))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn free_vars_defn;

 val mkshift_defn = Hol_defn "mkshift" `

(mkshift f k (CRaise e) = (CRaise (mkshift f k e)))
/\
(mkshift f k (CHandle e1 e2) = (CHandle (mkshift f k e1) (mkshift f (k+ 1) e2)))
/\
(mkshift f k (CVar v) = (CVar (if v < k then v else (f (v - k))+k)))
/\
(mkshift _ _ (CGvar v) = (CGvar v))
/\
(mkshift _ _ (CLit l) = (CLit l))
/\
(mkshift f k (CCon cn es) = (CCon cn (MAP (mkshift f k) es)))
/\
(mkshift f k (CLet bd e b) = (CLet bd (mkshift f k e) (mkshift f (if bd then k+ 1 else k) b)))
/\
(mkshift f k (CLetrec defs b) =  
(let ns = (LENGTH defs) in
  let defs = (MAP (\ cb . 
    (case cb of   (SOME _,_) => cb | (NONE,(az,b)) => (NONE,(az,mkshift f ((k+ns)+az) b)) ))
    defs) in
  CLetrec defs (mkshift f (k+ns) b)))
/\
(mkshift f k (CCall ck e es) = (CCall ck (mkshift f k e) (MAP (mkshift f k) es)))
/\
(mkshift f k (CPrim1 p1 e) = (CPrim1 p1 (mkshift f k e)))
/\
(mkshift f k (CPrim2 p2 e1 e2) = (CPrim2 p2 (mkshift f k e1) (mkshift f k e2)))
/\
(mkshift f k (CUpd b e1 e2 e3) = (CUpd b (mkshift f k e1) (mkshift f k e2) (mkshift f k e3)))
/\
(mkshift f k (CIf e1 e2 e3) = (CIf (mkshift f k e1) (mkshift f k e2) (mkshift f k e3)))
/\
(mkshift _ _ (CExtG n) = (CExtG n))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn mkshift_defn;

val _ = Define `
 (shift n = (mkshift (\ v .  v+n)))`;


 val _ = Define `

(opn_to_prim2 Plus = (INL (P2p CAdd)))
/\
(opn_to_prim2 Minus = (INL (P2p CSub)))
/\
(opn_to_prim2 Times = (INL (P2p CMul)))
/\
(opn_to_prim2 Divide = (INR (P2p CDiv)))
/\
(opn_to_prim2 Modulo = (INR (P2p CMod)))`;


 val _ = Define `

(binop_to_il (Opn opn) Ce1 Ce2 =  
((case opn_to_prim2 opn of
    INL p2 => CPrim2 p2 Ce1 Ce2
  | INR p2 =>
    CLet T Ce1
      (CLet T (shift( 1)( 0) Ce2)
        (CIf (CPrim2 (P2p CEq) (CVar( 0)) (CLit (IntLit(( 0 : int)))))
             (CRaise (CCon div_tag []))
             (CPrim2 p2 (CVar( 1)) (CVar( 0)))))
  )))
/\
(binop_to_il (Opb opb) Ce1 Ce2 =  
((case opb of
    Lt => CPrim2 (P2p CLt) Ce1 Ce2
  | Leq => CPrim2 (P2p CLt) (CPrim2 (P2p CSub) Ce1 Ce2) (CLit (IntLit(( 1 : int))))
  | opb =>
      CLet T Ce1 (
        CLet T (shift( 1)( 0) Ce2) (
          (case opb of
            Gt =>  CPrim2 (P2p CLt) (CVar( 0)) (CVar( 1))
          | Geq => CPrim2 (P2p CLt) (CPrim2 (P2p CSub) (CVar( 0)) (CVar( 1))) (CLit (IntLit(( 1 : int))))
          | _ => CLit (IntLit(( 0 : int))) (* should not happen *)
          )))
  )))
/\
(binop_to_il (Chopb opb) Ce1 Ce2 =  
(CLet T Ce1 (
    CLet T (shift( 1)( 0) Ce2) (
      let Ce1 = (CPrim1 COrd (CVar( 1))) in
      let Ce2 = (CPrim1 COrd (CVar( 0))) in
      (case opb of
        Lt => CPrim2 (P2p CLt) Ce1 Ce2
      | Leq => CPrim2 (P2p CLt) (CPrim2 (P2p CSub) Ce1 Ce2) (CLit (IntLit(( 1 : int))))
      | Gt =>  CPrim2 (P2p CLt) Ce2 Ce1
      | Geq => CPrim2 (P2p CLt) (CPrim2 (P2p CSub) Ce2 Ce1) (CLit (IntLit(( 1 : int))))
      )))))
/\
(binop_to_il Equality Ce1 Ce2 =  
(CLet T (CPrim2 (P2p CEq) Ce1 Ce2)
    (CIf (CPrim1 CIsBlock (CVar( 0))) (CVar( 0)) (CRaise (CCon eq_tag [])))))
/\
(binop_to_il Opapp Ce1 Ce2 =  
(CCall T Ce1 [Ce2]))
/\
(binop_to_il Opassign Ce1 Ce2 =  
(CUpd Up1 Ce1 (CLit (IntLit(( 0 : int)))) Ce2))
/\
(binop_to_il Aw8alloc Ce1 Ce2 =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CLit (IntLit(( 0 : int)))))
           (CRaise (CCon subscript_tag []))
           (CPrim2 (P2s CRefB) (CVar( 0)) (CVar( 1)))))))
/\
(binop_to_il Aalloc Ce1 Ce2 =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CLit (IntLit(( 0 : int)))))
           (CRaise (CCon subscript_tag []))
           (CPrim2 (P2s CRefA) (CVar( 0)) (CVar( 1)))))))
/\
(binop_to_il Aw8sub Ce1 Ce2 =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CLit (IntLit(( 0 : int)))))
           (CRaise (CCon subscript_tag []))
           (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CPrim1 CLenB (CVar( 1))))
                (CPrim2 (P2s CDerB) (CVar( 1)) (CVar( 0)))
                (CRaise (CCon subscript_tag [])))))))
/\
(binop_to_il Vsub Ce1 Ce2 =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CLit (IntLit(( 0 : int)))))
           (CRaise (CCon subscript_tag []))
           (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CPrim1 CLenV (CVar( 1))))
                (CPrim2 (P2p CDerV) (CVar( 1)) (CVar( 0)))
                (CRaise (CCon subscript_tag [])))))))
/\
(binop_to_il Asub Ce1 Ce2 =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CLit (IntLit(( 0 : int)))))
           (CRaise (CCon subscript_tag []))
           (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CPrim1 CLen (CVar( 1))))
                (CPrim2 (P2s CDerA) (CVar( 1)) (CVar( 0)))
                (CRaise (CCon subscript_tag [])))))))
/\
(binop_to_il Aw8length Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Vlength   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Alength   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Aw8update Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Aupdate   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Opref     Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Opderef   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Chr       Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Ord       Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Explode   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Implode   Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il Strlen    Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2])) (* should not happen *)
/\
(binop_to_il VfromList Ce1 Ce2 = (CCon tuple_tag [Ce1;Ce2]))`;
 (* should not happen *)

 val _ = Define `

(unop_to_il Opref Ce = (CPrim1 CRef Ce))
/\
(unop_to_il Opderef Ce = (CPrim1 CDer Ce))
/\
(unop_to_il Aw8length Ce = (CPrim1 CLenB Ce))
/\
(unop_to_il Vlength Ce = (CPrim1 CLenV Ce))
/\
(unop_to_il Alength Ce = (CPrim1 CLen Ce))
/\
(unop_to_il Strlen Ce  = (CPrim1 CLenS Ce))
/\
(unop_to_il Chr Ce =  
(CLet T Ce
    (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CLit (IntLit(( 0 : int)))))
         (CRaise (CCon chr_tag []))
         (CIf (CPrim2 (P2p CLt) (CVar( 0)) (CLit (IntLit(( 256 : int)))))
              (CPrim1 CChr (CVar( 0)))
              (CRaise (CCon chr_tag []))))))
/\
(unop_to_il Ord       Ce = (CPrim1 COrd Ce))
/\
(unop_to_il Explode   Ce = (CPrim1 CExplode Ce))
/\
(unop_to_il Implode   Ce = (CPrim1 CImplode Ce))
/\
(unop_to_il VfromList Ce = (CPrim1 CVfromList Ce))
/\
(unop_to_il (Opn _)   Ce = Ce) (* should not happen *)
/\
(unop_to_il (Opb _)   Ce = Ce) (* should not happen *)
/\
(unop_to_il (Chopb _) Ce = Ce) (* should not happen *)
/\
(unop_to_il Equality  Ce = Ce) (* should not happen *)
/\
(unop_to_il Opapp     Ce = Ce) (* should not happen *)
/\
(unop_to_il Opassign  Ce = Ce) (* should not happen *)
/\
(unop_to_il Aw8alloc  Ce = Ce) (* should not happen *)
/\
(unop_to_il Aw8sub    Ce = Ce) (* should not happen *)
/\
(unop_to_il Vsub      Ce = Ce) (* should not happen *)
/\
(unop_to_il Aw8update Ce = Ce) (* should not happen *)
/\
(unop_to_il Aalloc    Ce = Ce) (* should not happen *)
/\
(unop_to_il Asub      Ce = Ce) (* should not happen *)
/\
(unop_to_il Aupdate   Ce = Ce)`;
 (* should not happen *)

 val _ = Define `

(app_to_il (Op_pat (Op_i2 Aw8update)) [Ce1; Ce2; Ce3] =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CLet T (shift( 2)( 0) Ce3)
        (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CLit (IntLit(( 0 : int)))))
             (CRaise (CCon subscript_tag []))
             (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CPrim1 CLenB (CVar( 2))))
                  (CUpd UpB (CVar( 2)) (CVar( 1)) (CVar( 0)))
                  (CRaise (CCon subscript_tag []))))))))
/\
(app_to_il (Op_pat (Op_i2 Aupdate)) [Ce1; Ce2; Ce3] =  
(CLet T Ce1
    (CLet T (shift( 1)( 0) Ce2)
      (CLet T (shift( 2)( 0) Ce3)
        (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CLit (IntLit(( 0 : int)))))
             (CRaise (CCon subscript_tag []))
             (CIf (CPrim2 (P2p CLt) (CVar( 1)) (CPrim1 CLen (CVar( 2))))
                  (CUpd UpA (CVar( 2)) (CVar( 1)) (CVar( 0)))
                  (CRaise (CCon subscript_tag []))))))))
/\
(app_to_il (Op_pat (Op_i2 op)) [Ce1; Ce2] =  
(binop_to_il op Ce1 Ce2))
/\
(app_to_il (Op_pat (Op_i2 op)) [Ce] =  
(unop_to_il op Ce))
/\
(app_to_il (Op_pat (Init_global_var_i2 n)) [Ce] =  
(CPrim1 (CInitG n) Ce))
/\
(app_to_il (Tag_eq_pat n) [Ce] =  
(CPrim1 (CTagEq n) Ce))
/\
(app_to_il (El_pat n) [Ce] =  
(CPrim1 (CProj n) Ce))
/\
(app_to_il (Op_pat (Init_global_var_i2 _)) l = (CCon tuple_tag l)) (* should not happen *)
/\
(app_to_il (Tag_eq_pat _ ) l = (CCon tuple_tag l)) (* should not happen *)
/\
(app_to_il (El_pat _ )     l = (CCon tuple_tag l)) (* should not happen *)
/\
(app_to_il _               l = (CCon tuple_tag l))`;
 (* should not happen *)

 val _ = Define `

(exp_to_Cexp (Handle_pat e1 e2) =  
(CHandle (exp_to_Cexp e1) (exp_to_Cexp e2)))
/\
(exp_to_Cexp (Raise_pat e) = (CRaise (exp_to_Cexp e)))
/\
(exp_to_Cexp (Lit_pat l) = (CLit l))
/\
(exp_to_Cexp (Con_pat cn es) =  
(CCon cn (exps_to_Cexps es)))
/\
(exp_to_Cexp (Var_local_pat vn) = (CVar vn))
/\
(exp_to_Cexp (Var_global_pat vn) = (CGvar vn))
/\
(exp_to_Cexp (Fun_pat e) =  
(CLetrec [(NONE,( 1,shift( 1)( 1) (exp_to_Cexp e)))] (CVar( 0))))
/\
(exp_to_Cexp (App_pat op es) =  
(app_to_il op (exps_to_Cexps es)))
/\
(exp_to_Cexp (If_pat e1 e2 e3) =  
(let Ce1 = (exp_to_Cexp e1) in
  let Ce2 = (exp_to_Cexp e2) in
  let Ce3 = (exp_to_Cexp e3) in
  CIf Ce1 Ce2 Ce3))
/\
(exp_to_Cexp (Let_pat e b) =  
(let Ce = (exp_to_Cexp e) in
  let Cb = (exp_to_Cexp b) in
  CLet T Ce Cb))
/\
(exp_to_Cexp (Seq_pat e b) =  
(let Ce = (exp_to_Cexp e) in
  let Cb = (exp_to_Cexp b) in
  CLet F Ce Cb))
/\
(exp_to_Cexp (Letrec_pat defs b) =  
(CLetrec (MAP (\ e .  (NONE,( 1,e))) (exps_to_Cexps defs)) (exp_to_Cexp b)))
/\
(exp_to_Cexp (Extend_global_pat n) = (CExtG n))
/\
(exps_to_Cexps [] = ([]))
/\
(exps_to_Cexps (e::es) =  
(exp_to_Cexp e :: exps_to_Cexps es))`;


(* source to intermediate values *)

 val v_to_Cv_defn = Hol_defn "v_to_Cv" `

(v_to_Cv (Litv_pat l) = (CLitv l))
/\
(v_to_Cv (Conv_pat cn vs) =  
(CConv cn (vs_to_Cvs vs)))
/\
(v_to_Cv (Closure_pat env e) =  
(let Cenv = (vs_to_Cvs env) in
  let Ce = (exp_to_Cexp e) in
  CRecClos Cenv [(NONE, ( 1,shift( 1)( 1) Ce))]( 0)))
/\
(v_to_Cv (Recclosure_pat env defs vn) =  
(let Cenv = (vs_to_Cvs env) in
  let Cdefs = (MAP (\ e .  (NONE,( 1,e))) (exps_to_Cexps defs)) in
  CRecClos Cenv Cdefs vn))
/\
(v_to_Cv (Loc_pat n) = (CLoc n))
/\
(v_to_Cv (Vectorv_pat vs) = (CVectorv (vs_to_Cvs vs)))
/\
(vs_to_Cvs [] = ([]))
/\
(vs_to_Cvs (v::vs) = (v_to_Cv v :: vs_to_Cvs vs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn v_to_Cv_defn;
val _ = export_theory()

