(*Generated by Lem from mtiLang.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory semanticPrimitivesTheory astTheory bigStepTheory exhLangTheory conLangTheory decLangTheory patLangTheory;

val _ = numLib.prefer_num();



val _ = new_theory "mtiLang"

(* Introduces multi-argument functions *)

(*open import Pervasives*)
(*open import SemanticPrimitives*)
(*open import Ast*)
(*open import BigStep*)
(*open import ExhLang*)
(*open import ConLang*)
(*open import DecLang*)
(*open import PatLang*)

val _ = Hol_datatype `
 exp_mti =
    Raise_mti of exp_mti
  | Handle_mti of exp_mti => exp_mti
  | Lit_mti of lit
  | Con_mti of num => exp_mti list
  | Var_local_mti of num
  | Var_global_mti of num
  | Fun_mti of num => exp_mti
  | App_mti of op_pat => exp_mti list
  | If_mti of exp_mti => exp_mti => exp_mti
  | Let_mti of exp_mti => exp_mti
  | Seq_mti of exp_mti => exp_mti
  | Letrec_mti of (num # exp_mti) list => exp_mti
  | Extend_global_mti of num`;


val _ = Hol_datatype `
 v_mti =
    Litv_mti of lit
  | Conv_mti of num => v_mti list
  | Closure_mti of v_mti list => num => exp_mti
    (* The first v list is the partially applied arguments, 
       the second is the closure for the whole letrec *)
  | Recclosure_mti of v_mti list => v_mti list => (num # exp_mti) list => num
  | Loc_mti of num
  | Vectorv_mti of v_mti list`;


(*val collect_funs : nat -> exp_pat -> nat * exp_pat*)
 val _ = Define `
 
(collect_funs n (Fun_pat e) =  
(collect_funs (n + 1) e))
/\
(collect_funs n e =
  (n,e))`;


(*val collect_apps : list exp_pat -> list exp_pat*)
 val collect_apps_defn = Hol_defn "collect_apps" `
 (collect_apps [(App_pat (Op_pat (Op_i2 Opapp)) es); e2] =  
(e2 :: collect_apps es))
/\
(collect_apps es = es)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn collect_apps_defn;

(*val pat_to_mti : exp_pat -> exp_mti*)
 val pat_to_mti_defn = Hol_defn "pat_to_mti" `
 
(pat_to_mti (Raise_pat e) = (Raise_mti (pat_to_mti e)))
/\ 
(pat_to_mti (Handle_pat e1 e2) = (Handle_mti (pat_to_mti e1) (pat_to_mti e2)))
/\
(pat_to_mti (Lit_pat l) = (Lit_mti l))
/\
(pat_to_mti (Con_pat n es) = (Con_mti n (MAP pat_to_mti es)))
/\
(pat_to_mti (Var_local_pat n) = (Var_local_mti n))
/\
(pat_to_mti (Var_global_pat n) = (Var_global_mti n))
/\
(pat_to_mti (Fun_pat e) =  
 (let (n,e) = (collect_funs( 1) e) in
    Fun_mti n (pat_to_mti e)))
/\
(pat_to_mti (App_pat (Op_pat (Op_i2 Opapp)) es) =  
 (let es = (collect_apps es) in
    App_mti (Op_pat (Op_i2 Opapp)) (MAP pat_to_mti es)))
/\
(pat_to_mti (App_pat op es) = (App_mti op (MAP pat_to_mti es)))
/\
(pat_to_mti (If_pat e1 e2 e3) =  
 (If_mti (pat_to_mti e1) (pat_to_mti e2) (pat_to_mti e3)))
/\
(pat_to_mti (Seq_pat e1 e2) =  
 (Seq_mti (pat_to_mti e1) (pat_to_mti e2)))
/\
(pat_to_mti (Letrec_pat funs e) =  
(Letrec_mti (MAP (\ e .  ( 1, pat_to_mti e)) funs) (pat_to_mti e)))
/\
(pat_to_mti (Extend_global_pat n) = (Extend_global_mti n))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn pat_to_mti_defn;

(*val build_rec_env_mti : list (nat * exp_mti) -> list v_mti -> list v_mti*)
val _ = Define `
 (build_rec_env_mti funs cl_env =  
(GENLIST (Recclosure_mti [] cl_env funs) (LENGTH funs)))`;


val _ = Hol_datatype `
 app_res = 
    Exp_res of v_mti list => exp_mti
  | Val_res of v_mti`;


(*val do_opapp_mti : v_mti -> list v_mti -> maybe app_res*)
val _ = Define `
 (do_opapp_mti v args =  
((case v of
      Closure_mti env num_args e =>
        if LENGTH args = num_args then
          SOME (Exp_res (args ++ env) e)
        else if LENGTH args < num_args then
          SOME (Val_res (Closure_mti (args ++ env) (num_args - LENGTH args) e))
        else
          NONE
    | Recclosure_mti argenv recenv funs n =>
        if n < LENGTH funs then
          let (num_args, e) = (EL n funs) in
            if LENGTH args = num_args then
              SOME (Exp_res (((args ++ argenv) ++ build_rec_env_mti funs recenv) ++ recenv) e)
            else if LENGTH args < num_args then
              SOME (Val_res (Recclosure_mti (args ++ argenv) 
                            recenv  
                            (LUPDATE ((num_args - LENGTH args), e) n funs)
                            n))
            else
              NONE
        else
          NONE
    | _ => NONE
    )))`;


(*val do_eq_mti : v_mti -> v_mti -> eq_result*)
 val do_eq_mti_defn = Hol_defn "do_eq_mti" `

(do_eq_mti (Litv_mti l1) (Litv_mti l2) =  
(if lit_same_type l1 l2 then Eq_val (l1 = l2)
  else Eq_type_error))
/\
(do_eq_mti (Loc_mti l1) (Loc_mti l2) = (Eq_val (l1 = l2)))
/\
(do_eq_mti (Conv_mti tag1 vs1) (Conv_mti tag2 vs2) =  
(if (tag1 = tag2) /\ (LENGTH vs1 = LENGTH vs2) then
    do_eq_list_mti vs1 vs2
  else
    Eq_val F))
/\
(do_eq_mti (Vectorv_mti vs1) (Vectorv_mti vs2) =  
(if LENGTH vs1 = LENGTH vs2 then
    do_eq_list_mti vs1 vs2
  else
    Eq_val F))
/\
(do_eq_mti (Closure_mti _ _ _) (Closure_mti _ _ _) = Eq_closure)
/\
(do_eq_mti (Closure_mti _ _ _) (Recclosure_mti _ _ _ _) = Eq_closure)
/\
(do_eq_mti (Recclosure_mti _ _ _ _) (Closure_mti _ _ _) = Eq_closure)
/\
(do_eq_mti (Recclosure_mti _ _ _ _) (Recclosure_mti _ _ _ _) = Eq_closure)
/\
(do_eq_mti _ _ = Eq_type_error)
/\
(do_eq_list_mti [] [] = (Eq_val T))
/\
(do_eq_list_mti (v1::vs1) (v2::vs2) =  
((case do_eq_mti v1 v2 of
      Eq_closure => Eq_closure
    | Eq_type_error => Eq_type_error
    | Eq_val r =>
        if ~ r then
          Eq_val F
        else
          do_eq_list_mti vs1 vs2
  )))
/\
(do_eq_list_mti _ _ = (Eq_val F))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn do_eq_mti_defn;

(*val prim_exn_mti : nat -> v_mti*)
val _ = Define `
 (prim_exn_mti tag = (Conv_mti tag []))`;


(*val v_to_list_mti : v_mti -> maybe (list v_mti)*)
 val _ = Define `
 (v_to_list_mti (Conv_mti tag []) =  
 (if tag = nil_tag then
    SOME []
  else
    NONE))
/\ (v_to_list_mti (Conv_mti tag [v1;v2]) =  
(if tag = cons_tag  then
    (case v_to_list_mti v2 of
        SOME vs => SOME (v1::vs)
      | NONE => NONE
    )
  else
    NONE))
/\ (v_to_list_mti _ = NONE)`;


(*val v_mti_to_char_list : v_mti -> maybe (list char)*)
 val _ = Define `
 (v_mti_to_char_list (Conv_mti tag []) =  
(if tag = nil_tag then
    SOME []
  else
    NONE))
/\ (v_mti_to_char_list (Conv_mti tag [Litv_mti (Char c);v]) =  
(if tag = cons_tag then
    (case v_mti_to_char_list v of
        SOME cs => SOME (c::cs)
      | NONE => NONE
    )
  else
    NONE))
/\ (v_mti_to_char_list _ = NONE)`;


(*val char_list_to_v_mti : list char -> v_mti*)
 val char_list_to_v_mti_defn = Hol_defn "char_list_to_v_mti" `
 (char_list_to_v_mti [] = (Conv_mti nil_tag []))
/\ (char_list_to_v_mti (c::cs) =  
(Conv_mti cons_tag [Litv_mti (Char c); char_list_to_v_mti cs]))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn char_list_to_v_mti_defn;

(*val do_app_mti : count_store_genv v_mti -> op_pat -> list v_mti -> maybe (count_store_genv v_mti * result v_mti v_mti)*)
val _ = Define `
 (do_app_mti ((cnt,s),genv) op vs =  
((case (op,vs) of
      (Op_pat (Op_i2 (Opn op)), [Litv_mti (IntLit n1); Litv_mti (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti div_tag)))
        else
          SOME (((cnt,s),genv), Rval (Litv_mti (IntLit (opn_lookup op n1 n2))))
    | (Op_pat (Op_i2 (Opb op)), [Litv_mti (IntLit n1); Litv_mti (IntLit n2)]) =>
        SOME (((cnt,s),genv), Rval (Litv_mti (Bool (opb_lookup op n1 n2))))
    | (Op_pat (Op_i2 Equality), [v1; v2]) =>
        (case do_eq_mti v1 v2 of
            Eq_type_error => NONE
          | Eq_closure => SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti eq_tag)))
          | Eq_val b => SOME (((cnt,s),genv), Rval(Litv_mti (Bool b)))
        )
    | (Op_pat (Op_i2 Opassign), [Loc_mti lnum; v]) =>
        (case store_assign lnum (Refv v) s of
          SOME st => SOME (((cnt,st),genv), Rval (Litv_mti Unit))
        | NONE => NONE
        )
    | (Op_pat (Op_i2 Opderef), [Loc_mti n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME (((cnt,s),genv),Rval v)
          | _ => NONE
        )
    | (Op_pat (Op_i2 Opref), [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (((cnt,s'),genv), Rval (Loc_mti n))
    | (Op_pat (Init_global_var_i2 idx), [v]) =>
        if idx < LENGTH genv then
          (case EL idx genv of
              NONE => SOME (((cnt,s), LUPDATE (SOME v) idx genv), Rval (Litv_mti Unit))
            | SOME _ => NONE
          )
        else
          NONE
    | (Op_pat (Op_i2 Aw8alloc), [Litv_mti (IntLit n); Litv_mti (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
        else
          let (st,lnum) =            
(store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s)
          in
            SOME (((cnt,st),genv), Rval (Loc_mti lnum))
    | (Op_pat (Op_i2 Aw8sub), [Loc_mti lnum; Litv_mti (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH ws then
                    SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
                  else
                    SOME (((cnt,s),genv), Rval (Litv_mti (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Op_pat (Op_i2 Aw8length), [Loc_mti n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (((cnt,s),genv),Rval (Litv_mti (IntLit (int_of_num (LENGTH ws)))))
          | _ => NONE
        )
    | (Op_pat (Op_i2 Aw8update), [Loc_mti lnum; Litv_mti (IntLit i); Litv_mti (Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
            else
              let n = (Num (ABS ( i))) in
                if n >= LENGTH ws then
                  SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME st => SOME (((cnt,st),genv), Rval (Litv_mti Unit))
                  )
        | _ => NONE
        )
    | (Op_pat (Op_i2 Ord), [Litv_mti (Char c)]) =>
          SOME (((cnt,s),genv), Rval (Litv_mti(IntLit(int_of_num(ORD c)))))
    | (Op_pat (Op_i2 Chr), [Litv_mti (IntLit i)]) =>
        SOME (((cnt,s),genv),          
(if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rerr (Rraise (prim_exn_mti chr_tag))
          else
            Rval (Litv_mti(Char(CHR(Num (ABS ( i))))))))
    | (Op_pat (Op_i2 (Chopb op)), [Litv_mti (Char c1); Litv_mti (Char c2)]) =>
        SOME (((cnt,s),genv), Rval (Litv_mti (Bool (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2))))))
    | (Op_pat (Op_i2 Implode), [v]) =>
          (case v_mti_to_char_list v of
            SOME ls =>
              SOME (((cnt,s),genv), Rval (Litv_mti (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Op_pat (Op_i2 Explode), [Litv_mti (StrLit str)]) =>
        SOME (((cnt,s),genv), Rval (char_list_to_v_mti (EXPLODE str)))
    | (Op_pat (Op_i2 Strlen), [Litv_mti (StrLit str)]) =>
        SOME (((cnt,s),genv), Rval (Litv_mti(IntLit(int_of_num(STRLEN str)))))
    | (Op_pat (Op_i2 VfromList), [v]) =>
          (case v_to_list_mti v of
              SOME vs =>
                SOME (((cnt,s),genv), Rval (Vectorv_mti vs))
            | NONE => NONE
          )
    | (Op_pat (Op_i2 Vsub), [Vectorv_mti vs; Litv_mti (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
        else
          let n = (Num (ABS ( i))) in
            if n >= LENGTH vs then
              SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
            else 
              SOME (((cnt,s),genv), Rval (EL n vs))
    | (Op_pat (Op_i2 Vlength), [Vectorv_mti vs]) =>
        SOME (((cnt,s),genv), Rval (Litv_mti (IntLit (int_of_num (LENGTH vs)))))
    | (Op_pat (Op_i2 Aalloc), [Litv_mti (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
        else
          let (s',lnum) =            
(store_alloc (Varray (REPLICATE (Num (ABS ( n))) v)) s)
          in 
            SOME (((cnt,s'),genv), Rval (Loc_mti lnum))
    | (Op_pat (Op_i2 Asub), [Loc_mti lnum; Litv_mti (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH vs then
                    SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
                  else 
                    SOME (((cnt,s),genv), Rval (EL n vs))
          | _ => NONE
        )
    | (Op_pat (Op_i2 Alength), [Loc_mti n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (((cnt,s),genv),Rval (Litv_mti (IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Op_pat (Op_i2 Aupdate), [Loc_mti lnum; Litv_mti (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
            else 
              let n = (Num (ABS ( i))) in
                if n >= LENGTH vs then
                  SOME (((cnt,s),genv), Rerr (Rraise (prim_exn_mti subscript_tag)))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (((cnt,s'),genv), Rval (Litv_mti Unit))
                  )
        | _ => NONE
      )
    | (Tag_eq_pat n, [Conv_mti tag _]) =>
        SOME (((cnt,s),genv), Rval (Litv_mti (Bool (tag = n))))
    | (El_pat n, [Conv_mti _ vs]) =>
        if n < LENGTH vs then
          SOME (((cnt,s),genv), Rval (EL n vs))
        else
          NONE
    | _ => NONE
  )))`;


(*val do_if_mti : v_mti -> exp_mti -> exp_mti -> maybe exp_mti*)
val _ = Define `
 (do_if_mti v e1 e2 =  
(if v = Litv_mti (Bool T) then
    SOME e1
  else if v = Litv_mti (Bool F) then
    SOME e2
  else
    NONE))`;


(*val get_num_args : v_mti -> maybe nat*)
val _ = Define `
 (get_num_args v =  
((case v of
      Closure_mti _ n _ => SOME n
    | Recclosure_mti _ _ funs n => 
        if n < LENGTH funs then
          SOME (FST (EL n funs))
        else
          NONE
    | _ => NONE
  )))`;


val _ = Hol_reln ` (! ck env l s.

T
==>
evaluate_mti ck env s (Lit_mti l) (s, Rval (Litv_mti l)))

/\ (! ck env e s1 s2 v.
(evaluate_mti ck s1 env e (s2, Rval v))
==>
evaluate_mti ck s1 env (Raise_mti e) (s2, Rerr (Rraise v)))

/\ (! ck env e s1 s2 err.
(evaluate_mti ck s1 env e (s2, Rerr err))
==>
evaluate_mti ck s1 env (Raise_mti e) (s2, Rerr err))

/\ (! ck s1 s2 env e1 v e2.
(evaluate_mti ck s1 env e1 (s2, Rval v))
==>
evaluate_mti ck s1 env (Handle_mti e1 e2) (s2, Rval v))

/\ (! ck s1 s2 env e1 e2 v bv.
(evaluate_mti ck env s1 e1 (s2, Rerr (Rraise v)) /\
evaluate_mti ck (v::env) s2 e2 bv)
==>
evaluate_mti ck env s1 (Handle_mti e1 e2) bv)

/\ (! ck s1 s2 env e1 e2 err.
(evaluate_mti ck env s1 e1 (s2, Rerr err) /\
((err = Rtimeout_error) \/ (err = Rtype_error)))
==>
evaluate_mti ck env s1 (Handle_mti e1 e2) (s2, Rerr err))

/\ (! ck env tag es vs s s'.
(evaluate_list_mti ck env s es (s', Rval vs))
==>
evaluate_mti ck env s (Con_mti tag es) (s', Rval (Conv_mti tag vs)))

/\ (! ck env tag es err s s'.
(evaluate_list_mti ck env s es (s', Rerr err))
==>
evaluate_mti ck env s (Con_mti tag es) (s', Rerr err))

/\ (! ck env n s.
(LENGTH env > n)
==>
evaluate_mti ck env s (Var_local_mti n) (s, Rval (EL n env)))

/\ (! ck env n s.
(~ (LENGTH env > n))
==>
evaluate_mti ck env s (Var_local_mti n) (s, Rerr Rtype_error))

/\ (! ck env n v s genv.
((LENGTH genv > n) /\
(EL n genv = SOME v))
==>
evaluate_mti ck env (s,genv) (Var_global_mti n) ((s,genv), Rval v))

/\ (! ck env n s genv.
((LENGTH genv > n) /\
(EL n genv = NONE))
==>
evaluate_mti ck env (s,genv) (Var_global_mti n) ((s,genv), Rerr Rtype_error))

/\ (! ck env n s genv.
(~ (LENGTH genv > n))
==>
evaluate_mti ck env (s,genv) (Var_global_mti n) ((s,genv), Rerr Rtype_error))

/\ (! ck env n e s.
T
==>
evaluate_mti ck env s (Fun_mti n e) (s, Rval (Closure_mti env n e)))

/\ (! ck env s1 e s2 es bv v.
(evaluate_mti ck env s1 e (s2, Rval v) /\
evaluate_opapp_mti ck env s2 v es bv)
==>
evaluate_mti ck env s1 (App_mti (Op_pat (Op_i2 Opapp)) (e::es)) bv)

/\ (! ck env s1 op es s2 vs s3 res.
(evaluate_list_mti ck env s1 es (s2, Rval vs) /\
(do_app_mti s2 op vs = SOME (s3, res)) /\
(op <> Op_pat (Op_i2 Opapp)))
==>
evaluate_mti ck env s1 (App_mti op es) (s3, res))

/\ (! ck env s1 op es s2 vs.
(evaluate_list_mti ck env s1 es (s2, Rval vs) /\
(do_app_mti s2 op vs = NONE) /\
(op <> Op_pat (Op_i2 Opapp)))
==>
evaluate_mti ck env s1 (App_mti op es) (s2, Rerr Rtype_error))

/\ (! ck env s1 op es s2 err.
(evaluate_list_mti ck env s1 es (s2, Rerr err))
==>
evaluate_mti ck env s1 (App_mti op es) (s2, Rerr err))

/\ (! ck env e1 e2 e3 v e' bv s1 s2.
(evaluate_mti ck env s1 e1 (s2, Rval v) /\
(do_if_mti v e2 e3 = SOME e') /\
evaluate_mti ck env s2 e' bv)
==>
evaluate_mti ck env s1 (If_mti e1 e2 e3) bv)

/\ (! ck env e1 e2 e3 v s1 s2.
(evaluate_mti ck env s1 e1 (s2, Rval v) /\
(do_if_mti v e2 e3 = NONE))
==>
evaluate_mti ck env s1 (If_mti e1 e2 e3) (s2, Rerr Rtype_error))

/\ (! ck env e1 e2 e3 err s s'.
(evaluate_mti ck env s e1 (s', Rerr err))
==>
evaluate_mti ck env s (If_mti e1 e2 e3) (s', Rerr err))

/\ (! ck env e1 e2 v bv s1 s2.
(evaluate_mti ck env s1 e1 (s2, Rval v) /\
evaluate_mti ck (v::env) s2 e2 bv)
==>
evaluate_mti ck env s1 (Let_mti e1 e2) bv)

/\ (! ck env e1 e2 err s s'.
(evaluate_mti ck env s e1 (s', Rerr err))
==>
evaluate_mti ck env s (Let_mti e1 e2) (s', Rerr err))

/\ (! ck env e1 e2 v bv s1 s2.
(evaluate_mti ck env s1 e1 (s2, Rval v) /\
evaluate_mti ck env s2 e2 bv)
==>
evaluate_mti ck env s1 (Seq_mti e1 e2) bv)

/\ (! ck env e1 e2 err s s'.
(evaluate_mti ck env s e1 (s', Rerr err))
==>
evaluate_mti ck env s (Seq_mti e1 e2) (s', Rerr err))

/\ (! ck env funs e bv s.
(evaluate_mti ck ((build_rec_env_mti funs env)++env) s e bv)
==>
evaluate_mti ck env s (Letrec_mti funs e) bv)

/\ (! ck env n s genv.
T
==>
evaluate_mti ck env (s,genv) (Extend_global_mti n) ((s,(genv++GENLIST (\n .  
  (case (n ) of ( _ ) => NONE )) n)), Rval (Litv_mti Unit)))

/\ (! ck env s.
T
==>
evaluate_list_mti ck env s [] (s, Rval []))

/\ (! ck env e es v vs s1 s2 s3.
(evaluate_mti ck env s1 e (s2, Rval v) /\
evaluate_list_mti ck env s2 es (s3, Rval vs))
==>
evaluate_list_mti ck env s1 (e::es) (s3, Rval (v::vs)))

/\ (! ck env e es err s s'.
(evaluate_mti ck env s e (s', Rerr err))
==>
evaluate_list_mti ck env s (e::es) (s', Rerr err))

/\ (! ck env e es v err s1 s2 s3.
(evaluate_mti ck env s1 e (s2, Rval v) /\
evaluate_list_mti ck env s2 es (s3, Rerr err))
==>
evaluate_list_mti ck env s1 (e::es) (s3, Rerr err))

/\ (! ck env s v.
T
==>
evaluate_opapp_mti ck env s v [] (s, Rval v))

/\ (! ck env s1 v es count2 s2 genv2 vs env2 e2 s3 v3 bv num_args. (~ (es = []) /\
(get_num_args v = SOME num_args) /\
evaluate_list_mti ck env s1 (TAKE num_args es) (((count2,s2),genv2), Rval vs) /\
(do_opapp_mti v vs = SOME (Exp_res env2 e2)) /\
(ck ==> ~ (count2 =( 0))) /\
(LENGTH es = num_args) /\
evaluate_mti ck env2 (((if ck then count2 - num_args else count2),s2),genv2) e2 (s3,Rval v3) /\
evaluate_opapp_mti ck env s3 v3 (DROP num_args es) bv)
==>
evaluate_opapp_mti ck env s1 v es bv)

/\ (! ck env s1 v es count3 s3 genv3 vs num_args. (~ (es = []) /\
(get_num_args v = SOME num_args) /\
evaluate_list_mti ck env s1 (TAKE num_args es) (((count3,s3),genv3), Rval vs) /\
(do_opapp_mti v vs = SOME (Val_res v)) /\
(ck ==> ~ (count3 =( 0))))
==>
evaluate_opapp_mti ck env s1 v es (((count3,s3),genv3), Rval v))`;
val _ = export_theory()

