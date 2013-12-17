(*Generated by Lem from printer.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_list_extraTheory astTheory semanticPrimitivesTheory compilerLibTheory;

val _ = numLib.prefer_num();



val _ = new_theory "printer"

(* observable values *)
(*open import Pervasives*)
(*import List_extra*)

(*open import Ast*)
(*open import SemanticPrimitives*)
(*open import CompilerLib*)

val _ = Hol_datatype `
 ov =
    OLit of lit
  | OConv of  ( conN id)option => ov list
  | OFn
  | OLoc of num (* machine, not semantic, address *)
  | OError`;
 (* internal machine value (pointer) that should not appear *)

 val v_to_ov_defn = Hol_defn "v_to_ov" `

(v_to_ov _ (Litv l) = (OLit l))
/\
(v_to_ov s (Conv cn vs) = (OConv cn (MAP (v_to_ov s) vs)))
/\
(v_to_ov _ (Closure _ _ _) = OFn)
/\
(v_to_ov _ (Recclosure _ _ _) = OFn)
/\
(v_to_ov s (Loc n) = (OLoc (EL n s)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn v_to_ov_defn;

 val _ = Define `

(ov_to_string (OLit (IntLit (i:int))) = (int_to_string i))
/\
(ov_to_string (OLit (Bool T)) = "true")
/\
(ov_to_string (OLit (Bool F)) = "false")
/\
(ov_to_string (OLit Unit) = "()")
/\
(ov_to_string (OConv _ _) = "<constructor>")
(*
ov_to_string (OConv cn vs) =
  (id_to_string cn)^" "^
  match intersperse ", " (List.map ov_to_string vs) with
  | [s] -> s
  | ls -> "("^Hol.FLAT ls^")"
  end
*)
/\
(ov_to_string (OLoc _) = "<ref>")
/\
(ov_to_string OFn = "<fn>")
/\
(ov_to_string OError = "<error>")`;

val _ = export_theory()
