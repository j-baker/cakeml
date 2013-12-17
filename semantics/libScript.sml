(*Generated by Lem from lib.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_list_extraTheory;

val _ = numLib.prefer_num();



val _ = new_theory "lib"

(*open import Pervasives*)
(*import List_extra*)

(* TODO: look for these in the built-in library *)

(*val int_to_num : integer -> nat*)

(*val num_to_string : nat -> string*)

(*val all_distinct : forall 'a. list 'a -> bool*)

(*val rtc : forall 'a. ('a -> 'a -> bool) -> ('a -> 'a -> bool)*)

(*val count_list : nat -> list nat*)

(*val ^ : string -> string -> string*)

(* The builtin List.zip maps to list_combine in HOL, but I want to map to ZIP *)
(*val ZIP : forall 'a 'b. list 'a -> list 'b -> list ('a * 'b)*)

(* Environments *)
val _ = type_abbrev((* ( 'a, 'b) *) "env" , ``: ('a#'b) list``);

(*val emp : forall 'a 'b. env 'a 'b*)
val _ = Define `
 (emp = ([]))`;


(*val lookup : forall 'a 'b. Eq 'a => 'a -> env 'a 'b -> maybe 'b*)
 val _ = Define `

(lookup n [] = NONE)
/\
(lookup n ((n',v)::e) =  
(if n' = n then
    SOME v
  else
    lookup n e))`;


(*val bind : forall 'a 'b. 'a -> 'b -> env 'a 'b -> env 'a 'b*)
val _ = Define `
 (bind n v e = ((n,v)::e))`;


(*val merge : forall 'a 'b. env 'a 'b -> env 'a 'b -> env 'a 'b*)
val _ = Define `
 (merge e1 e2 = (e1 ++ e2))`;


val _ = export_theory()
