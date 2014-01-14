(*********************************************************************)
(*                                                                   *)
(*                         Dependent ML                              *)
(*                                                                   *)
(*                       (c) Hongwei Xi                              *)
(*                           July 2000                               *)
(*                                                                   *)
(*                     University of Cincinnati                      *)
(*                                                                   *)
(*                  Distributed by permission only.                  *)
(*                                                                   *)
(*********************************************************************)

(* the wrap function is adopted from OCaml *)

module G = Dmlglo
module L = Dmlloc

let show_line_number () =
    let _ =
      print_string ("The line number is " ^ string_of_int (!Dmllexer.linenum))
    in print_newline ()

let wrap parsing_fun lexbuf =
  try
    let ast = parsing_fun Dmllexer.token lexbuf in
    let _ = Parsing.clear_parser() in ast
  with
    | Dmllexer.Error msg as err ->
      let _ = print_string msg in
      let _ = print_newline () in
      let _ = show_line_number () in raise err
    | Parsing.Parse_error as err ->
      let _ = print_string ("Parsing error:\n") in
      let _ = show_line_number () in raise err


let current_program: Dmlsyn.decl list ref = ref []

let program = wrap Dmlparser.top

let parse ic = (* ic: in_channel *)
  let _ = Dmllexer.linenum := 0 in
  let lexbuf = Lexing.from_channel ic in
  try
    let _ = current_program := program lexbuf in
    let _ = print_string "The program has been successfully parsed.\n" in
    let _ = close_in ic in !current_program
  with
    | exc -> let _ = close_in ic in raise exc

