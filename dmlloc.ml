(*******************************************************************)
(*                                                                 *)
(*                         Dependent ML                            *)
(*                                                                 *)
(*                      (c) Hongwei Xi                             *)
(*                          July 2000                              *)
(*                                                                 *)
(*                   University of Cincinnati                      *)
(*                                                                 *)
(*                Distributed by permission only.                  *)
(*                                                                 *)
(*******************************************************************)

(* dmlloc - Handling the locations of symbols. *)

type location = { loc_s: int; loc_e: int }

let none_loc = { loc_s = -1; loc_e = -1 }

let symbol_loc () = {
  loc_s = Parsing.symbol_start();
  loc_e = Parsing.symbol_end()
}

let loc_pr loc =
  "Location: Char: " ^ (string_of_int loc.loc_s) ^ "-" ^ (string_of_int loc.loc_e)

let print_loc loc =
  let _ = print_string "Characters " in
  let _ = print_int loc.loc_s; print_string "-" in
  let _ = print_int loc.loc_e; print_string ":"
  in Format.force_newline()

