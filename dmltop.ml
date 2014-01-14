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

let (type_constraints: (Dmlsyn.tc list) ref) = ref []
let (vec_constraints: (Dmlsyn.ivec list list) ref) = ref []
let (unsolved_constraint: ((int * int array) list * int array list) ref) = ref ([], [])

let initenv =
  let prelude = Dmlpar.parse (open_in "prelude.dml") in
  let env = { Dmlsyn.env_tctx = []; Dmlsyn.env_ictx = [];
	      Dmlsyn.env_def = Dmlglo.builtin_def;
	      Dmlsyn.env_tcs = Dmlglo.builtin_tcs;
	      Dmlsyn.env_isab = Dmlglo.builtin_isab } in
  let (_, env) = Dmlintern.trans_program env prelude
  in env

let top filename =
  let ic =
    if (filename = "") then stdin
    else open_in ("EXAMPLES/" ^ filename ^ ".dml") in
  let program = Dmlpar.parse ic in
  let (program, _) = Dmlintern.trans_program initenv program in
  let _ =
     print_string "The program is in internal representation.\n" in
  let _ = Dmlpar.current_program := program in
  let tclist = Dmldtc.dtc_program program in
  let _ = type_constraints := tclist in
  let _ = print_string "type constraints are collected.\n" in
  let tclist = Dmlsim.solve_btv_all tclist in
  let _ = print_string "btv solving is done.\n" in
  let iplist = Dmlsim.solve_biv [] tclist in
  let _ = print_string "biv solving is done.\n" in
(*
  let _ = print_string ("iplist = " ^ Dmldeb.ip_list_pr iplist ^ "\n") in
*)
  let iveclistlist = Dmlvec.main iplist in
  let _ = vec_constraints := iveclistlist in
  let n = List.length iveclistlist in
  let _ = print_string ("iveclistlist: " ^ (string_of_int n) ^ "\n") in
  let _ =
    try Dmlsol.main iveclistlist
    with Dmlsol.Unsolved_constraint (eqs, veclist) ->
      unsolved_constraint := (eqs, veclist);
      raise Dmlglo.Unsolved_constraint in
  let _ = print_string "dependent type checking is successfully done!\n" in ()

