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

(* dmlglo: declare some globals *)

let print_line msg =
  let _ = print_string msg in Format.force_newline ()

open Dmlsyn

exception Fatal_error of string
exception Not_available of string
exception Unbound_index_variable of string
exception Undeclared_type_constructor of string
exception Unbound_type_variable of string
exception Unbound_variable of string
exception Unify_error
exception Unsolved_constraint

let abort msg = raise (Fatal_error msg)
let sorry msg = raise (Not_available msg)

let warning msg = print_string ("Warning: " ^ msg ^ "\n")

let nat_is = {
  isab_nam = "nat";
  isab_def= is_nat
} 

let neg_is = {
  isab_nam = "neg";
  isab_def= is_neg
} 

let pos_is = {
  isab_nam = "pos";
  isab_def= is_pos
}

let bool_is = {
  isab_nam = "bool";
  isab_def= is_bool
}

let builtin_isab = [
  nat_is; neg_is; pos_is; bool_is
] 

(* array is an array without size *)
let array_tc =
  let ubiv = to_ubiv "array" is_nat
  in { tycon_nam = "array";
       tycon_con = Some [];
       tycon_des = Some [];
       tycon_tpa = [TDvar (to_btv "array")];
       tycon_ind = ([IDvar ubiv], [I_u ubiv]) }

let bool_tc =
  let ubiv = to_ubiv "bool" is_bool
  in { tycon_nam = "bool";
       tycon_con = Some [];
       tycon_des = Some [];
       tycon_tpa = [];
       tycon_ind = ([IDvar ubiv], [I_u ubiv]) }

let char_tc = {
  tycon_nam = "char";
  tycon_con = Some [];
  tycon_des = Some [];
  tycon_tpa = [];
  tycon_ind = ([], [])
}

let exc_tc = {
  tycon_nam = "exc";
  tycon_con = Some [];
  tycon_des = Some [];
  tycon_tpa = [];
  tycon_ind = ([], [])
} 

let float_tc = {
  tycon_nam = "float";
  tycon_con = Some [];
  tycon_des = Some [];
  tycon_tpa = [];
  tycon_ind = ([], [])
} 

let int_tc =
  let ubiv = to_ubiv "int" ISint
  in { tycon_nam = "int";
       tycon_con = Some [];
       tycon_des = Some [];
       tycon_tpa = [];
       tycon_ind = ([IDvar ubiv], [I_u ubiv]) } 

let string_tc = {
  tycon_nam = "string";
  tycon_con = Some [];
  tycon_des = Some [];
  tycon_tpa = [];
  tycon_ind = ([], [])
}

let builtin_tcs = [
  array_tc; bool_tc; char_tc; float_tc; int_tc; string_tc
] 

let dt_char = mkdt_no_loc (DT_nam([], char_tc, []))
let dt_bool ind = mkdt_no_loc (DT_nam([], bool_tc, [ind]))
let dt_exc = mkdt_no_loc (DT_nam([], exc_tc, []))
let dt_float = mkdt_no_loc (DT_nam([], float_tc, []))
let dt_int ind = mkdt_no_loc (DT_nam([], int_tc, [ind]))
let dt_int_e = mkdt_no_loc (DT_nam([], int_tc, []))
let dt_string = mkdt_no_loc (DT_nam([], string_tc, []))
let dt_unit = mkdt_no_loc (DTtup [])

let dt_u btv = mkdt_no_loc (DT_u btv)

let dt_nam tvs tc indlist = mkdt_no_loc (DT_nam (tvs, tc, indlist))

let dt_fun dt1 dt2 = mkdt_no_loc (DTfun (dt1, dt2))

let dt_tup dtlist = mkdt_no_loc (DTtup dtlist)

let dt_uni ictx dt =
  match ictx with
    [] -> dt
  | _ -> mkdt_no_loc (DT_uni (ictx, dt))

let dt_lam tctx dt =
  match tctx with
    [] -> dt
  | _ -> mkdt_no_loc (DTlam (tctx, dt))

let dt_const = function
    Cboo b -> if b then dt_bool (Iint 1) else dt_bool (Iint 0)
  | Ccha _ -> dt_char
  | Cflo _ -> dt_float
  | Cint i -> dt_int (Iint i)
  | Cstr _ -> dt_string

let builtin_def =
  List.map
    (function (f, dt) -> (f, E_fun { fun_nam = f; fun_typ = Some dt })) []

let rec is_check e =
  match e.exp_dsc with
    Evar _ -> true
  | E_var _ -> true
  | E_fun _ -> true
  | Ecst _ -> true
  | E_cstr _ -> true
  | Eapp _ -> false
  | Elet _ -> false
  | Ecas _ -> false
  | Efn _ -> true
  | Etup es -> List.for_all is_check es
  | Eann (e, _) -> false

