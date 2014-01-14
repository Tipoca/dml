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

(* dmldeb: functions for debugging: not for others :-) *)

open Dmlsyn

let rec ind_pr = function
    Ivar name -> name
  | I_u ubiv -> ubiv_pr ubiv
  | I_e ebiv -> begin
      match ebiv.ebiv_link with
        Inolink -> ebiv_pr ebiv
      | Ilinkto ind -> ind_pr ind
    end
  | Iint i -> string_of_int i
  | Ifun (name, indlist) -> name ^ "(" ^ (ind_list_pr indlist) ^ ")"

and ind_list_pr = function
    [] -> ""
  | [ind] -> ind_pr ind
  | ind :: indlist -> (ind_pr ind) ^ "," ^ (ind_list_pr indlist)

and met_pr mu = ind_list_pr mu

and ubiv_pr ubiv =
  let s = "{" ^ (ubiv.ubiv_name) ^ ";" in
  let s =
    match ubiv.ubiv_link with
      Inolink -> s ^ "nolink"
    | Ilinkto ind -> s ^ ("link: " ^ (ind_pr ind))
  in s ^ "}"

and ubiv_list_pr = function
    [] -> ""
  | [ubiv] -> ubiv_pr ubiv
  | ubiv :: rest -> (ubiv_pr ubiv ^ ";" ^ ubiv_list_pr rest)

and ebiv_pr ebiv =
  let s = "{" ^ (ebiv.ebiv_name) ^ ";" in
  let s =
    match ebiv.ebiv_link with
      Inolink ->
      s ^ "nolink" ^ ";" ^ "ubivlist: " ^ (ubiv_list_pr ebiv.ebiv_ubiv)
    | Ilinkto ind ->
      s ^ "link: " ^ (ind_pr ind) ^ ";" ^ "ubivlist: " ^ (ubiv_list_pr ebiv.ebiv_ubiv)
  in s ^ "}"

let rec ip_pr = function
    IPlt (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ "<" ^ (ind_pr ind2) ^ ")"
  | IPlte (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ "<=" ^ (ind_pr ind2) ^ ")"
  | IPgt (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ ">" ^ (ind_pr ind2) ^ ")"
  | IPgte (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ ">=" ^ (ind_pr ind2) ^ ")"
  | IPeq (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ "=" ^ (ind_pr ind2) ^ ")"
  | IPneq (ind1, ind2) -> "(" ^ (ind_pr ind1) ^ "!=" ^ (ind_pr ind2) ^ ")"
  | IPconj iplist -> "[" ^ (ip_list_pr iplist) ^ "]"
  | IPdisj iplist -> "{" ^ (ip_list_pr iplist) ^ "}"
  | IPuni (ictx, iplist) ->
    "[" ^ (ictx_pr ictx) ^ "] -> [" ^ (ip_list_pr iplist) ^ "]"

and ip_list_pr = function
    [] -> ""
  | [ip] -> ip_pr ip
  | ip :: iplist -> (ip_pr ip) ^ "," ^ (ip_list_pr iplist)

and ictx_pr = function
    [] -> ""
  | [IDvar biv] -> (ubiv_pr biv)
  | [IDprop ip] -> (ip_pr ip)
  | IDvar biv :: rest -> (ubiv_pr biv) ^ "," ^ (ictx_pr rest)
  | IDprop ip :: rest -> (ip_pr ip) ^ "," ^ (ictx_pr rest)

let isort_pr = function
    ISint -> "int"
  | ISnam name -> name
  | IS_nam isab -> isab.isab_nam
  | ISsub(ubiv, ip) -> "{" ^ (ubiv_pr ubiv) ^ "|" ^ (ip_pr ip) ^ "}"

let ivar_decl_pr = function
    IDvar ubiv -> ubiv_pr ubiv
  | IDprop ip -> ip_pr ip

let rec ivar_decl_list_pr = function
    [] -> ""
  | [id] -> ivar_decl_pr id
  | IDvar ubiv :: rest -> (ubiv_pr ubiv) ^ "," ^ (ivar_decl_list_pr rest)
  | IDprop ip :: rest -> (ip_pr ip) ^ "|" ^ (ivar_decl_list_pr rest)

let tcon_pr tcon = tcon.tycon_nam

let rec et_pr = function
    ETvar name -> "ETvar(" ^ name ^ ")"
  | ET_u btv -> "ET_u(" ^ (btv_e_pr btv) ^ ")"
  | ET_e btv -> "ET_e(" ^ (btv_e_pr btv) ^ ")"
  | ETnam (etlist, name) -> "<" ^ (et_list_pr etlist) ^ ">" ^ name
  | ET_nam (etlist, tcon) -> "<" ^ (et_list_pr etlist) ^ ">" ^ (tcon_pr tcon)
  | ETtup etlist -> "ETtup" ^ "(" ^ (et_list_pr etlist) ^ ")"
  | ETfun (et1, et2) -> (et_pr et1) ^ " -> " ^ (et_pr et2)
  | ETlam (tctx, et) -> "DTlam(" ^ (tctx_e_pr tctx) ^ "," ^ (et_pr et)

and et_list_pr = function
    [] -> ""
  | [et] -> et_pr et
  | et :: etlist -> (et_pr et) ^ "," ^ (et_list_pr etlist)

and nm_et_list_pr = function
    [] -> ""
  | [nm, et] -> nm ^ ": " ^ (et_pr et)
  | (nm, et) :: rest -> nm ^ ": " ^ (et_pr et) ^ "," ^ (nm_et_list_pr rest)

and btv_e_pr btv =
  let s = "{" ^ (btv.btv_name) ^ ";" in
  let s =
    match btv.btv_etlink with
      ETnolink -> s ^ "nolink"
    | ETlinkto et -> s ^ ("link: " ^ (et_pr et))
  in s ^ "}"

and tctx_e_pr = function
    [] -> ""
  | TDvar btv :: rest -> (btv_e_pr btv) ^ "," ^ (tctx_e_pr rest)

let rec dt_pr {dt_dsc=tdsc} = dt_dsc_pr tdsc

and dt_list_pr = function
    [] -> ""
  | [dt] -> dt_pr dt
  | dt :: dtlist -> (dt_pr dt) ^ "," ^ (dt_list_pr dtlist)

and nm_dt_list_pr = function
    [] -> ""
  | [(nm, dt)] -> nm ^ ": " ^ (dt_pr dt)
  | (nm, dt) :: rest -> nm ^ ": " ^ (dt_pr dt) ^ ";" ^ (nm_dt_list_pr rest)

and dt_dsc_pr = function
    DTvar name -> "DTvar(" ^ name ^ ")"
  | DT_u btv -> "DT_u(" ^ (btv_d_pr btv) ^ ")"
  | DT_e btv -> "DT_e(" ^ (btv_d_pr btv) ^ ")"
  | DTnam (dtlist, name, indlist) ->
    "<" ^ (dt_list_pr dtlist) ^ ">" ^ name ^ "(" ^ (ind_list_pr indlist) ^ ")"
  | DT_nam (dtlist, tc, indlist) ->
      "<" ^ (dt_list_pr dtlist) ^ ">" ^ (tcon_pr tc) ^
      "(" ^ (ind_list_pr indlist) ^ ")"
  | DTtup dtlist -> "DTtup" ^ "(" ^ (dt_list_pr dtlist) ^ ")"
  | DTexi (ictx, dt) -> "DTexi" ^ "[" ^ (ictx_pr ictx) ^ "]" ^ (dt_pr dt)
  | DT_exi (ictx, dt) -> "DT_exi" ^ "[" ^ (ictx_pr ictx) ^ "]" ^ (dt_pr dt)
  | DTuni (ictx, dt) -> "DTuni" ^ "[" ^ (ictx_pr ictx) ^ "]" ^ (dt_pr dt)
  | DT_uni (ictx, dt) -> "DT_uni" ^ "[" ^ (ictx_pr ictx) ^ "]" ^ (dt_pr dt)
  | DTfun (dt1, dt2) -> (dt_pr dt1) ^ ") -> " ^ (dt_pr dt2)
  | DTmet (mu, dt) -> "DTmet"
  | DTlam (tctx, dt) -> "DTlam(" ^ (tctx_d_pr tctx) ^ "," ^ (dt_pr dt)

and btv_d_pr btv =
  let s = "{" ^ (btv.btv_name) ^ ";" in
  let s =
    match btv.btv_dtlink with
      DTnolink -> s ^ "nolink"
    | DTlinkto dt -> s ^ ("link: " ^ (dt_pr dt))
  in s ^ "}"

and tctx_d_pr = function
    [] -> ""
  | TDvar btv :: rest -> (btv_d_pr btv) ^ "," ^ (tctx_d_pr rest)

let vd_pr vd = vd.var_nam
let rec vd_list_pr = function
    [] -> ""
  | [vd] -> vd_pr vd
  | vd  :: vdlist -> (vd_pr vd) ^ ", " ^ (vd_list_pr vdlist) 

let fd_pr fd = fd.fun_nam

let cd_pr cd = cd.con_nam

let vd_dt_pr (vd, dt) = "(" ^ (vd_pr vd) ^ ", " ^ (dt_pr dt) ^ ")"

let rec vd_dt_list_pr = function
    [] -> ""
  | (vd, dt) :: rest -> vd_dt_pr (vd, dt) ^ (vd_dt_list_pr rest)

let const_pr = function
    Cboo b -> if b then "true" else "false"
  | Ccha ch -> String.make 1 ch
  | Cflo f -> string_of_float f
  | Cint i -> string_of_int i
  | Cstr s -> s

let rec pat_pr {pat_dsc=pdsc} = pat_dsc_pr pdsc

and pat_dsc_pr = function
    Pvar name -> "Pvar(" ^ name ^ ")"
  | P_var vd -> "P_var(" ^ (vd_pr vd) ^ ")"
  | Pany -> "_"
  | Pcst c ->  "Pcst(" ^ (const_pr c) ^ ")"
  | Pcstr (name, pat) -> "Pcstr(" ^ name ^ "," ^ (pat_pr pat) ^ ")"
  | P_cstr_0 cd -> "Pcstr(" ^ (cd_pr cd) ^ ")"
  | P_cstr_1 (cd, pat) -> "Pcstr(" ^ (cd_pr cd) ^ "," ^ (pat_pr pat) ^ ")"
  | Ptup (patlist) -> "Ptup(" ^ (pat_list_pr patlist) ^ ")"
  | Pas (name, pat) -> "Pas(" ^ name ^ "," ^ pat_pr pat ^ ")"
  | P_as (vd, pat) -> "P_as(" ^ vd_pr vd ^ "," ^ pat_pr pat ^ ")"

and pat_list_pr = function
    [] -> ""
  | [pat] -> pat_pr pat
  | pat :: rest -> (pat_pr pat) ^ "," ^ (pat_list_pr rest)

let rec exp_pr {exp_dsc=edsc} = exp_dsc_pr edsc

and exp_opt_pr = function
    None -> ""
  | Some exp -> exp_pr exp

and exp_dsc_pr = function
    Evar name -> "Evar(" ^ name ^ ")"
  | E_var vd -> "E_var(" ^ (vd_pr vd) ^ ")"
  | E_fun fd -> "E_fun(" ^ (fd_pr fd) ^ ")"
  | Ecst c -> "Ecst(" ^ (const_pr c) ^ ")"
  | E_cstr cd -> "E_cstr(" ^ (cd_pr cd) ^ ")"
  | Eapp (e1, e2) -> "Eapp(" ^ (exp_pr e1) ^ "," ^ (exp_pr e2) ^ ")"
  | Etup (es) -> "Etup(" ^ (exp_list_pr es) ^ ")"
  | Ecas _ -> "Ecas"
  | Eann (e, dt) -> "Eann(" ^ (exp_pr e) ^ ": " ^ (dt_pr dt) ^ ")"
  | _ -> fatal ("exp_dsc_pr")

and exp_list_pr = function
    [] -> ""
  | [exp] -> exp_pr exp
  | exp :: rest -> (exp_pr exp) ^ "," ^ (exp_list_pr rest)

and name_exp_list_pr = function
    [] -> ""
  | [name, exp] -> "(" ^ name ^ ": " ^ (exp_pr exp) ^ ")"
  | (name, exp) :: rest ->
      "(" ^ name ^ ": " ^ (exp_pr exp) ^ ")" ^ ";" ^ (name_exp_list_pr rest)

and pat_exp_list_pr = function
    [] -> ""
  | (pat, exp) :: rest ->
      (pat_pr pat) ^ ": " ^ (exp_pr exp) ^ "; " ^ (pat_exp_list_pr rest)

let rec show_iplistlist = function
    [] -> ()
  | iplist :: rest ->
    (print_string (ip_list_pr iplist);
     print_newline ();
     show_iplistlist rest)

let rec tc_pr = function
    TCco (dt, dt') ->
      "TCco(" ^ (dt_pr dt) ^ " <= " ^ (dt_pr dt') ^ ")"
  | TCeq (dt, dt') ->
      "TCeq(" ^ (dt_pr dt) ^ " <= " ^ (dt_pr dt') ^ ")"
  | TCmet0 mu -> "TCmet0(" ^ (met_pr mu) ^ ")"
  | TCmet (mu1, mu2) ->
      "TCmet(" ^ (met_pr mu1) ^ " <= " ^ (met_pr mu2) ^ ")"
  | TCips iplist ->
      "TCips(" ^ (ip_list_pr iplist) ^ ")"
  | TCuni (ictx, tclist) ->
      "TCuni(" ^ (ictx_pr ictx) ^ " | " ^ (tc_list_pr tclist) ^ ")"

and tc_list_pr = function
    [] -> ""
  | [tc] -> tc_pr tc
  | tc :: tclist -> (tc_pr tc) ^ ", " ^ (tc_list_pr tclist)

let print_vec vec =
  for i = 0 to Array.length vec - 1 do
    print_int (vec.(i)); print_string "; ";
  done; print_newline ()

let rec print_veclist = function
    [] -> print_newline ()
  | vec :: veclist -> print_vec vec; print_veclist veclist
