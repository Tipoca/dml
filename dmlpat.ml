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

(* dmlpat: type-checking pattern matching clauses *)

open Dmlsyn

module L = Dmlloc
module G = Dmlglo
module D = Dmldeb
module C = Dmlcop
module S = Dmlsim

let dt_tv_ins dt =
  match dt.dt_dsc with
    DTlam(tctx, dt) ->
      let _ = C.bind_tctx tctx in
      let dt = C.cp_dt dt in
      let _ = C.unbind_tctx tctx in dt
  | _ -> dt

let dt_iv_ope dt = (* for constructors in patterns *)
  match dt.dt_dsc with
    DT_uni (ictx, dt) ->
      let newictx = C.cp_ictx ictx in
      let newdt = C.cp_dt dt in
      let _ = C.unbind_ictx ictx in (newictx, newdt)
  | DTlam _ -> G.abort ("dt_iv_ope: DTlam: " ^ (D.dt_pr dt))
  | _ -> ([], dt)

let rec ictx_of_ind ictx (ind, ind') =
  IDprop (IPeq (ind, ind')) :: ictx

and ictx_of_ind_list ictx = function
    [], [] -> ictx
  | (ind :: rest, ind' :: rest') ->
      let ictx = ictx_of_ind ictx (ind, ind')
      in ictx_of_ind_list ictx (rest, rest')
  | _ -> G.abort ("ictx_of_ind_list: unequal length")

let rec dt_list_link = function
    [], [] -> ()
  | (dt :: rest, dt' :: rest') -> begin
      match dt.dt_dsc with
	DT_e ({ btv_dtlink = DTnolink } as btv) ->
	  btv.btv_dtlink <- DTlinkto dt'; dt_list_link (rest, rest')
      |	_ -> G.abort ("dt_list_link: " ^ (D.dt_pr dt))
  end      
  | _ -> G.abort ("dt_list_link: unequal length")

let rec ictx_of_dt ictx ({ dt_dsc = tdsc }, { dt_dsc = tdsc' }) =
(*
  let _ = print_string ("ictx_of_dt: " ^ (D.dt_dsc_pr tdsc) ^ ", " ^ (D.dt_dsc_pr tdsc') ^ "\n") in
*)
  match tdsc, tdsc' with
    DT_nam(dtlist, tcon, indlist), DT_nam(dtlist', tcon', indlist') ->
      if tcon = tcon' then
      	let _ = dt_list_link (dtlist, dtlist')
      	in ictx_of_ind_list ictx (indlist, indlist')
      else G.abort ("ictx_of_dt: " ^ (D.dt_dsc_pr tdsc) ^
		    " <> " ^ (D.dt_dsc_pr tdsc'))
  | _ -> G.abort ("ictx_of_dt: " ^ (D.dt_dsc_pr tdsc) ^
		  " <> " ^ (D.dt_dsc_pr tdsc'))

let rec bat_of_pat bat dt pat =
  match dt.dt_dsc with
    DT_e btv -> begin
      match btv.btv_dtlink with
	DTnolink -> G.abort("bat_of_pat: DT_e: no link")
      |	DTlinkto dt -> bat_of_pat bat dt pat
    end
  | DT_exi (ictx, dt) ->
      let newictx = C.cp_ictx ictx in
      let newdt = C.cp_dt dt in
      let _ = C.unbind_ictx ictx in
      let _ = bat.bat_ictx <- newictx @ bat.bat_ictx in
      let _ =
	bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist newictx
      in bat_of_pat bat newdt pat
  | _ -> bat_of_pat_dsc bat dt pat.pat_dsc
      
and bat_of_pat_dsc bat dt = function
    P_var vd ->
      let (ictx, dt) = (C.open_dt [] dt) in
      let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
      let _ =
	bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist ictx
      in vd.var_typ <- Some dt
  | Pany -> ()
  | Pcst c ->
      let ictx = ictx_of_dt [] (G.dt_const c, dt) in
      let _ = bat.bat_ictx <- ictx @ bat.bat_ictx
      in bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist ictx
  | P_cstr_0 cd ->
      let (ictx, cdt) = dt_iv_ope (dt_tv_ins cd.con_typ) in
      let ictx = ictx_of_dt ictx (cdt, dt) in
      let _ = bat.bat_ictx <- ictx @ bat.bat_ictx
      in bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist ictx
  | P_cstr_1 (cd, pat) ->
      let (ictx, cdt) = dt_iv_ope (dt_tv_ins cd.con_typ)
      in begin
      	match cdt.dt_dsc with
	  DTfun (arg_dt, res_dt) ->
	    let ictx = ictx_of_dt ictx (res_dt, dt) in
      	    let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
      	    let _ =
	      bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist ictx
	    in bat_of_pat bat arg_dt pat
      	| _ -> G.abort ("bat_of_pat_dsc: constructor type: " ^ (D.dt_pr cdt))
      end	  
  | Ptup (patlist) -> begin
      match dt.dt_dsc with
	DTtup dtlist -> bat_of_pat_list bat (dtlist, patlist)
      |	_ -> G.abort ("bat_of_pat_dsc: tuple type: " ^ (D.dt_pr dt))
    end
  | P_as (vd, pat) ->
      let (ictx, dt) = (C.open_dt [] dt) in
      let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
      let _ =
	bat.bat_ubivlist <- ubivlist_of_ictx bat.bat_ubivlist ictx
      in (vd.var_typ <- Some dt; bat_of_pat bat dt pat)
  | pdsc -> G.abort ("bat_of_pat: pdsc: " ^ (D.pat_dsc_pr pdsc))

and bat_of_pat_list bat = function
    [], [] -> ()
  | (dt :: dtlist, pat :: patlist) ->
      let ictx = bat_of_pat bat dt pat
      in bat_of_pat_list bat (dtlist, patlist)
  | _ -> G.abort ("bat_of_pat_list: unequal length")
