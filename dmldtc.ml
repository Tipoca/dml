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

(* Dmldtc: dependent type-checking *)

open Dmlsyn
module C = Dmlcop
module D = Dmldeb
module G = Dmlglo
module P = Dmlpat
module S = Dmlsim

let dt_iv_ins bat (ictx, dt) =
  let (ivs, ips) = C.bind_ictx (bat.bat_ubivlist) ([], []) ictx in
  let _ = bat.bat_tclist <- TCips ips :: bat.bat_tclist in
  let dt = C.cp_dt dt in
  let _ = C.unbind_ictx ictx in dt

let dt_of_vd vd =
  match vd.var_typ with
    Some dt -> dt
  | None -> G.abort ("dt_of_vd: " ^ D.vd_pr vd ^ ": no type")

let dt_of_fd fd =
  match fd.fun_typ with
    Some dt -> dt
  | None -> G.abort ("dt_of_fd: " ^ D.fd_pr fd ^ ": no type")

let mu_of_bat bat (f: string) =
  let rec aux = function
      [] -> None
    | (fs, mu) :: rest ->
	if List.exists (function f' -> f = f') fs then Some mu
	else aux rest
  in aux (bat.bat_fs_mu_list)

let tc_of_bat bat =
  let tc = TCuni (bat.bat_ictx, bat.bat_tclist) in
  let rec aux tc = function
      [] -> tc
    | (ictx, tclist) :: rest ->
	let tc = TCuni(ictx, tc :: tclist) in aux tc rest
  in aux tc (bat.bat_ictx_tclist_list)


let push_bat_ictx newictx bat =
  let ictx = bat.bat_ictx in
  let tclist = bat.bat_tclist in
  let _ = bat.bat_ubivlist <- ubivlist_of_ictx (bat.bat_ubivlist) newictx in
  let _ = bat.bat_ictx <- newictx in
  let _ = bat.bat_tclist <- []
  in bat.bat_ictx_tclist_list <- (ictx, tclist) :: bat.bat_ictx_tclist_list 

let rec uncurry_app args e =
  match e.exp_dsc with
    Eapp (e1, e2) -> uncurry_app (e2 :: args) e1
  | _ -> (e, args)

let rec dto_exp bat e  = dto_exp_dsc bat (e.exp_dsc)

and dto_exp_dsc bat = function
    E_var vd -> begin
      match vd.var_typ with
	Some dt -> dt
      |	None -> G.abort ("dto_exp: " ^ D.vd_pr vd ^ ": no type")
    end
  | E_fun fd -> begin
      match fd.fun_typ with
	Some dt -> dt
      |	None -> G.abort ("dto_exp: " ^ D.fd_pr fd ^ ": no type")
    end
  | Ecst c -> G.dt_const c
  | E_cstr cd -> cd.con_typ
  | Eapp (e1, e2) -> dto_app bat e1 e2
  | Elet (decls, e) -> G.abort ("dto_exp_dsc: let")
  | Ecas _ -> G.abort ("dto_exp_dsc: case")
  | Efn  _ -> G.abort ("dto_exp_dsc: fn")
  | Etup es -> dto_exp_list bat [] es
  | Eann (e, dt) -> let _ = dtc_exp dt bat e in dt
  | _ -> G.abort ("dto_exp_dsc")

and dto_exp_list bat res = function
    [] -> mkdt_no_loc (DTtup (List.rev res))
  | e :: es ->
      let dt = dto_exp bat e
      in dto_exp_list bat (dt :: res) es

and dto_args bat ictx res = function
    [] -> (ictx, List.rev res)
  | e :: es ->
      if G.is_check e then dto_args bat ictx ((e, None) :: res) es
      else
	let dt = dto_exp bat e in
(*
        let _ = print_string ("dto_args: " ^ D.dt_pr dt ^ "\n") in
*)
        let (ictx, dt) = C.open_dt ictx dt in
(*
        let _ = print_string ("dto_args: " ^ D.dt_pr dt ^ "\n") in
*)
	dto_args bat ictx ((e, Some dt) :: res) es
    
and dto_app bat e1 e2 =
  let (e, es) =  uncurry_app [e2] e1 in
  let f =
    match e.exp_dsc with
      E_fun fd -> Some (fd.fun_nam) | _ -> None in
  let (ictx, e_odt_list) = dto_args bat [] [] es
  in begin
     match ictx with
       [] -> dto_app_aux f ictx bat (dto_exp bat e) e_odt_list
     | _ ->
	 let ori_ictx = bat.bat_ictx in
	 let ori_ubivlist = bat.bat_ubivlist in
	 let ori_tclist = bat.bat_tclist in
	 let ori_ictx_tclist_list = bat.bat_ictx_tclist_list in
	 let _ = bat.bat_ictx <- ictx in
	 let _ = bat.bat_ubivlist <- ubivlist_of_ictx ori_ubivlist ictx in
	 let _ = bat.bat_tclist <- [] in
	 let _ = bat.bat_ictx_tclist_list <- [] in
	 let fun_dt = dto_exp bat e in
	 let res_dt = dto_app_aux f ictx bat fun_dt e_odt_list in
	 let tc = tc_of_bat bat in
	 let _ = bat.bat_ictx <- ori_ictx in
	 let _ = bat.bat_ubivlist <- ori_ubivlist in
	 let _ = bat.bat_tclist <- tc :: ori_tclist in
	 let _ = bat.bat_ictx_tclist_list <- ori_ictx_tclist_list
	 in res_dt
  end

and dto_app_aux f ictx bat dt = function
    [] -> begin
      match ictx with [] -> dt | _ -> mkdt_no_loc (DT_exi (ictx, dt))
    end
  | (e, odt) :: rest ->
      let dt = P.dt_tv_ins dt in
      let dt =
	match dt.dt_dsc with
	  DT_uni (ictx, dt) -> dt_iv_ins bat (ictx, dt)
	| _ -> dt in
      let dt =
	match dt.dt_dsc with
	  DTmet (mu, dt) -> begin
	    match f with
	      Some f -> begin
		match mu_of_bat bat f with
		  None -> dt
		| Some mu' ->
(*
		    let _ = print_string ("mu = " ^ D.met_pr mu ^ "\n") in
		    let _ = print_string ("mu' = " ^ D.met_pr mu' ^ "\n") in
*)
		    let _ = S.cons_bat_tc bat (TCmet (mu, mu'))
		    in dt
  	      end
	    | _ -> G.abort ("dto_app_aux: metric type")
	  end
	| _ -> dt
      in match odt with
	None -> begin
	  match dt.dt_dsc with
	    DTfun (dt1, dt2) ->
	      let _ = dtc_exp dt1 bat e
	      in dto_app_aux f ictx bat dt2 rest
	  | _ -> G.abort ("dto_app_aux: not function type: " ^ D.dt_pr dt)
      	end
      |	Some arg_dt -> begin
(*
	  let _ = print_string ("dto_app_aux: arg_dt: " ^ D.dt_pr arg_dt ^ "\n") in
*)
	  match dt.dt_dsc with
	    DTfun (dt1, dt2) ->
(*
	      let _ = print_string ("dto_app_aux: dt1: " ^ D.dt_pr dt1 ^ "\n") in
*)
	      let _ = S.cons_bat_tcco bat (arg_dt, dt1) in
(*
	      let _ = print_string ("dto_app_aux: dt1: " ^ D.dt_pr dt1 ^ "\n") in
*)
	      dto_app_aux f ictx bat dt2 rest
	  | _ -> G.abort ("dto_app_aux: not function type: " ^ D.dt_pr dt)
        end
	      
and dtc_exp exp_dt bat e =
  match exp_dt.dt_dsc with
    DT_e btv -> begin
      match btv.btv_dtlink with
 	DTlinkto exp_dt -> dtc_exp exp_dt bat e
      |	DTnolink ->
	  let dt = dto_exp bat e
	  in S.cons_bat_tcco bat (dt, exp_dt)
    end
  | _ -> dtc_exp_dsc exp_dt bat e.exp_dsc

and dtc_exp_list bat = function
    [], [] -> ()
  | dt :: dts, e :: es ->
    (dtc_exp dt bat e; dtc_exp_list bat (dts, es))
  | _, _ -> G.abort ("dtc_exp_list: unequal length")

and dtc_exp_dsc exp_dt bat = function
    E_var vd -> begin
      match vd.var_typ with
	Some dt ->  S.cons_bat_tcco bat (dt, exp_dt)
      |	None -> vd.var_typ <- Some (exp_dt)
    end
  | Elet (decls, e) -> 
      let ori_ubivlist = bat.bat_ubivlist in
      let ori_ictx = bat.bat_ictx in
      let ori_tclist = bat.bat_tclist in
      let ori_ictx_tclist_list = bat.bat_ictx_tclist_list in
      let _ = bat.bat_ictx <- [] in
      let _ = bat.bat_tclist <- [] in
      let _ = bat.bat_ictx_tclist_list <- [] in
      let _ = dtc_decls bat decls in
      let _ = dtc_exp exp_dt bat e in
      let tc = tc_of_bat bat in
      let _ = bat.bat_ictx <- ori_ictx in
      let _ = bat.bat_ubivlist <- ori_ubivlist in
      let _ = bat.bat_tclist <- tc :: ori_tclist in
      let _ = bat.bat_ictx_tclist_list <- ori_ictx_tclist_list
      in ()
  | Ecas (e, p_e_list) ->
      let pat_dt = dto_exp bat e in
      let (ictx, pat_dt) = C.open_dt [] pat_dt
      in dtc_pat_exp_list exp_dt pat_dt ictx bat p_e_list
  | Efn p_e_list ->
      let rec aux (res: icontext) dt =
  	match dt.dt_dsc with
	  DT_uni (ictx, dt) -> aux (ictx @ res) dt
	| DTfun (dt1, dt2) -> (res, dt1, dt2)
  	| _ ->
	    G.abort ("dtc_exp_dsc: Efn: not function type: " ^ D.dt_pr dt) in
      let (ictx, pat_dt, exp_dt) = aux [] exp_dt
      in dtc_pat_exp_list exp_dt pat_dt ictx bat p_e_list
  | Etup es as edsc -> begin
      match exp_dt.dt_dsc with
	DTtup dts -> dtc_exp_list bat (dts, es)
      |	DT_exi (ictx, dt) ->
	  let dt = dt_iv_ins bat (ictx, dt)
	  in dtc_exp_dsc dt bat edsc
      |	_ -> G.abort ("dtc_exp_dsc: Etup2: " ^ D.dt_pr exp_dt)
    end
  | edsc ->
      let dt = dto_exp_dsc bat edsc
      in S.cons_bat_tcco bat (dt, exp_dt)

and dtc_pat_exp exp_dt pat_dt ictx ubivlist bat (p, e) =
  let _ = bat.bat_ictx <- ictx in
  let _ = bat.bat_ubivlist <- ubivlist in
  let _ = bat.bat_tclist <- [] in
  let _ = bat.bat_ictx_tclist_list <- [] in
  let _ = P.bat_of_pat bat pat_dt p in
  let _ = dtc_exp exp_dt bat e
  in tc_of_bat bat

and dtc_pat_exp_list exp_dt pat_dt ictx bat p_e_list =
    let ori_ubivlist = bat.bat_ubivlist in
    let ori_ictx = bat.bat_ictx in
    let ori_tclist = bat.bat_tclist in
    let ori_ictx_tclist_list = bat.bat_ictx_tclist_list in
    let ubivlist = ubivlist_of_ictx ori_ubivlist ictx in
    let tclist =
      dtc_pat_exp_list_aux exp_dt pat_dt ictx ubivlist bat [] p_e_list in
    let tc = TCuni (ictx, tclist) in
    let _ = bat.bat_ictx <- ori_ictx in
    let _ = bat.bat_ubivlist <- ori_ubivlist in
    let _ = bat.bat_ictx_tclist_list <- ori_ictx_tclist_list in
    let _ = bat.bat_tclist <- tc :: ori_tclist
    in ()

and dtc_pat_exp_list_aux exp_dt pat_dt ictx ubivlist bat tclist = function
    [] -> tclist
  | (p, e) :: rest ->
      let tc = dtc_pat_exp exp_dt pat_dt ictx ubivlist bat (p, e) in
      let _ = S.cons_bat_tc bat tc
      in dtc_pat_exp_list_aux
 	   exp_dt pat_dt ictx ubivlist bat (tc :: tclist) rest

and dtc_fd fs bat fd =
  let ori_ictx = bat.bat_ictx in
  let ori_ubivlist = bat.bat_ubivlist in
  let ori_tclist = bat.bat_tclist in
  let ori_ictx_tclist_list = bat.bat_ictx_tclist_list in
  let dt =
    match fd.fd_typ with
      Some dt -> dt
    | None -> G.abort ("dto_fdecl: no type: " ^ fd.fd_nam) in
  let dt =
    match dt.dt_dsc with
      DTlam (tctx, dt) -> dt | _ -> dt in
  let (ictx, dt) =
    match dt.dt_dsc with
      DT_uni (ictx, dt) -> (ictx, dt) | _ -> ([], dt) in
  let ubivlist = ubivlist_of_ictx ori_ubivlist ictx in
  let tclist =
    dtc_pats_exp_list fs dt ictx ubivlist ori_tclist bat (fd.fd_bod) in
  let _ = bat.bat_ictx <- ori_ictx in
  let _ = bat.bat_ubivlist <- ori_ubivlist in
  let _ = bat.bat_tclist <- tclist in
  let _ = bat.bat_ictx_tclist_list <- ori_ictx_tclist_list
  in ()

and dtc_pats_exp fs exp_dt bat e = function
    [] -> let _ = dtc_exp exp_dt bat e in tc_of_bat bat
  | p :: ps -> begin
      match exp_dt.dt_dsc with
	DTfun (dt1, dt2) ->
	  let (ictx, dt1) = C.open_dt [] dt1 in
	  let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
	  let _ =
	    bat.bat_ubivlist <- ubivlist_of_ictx (bat.bat_ubivlist) ictx in
	  let _ = P.bat_of_pat bat dt1 p in
	  let exp_dt =
	    match dt2.dt_dsc with
	      DT_uni (ictx, dt) ->
		let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
		let _ =
		  bat.bat_ubivlist <- ubivlist_of_ictx (bat.bat_ubivlist) ictx
		in dt
	    | _ -> dt2
	  in dtc_pats_exp fs exp_dt bat e ps
      |	DTmet (mu, dt) ->
(*
	  let _ = print_string ("dtc_pats_exp: mu = " ^ D.met_pr mu ^ "\n") in
*)
	  let _ = bat.bat_tclist <- TCmet0 mu :: bat.bat_tclist in
	  let _ = bat.bat_fs_mu_list <- (fs, mu) :: bat.bat_fs_mu_list
	  in dtc_pats_exp fs dt bat e (p :: ps)
      |	_ -> G.abort ("dtc_pats_exp: exp_dt: " ^ D.dt_pr exp_dt)
    end

and dtc_pats_exp_list fs exp_dt ictx ubivlist tclist bat = function
    [] -> tclist
  | (ps, e) :: rest ->
      let _ = bat.bat_ictx <- ictx in
      let _ = bat.bat_ubivlist <- ubivlist in
      let _ = bat.bat_tclist <- [] in
      let _ = bat.bat_ictx_tclist_list <- [] in
      let tc = dtc_pats_exp fs exp_dt bat e ps
      in dtc_pats_exp_list fs exp_dt ictx ubivlist (tc :: tclist) bat rest

and dtc_fds bat fds =
  let ori_fs_mu_list = bat.bat_fs_mu_list in
  let fs = List.map (function fd -> fd.fd_nam) fds in
  let rec aux = function
    [] -> ()
  | fd :: fds -> (dtc_fd fs bat fd; aux fds) in
  let _ = aux fds
  in bat.bat_fs_mu_list <- ori_fs_mu_list

and dtc_vds bat p_dt_list = function
    [] ->
      let _ = push_bat_ictx [] bat in
      let rec aux bat = function
	  [] -> ()
	| (p, dt) :: p_dt_list ->
	    let (ictx, dt) = C.open_dt [] dt in
	    let _ = bat.bat_ictx <- ictx @ bat.bat_ictx in
	    let _ =
	      bat.bat_ubivlist <- ubivlist_of_ictx (bat.bat_ubivlist) ictx in
	    let _ = P.bat_of_pat bat dt p
	    in aux bat p_dt_list
      in aux bat p_dt_list
  | vd :: vds ->
      let dt = dto_exp bat vd.vd_exp
      in dtc_vds bat ((vd.vd_pat, dt) :: p_dt_list) vds

and dtc_decls bat = function
    [] -> ()
  | Fdecl fds :: rest ->
      let _ = dtc_fds bat fds in dtc_decls bat rest
  | Vdecl vds :: rest ->
      let _ = dtc_vds bat [] vds in dtc_decls bat rest
  | _ :: rest -> dtc_decls bat rest

let dtc_program program =
  let bat =
    { bat_ictx = []; bat_ubivlist = []; bat_fs_mu_list = [];
      bat_tclist = []; bat_ictx_tclist_list = []; } in
  let _ = dtc_decls bat program in
  let tc = tc_of_bat bat
  in tc :: bat.bat_tclist
