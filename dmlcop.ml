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

(* Dmlcop: copy functions on index objects and types *)

open Dmlsyn

module G = Dmlglo
module D = Dmldeb

let tvar_counter = ref 0
and i_u_counter = ref 0
and i_e_counter = ref 0

let reset_counters () =
  (tvar_counter := 0; i_u_counter := 0; i_e_counter := 0)

let newbtv () = 
  let name = string_of_int !tvar_counter in
  let _ = tvar_counter := !tvar_counter + 1
  in to_btv name

let new_ubiv is =
  let name = string_of_int !i_u_counter in
  let _ = i_u_counter := !i_u_counter + 1
  in to_ubiv name is

let new_ebiv ubivlist is =
  let name = string_of_int !i_e_counter in
  let _ = i_e_counter := !i_e_counter + 1
  in to_ebiv name ubivlist is

let new_i_u is = I_u (new_ubiv is)

let new_i_e ubivlist is = I_e (new_ebiv ubivlist is)

let rec bind_tctx = function
    [] -> ()
  | TDvar btv :: rest ->
      let newbtv = newbtv () in
      let _ =
      	match btv.btv_etlink with
          ETnolink ->
	    btv.btv_etlink <- ETlinkto (ET_e newbtv)
      	| ETlinkto _ ->
	    G.abort ("bind_tctx: illegal btv: " ^ (D.btv_e_pr btv)) in
      let _ =
	match btv.btv_dtlink with
          DTnolink ->
	    let dt = mkdt_no_loc (DT_e newbtv)
	    in btv.btv_dtlink <- DTlinkto dt
      	| DTlinkto _ ->
	    G.abort ("bind_dtctx: illegal btv: " ^ (D.btv_d_pr btv))
      in bind_tctx rest

let rec unbind_tctx = function
    [] -> ()
  | TDvar btv :: rest ->
    let _ = btv.btv_etlink <- ETnolink in
    let _ = btv.btv_dtlink <- DTnolink
    in unbind_tctx rest

let rec cp_ind = function    
    I_u ubiv as ind -> begin
       match ubiv.ubiv_link with
         Inolink -> ind
       | Ilinkto ind -> cp_ind ind
    end
  | I_e ebiv as ind -> begin
      match ebiv.ebiv_link with
         Inolink -> ind
       | Ilinkto ind -> cp_ind ind
    end
  | Iint _ as ind -> ind
  | Ifun(name, indlist) -> Ifun(name, List.map cp_ind indlist)
  | ind -> G.abort ("cp_ind: " ^ (D.ind_pr ind))

and cp_ip = function
    IPlt (ind1, ind2) -> IPlt (cp_ind ind1, cp_ind ind2)
  | IPlte (ind1, ind2) -> IPlte (cp_ind ind1, cp_ind ind2)
  | IPeq (ind1, ind2) -> IPeq (cp_ind ind1, cp_ind ind2)
  | IPneq (ind1, ind2) -> IPneq (cp_ind ind1, cp_ind ind2)
  | IPgte (ind1, ind2) -> IPgte (cp_ind ind1, cp_ind ind2)
  | IPgt (ind1, ind2) -> IPgt (cp_ind ind1, cp_ind ind2)
  | IPconj iplist -> IPconj (List.map cp_ip iplist)
  | IPdisj iplist -> IPdisj (List.map cp_ip iplist)
  | ip -> G.abort ("cp_ip: " ^ (D.ip_pr ip))

and cp_is = function
    ISint as is -> is
  | IS_nam isab as is -> is
  | ISsub (ubiv, ip) ->
      let newubiv = cp_ubiv ubiv in
      let ip = cp_ip ip in
      let _ = ubiv.ubiv_link <- Inolink in ISsub(newubiv, ip)
  | ISnam name -> G.abort ("cp_is: ISnam: " ^ name)

and cp_ubiv ubiv = (* must unbind ubiv later!!! *)
  let is = cp_is ubiv.ubiv_sort in
  let newubiv = { ubiv with ubiv_sort=is } in
  let _ = ubiv.ubiv_link <- Ilinkto (I_u newubiv) in newubiv

let cp_opt_ind = function
    None -> None
  | Some ind -> Some (cp_ind ind)

let cp_mu mu = List.map cp_ind mu

let cp_omu = function
    None -> None
  | Some mu -> Some (cp_mu mu)

let rec bind_ictx ubivlist (ebivlist, iplist) = function
    [] -> (ebivlist, iplist)
  | IDvar ubiv :: rest -> begin
      match ubiv.ubiv_link with
        Inolink ->
        let ebiv = new_ebiv ubivlist (ubiv.ubiv_sort) in
        let _ = ubiv.ubiv_link <- Ilinkto (I_e ebiv)
	in bind_ictx ubivlist (ebiv :: ebivlist, iplist) rest
      | Ilinkto _ ->
	  G.abort ("bind_ictx: illegal ubiv: " ^ (D.ubiv_pr ubiv))
    end
  | IDprop ip :: rest ->
      bind_ictx ubivlist (ebivlist, cp_ip ip :: iplist) rest

let rec unbind_ictx = function
    [] -> () 
  | IDvar ubiv :: rest ->
      let _ = ubiv.ubiv_link <- Inolink in unbind_ictx rest
  | IDprop _ :: rest -> unbind_ictx rest

let rec unbind_ubivlist = function
    [] -> () 
  | ubiv :: rest ->
      let _ = ubiv.ubiv_link <- Inolink in unbind_ubivlist rest

(* The following code needs some attention! *)
(* After cp_ictx is done, unbind_ictx *must* be called *)
let cp_idecl = function
    IDvar ubiv ->
      let newubiv = cp_ubiv ubiv in
      let _ = ubiv.ubiv_link <- Ilinkto (I_u newubiv)
      in IDvar newubiv
  | IDprop ip -> IDprop (cp_ip ip)

let cp_ictx ictx = List.map cp_idecl ictx

let rec cp_et = function
    ET_u btv as et -> begin
      match btv.btv_etlink with
        ETnolink -> et
      | ETlinkto et -> et
     end
  | ET_e btv as et -> begin
      match btv.btv_etlink with
        ETnolink -> et
      | ETlinkto et -> cp_et et
     end
  | ET_nam (etlist, tcon) -> ET_nam (List.map cp_et etlist, tcon)
  | ETtup etlist -> ETtup (List.map cp_et etlist)
  | ETfun (et1, et2) -> ETfun(cp_et et1, cp_et et2)
  | et -> G.abort ("cp_et: impossible: " ^ (D.et_pr et))

and cp_nm_et (nm, et) = (nm, cp_et et)

let rec cp_dt dt =
  match dt.dt_dsc with
    DT_u btv -> begin
      match btv.btv_dtlink with
        DTnolink -> dt
      | DTlinkto dt -> dt
    end
  |  DT_e btv -> begin
      match btv.btv_dtlink with
        DTnolink -> dt
      | DTlinkto dt -> cp_dt dt
     end
  | _ -> {
      dt_dsc = cp_dt_dsc dt.dt_dsc;
      dt_et = cp_et dt.dt_et;
      dt_is_e = dt.dt_is_e;
      dt_loc = dt.dt_loc
    } 

and cp_dt_dsc = function
    DT_nam (dtlist, tc, indlist) ->
    let dtlist = List.map cp_dt dtlist in
    let indlist = List.map cp_ind indlist
    in DT_nam (dtlist, tc, indlist)
  | DTtup dtlist -> DTtup (List.map cp_dt dtlist)
  | DT_exi (ictx, dt) ->
    let newictx = cp_ictx ictx in
    let newdt = cp_dt dt in
    let _ = unbind_ictx ictx in DT_exi (newictx, newdt)
  | DT_uni (ictx, dt) ->
    let newictx = cp_ictx ictx in
    let newdt = cp_dt dt in
    let _ = unbind_ictx ictx in DT_uni (newictx, newdt)
  | DTfun (dt1, dt2) -> DTfun(cp_dt dt1, cp_dt dt2)
  | DTmet (mu, dt) -> DTmet (cp_mu mu, cp_dt dt)
  | tdsc -> G.abort ("cp_dt: impossible: " ^ (D.dt_dsc_pr tdsc))

let rec cp_vd_dt_list res = function
    [] -> List.rev res
  | (vd, dt) :: rest -> cp_vd_dt_list ((vd, cp_dt dt) :: res) rest

let rec iplist_of_isort ind (res: iprop list) is = 
  match is with
    ISint -> res
  | IS_nam isab -> iplist_of_isort ind res (isab.isab_def)
  | ISsub (ubiv, ip) ->
      let _ = ubiv.ubiv_link <- Ilinkto ind in
      let ip = cp_ip ip in
      let _ = ubiv.ubiv_link <- Inolink
      in iplist_of_isort ind (ip :: res) (ubiv.ubiv_sort)
  | ISnam name -> G.abort ("iplist_of_isort: ISnam: " ^ name)

let rec open_dt (res: icontext) dt =
  match dt.dt_dsc with
    DT_exi (ictx, dt) ->
      let newictx = cp_ictx ictx in
      let newdt = cp_dt dt in
      let _ = unbind_ictx ictx
      in open_dt (newictx @ res) newdt
  | DT_nam (dtlist, tc, []) ->
      let (ictx, indlist) = tc.tycon_ind in
      let newictx = cp_ictx ictx in
      let indlist = List.map cp_ind indlist in
      let _ = unbind_ictx ictx
      in (newictx @ res, mkdt_no_loc (DT_nam (dtlist, tc, indlist)))
  | DTtup dts ->
      let (res, dts) = open_dt_list res [] dts
      in (res, mkdt_no_loc (DTtup dts))
  | DT_e btv -> begin
      match btv.btv_dtlink with
	DTnolink -> G.abort ("open_dt: DT_e: btv has no link")
      |	DTlinkto dt -> open_dt res dt
    end
  | _ -> (res, dt)

and open_dt_list res res_dt = function
    [] -> (res, List.rev res_dt)
  | dt :: dts ->
      let (res, dt) = open_dt res dt
      in open_dt_list res (dt :: res_dt) dts
