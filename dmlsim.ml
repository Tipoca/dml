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

(* dmlsim: simplify generated type constraints *)

open Dmlsyn
module G = Dmlglo
module C = Dmlcop
module D = Dmldeb

exception Occurs_check

let rec occurs_check ubivlist = function
    I_u ubiv -> if List.memq ubiv ubivlist then () else raise Occurs_check
  | I_e ebiv ->
      let rec aux = function
	  [] -> ()
	| ubiv :: rest ->
	    if List.memq ubiv ubivlist then aux rest else raise Occurs_check
      in aux (ebiv.ebiv_ubiv)
  | Iint _ -> ()
  | Ifun (_, indlist) -> occurs_check_list ubivlist indlist
  | ind -> G.abort ("occurs_check: " ^ (D.ind_pr ind))

and occurs_check_list ubivlist = function
    [] -> ()
  | ind :: rest -> (occurs_check ubivlist ind; occurs_check_list ubivlist rest)

let rec sol_biv_met0 (res: iprop list) ictx = function
    [] -> res
  | ind :: indlist ->
      sol_biv_met0 (IPuni (ictx, [IPgte (ind, Iint 0)]) :: res) ictx indlist

let rec sol_biv_met (res: iprop list) ictx = function
    [], [] -> IPuni (ictx, [IPdisj []]) :: res
  | ind1 :: mu1, ind2 :: mu2 ->
      sol_biv_met
        (IPuni (ictx, [IPlte (ind1, ind2)]) :: res)
        (IDprop (IPeq (ind1, ind2)) :: ictx) (mu1, mu2)
  | _ ->  G.abort ("sol_biv_met: unequal length")

let rec sol_biv_ebiv (res: iprop list) ebiv ind' =
  match ind' with
    I_e ebiv' -> begin
      match ebiv'.ebiv_link with
	Ilinkto ind' -> sol_biv_ebiv res ebiv ind'
      |	Inolink -> begin
	  if ebiv == ebiv' then res
	  else try
      	    occurs_check (ebiv.ebiv_ubiv) ind';
	    let res = C.iplist_of_isort (I_e ebiv) res (ebiv.ebiv_sort)
	    in (ebiv.ebiv_link <- Ilinkto ind'; res)
	  with Occurs_check ->
 	    let ind = I_e ebiv
	    in begin try
	      occurs_check (ebiv'.ebiv_ubiv) ind;
	      let res = C.iplist_of_isort ind' res (ebiv'.ebiv_sort)
	      in (ebiv'.ebiv_link <- Ilinkto ind; res)
	    with Occurs_check -> IPeq (ind, ind') :: res
	    end
      end
    end
  | _ -> begin try
      occurs_check (ebiv.ebiv_ubiv) ind';
      let res = C.iplist_of_isort (I_e ebiv) res (ebiv.ebiv_sort)
      in (ebiv.ebiv_link <- Ilinkto ind'; res)
  with Occurs_check -> IPeq (I_e ebiv, ind') :: res
  end

let rec sol_biv_eq (res: iprop list) = function
    I_e ebiv, ind' -> begin
      match ebiv.ebiv_link with
	Inolink -> sol_biv_ebiv res ebiv ind'
      |	Ilinkto ind -> sol_biv_eq res (ind, ind')
    end
  | ind, (I_e ebiv' as ind') -> begin
      match ebiv'.ebiv_link with
	Inolink -> begin try
	  occurs_check (ebiv'.ebiv_ubiv) ind;
	  let res = C.iplist_of_isort ind' res (ebiv'.ebiv_sort)
	  in (ebiv'.ebiv_link <- Ilinkto ind; res)
	with Occurs_check -> IPeq (ind, ind') :: res end
      |	Ilinkto ind' -> sol_biv_eq res (ind, ind')
  end
  | ind, ind' -> IPeq (ind, ind') :: res
    
let rec sol_biv_ips (res: iprop list) = function
    [] -> res
  | IPeq (ind, ind') :: rest ->
      let res = sol_biv_eq res (ind, ind') in sol_biv_ips res rest
  | IPconj iplist :: rest -> sol_biv_ips res (iplist @ rest)
  | ip :: rest -> sol_biv_ips (ip :: res) rest

let rec solve_biv (res: iprop list) = function
    [] -> res
  | tc :: rest ->
      let res =
      	match tc with
	  TCmet0 mu -> sol_biv_met0 res [] mu
      	| TCmet (mu1, mu2) -> sol_biv_met res [] (mu1, mu2)
      	| TCips iplist -> sol_biv_ips res iplist
      	| TCuni (ictx, tclist) ->
	    let iplist = solve_biv [] tclist
	    in IPuni (ictx, iplist) :: res
	| tc -> G.abort ("solve_biv: " ^ (D.tc_pr tc))
      in solve_biv res rest

let btv_elim = ref false

let sol_btv_ind (res: iprop list) (ind, ind') = sol_biv_eq res (ind, ind')

let rec sol_btv_ind_list (res: iprop list) = function
    [], [] -> res
  | ind :: rest, ind' :: rest' ->
      let res = sol_btv_ind res (ind, ind')
      in sol_btv_ind_list res (rest, rest')
  | _ -> G.abort ("sol_btv_ind_list: unequal length")

let rec sol_btv_eq (res: tc list) (dt, dt') =
  match (dt.dt_dsc, dt'.dt_dsc) with
    DT_e btv, tdsc' -> begin
      match btv.btv_dtlink with
	DTnolink -> begin
	  btv_elim := true;
	  match tdsc' with
	    DT_e btv' ->
	      if btv == btv' then res
	      else (btv.btv_dtlink <- DTlinkto dt'; res)
	  | _ -> (btv.btv_dtlink <- DTlinkto dt'; res)
	end
      |	DTlinkto dt -> sol_btv_eq res (dt, dt')
  end
  | tdsc, DT_e btv' -> begin
      match btv'.btv_dtlink with
	DTnolink -> (btv_elim := true; btv'.btv_dtlink <- DTlinkto dt; res)
      |	DTlinkto dt' -> sol_btv_eq res (dt, dt')
  end
  | tdsc, tdsc' -> sol_btv_eq_dsc res (tdsc, tdsc')

and sol_btv_eq_dsc (res: tc list) = function
    DT_u btv, DT_u btv' ->
      if btv == btv' then res
      else G.abort ("sol_btv_eq_dsc: different type variables")
  | DT_nam(dtlist, tcon, indlist), DT_nam(dtlist', tcon', indlist') ->
      if tcon == tcon' then
	let iplist = sol_btv_ind_list [] (indlist, indlist') in
	let res = TCips iplist :: res
	in sol_btv_eq_list res (dtlist, dtlist')
      else G.abort ("sol_btv_eq: DT_nam: " ^
		    (D.tcon_pr tcon) ^ " <> " ^ (D.tcon_pr tcon'))
  | DTtup dtlist, DTtup dtlist' -> sol_btv_eq_list res (dtlist, dtlist')
  | DTfun (dt1, dt2), DTfun (dt1', dt2') ->
      let res =
	sol_btv_eq res (dt1', dt1) in sol_btv_eq res (dt2, dt2')
  | tdsc, tdsc' -> G.abort ("sol_btv_eq_dsc: " ^
			    (D.dt_dsc_pr tdsc) ^ " <> " ^ (D.dt_dsc_pr tdsc'))

and sol_btv_eq_list (res: tc list) = function
    [], [] -> res
  | dt :: dtlist, dt' :: dtlist' ->
      let res = sol_btv_eq res (dt, dt')
      in sol_btv_eq_list res (dtlist, dtlist')
  | _ -> G.abort ("sol_btv_eq_list: unequal length")

(* the following two functions are highly heuristic! *)
let sol_btv_heu_l btv dt dt' res = (btv.btv_dtlink <- DTlinkto dt'; res)

let sol_btv_heu_r dt btv' dt' res =
  match dt.dt_is_e with
    true -> (btv'.btv_dtlink <- DTlinkto dt; res)
  | false -> TCco (dt, dt') :: res

let rec sol_btv_co ubivlist (res: tc list) (dt, dt') =
  match (dt.dt_dsc, dt'.dt_dsc) with
    DT_e btv, _ -> begin
      match btv.btv_dtlink with
	DTlinkto dt -> sol_btv_co ubivlist res (dt, dt')
      |	DTnolink -> sol_btv_heu_l btv dt dt' res
  end
  | _, DT_e btv' -> begin
      match btv'.btv_dtlink with
	DTlinkto dt' -> sol_btv_co ubivlist res (dt, dt')
      |	DTnolink -> sol_btv_heu_r dt btv' dt' res
  end
  | _ -> sol_btv_co_aux ubivlist res (dt, dt')

and sol_btv_co_aux ubivlist res (dt, dt') = 
  match (dt.dt_dsc, dt'.dt_dsc) with
    _, DTlam (tctx', dt') -> sol_btv_co ubivlist res (dt, dt')
  | DTlam (tctx, dt), _ ->
      let _ = C.bind_tctx tctx in
      let dt = C.cp_dt dt in
      let _ = C.unbind_tctx tctx
      in sol_btv_co ubivlist res (dt, dt')
  | DT_exi (ictx, dt), _ ->
      let ubivlist = ubivlist_of_ictx ubivlist ictx in
      let tclist = sol_btv_co ubivlist [] (dt, dt')
      in TCuni (ictx, tclist) :: res
  | _, DT_uni (ictx, dt') ->
      let ubivlist = ubivlist_of_ictx ubivlist ictx in
      let tclist = sol_btv_co ubivlist [] (dt, dt')
      in TCuni (ictx, tclist) :: res
  | _, DT_exi (ictx, dt') ->
      let (_, iplist) = C.bind_ictx ubivlist ([], []) ictx in
      let dt' = C.cp_dt dt' in
      let _ = C.unbind_ictx ictx
      in sol_btv_co ubivlist (TCips iplist :: res) (dt, dt')
  | DT_uni (ictx, dt), _ ->
      let (_, iplist) = C.bind_ictx ubivlist ([], []) ictx in
      let dt = C.cp_dt dt in
      let _ = C.unbind_ictx ictx
      in sol_btv_co ubivlist (TCips iplist :: res) (dt, dt')
  | DT_u btv, DT_u btv' ->
      if btv = btv' then res
      else G.abort ("sol_btv_co_aux: DT_u: " ^
		    (D.btv_d_pr btv) ^ " <> " ^ (D.btv_d_pr btv'))
  | DT_nam (dtlist, tcon, indlist), DT_nam(dtlist', tcon', indlist') ->
      if tcon == tcon' then
	let res =
	  match indlist, indlist' with
	    _, [] -> res (* type closure *)
	  | _ ->
(*
	      let _ = print_string ("DT_nam: " ^ (D.tcon_pr tcon) ^ "\n") in
	      let _ = print_string ("indlist: " ^ (D.ind_list_pr indlist) ^ "\n") in
	      let _ = print_string ("indlist': " ^ (D.ind_list_pr indlist') ^ "\n") in
*)
	      let iplist = sol_btv_ind_list [] (indlist, indlist')
	      in TCips iplist :: res in
 	if (tcon == G.array_tc) then
	  sol_btv_eq_list res (dtlist, dtlist')
        else sol_btv_co_list ubivlist res (dtlist, dtlist')
      else G.abort ("sol_btv_co_aux: DT_nam: " ^
		    (D.tcon_pr tcon) ^ " <> " ^ (D.tcon_pr tcon'))
  | DTtup dtlist, DTtup dtlist' -> sol_btv_co_list ubivlist res (dtlist, dtlist')
  | DTfun (dt1, dt2), DTfun (dt1', dt2') ->
      let res = sol_btv_co ubivlist res (dt1', dt1)
      in sol_btv_co ubivlist res (dt2, dt2')
  | tdsc, tdsc' -> G.abort ("sol_btv_co_aux: " ^
			    (D.dt_dsc_pr tdsc) ^ " <> " ^ (D.dt_dsc_pr tdsc'))

and sol_btv_co_list ubivlist (res: tc list) = function
    [], [] -> res
  | dt :: dtlist, dt' :: dtlist' ->
      let res = sol_btv_co ubivlist res (dt, dt')
      in sol_btv_co_list ubivlist res (dtlist, dtlist')
  | _ -> G.abort ("sol_btv_co_list: unequal length")

let rec solve_btv ubivlist (res: tc list) = function
    [] -> List.rev res
  | tc :: rest ->
      let res =
      	match tc with
	  TCco (dt, dt') -> sol_btv_co ubivlist res (dt, dt')
      	| TCeq (dt, dt') -> sol_btv_eq res (dt, dt')
  	| TCmet0 _ -> tc :: res
	| TCmet _ -> tc :: res
  	| TCips _ -> tc :: res
  	| TCuni (ictx, tclist) ->
	    let ubivlist = ubivlist_of_ictx ubivlist ictx
	    in TCuni (ictx, solve_btv ubivlist [] tclist) :: res
      in solve_btv ubivlist res rest

let rec solve_btv_all tclist =
  let tclist = solve_btv [] [] tclist
  in if !btv_elim then 
    (btv_elim := false; solve_btv_all tclist)
  else tclist

let cons_bat_tc bat tc =
  let tclist = tc :: bat.bat_tclist
  in bat.bat_tclist <- tclist

let cons_bat_tcco bat (dt, dt') =
  let tclist = sol_btv_co (bat.bat_ubivlist) (bat.bat_tclist) (dt, dt')
  in bat.bat_tclist <- tclist
