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

(* dmlintern: translate syntax trees into internal representation *)

open Dmlsyn
module L = Dmlloc
module G = Dmlglo
module D = Dmldeb

let rec tcon_lookup name = function
    [] -> raise Not_found
  | tcon :: rest ->
      if name = tcon.tycon_nam then tcon else tcon_lookup name rest

let rec tvar_lookup name = function
    [] -> raise Not_found
  | TDvar ({btv_name=name'} as btv) :: tctx ->
    if name = name' then btv else tvar_lookup name tctx

let rec ivar_lookup name = function
    [] -> raise Not_found
  | IDprop _ :: ictx -> ivar_lookup name ictx
  | IDvar ({ubiv_name=name'} as ubiv) :: ictx ->
    if name = name' then ubiv else ivar_lookup name ictx

let rec trans_ind env = function
    Ivar name -> begin
      try let ubiv = ivar_lookup name (env.env_ictx) in I_u ubiv
      with Not_found -> raise (G.Unbound_index_variable name)
    end
  | I_u _ -> G.abort ("trans_ind: I_var: impossible!")
  | I_e _ -> G.abort ("trans_ind: I_exvar: impossible!")
  | Iint _ as ind -> ind
  | Ifun (name, indlist) ->
      Ifun (name, List.map (trans_ind env) indlist)

let rec trans_opt_ind env = function
    None -> None
  | Some ind -> Some (trans_ind env ind)

let rec trans_ip env =  function
    IPlt (ind1, ind2) -> IPlt (trans_ind env ind1, trans_ind env ind2) 
  | IPlte (ind1, ind2) -> IPlte (trans_ind env ind1, trans_ind env ind2)
  | IPeq (ind1, ind2) -> IPeq (trans_ind env ind1, trans_ind env ind2)
  | IPneq (ind1, ind2) -> IPneq (trans_ind env ind1, trans_ind env ind2)
  | IPgte (ind1, ind2) -> IPgte (trans_ind env ind1, trans_ind env ind2)
  | IPgt (ind1, ind2) -> IPgt (trans_ind env ind1, trans_ind env ind2)
  | IPconj iproplist -> IPconj (List.map (trans_ip env) iproplist)
  | IPdisj iproplist -> IPdisj (List.map (trans_ip env) iproplist)
  | IPuni (_, _) -> G.abort ("trans_ip: IPiml")

let rec isab_lookup name = function
    [] -> raise Not_found
  | isab :: rest ->
      if name = isab.isab_nam then isab else isab_lookup name rest

let rec trans_is env = function
    ISint -> ISint
  | ISnam name -> begin
      try IS_nam (isab_lookup name env.env_isab)
      with Not_found -> G.abort ("trans_is: ISnam: " ^ name)
  end
  | ISsub (ubiv, iprop) ->
      let ubiv = { ubiv with ubiv_sort=trans_is env ubiv.ubiv_sort } in
      let env = { env with env_ictx = IDvar ubiv :: env.env_ictx}
      in ISsub (ubiv, trans_ip env iprop)
  | IS_nam _ as is ->  G.abort ("trans_is: IS_nam: " ^ (D.isort_pr is))

let rec trans_ivd env = function
    IDvar ubiv -> IDvar { ubiv with ubiv_sort=trans_is env ubiv.ubiv_sort }
  | IDprop ip -> IDprop (trans_ip env ip)

let rec trans_ictx env result = function
    [] -> (List.rev result, env)
  | ivd :: rest ->
      let ivd = trans_ivd env ivd in
      let env = { env with env_ictx = ivd :: env.env_ictx}
      in trans_ictx env (ivd :: result) rest

let rec trans_et env = function
    ETvar name -> begin
      try
        let btv = tvar_lookup name (env.env_tctx) in ET_u btv
      with
        | Not_found -> raise (G.Unbound_type_variable name)
    end
  | ETnam (etlist, name) ->
      let tcon =
	try tcon_lookup name env.env_tcs
	with Not_found -> raise (G.Undeclared_type_constructor name) in
      ET_nam (List.map (trans_et env) etlist, tcon)
  | ETtup etlist -> ETtup (List.map (trans_et env) etlist)
  | ETfun (et1, et2) -> ETfun (trans_et env et1, trans_et env et2)
  | ETlam (tctx, et) ->
      let env = { env with env_tctx = tctx @ env.env_tctx }
      in ETlam (tctx, trans_et env et)
  | et -> G.abort ("trans_et: " ^ (D.et_pr et))

let trans_metric env mu = List.map (trans_ind env) mu

let rec trans_dt env ({dt_dsc=tdsc; dt_et=et} as dt) =
  { dt with
    dt_dsc = trans_dt_dsc env tdsc;
    dt_et = trans_et env et
  }

and trans_opt_dt env = function
    None -> None
  | Some dt -> Some (trans_dt env dt)

and trans_dt_dsc env = function
    DTvar name -> begin
      try
        let btv = tvar_lookup name (env.env_tctx) in DT_u btv
      with
        | Not_found -> raise (G.Unbound_type_variable name)
    end
  | DTnam (dtlist, name, indlist) ->
      let tcon =
	try tcon_lookup name env.env_tcs
	with Not_found -> raise (G.Undeclared_type_constructor name) in
      let dtlist = List.map (trans_dt env) dtlist in
      let indlist =  List.map (trans_ind env) indlist
      in DT_nam (dtlist, tcon, indlist)
  | DTtup dtlist -> DTtup (List.map (trans_dt env) dtlist)
  | DTexi (ictx, dt) ->
      let (ictx, env) = trans_ictx env [] ictx in
      let dt = trans_dt env dt
    in DT_exi (ictx, dt)
  | DTuni (ictx, dt) ->
      let (ictx, env) = trans_ictx env [] ictx in
      let dt = trans_dt env dt
      in DT_uni (ictx, dt)
  | DTfun (dt1, dt2) -> DTfun (trans_dt env dt1, trans_dt env dt2)
  | DTmet (mu, dt) -> DTmet (trans_metric env mu, trans_dt env dt)
  | DTlam (tctx, dt) ->
      let env = { env with env_tctx = tctx @ env.env_tctx }
      in DTlam (tctx, trans_dt env dt)
  | tdsc -> G.abort ("trans_dt: " ^ (D.dt_dsc_pr tdsc))

let rec name_lookup name = function
    [] -> raise Not_found
  | (name', e) :: def ->
      if name = name' then e
      else name_lookup name def

let trans_sd env = function
    { sd_nam = name; sd_def = is } ->
      let is = trans_is env is in
      let isab = { isab_nam = name; isab_def = is } in
      let env = { env with env_isab = isab :: env.env_isab }
      in ({ sd_nam = name; sd_def = is }, env)

let rec tctx_to_tvs tvs = function
    [] -> List.rev tvs
  | TDvar btv :: tctx -> tctx_to_tvs (G.dt_u btv :: tvs) tctx

let trans_ufield tctx tcon env = function
    { uf_nam=name; uf_qua = ictx; uf_arg = odt; uf_res = indlist } ->
      let ori_ictx = env.env_ictx in
      let (ictx, env) = trans_ictx env [] ictx in
      let odt = trans_opt_dt env odt in
      let indlist = List.map (trans_ind env) indlist in
      let tvs = tctx_to_tvs [] tctx in
      let cstr_dt =
	match odt with
	  None -> G.dt_nam tvs tcon indlist
	| Some dt -> G.dt_fun dt (G.dt_nam tvs tcon indlist) in
      let cstr_dt = G.dt_uni ictx cstr_dt in
      let cstr_dt = G.dt_lam tctx cstr_dt in
      let cd = { con_nam = name; con_typ = cstr_dt } in
      let def = (name, E_cstr cd) :: env.env_def
      in ({ env with env_ictx = ori_ictx; env_def = def }, cd,
	  { uf_nam=name; uf_qua = ictx; uf_arg = odt; uf_res = indlist })

let rec trans_uflist tctx tcon env cdlist uflist = function
    [] -> (env, List.rev cdlist, List.rev uflist)
  | uf :: rest ->
      let (env, cd, uf) = trans_ufield tctx tcon env uf
      in trans_uflist tctx tcon env (cd :: cdlist) (uf :: uflist) rest

let ictx_indlist_of name islist =
  let rec aux n (ictx, indlist) = function
      [] -> (List.rev ictx, List.rev indlist)
    | is :: islist ->
      	let name_n = name ^ (string_of_int n) in
      	let ubiv = to_ubiv name_n is
      	in aux (n+1) (IDvar ubiv :: ictx, I_u ubiv :: indlist) islist
  in aux 0 ([], []) islist

let trans_uds env uds =
  let rec aux (tc_ud_list, tcs) = function
      [] -> (tc_ud_list, tcs)
    | ud :: uds ->
	let tctx = ud.ud_tvs in
	let name = ud.ud_nam in
      	let islist = List.map (trans_is env) ud.ud_sts in
      	let ictx_indlist = ictx_indlist_of name islist in
      	let tc = { tycon_nam=name; tycon_con=None; tycon_des=Some [];
		   tycon_tpa=env.env_tctx; tycon_ind=ictx_indlist } in
	let ud = { ud with ud_sts = islist }
	in aux ((tc, ud) :: tc_ud_list, tc :: tcs) uds in
  let (tc_ud_list, tcs) = aux ([], env.env_tcs) uds in
  let env = { env with env_tcs = tcs } in
  let ori_tctx = env.env_tctx in
  let rec aux (uds, env) = function
      [] ->  (uds, {env with env_tctx = ori_tctx})
    | (tc, ud) :: tc_ud_list ->
	let tctx = ud.ud_tvs in
	let env = {env with env_tctx = tctx @ ori_tctx} in
      	let (env, cdlist, uflist) =
	  trans_uflist tctx tc env [] [] ud.ud_fds in
      	let _ = tc.tycon_con <- Some cdlist in
	let ud = { ud with ud_fds=uflist }
	in aux (ud :: uds, env) tc_ud_list
  in aux ([], env) tc_ud_list


let rec trans_pat env ({pat_dsc=pdsc} as pat) =
  let (pdsc, env) = trans_pat_dsc env pdsc
  in ({ pat with pat_dsc=pdsc }, env)

and trans_pat_dsc env = function
    Pvar name -> begin
      try
	let e = name_lookup name (env.env_def)
      	in match e with
	  E_cstr cd -> (P_cstr_0 cd, env)
	| _ -> raise Not_found
      with Not_found ->
	let vd = {var_nam = name; var_typ = None} in
	let env = { env with env_def = (name, E_var vd) :: env.env_def }
	in (P_var vd, env)
    end
  | P_var _ -> G.abort ("trans_pat: P_var: impossible!")
  | Pany as pdsc -> (pdsc, env)
  | Pcst _ as pdsc -> (pdsc, env)
  | Pcstr (name, p) ->
      let e =
	try name_lookup name (env.env_def)
	with Not_found -> raise (G.Unbound_variable name) in
      begin
	match e with
	  E_cstr cd ->
	    let (p, env) = trans_pat env p
	    in (P_cstr_1 (cd, p), env)
	| _ -> raise (G.Unbound_variable name)
      end
  | Ptup ps ->
      let (ps, env) = trans_pats env [] ps
      in (Ptup ps, env)
  | Pas (name, p) ->
      let vd = {var_nam = name; var_typ = None} in
      let env = { env with env_def = (name, E_var vd) :: env.env_def } in
      let (p, env) = trans_pat env p
      in (P_as (vd, p), env)
  | pdsc -> G.abort ("trans_pat: pdsc: " ^ D.pat_dsc_pr pdsc)

and trans_pats env res = function
    [] -> (List.rev res, env)
  | p :: ps ->
      let (p, env) = trans_pat env p
      in trans_pats env (p :: res) ps

let rec trans_exp env ({exp_dsc=edsc} as exp) =
  try { exp with exp_dsc=trans_exp_dsc env edsc }
  with G.Unbound_variable name ->
     let _ = L.print_loc exp.exp_loc in
     let _ = G.print_line ("Variable " ^ name ^ " is unbound")
     in G.abort ("trans_exp: " ^ (D.exp_pr exp))

and trans_exp_dsc env = function
    Evar name -> begin
      try name_lookup name (env.env_def)
      with Not_found -> raise (G.Unbound_variable name)
    end
  | Ecst _ as e -> e
  | Eapp (e1, e2) -> Eapp (trans_exp env e1, trans_exp env e2)
  | Etup es -> Etup (List.map (trans_exp env) es)
  | Ecas (e, p_e_list) ->
      let e = trans_exp env e in
      let p_e_list = List.map (trans_pat_exp env) p_e_list
      in Ecas (e, p_e_list)
  | Efn p_e_list -> Efn (List.map (trans_pat_exp env) p_e_list)
  | Elet (decls, e) ->
      let (decls, env) = trans_decls env [] decls
      in Elet (decls, trans_exp env e)
  | Eann (e, dt) -> Eann (trans_exp env e, trans_dt env dt)
  | edsc -> G.abort ("trans_exp: " ^ (D.exp_dsc_pr edsc))

and trans_pat_exp env (p, e) =
  let (p, env') = trans_pat env p
  in (p, trans_exp env' e)

and trans_pats_exp env (ps, e) =
  let (ps, env') = trans_pats env [] ps
  in (ps, trans_exp env' e)

and trans_vd env {vd_pat = p; vd_exp = e} =
  let e =  trans_exp env e in
  let (p, env) = trans_pat env p
  in (env, {vd_pat = p; vd_exp = e})

and trans_vds env vds =
  let es = List.map (function vd -> vd.vd_exp) vds in
  let es = List.map (trans_exp env) es in
  let ps = List.map (function vd -> vd.vd_pat) vds in
  let (ps, env) = trans_pats env [] ps in
  let vds =
    List.map2 (function p -> function e -> {vd_pat=p; vd_exp=e}) ps es
  in (vds, env)

and trans_fd_typ env fd =
  let env = {env with env_tctx = fd.fd_tvs @ env.env_tctx} in
  let odt = trans_opt_dt env fd.fd_typ
  in { fd with fd_typ = odt}  

and trans_fd_bod env fd =
  let rec aux ictx = function
      ([], _) -> ictx
    | (p :: ps' as ps, dt) ->
      	match dt.dt_dsc with
          DT_uni (ictx', dt) -> aux (ictx' @ ictx) (ps, dt)
        | DTfun (_, dt) -> aux ictx (ps', dt)
	| DTlam (_, dt) -> aux ictx (ps, dt)
        | DTmet (_, dt) -> aux ictx (ps, dt)
      	| tdsc -> G.abort ("trans_fd_bod: aux: " ^ (D.dt_dsc_pr tdsc)) in
  let aux_opt ictx = function
      (_, None) -> ictx
    | (ps, Some dt) -> aux ictx (ps, dt) in
  let fd_bod = fd.fd_bod in
  let ps =
    match fd_bod with
      (ps, _) :: _ -> ps
    | [] -> G.abort ("trans_fd_bod: empty function body") in
  let env =
    {env with
      env_tctx = fd.fd_tvs @ env.env_tctx;
      env_ictx = aux_opt env.env_ictx (ps, fd.fd_typ)} in
  let ps_e_list = List.map (trans_pats_exp env) fd.fd_bod
  in { fd with fd_bod = ps_e_list }  

and trans_fds env fds =
  let fds = List.map (trans_fd_typ env) fds in
  let rec aux def = function
      [] -> def
    | fd :: fds ->
	let name = fd.fd_nam in
	let fund = { fun_nam = name; fun_typ = fd.fd_typ }
	in aux ((name, E_fun fund) :: def) fds in
  let env = { env with env_def = aux (env.env_def) fds } in
  let fds = List.map (trans_fd_bod env) fds
  in (fds, env)

and trans_decl env = function
    Fdecl fds ->
      let (fds, env) = trans_fds env fds
      in (Fdecl fds, env)
  | Sdecl sd ->
      let (sd, env) = trans_sd env sd
      in (Sdecl sd, env)
  | Udecl uds ->
      let (uds, env) = trans_uds env uds
      in (Udecl uds, env)
  | Vdecl vds ->
      let (vds, env) = trans_vds env vds
      in (Vdecl vds, env)
  | VTdecl vd ->
      let name = vd.var_nam in
      let odt = trans_opt_dt env vd.var_typ in
      let vd = {var_nam = name; var_typ = odt} in
      let env = {env with env_def = (name, E_var vd) :: env.env_def}
      in (VTdecl vd, env)

and trans_decls env res = function
    [] -> (List.rev res, env)
  | decl :: decls ->
      let (decl, env) = trans_decl env decl
      in trans_decls env (decl :: res) decls

let trans_program env program =
  trans_decls env [] program
