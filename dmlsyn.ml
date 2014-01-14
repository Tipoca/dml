(*******************************************************************)
(*                                                                 *)
(*                         Dependent ML                            *)
(*                                                                 *)
(*                       (c) Hongwei Xi                            *)
(*                           July 2000                             *)
(*                                                                 *)
(*                   University of Cincinnati                      *)
(*                                                                 *)
(*                Distributed by permission only.                  *)
(*                                                                 *)
(*******************************************************************)
(* dmlsyn data structures for the syntax tree *)

module L = Dmlloc

exception Fatal of string

let fatal msg = raise (Fatal msg)

type index =
    Ivar of string
  | I_u of u_bound_ivar
  | I_e of e_bound_ivar
  | Iint of int
  | Ifun of string * index list

and ilink = Inolink | Ilinkto of index

and iprop =
    IPlt of index * index
  | IPlte of index * index
  | IPgt of index * index
  | IPgte of index * index
  | IPeq of index * index
  | IPneq of index * index
  | IPconj of iprop list
  | IPdisj of iprop list
  | IPuni of icontext * iprop list
    (* for an internal use: solve_dt_co: DTexi *)

and isort =
    ISint
  | ISnam of string
  | IS_nam of isort_abbrev
  | ISsub of u_bound_ivar * iprop (* { a:gamma | P } *)

and isort_abbrev = {
    isab_nam: string;
    isab_def: isort
  } 

and u_bound_ivar = {
    ubiv_name: string;
    mutable ubiv_link: ilink;
    ubiv_sort: isort;
    mutable ubiv_num: int
  } 

and e_bound_ivar = {
    ebiv_name: string;
    mutable ebiv_link: ilink;
    ebiv_sort: isort;
    mutable ebiv_ubiv: u_bound_ivar list
  } 

and ivar_d = IDvar of u_bound_ivar | IDprop of iprop

and icontext = ivar_d list

and metric = index list

type etype =
    ETvar of string
  | ET_u of bound_tvar
  | ET_e of bound_tvar
  | ETnam of etype list * string
  | ET_nam of etype list * type_cstr
  | ETtup of etype list
  | ETfun of etype * etype
  | ETlam of tcontext * etype

and dtype = {
    dt_dsc: dtype_dsc;
    dt_et: etype;
    dt_is_e: bool;
    dt_loc: L.location
  } 

and dtype_dsc =
    DTvar of string
  | DT_u of bound_tvar
  | DT_e of bound_tvar
  | DTnam of dtype list * string * index list
  | DT_nam of dtype list * type_cstr * index list
  | DTtup of dtype list
  | DTexi of icontext * dtype
  | DT_exi of icontext * dtype
  | DTuni of icontext * dtype
  | DT_uni of icontext * dtype
  | DTfun of dtype * dtype
  | DTmet of metric * dtype
  | DTlam of tcontext * dtype

and bound_tvar = {
    btv_name: string;
    mutable btv_dtlink: dtlink;
    mutable btv_etlink: etlink
  }

and tvar_d = TDvar of bound_tvar

and tcontext = tvar_d list

and dtlink = DTnolink | DTlinkto of dtype 

and etlink = ETnolink | ETlinkto of etype 

and var_d = {
    var_nam: string;
    mutable var_typ: dtype option;
  } 

and fun_d = {
    fun_nam: string;
    mutable fun_typ: dtype option;
  } 

and con_d = {
    con_nam: string;
    con_typ: dtype
  } 

and type_cstr = {
    tycon_nam: string;
    mutable tycon_con: con_d list option; (* constructors *)
    mutable tycon_des: fun_d list option; (* destructors *)
    tycon_tpa: tcontext;
    tycon_ind: icontext * index list
  }

let et_of_dt dt = dt.dt_et

let etlist_of_dtlist dtlist = List.map et_of_dt dtlist

let rec era_dt_dsc = function
    DTvar name -> ETvar name
  | DTnam (dtlist, name, _) -> ETnam (etlist_of_dtlist dtlist, name)
  | DT_nam (dtlist, tcon, _) -> ET_nam (etlist_of_dtlist dtlist, tcon)
  | DTtup dtlist -> ETtup (etlist_of_dtlist dtlist)
  | DTexi (_, dt) -> et_of_dt dt
  | DT_exi (_, dt) -> et_of_dt dt
  | DTuni (_, dt) -> et_of_dt dt
  | DT_uni (_, dt) -> et_of_dt dt
  | DTfun (dt1, dt2) -> ETfun (et_of_dt dt1, et_of_dt dt2)
  | DTmet (_, dt) -> et_of_dt dt
  | DTlam (tctx, dt) -> ETlam (tctx, et_of_dt dt)
  | DT_u btv -> ET_u btv
  | DT_e btv -> begin
      match btv.btv_dtlink with
        DTnolink -> ET_e btv
      | DTlinkto dt -> et_of_dt dt
    end

let is_era dt = dt.dt_is_e

let rec is_era_list = function
    [] -> true
  | dt :: rest -> (is_era dt) && (is_era_list rest)

let rec is_era_nm_list = function
    [] -> true
  | (_, dt) :: rest -> (is_era dt) && (is_era_nm_list rest)

let rec is_era_dsc = function
    DTvar _ -> true
  | DTnam (dtlist, _, indlist) -> begin
      match indlist with
	[] -> is_era_list dtlist
      |	_ -> false
    end
  | DT_nam (dtlist, _, indlist) -> begin
      match indlist with
	[] -> is_era_list dtlist
      |	_ -> false
    end
  | DTtup dtlist -> is_era_list dtlist
  | DTexi _ -> false
  | DT_exi _ -> false
  | DTuni _ -> false
  | DT_uni _ -> false
  | DTfun (dt1, dt2) -> (is_era dt1) && (is_era dt2)
  | DTmet (_, dt) -> is_era dt
  | DTlam (_, dt) -> is_era dt
  | DT_u _ -> true
  | DT_e btv -> begin
      match btv.btv_dtlink with
        DTnolink -> true
      | DTlinkto dt -> is_era dt
    end

let mkdt tdsc = {
  dt_dsc = tdsc;
  dt_is_e = is_era_dsc tdsc;
  dt_et = era_dt_dsc tdsc;
  dt_loc = L.symbol_loc ()
} 

let mkdt_no_loc tdsc = {
  dt_dsc = tdsc;
  dt_is_e = is_era_dsc tdsc;
  dt_et = era_dt_dsc tdsc;
  dt_loc = L.none_loc
}

let mkdt_nam (dts, name, inds) =
  match name with
    "unit" -> mkdt (DTtup [])
  | _ -> mkdt (DTnam (dts, name, inds))

let mkdt_tup = function
    [dt] -> dt
  | dts -> mkdt (DTtup dts)

let rec dt_of_et = function
    ETvar name -> mkdt_no_loc (DTvar name)
  | ET_u btv -> mkdt_no_loc (DT_u btv)
  | ET_e btv -> mkdt_no_loc (DT_e btv)
  | ETnam (etlist, name) ->
      mkdt_no_loc (DTnam (List.map dt_of_et etlist, name, []))
  | ET_nam (etlist, tcon) ->
      mkdt_no_loc (DT_nam (List.map dt_of_et etlist, tcon, []))
  | ETtup etlist -> mkdt_no_loc (DTtup (List.map dt_of_et etlist))
  | ETfun (et1, et2) -> mkdt_no_loc (DTfun (dt_of_et et1, dt_of_et et2))
  | ETlam (tctx, et) -> mkdt_no_loc (DTlam (tctx, dt_of_et et))

type isort_d = {
    sd_nam: string;
    sd_def: isort;
  } 

type record_field = {
    rf_nam: string;
    rf_mut: bool;
    rf_typ: dtype
  } 

type record_d = {
    rd_nam: string;
    rd_tvs: tvar_d list;
    rd_ivs: ivar_d list;
    rd_ind: index list;
    rd_fds: record_field list
  }

type union_field = {
    uf_nam: string;
    uf_arg: dtype option;
    uf_res: index list;
    uf_qua: ivar_d list
  } 

type union_d = {
    ud_nam: string;
    ud_tvs: tvar_d list;
    ud_sts: isort list;
    ud_fds: union_field list
  }

type infixop = INFop of string

type constant =
    Cboo of bool
  | Ccha of char
  | Cflo of float
  | Cint of int
  | Cstr of string

type pattern = {
    pat_dsc: pat_dsc;
    pat_loc: L.location;
    mutable pat_dt: dtype option;
    mutable pat_et: etype option
  } 

and pat_dsc =
    Pvar of string
  | P_var of var_d
  | Pany
  | Pcst of constant
  | Pcstr of string * pattern
  | P_cstr_0 of con_d
  | P_cstr_1 of con_d * pattern
  | Ptup of pattern list
  | Pas of string * pattern
  | P_as of var_d * pattern

and expression = {
    exp_dsc: exp_dsc;
    exp_loc: L.location;
    mutable exp_dt: dtype option;
    mutable exp_et: etype option
  }

and exp_dsc =
    Evar of string
  | E_var of var_d
  | E_fun of fun_d
  | Ecst of constant
  | E_cstr of con_d
  | Eapp of expression * expression
  | Elet of decl list * expression
  | Ecas of expression * (pattern * expression) list
  | Efn of (pattern * expression) list
  | Etup of expression list
  | Eann of expression * dtype

and value_d = {
    vd_pat: pattern;
    vd_exp: expression
  } 

and function_d = {
    fd_nam: string;
    fd_tvs: tvar_d list;
    fd_typ: dtype option;
    fd_bod: (pattern list * expression) list;
  }

and decl =
    Fdecl of function_d list
  | Sdecl of isort_d
  | Udecl of union_d list
  | Vdecl of value_d list
  | VTdecl of var_d

let mk_function_d tvs f_ps_exp_list odt =
  let (nam, n) =
    match f_ps_exp_list with
      (f, (ps, _)) :: _ -> (f, List.length ps)
    | [] -> fatal ("mk_function_d: no clauses") in
  let _ = if n = 0 then fatal ("mk_function_d: no arguments") in
  let odt =
    match odt with
      None -> None
    | Some dt -> begin
	match tvs with
	  [] -> odt
	| _ -> Some (mkdt_no_loc (DTlam (tvs, dt)))
      end in
  let ps_exp_list =
    List.map
      (function (f, (ps, _ as ps_exp)) ->
         if (f = nam) && (List.length ps = n) then ps_exp
	 else fatal ("mk_function_d: unequal argument lengths"))
      f_ps_exp_list
  in { fd_nam = nam; fd_tvs = tvs;
       fd_typ = odt; fd_bod = ps_exp_list }

type opname = IPLT | IPGT | IPLTE | IPGTE | IPEQ | IPNEQ

let mk_infix_ind ind1 (INFop opname) ind2 = Ifun(opname, [ind1; ind2])

let mk_infix_bool_ind_seq
    (INFop opname1, ind1, indlist) (INFop opname2) ind2 =
  (INFop opname2, ind2, Ifun(opname2, [ind1; ind2]) :: indlist)

let ind_of_bool_ind_seq (_, _, indlist) =
  match indlist with
    [ind] -> ind
  | _ -> Ifun ("/\\", indlist)

let rec ip_of_ind = function
    Ifun ("/\\", indlist) -> IPconj (List.map ip_of_ind indlist)
  | Ifun ("\\/", indlist) -> IPdisj (List.map ip_of_ind indlist)	    
  | Ifun ("<", [ind1; ind2]) -> IPlt (ind1, ind2)
  | Ifun ("<=", [ind1; ind2]) -> IPlte (ind1, ind2)
  | Ifun (">", [ind1; ind2]) -> IPgt (ind1, ind2)
  | Ifun (">=", [ind1; ind2]) -> IPgte (ind1, ind2)
  | Ifun ("=", [ind1; ind2]) -> IPeq (ind1, ind2)
  | Ifun ("<>", [ind1; ind2]) -> IPneq (ind1, ind2)
  | Ifun (name, _) -> fatal ("ip_of_ind: fun: " ^ name)
  | _ -> fatal ("ip_of_ind: not fun" )

let to_ubiv name isort = {
  ubiv_name = name;
  ubiv_link = Inolink;
  ubiv_sort = isort;
  ubiv_num = 0
} 

let to_ebiv name ubivlist isort = {
  ebiv_name = name;
  ebiv_link = Inolink;
  ebiv_sort = isort;
  ebiv_ubiv = ubivlist
} 

let isnat = ISsub(to_ubiv "nat" ISint, IPgte(Ivar "nat", Iint 0))
let isbool = ISsub(to_ubiv "bool" ISint,
		  IPconj[IPgte(Ivar "bool", Iint 0);
			 IPlte(Ivar "bool", Iint 1)])

let is_nat =
  let ubiv = to_ubiv "nat" ISint
  in ISsub(ubiv, IPgte(I_u ubiv, Iint 0))

let is_pos =
  let ubiv = to_ubiv "pos" ISint
  in ISsub(ubiv, IPgt(I_u ubiv, Iint 0))

let is_neg =
  let ubiv = to_ubiv "neg" ISint
  in ISsub(ubiv, IPlt(I_u ubiv, Iint 0))

let isint_lr ind1 ind2 =
  let ubiv = to_ubiv "int_lr" ISint
  in ISsub(ubiv, IPconj [IPlt(ind1, Ivar "int_lr");
			 IPlt(Ivar "int_lr", ind2)])

let isint_lR ind1 ind2 =
  let ubiv = to_ubiv "int_lR" ISint
  in ISsub(ubiv, IPconj [IPlt(ind1, Ivar "int_lR");
			 IPlte(Ivar "int_lR", ind2)])

let isint_Lr ind1 ind2 =
  let ubiv = to_ubiv "int_Lr" ISint
  in ISsub(ubiv, IPconj [IPlte(ind1, Ivar "int_Lr");
			 IPlt(Ivar "int_Lr", ind2)])

let isint_LR ind1 ind2 =
  let  ubiv = to_ubiv "int_LR" ISint
  in ISsub(ubiv, IPconj [IPlte(ind1, Ivar "int_LR");
			 IPlte(Ivar "int_LR", ind2)])

let is_bool =
  let ubiv = to_ubiv "nat" ISint
  in ISsub(ubiv, IPconj[IPgte(I_u ubiv, Iint 0); IPlte(I_u ubiv, Iint 1)])

let to_btv name = {
  btv_name = name;
  btv_dtlink = DTnolink;
  btv_etlink = ETnolink
}

let dtnat_dsc =
  let ubiv = to_ubiv "nat" isnat
  in DTexi ([IDvar ubiv], mkdt_no_loc (DTnam([], "int", [Ivar "nat"])))

let dtint_lr_dsc ind1 ind2 =
  let ubiv = to_ubiv "int_lr" (isint_lr ind1 ind2)
  in DTexi ([IDvar ubiv], mkdt_no_loc (DTnam([], "int", [Ivar "int_lr"])))

let dtint_lR_dsc ind1 ind2 =
  let ubiv = to_ubiv "int_lR" (isint_lR ind1 ind2)
  in DTexi ([IDvar ubiv], mkdt_no_loc (DTnam([], "int", [Ivar "int_lR"])))

let dtint_Lr_dsc ind1 ind2 =
  let ubiv = to_ubiv "int_Lr" (isint_Lr ind1 ind2)
  in DTexi ([IDvar ubiv], mkdt_no_loc (DTnam([], "int", [Ivar "int_Lr"])))

let dtint_LR_dsc ind1 ind2 =
  let ubiv = to_ubiv "int_LR" (isint_LR ind1 ind2)
  in DTexi ([IDvar ubiv], mkdt_no_loc (DTnam([], "int", [Ivar "int_LR"])))

let fun_arg_dt dt =
  match dt.dt_dsc with
  | DTnam (dtlist, name, _) -> mkdt_no_loc (DTnam (dtlist, name, []))
  | DT_nam (dtlist, tcon, _) -> mkdt_no_loc (DT_nam (dtlist, tcon, []))
  |  _ -> dt

let punit = {
  pat_dsc = Ptup [];
  pat_loc = L.none_loc;
  pat_dt = None;
  pat_et = None
} 

let pbool b = {
  pat_dsc = Pcst (Cboo b);
  pat_loc = L.none_loc;
  pat_dt = None;
  pat_et = None
} 

let mkpat pdsc = {
  pat_dsc = pdsc;
  pat_loc = L.symbol_loc ();
  pat_dt = None;
  pat_et = None
}

let mkpat_tup = function
    [p] -> p
  | ps -> {
      pat_dsc = Ptup ps;
      pat_loc = L.symbol_loc ();
      pat_dt = None;
      pat_et = None
    }

let rec mkpat_list = function
    [] -> mkpat (Pvar "nil")
  | p :: ps ->
      let p1 = mkpat_list ps in
      let p2 = mkpat_tup [p; p1]
      in mkpat (Pcstr ("cons", p2))

let eunit = {
  exp_dsc = Etup [];
  exp_loc = L.none_loc;
  exp_dt = None;
  exp_et = None
}

let mkexp edsc = {
  exp_dsc = edsc;
  exp_loc = L.symbol_loc ();
  exp_dt = None;
  exp_et = None
}

let mkexp_tup = function
    [e] -> e
  | es -> {
      exp_dsc = Etup es;
      exp_loc = L.none_loc;
      exp_dt = None;
      exp_et = None
    }

let mkexp_if (e, e1, e2) =
  mkexp (Ecas (e, [(pbool true, e1); (pbool false, e2)]))

let rec mkexp_list = function
    [] -> {
      exp_dsc = Evar "nil";
      exp_loc = L.none_loc;
      exp_dt = None;
      exp_et = None
    } 
  | e :: es ->
      let e1 = mkexp_list es in
      let e2 = mkexp_tup [e; e1]
      in mkexp (Eapp (mkexp (Evar "cons"), e2))

let mk_infix_exp e1 (INFop opname) e2 =
  let e = mkexp_tup [e1; e2]
  in { exp_dsc = Eapp (mkexp (Evar opname), e);
       exp_loc = L.symbol_loc ();
       exp_dt = None;
       exp_et = None }

let rec ubivlist_of_ictx res = function
    [] -> res
  | IDvar ubiv :: rest -> ubivlist_of_ictx (ubiv :: res) rest
  | IDprop _ :: rest -> ubivlist_of_ictx res rest

type tc =
    TCco of dtype * dtype
  | TCeq of dtype * dtype
  | TCmet0 of metric
  | TCmet of metric * metric
  | TCips of iprop list
  | TCuni of icontext * tc list

type environment = {
    env_ictx: icontext;
    env_tctx: tcontext;
    env_def: (string * exp_dsc) list; (* defined functions and constructors *)
    env_tcs: type_cstr list; (* defined type constructors *)
    env_isab: isort_abbrev list; (* defined index sort abbreviations *)
  } 

type batch = {
    mutable bat_ictx: icontext;  (* local *)
    mutable bat_ubivlist: u_bound_ivar list;
    mutable bat_fs_mu_list: (string list * metric) list;
    mutable bat_tclist: tc list;
    mutable bat_ictx_tclist_list: (icontext * tc list) list;
  }

type ivec =
    IVgte of int array
  | IVeq of int array
  | IVconj of ivec list
  | IVdisj of ivec list
