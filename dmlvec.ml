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

(* dmlvec: solve the index contrants *)

open Dmlsyn
module G = Dmlglo
module C = Dmlcop
module D = Dmldeb
module A = Array

let bool_ind = function
    Ifun("<", _) -> true
  | Ifun("<=", _) -> true
  | Ifun(">", _) -> true
  | Ifun(">=", _) -> true
  | Ifun("=", _) -> true
  | Ifun("<>", _) -> true
  | Ifun("&&", _) -> true
  | Ifun("||", _) -> true
  | _ -> false

let rec ipeq res = function
    (Ifun ("<", [ind1; ind2]), true) -> IPlt (ind1, ind2) :: res
  | (Ifun ("<", [ind1; ind2]), false) -> IPgte (ind1, ind2) :: res
  | (Ifun ("<=", [ind1; ind2]), true) -> IPlte (ind1, ind2) :: res
  | (Ifun ("<=", [ind1; ind2]), false) -> IPgt (ind1, ind2) :: res
  | (Ifun (">", [ind1; ind2]), true) -> IPgt (ind1, ind2) :: res
  | (Ifun (">", [ind1; ind2]), false) -> IPlte (ind1, ind2) :: res
  | (Ifun (">=", [ind1; ind2]), true) -> IPgte (ind1, ind2) :: res
  | (Ifun (">=", [ind1; ind2]), false) -> IPlt (ind1, ind2) :: res
  | (Ifun ("<>", [ind1; ind2]), true) -> IPneq (ind1, ind2) :: res
  | (Ifun ("<>", [ind1; ind2]), false) -> IPeq (ind1, ind2) :: res
  | (Ifun ("=", [ind1; ind2]), true) -> IPeq (ind1, ind2) :: res
  | (Ifun ("=", [ind1; ind2]), false) -> IPneq (ind1, ind2) :: res
  | (Ifun ("&&", [ind1; ind2]), true) ->
      let res = ipeq res (ind1, true) in ipeq res (ind2, true)
  | (Ifun ("&&", [ind1; ind2]), false) ->
      IPdisj [IPeq (ind1, Iint 0); IPeq (ind1, Iint 0)] :: res
  | (Ifun ("||", [ind1; ind2]), true) ->
      IPdisj [IPeq (ind1, Iint 1); IPeq (ind1, Iint 1)] :: res
  | (Ifun ("||", [ind1; ind2]), false) ->
      let res = ipeq res (ind1, false) in ipeq res (ind2, false)
  | (ind, _) -> G.abort ("unknown index function: " ^ (D.ind_pr ind))

let bool_eq iplist (ind, ind') =
  match bool_ind ind, bool_ind ind' with
    (true, false) -> begin
      match ind' with
      	Iint 1 -> ipeq iplist (ind, true)
      | Iint 0 -> ipeq iplist (ind, false)
      | _ -> G.abort ("iplist_of_ictx: IPeq: not a boolean: " ^
		      (D.ind_pr ind'))
    end
  | (false, true) -> begin
      match ind with
      	Iint 1 -> ipeq iplist (ind', true)
      | Iint 0 -> ipeq iplist (ind', false)
      | _ -> G.abort ("iplist_of_ictx: IPeq: not a boolean: " ^
		      (D.ind_pr ind))
    end
  | (true, true) -> G.sorry ("bool_eq: " ^
			     (D.ind_pr ind) ^ " = " ^ (D.ind_pr ind'))
  | (false, false) -> IPeq (ind, ind') :: iplist

let rec iplist_of_ictx iplist = function
    [] -> iplist
  | IDvar ubiv :: rest ->
      let iplist = C.iplist_of_isort (I_u ubiv) iplist (ubiv.ubiv_sort)
      in iplist_of_ictx iplist rest
  | IDprop ip :: rest -> begin
      match ip with
	IPeq (ind, ind') ->
	  let iplist = bool_eq iplist (ind, ind')
	  in iplist_of_ictx iplist rest
      |	IPneq (ind, ind') ->
	  if bool_ind ind' then
	    let iplist =
	      match ind with
	      	Iint 0 -> ipeq iplist (ind', true)
	      | Iint 1 -> ipeq iplist (ind', false)
	      | _ -> G.abort ("iplist_of_ictx: IPneq: not a boolean: " ^
			      (D.ind_pr ind'))
	    in iplist_of_ictx iplist rest
	  else iplist_of_ictx (ip :: iplist) rest
      |	_ -> iplist_of_ictx (ip :: iplist) rest
  end

let rec neg_ip (res: iprop list) = function
    IPlt (ind, ind') ->  IPgte (ind, ind') :: res
  | IPlte (ind, ind') -> IPgt (ind, ind') :: res
  | IPgt (ind, ind') -> IPlte (ind, ind') :: res
  | IPgte (ind, ind') -> IPlt (ind, ind') :: res
  | IPneq (ind, ind') -> IPeq (ind, ind') :: res
  | IPeq (ind, ind') -> IPneq (ind, ind') :: res
  | IPdisj iplist -> neg_ip_list res iplist
  | IPconj iplist -> IPdisj (neg_ip_list [] iplist) :: res
  | ip -> G.abort ("neg_ip: " ^ (D.ip_pr ip))

and neg_ip_list res = function
    [] -> res
  | ip :: iplist ->
      let res = neg_ip res ip in neg_ip_list res iplist

let rec neg_iplist (cond: iprop list) (res: iprop list list) = function
    [] -> res
  | ip :: rest -> begin
      match ip with
      	IPeq (ind, ind') ->
	  if bool_ind ind then
	    let rest =
	      match ind' with
	      	Iint 1 -> ipeq rest (ind, false)
	      | Iint 0 -> ipeq rest (ind, true)
	      | _ -> G.abort ("neg_iplist: IPeq: not a boolean: " ^ (D.ind_pr ind'))
	    in neg_iplist cond res rest
	  else neg_iplist cond ((IPneq (ind, ind') :: cond) :: res) rest
      | IPconj iplist -> neg_iplist cond res (iplist @ rest)
      | IPdisj iplist -> neg_iplist cond ((neg_ip_list cond iplist) :: res) rest
      | IPuni (ictx, iplist) ->
	  let newcond = iplist_of_ictx cond ictx in
	  let newres = neg_iplist newcond [] iplist
	  in neg_iplist cond (newres @ res) rest
      |	ip -> neg_iplist cond ((neg_ip cond ip) :: res) rest
  end

let ivs_of_iplist iplist =
  let counter = ref 0 in
  let rec aux_ind ivs ips = function
      Ivar _ ->  G.abort ("ivs_of_iplist: aux_ind: Ivar")
    | I_u ubiv as ind -> begin
	match ubiv.ubiv_num with
	  0 -> (counter := !counter + 1;
	    	ubiv.ubiv_num <- !counter;
		(ubiv :: ivs, ips, ind))
	| _ -> (ivs, ips, ind)
      end
    | I_e ebiv -> begin
	match ebiv.ebiv_link with
	  Inolink -> G.abort ("ivs_of_iplist: aux_ind: unlinked ebiv: " ^
			      (D.ebiv_pr ebiv))
	| Ilinkto ind -> aux_ind ivs ips ind
      end
    | Iint _ as ind -> (ivs, ips, ind)
    | Ifun ("abs", [ind1]) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let ind2 = Ifun ("uminus", [ind1]) in
	let ubiv = C.new_ubiv ISint in
	let _ = (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	let ind = I_u ubiv in
        let ip1 = IPgte (ind, Iint 0) in
	let ip2 = IPdisj [IPeq (ind, ind1);IPeq (ind, ind2)]
	in (ubiv :: ivs, ip1 :: ip2 :: ips, ind)
    | Ifun ("/", [ind1; ind2]) as ind ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in begin
	  match ind2 with
	    Iint i -> begin
	      match i > 0 with
		true ->
	      	  let ubiv = C.new_ubiv ISint in
	      	  let _ =
		    (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	      	  let ind = Ifun("*", [I_u ubiv; Iint i]) in
	      	  let ip1 = IPgte (ind1, ind) in
	      	  let ip2 = IPlt (ind1, Ifun("+", [ind; Iint i]))
	      	  in (ubiv :: ivs, ip1 :: ip2 :: ips, I_u ubiv)
	      |	false ->
		  G.abort ("ivs_of_iplist: aux_ind: division by a negative: " ^
			   D.ind_pr ind)
	    end
	  | _ ->
	      G.abort ("ivs_of_iplist: aux_ind: division by a nonconstant:" ^
		       D.ind_pr ind)
	end
    | Ifun ("mod", [ind1; ind2]) as ind ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in begin
	  match ind2 with
	    Iint i -> begin
	      match i > 0 with
	      	true ->
		  let ubiv = C.new_ubiv ISint in
		  let _ =
		    (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
		  let ind = Ifun("*", [I_u ubiv; Iint i]) in
		  let ip1 = IPgte (ind1, ind) in
		  let ip2 = IPlt (ind1, Ifun("+", [ind; Iint i]))
		  in (ubiv :: ivs, ip1 :: ip2 :: ips, Ifun ("-", [ind1; ind]))
	      |	false -> G.abort ("ivs_of_iplist: aux_ind: modulo a negative")
  	    end
	  | _ -> G.abort ("ivs_of_iplist: aux_ind: modulo a nonconstant :" ^
			  D.ind_pr ind)
	end
    | Ifun ("max", [ind1; ind2]) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2 in
	let ubiv = C.new_ubiv ISint in
	let _ = (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	let ind = I_u ubiv in
	let ip1 = IPlte (ind1, ind) in
	let ip2 = IPlte (ind2, ind) in
	let ip3 = IPdisj[IPgte (ind1, ind); IPgte (ind2, ind)]
	in (ubiv :: ivs, ip1 :: ip2 :: ip3 :: ips, ind)
    | Ifun ("min", [ind1; ind2]) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2 in
	let ubiv = C.new_ubiv ISint in
	let _ = (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	let ind = I_u ubiv in
	let ip1 = IPgte (ind1, ind) in
	let ip2 = IPgte (ind2, ind) in
	let ip3 = IPdisj[IPlte (ind1, ind); IPlte (ind2, ind)]
	in (ubiv :: ivs, ip1 :: ip2 :: ip3 :: ips, ind)
    | Ifun ("=", [ind1; ind2]) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2 in
	let ubiv = C.new_ubiv ISint in
	let _ = (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	let ind = I_u ubiv in
	let ip1 =
	  IPdisj[IPgt (ind, Iint 0); IPlt (ind1, ind2); IPgt (ind1, ind2)] in
	let ip2 = IPdisj[IPlt (ind, Iint 1); IPlte (ind1, ind2)] in
	let ip3 = IPdisj[IPlt (ind, Iint 1); IPgte (ind1, ind2)]
	in (ubiv :: ivs, ip1 :: ip2 :: ip3 :: IPlte (ind, Iint 1) :: IPgte (ind, Iint 0) :: ips, ind)
    | Ifun ("<>", [ind1; ind2]) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2 in
	let ubiv = C.new_ubiv ISint in
	let _ = (counter := !counter + 1; ubiv.ubiv_num <- !counter) in
	let ind = I_u ubiv in
	let ip1 = IPdisj[IPgt (ind, Iint 0); IPlte (ind1, ind2)] in
	let ip2 = IPdisj[IPgt (ind, Iint 0); IPgte (ind1, ind2)] in
	let ip3 =
	  IPdisj[IPlt (ind, Iint 1); IPlt (ind1, ind2); IPgt (ind1, ind2)]
	in (ubiv :: ivs, ip1 :: ip2 :: ip3 :: IPlte (ind, Iint 1) :: IPgte (ind, Iint 0) :: ips, ind)
    | Ifun (name, indlist) as ind ->
	let (ivs, ips, indlist) = aux_ind_list ivs ips [] indlist
	in (ivs, ips, Ifun (name, indlist))

  and aux_ind_list ivs ips (res: index list) = function
      [] -> (ivs, ips, List.rev res)
    | ind :: rest ->
	let (ivs, ips, ind) = aux_ind ivs ips ind
	in aux_ind_list ivs ips (ind :: res) rest in
  let rec aux_ip ivs ips = function
      IPlt (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPlt (ind1, ind2))
    | IPlte (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPlte (ind1, ind2))
    | IPgt (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPgt (ind1, ind2))
    | IPgte (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPgte (ind1, ind2))
    | IPeq (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPeq (ind1, ind2))
    | IPneq (ind1, ind2) ->
	let (ivs, ips, ind1) = aux_ind ivs ips ind1 in
	let (ivs, ips, ind2) = aux_ind ivs ips ind2
	in (ivs, ips, IPneq (ind1, ind2))
    | IPconj iplist ->
	let (ivs, ips, iplist) = aux_ip_list ivs ips [] iplist
	in (ivs, ips, IPconj iplist)
    | IPdisj iplist ->
	let (ivs, ips, iplist) = aux_ip_list ivs ips [] iplist
	in (ivs, ips, IPdisj iplist)
    | IPuni _ -> G.abort ("ivs_of_iplist: aux_ip: IPuni")
  and aux_ip_list ivs ips res = function
      [] -> (ivs, ips, List.rev res)
    | ip :: rest ->
	let (ivs, ips, ip) = aux_ip ivs ips ip
	in aux_ip_list ivs ips (ip :: res) rest in
  let (ivs, ips, iplist) = aux_ip_list [] [] [] iplist
  in (ivs, ips @ iplist)

let rec untag_ivs = function
    [] -> ()
  | ubiv :: rest -> ubiv.ubiv_num <- 0; untag_ivs rest

let ivec_of_ip n ip =
  let rec aux_ind vec coef = function
      I_u ubiv -> let i = ubiv.ubiv_num in vec.(i) <- vec.(i) + coef
    | I_e ebiv -> begin
      match ebiv.ebiv_link with
	  Inolink -> G.abort ("vec_of_ip: aux_ind: I_e: unlinked ebiv")
	| Ilinkto ind -> aux_ind vec coef ind
      end
    | Iint i -> vec.(0) <- vec.(0) + i * coef
    | Ifun ("uminus", [ind]) -> aux_ind vec (-coef) ind
    | Ifun ("+", [ind1; ind2]) ->
	aux_ind vec coef ind1; aux_ind vec coef ind2
    | Ifun ("-", [ind1; ind2]) ->
	aux_ind vec coef ind1; aux_ind vec (-coef) ind2
    | Ifun ("*", [Iint i; ind]) -> aux_ind vec (i * coef) ind
    | Ifun ("*", [ind; Iint i]) -> aux_ind vec (i * coef) ind
    | ind -> G.abort ("vec_of_ip: aux_ind: " ^ (D.ind_pr ind)) in
  let rec aux_ip = function
      IPeq (ind1, ind2) ->
  	let vec = A.make (n + 1) 0
	in begin
	  aux_ind vec 1 ind1; aux_ind vec (-1) ind2; IVeq vec
	end
    | IPneq (ind1, ind2) ->
	let ivec1 = aux_ip (IPlt (ind1, ind2)) in
	let ivec2 = aux_ip (IPgt (ind1, ind2))
	in IVdisj [ivec1; ivec2]      
    | IPlt (ind1, ind2) ->
  	let vec = A.make (n + 1) 0
  	in begin
	  aux_ind vec (-1) ind1; aux_ind vec 1 ind2;
	  vec.(0) <- vec.(0) - 1; IVgte vec
	end
    | IPlte (ind1, ind2) ->
	let vec = A.make (n + 1) 0
	in aux_ind vec (-1) ind1; aux_ind vec 1 ind2; IVgte vec
    | IPgt (ind1, ind2) ->
  	let vec = A.make (n + 1) 0
	in begin
	  aux_ind vec 1 ind1; aux_ind vec (-1) ind2;
	  vec.(0) <- vec.(0) - 1; IVgte vec
	end
    | IPgte (ind1, ind2) ->
	let vec = A.make (n + 1) 0
	in aux_ind vec 1 ind1; aux_ind vec (-1) ind2; IVgte vec
    | IPconj iplist -> IVconj (List.map aux_ip iplist)
    | IPdisj iplist -> IVdisj (List.map aux_ip iplist)
    | ip -> G.abort ("vec_of_ip: aux_ip: " ^ (D.ip_pr ip))
  in aux_ip ip

let rec iveclist_of_iplist n res = function
    [] -> res
  | IPneq (ind1, ind2) :: rest ->
      let ivec1 = ivec_of_ip n (IPlt (ind1, ind2)) in
      let ivec2 = ivec_of_ip n (IPgt (ind1, ind2))
      in iveclist_of_iplist n (IVdisj [ivec1; ivec2] :: res) rest
  | IPconj ips :: rest -> iveclist_of_iplist n res (ips @ rest)
  | IPdisj ips :: rest ->
      let ivecs = List.map (ivec_of_ip n) ips
      in iveclist_of_iplist n (IVdisj ivecs :: res) rest
  | ip :: rest ->
      let ivec = ivec_of_ip n ip
      in iveclist_of_iplist n (ivec :: res) rest

let main iplist =
  let iplistlist = neg_iplist [] [] iplist in
(*
  let _ = D.show_iplistlist iplistlist in
*)
  let aux iplist =
    let (ivs, ips) = ivs_of_iplist iplist in
    let n = List.length ivs in
    let iveclist = iveclist_of_iplist n [] ips in
    let _ = untag_ivs ivs
    in iveclist
  in List.map aux iplistlist
