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

(* dmlsol: solve linear constraints *)

open Dmlsyn
module G = Dmlglo
module D = Dmldeb
module A = Array

exception Tautology
exception Contradiction

let rec gcd_nat m n =
  if n = 0 then m else gcd_nat n (m mod n)

let gcd m n =
  if m < 0 then
    if n < 0 then gcd_nat (-m) (-n) else gcd_nat (-m) n
  else
    if n < 0 then gcd_nat m (-n) else gcd_nat m n  

let ceiling i g = (* g is required to be a natural number *)
  if i > 0 then
    if i mod g = 0 then i / g else i / g + 1
  else i / g

let floor i g = (* g is required to be a natural number *)
  if i > 0 then i / g else if i mod g = 0 then i / g else i / g - 1

let vec_inspect_gte vec = (* yields the first non zero coefficient *)
(*
  let _ = print_string "vec_inspect:\n" in
  let _ = D.print_vec vec in
*)
  let length = A.length vec in
  let rec aux g i =
    if i = length then
      if g = 0 then
        if vec.(0) < 0 then raise Contradiction else raise Tautology
      else if g = 1 then ()
      else begin
	vec.(0) <- floor vec.(0) g;
	for i = 1 to length - 1 do
      	  vec.(i) <-  vec.(i) / g
    	done
      end
    else aux (gcd g (vec.(i))) (i+1) in
  aux 0 1 (* Notice: coefficients start at 1! *)

let vec_inspect_eq vec = (* yields the first non zero coefficient *)
(*
  let _ = print_string "vec_inspect:\n" in
  let _ = D.print_vec vec in
*)
  let length = A.length vec in
  let rec aux g i =
    if i = length then
      if g = 0 then
        if vec.(0) <> 0 then raise Contradiction else raise Tautology
      else if g = 1 then ()
      else
	let const = vec.(0) in
	let quot = floor const g
	in begin
	  if quot * g <> const then raise Contradiction;
	  vec.(0) <- quot;
	  for i = 1 to length - 1 do
      	    vec.(i) <-  vec.(i) / g
    	  done
	end
    else aux (gcd g (vec.(i))) (i+1) in
  aux 0 1 (* Notice: coefficients start at 1! *)

let vec_least_co vec = (* yields the least non zero coefficient *)
  let length = A.length vec in
  let rec aux l c i =
    if i = length || c = 1 then l
    else
      let l' = i in
      let c' = vec.(i) in
      if c' = 0 then aux l c (i+1)
      else if c = 0 then aux l' c' (i+1)
      else if abs (c) <= abs (c') then aux l c (i+1)
      else aux  l' c' (i+1)
  in aux 0 0 1

let vec_add n vec n' vec' =
  let length = A.length vec in
  let ans = A.make length 0 in
  let _ =
    for i = 0 to length - 1 do
      ans.(i) <-  n * vec.(i) + n' * vec'.(i)
    done
  in ans

let vec_combine i neg pos veclist =
  let vec = vec_add pos.(i) neg (- neg.(i)) pos in
  try
    let _ = vec_inspect_gte vec in vec :: veclist
  with Tautology -> veclist

let vec_split i (veclist: (int array) list) =
  let rec aux none_set neg_set pos_set = function
      [] -> (none_set, neg_set, pos_set)
    | vec :: rest ->
      if vec.(i) < 0 then aux none_set (vec :: neg_set) pos_set rest
      else if vec.(i) > 0 then aux none_set neg_set (vec :: pos_set) rest
           else aux (vec :: none_set) neg_set pos_set rest in
  let rec auxpos veclist neg = function
      [] -> veclist
    | pos :: rest -> auxpos (vec_combine i neg pos veclist) neg rest in
  let rec auxnegpos veclist pos_set = function
      [] -> veclist
    | neg :: rest -> auxnegpos (auxpos veclist neg pos_set) pos_set rest in
  let (none_set, neg_set, pos_set) = aux [] [] [] veclist
  in auxnegpos none_set pos_set neg_set

let solve_veclist (veclist: (int array) list) =
  let rec screen veclist = function
      [] -> List.rev veclist
    | vec :: rest ->
      	try let _ = vec_inspect_gte vec in screen (vec :: veclist) rest
      	with Tautology -> screen veclist rest in
  let rec sol = function
      vec :: _ as veclist -> sol (vec_split (vec_least_co vec) veclist)
    | _ -> () in
  let veclist = screen [] veclist in sol veclist
(*
  in match veclist with
    [] -> ()
  | vec :: veclist ->
      let veclist = Dmlrel.main vec veclist
      in sol (vec :: veclist)
*)
    
(*
let rec solve_veclistlist
    (rest: (int array) list list)
    (used: (int array) list list)
    (hdlist: (int array) list)
    (tllist: (int array) list list) =
  let _ =
    try solve_veclist hdlist
    with Contradiction -> solve_veclistlist_next rest used hdlist tllist
  in begin
    match rest with
      [] -> ()
    | [] :: rest -> raise Contradiction
    | (hd :: tl as veclist) :: rest ->
      	solve_veclistlist
	  rest (veclist :: used) (hd :: hdlist) (tl :: tllist)
  end

and solve_veclistlist_next rest used hdlist = function
    [] :: tllist ->
      solve_veclistlist_next
	(List.hd used :: rest) (List.tl used) (List.tl hdlist) tllist
  | (vec :: veclist) :: tllist  ->
      solve_veclistlist
	rest used (vec :: List.tl hdlist) (veclist :: tllist)
  | [] -> raise Contradiction
*)

exception Unsolved_constraint of (int * int array) list * (int array) list

let eq_vec (i, evec) vec =
  let ec = evec.(i) in
  let c = vec.(i) in
  if ec > 0 then vec_add ec vec (-c) evec
  else vec_add (-ec) vec c evec

let rec eq_vecs (i, evec) res = function
    [] -> res
  | vec :: vecs ->
      let vec = eq_vec (i, evec) vec
      in eq_vecs (i, evec) (vec :: res) vecs

let rec vec_eqs vec = function
    [] -> vec
  | (i, evec) :: eqs ->
      let vec = eq_vec (i, evec) vec
      in vec_eqs vec eqs

let rec solve_iveclist eqs veclist = function
    [] -> raise (Unsolved_constraint (eqs, veclist))
  | ivec :: rest -> begin
      match ivec with
	IVgte vec ->
	  let vec = vec_eqs vec eqs
	  in begin
	    solve_veclist (vec :: veclist);
	    solve_iveclist eqs (vec :: veclist) rest
	  end
      |	IVeq evec ->
	  let evec = vec_eqs evec eqs
	  in begin
	    try
	      let _ = vec_inspect_eq evec in
	      let i = vec_least_co evec in
	      let veclist = eq_vecs (i, evec) [] veclist
	      in begin
		solve_veclist veclist;
	      	solve_iveclist (eqs @ [(i, evec)]) veclist rest
	      end
	    with Tautology -> solve_iveclist eqs veclist rest
	  end
      | IVconj ivecs -> solve_iveclist eqs veclist (ivecs @ rest)
      |	IVdisj ivecs -> solve_iveclist_disj eqs veclist rest ivecs
    end

and solve_iveclist_disj eqs veclist rest = function
    [] -> raise Contradiction
  | ivec :: ivecs -> begin
      try solve_iveclist eqs veclist (ivec :: rest)
      with Contradiction ->
	solve_iveclist_disj eqs veclist rest ivecs
    end

let number_of_constraints iveclist =
  let rec aux = function
      IVgte _ -> 1
    | IVeq _ -> 1
    | IVconj iveclist -> aux_conj 1 iveclist
    | IVdisj iveclist -> aux_disj 0 iveclist

  and aux_conj n = function
      [] -> n
    | ivec :: rest -> aux_conj (n * aux ivec) rest

  and aux_disj n = function
      [] -> n
    | ivec :: rest -> aux_disj (n + aux ivec) rest
  in aux_conj 1 iveclist
 
let rec main = function
    [] -> ()
  | iveclist :: rest ->
      try solve_iveclist [] [] iveclist
      with Contradiction -> main rest
