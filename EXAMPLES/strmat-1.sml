datatype pattern =
  Empty (* empty string matches Empty *)
| Char of char (* "c" matches Char (c) *)
| Plus of pattern * pattern
  (* cs matches Plus(p1, p2) if cs matches either p1 or p2 *)
| Times of pattern * pattern
  (* cs matches Times(p1, p2) if a prefix of cs matches p1 and
     the rest matches p2 *)
| Star of pattern
  (* cs matches Star(p) if cs matches some, possibly 0, copies of p *)

(* 'length' computes the length of a list *)
fun('a)
  length (xs) =
    let
       fun len ([], n) = n
         | len (x :: xs, n) = len (xs, n+1)
    in
       len (xs, 0)
    end

val counter = ref 0

fun acc i cs k = fn
    Empty => k (i, cs)
  | Char(c) =>
    (case cs of
       [] => false
     | c' :: cs' => if (c = c') then k (i-1, cs') else false)
  | Plus(p1, p2) => if acc i cs k p1 then true else acc i cs k p2
  | Times(p1, p2) => acc i cs (fn (i', cs') => acc i' cs' k p2) p1
  | p as Star(p0) =>
    if k (i, cs) then true
    else acc i cs (fn (i', cs') =>
                     if i' = i then false else acc i' cs' k p) p0
(* 'explode' turns a string into a list of characters *)

fun accept p s =
  let
      val cs = explode s
      val i = length cs
  in
      acc i cs (fn (i, _) => i = 0) p
  end
