datatype pattern =
  Empty (* empty string matches Empty *)
| Char of char (* "c" matches Char (c) *)
| Plus of pattern * pattern
| Times of pattern * pattern
| Star of pattern

datatype pattern' =
  Nil'
| Empty'
| Char' of char
| Plus' of pattern' * pattern'
| Times' of pattern' * pattern'
| Star' of pattern'

fun delta Empty = Empty'
  | delta (Char _) = Nil'
  | delta (Plus (p1, p2)) =
    (case (delta p1, delta p2) of
      (Nil', Nil') => Nil' | _ => Empty')
  | delta (Times (p1, p2)) =
    (case (delta p1, delta p2) of
       (Empty', Empty') => Empty' | _ => Nil')
  | delta (Star p) = Empty'

fun norm Empty = Nil'
  | norm (Char c) = Char' c
  | norm (Plus (p1, p2)) = Plus' (norm p1, norm p2)
  | norm (Times (p1, p2)) =
    let
        val p1' = norm p1
        and p2' = norm p2
    in
        Plus' (Plus' (Times' (delta p1, p2'), Times' (p1', delta p2)),
               Times' (p1', p2'))
    end
  | norm (Star p) =
    let
        val p' = norm p
    in
        Times' (p', Star' p')
    end

fun acc cs k = fn
    Nil' => false
  | Empty' => k (cs)
  | Char'(c) =>
    (case cs of
       [] => false
     | c' :: cs' => if (c = c') then k (cs') else false)
  | Plus'(p1, p2) => if acc cs k p1 then true else acc cs k p2
  | Times'(p1, p2) => acc cs (fn cs' => acc cs' k p2) p1
  | p as Star'(p0) =>
    if k (cs) then true else acc cs (fn cs' => acc cs' k p) p0

(* 'explode' turns a string into a list of characters *)
fun accept p s =
  let
      val cs = explode s
      val k0 = (fn [] => true | _ :: _ => false)
  in
      if acc cs k0 (delta p) then true else acc cs k0 (norm p)
  end
