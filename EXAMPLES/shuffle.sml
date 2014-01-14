(*
fun ('a)
  shuffle nil = nil
| shuffle xs =
  case reverse xs of x :: xs => x :: shuffle (xs)
withtype {n:nat} 'a list(n) -> 'a list(n)
*)

datatype 'a list =
  nil | cons of 'a * 'a list

fun reverse (xs) =
  let
      fun('a)
        revApp xs = fn nil => xs | cons (y, ys) => revApp (cons (y, xs)) ys
  in
      revApp nil xs
  end

fun
  shuffle nil = nil
| shuffle (cons (x, xs)) = cons (x, shuffle (reverse xs))
