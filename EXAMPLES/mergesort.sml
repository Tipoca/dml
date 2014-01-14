datatype 'a llist =
    lnil | lcons of 'a list * 'a llist

fun('a)
  merge ([], ys) = ys
| merge (xs, []) = xs
| merge (xs as x :: xs', ys as y :: ys') =
  if x < y then x :: merge (xs', ys) else y :: merge (xs, ys')

fun('a)
  initlist [] = lnil
| initlist (l as [x]) = lcons (l, lnil)
| initlist (x1 :: x2 :: xs) =
  let
      val l = if x1 < x2 then [x1, x2] else [x2, x1]
  in
      lcons (l, initlist xs)
  end

fun('a)
  lmerge (ls as lnil) = ls
| lmerge (ls as lcons (_, lnil)) = ls
| lmerge (lcons (l1, lcons (l2, ls))) =
  lcons (merge (l1, l2), lmerge ls)

fun('a)
  mergeAll lnil = []
| mergeAll (lcons (l, lnil)) = l
| mergeAll (ls as lcons (_, _)) = mergeAll (lmerge ls)

fun('a) mergesort l = mergeAll (initlist l)
 