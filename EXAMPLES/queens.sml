structure A = Array

fun dots_pr(n) =
  if n <= 0 then () else
    let val _ = print "." in dots_pr(n-1) end
(*
withtype {n:int} <max(n,0)> => int(n) -> unit
*)

fun board_pr_aux (i, size, board) =
  if i = size then print "\n"
  else
    let
       val qi = A.sub (board, i)
       val _ = dots_pr (qi-1)
       val _ = print "Q"
       val _ = dots_pr (size - qi)
       val _ = print "\n"
    in
       board_pr_aux (i+1, size, board)
    end
(*
withtype {i:nat,s:nat | i <= s} <s-i> =>
           int (i) * int(s) * int array(s) -> unit
*)


fun board_pr (size, board) = board_pr_aux (0, size, board)
(*
withtype {s:nat} <> => int (s) * int array(s) -> unit
*)

fun test(j, i, qi, board) =
  if (j < i) then
    let
       val qj = A.sub (board, j)
    in
       if qi = qj then false
       else if Int.abs (qi - qj) = i - j then false
            else test (j+1, i, qi, board)
    end
  else true
(*
withtype {j:nat,i:nat, s:nat | j <= i < s} <i-j> =>
           int(j) * int(i) * int * int array(s) -> bool
*)

fun loop (i, size, board) =
  let
     val next = 1 + A.sub (board, i)
  in
     if next > size then
       let
	  val _ = A.update (board, i, 0)
       in
          if i = 0 then () else loop (i-1, size, board)
       end
     else
       let
          val _ = A.update (board, i, next)
       in
          if test (0, i, next, board) then
            if (i+1 = size) then
              let
                 val _ = board_pr (size, board)
              in
                 loop (i, size, board)
              end
            else loop (i+1, size, board)
          else
             loop (i, size, board)
       end
  end
(*
withtype {i:nat,s:nat | i < s}
           int(i) * int(s) * int array(s) -> unit
*)


fun queens (size) = loop (0, size, A.array (size, 0))
(*
withtype {s:pos} int(s) -> unit
*)

val _ = queens (8)
