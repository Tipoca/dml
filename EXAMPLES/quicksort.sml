fun
  qs cmp xs =
    case xs of
      [] => []
    | x :: xs' => par cmp (x, [], [], xs')

and
  par cmp (x, l, r, xs) =
    case xs of
      [] => qs cmp l @ (x :: qs cmp r)
    | x' :: xs' => if cmp(x', x) then par cmp (x, x' :: l, r, xs')
                 else par cmp (x, l, x' :: r, xs')
