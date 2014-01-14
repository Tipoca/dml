fun f91 (x) =
  if (x <= 100) then f91 (f91 (x + 11)) else x - 10
