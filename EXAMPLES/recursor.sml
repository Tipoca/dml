fun('a) R n u v = if (n = 0) then u else v (n-1) (R (n-1) u v)
