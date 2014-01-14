exception Bad_Char

fun f [] k = k []
  | f (c :: cs) k =
    if c = #"(" then f cs (fn cs' => (f cs' k) + 1)
    else if c = #")" then k (cs) - 1 else raise Bad_Char

fun bal s = (f (explode s) (fn _ => 0) = 0)
