exception Bad_Char

fun f [] k = k []
  | f (c :: cs) k =
    if c = #"(" then f cs (fn cs' => not (f cs' k))
    else if c = #")" then not (k (cs)) else raise Bad_Char

fun bal s = f (explode s) (fn _ => true)
