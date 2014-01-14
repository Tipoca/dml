datatype 'a Tree = E | T of 'a * 'a Tree * 'a Tree

fun map f E = E
  | map f (T (x, a, b)) = T (f(x), map f a, map f b)

fun bfLab i [] [] = ()
  | bfLab i [] ts' = bfLab i (List.rev ts') []
  | bfLab i (E :: ts) ts' = bfLab i ts ts'
  | bfLab i (T (r, a, b) :: ts) ts' = (r := i; bfLab (i+1) ts (b :: a :: ts'))

fun bfnum t =
  let
      val t = map (fn _ => ref 0) t
      val _ = bfLab 1 [t] []
  in
      map (fn r => !r) t
  end

(*
fun bfLab (i, [], i', ts') = bfLab' (i'-1, ts', i', [])
  | bfLab (i, E :: ts, i', ts') = bfLab (i, ts, i', ts')
  | bfLab (i, T (r, a, b) :: ts, i', ts') =
    let
	val _ = r := i
    in
	case (a, b) of
	  (E, E) => bfLab (i+1, ts, i'+1, ts')
        | (E, _) => bfLab (i+1, ts, i'+2, b :: ts')
        | (_, E) => bfLab (i+1, ts, i'+2, a :: ts')
        | _ => bfLab (i+1, ts, i'+3, b :: a :: ts')
    end

and bfLab' (i, [], i', []) = ()
  | bfLab' (i, [], i', ts') = bfLab (i', ts', i', [])
  | bfLab' (i, T (r, a, b) :: ts, i', ts') =
    (r := i; bfLab' (i-1, ts, i', a :: b :: ts'))

fun bfnum t =
  let
      val t = map (fn _ => ref 0) t
      val _ = bfLab (1, [t], 1, [])
  in
      map (fn r => !r) t
  end

fun bfLab (i, [], i', ts') =
    let
	val (Ts, _) = bfLab' (i'-1, ts', i', [])
    in
	([], Ts)
    end
  | bfLab (i, E :: ts, i', ts') =
    let
	val (Ts, Ts') = bfLab (i, ts, i', ts')
    in
	(E :: Ts, Ts')
    end
  | bfLab (i, T (_, a, b) :: ts, i', ts') =
    case (a, b) of
	(E, E) =>
	    let
		val (Ts, Ts') = bfLab (i+1, ts, i'+1, ts')
	    in
		(T (i, E, E) :: Ts, Ts')
	    end
      | (_, E) => 
	    let
		val (Ts, A :: Ts') = bfLab (i+1, ts, i'+2, a :: ts')
	    in
		(T (i, A, E) :: Ts, Ts')
	    end
      | (E, _) =>
	    let
		val (Ts, B :: Ts') = bfLab (i+1, ts, i'+2, b :: ts')
	    in
		(T (i, E, B) :: Ts, Ts')
	    end
      | _ =>
	    let
		val (Ts, B :: A :: Ts') = bfLab (i+1, ts, i'+3, b :: a :: ts')
	    in
		(T (i, A, B) :: Ts, Ts')
	    end


and bfLab' (i, [], i', []) = ([], [])
  | bfLab' (i, [], i', ts') =
    let
	val (Ts, _) = bfLab (i', ts', i', [])
    in
	([], Ts)
    end
  | bfLab' (i, T (r, a, b) :: ts, i', ts') =
    let
	val (Ts, A :: B :: Ts') = bfLab' (i-1, ts, i', a :: b :: ts')
    in
	(T (i, A, B) :: Ts, Ts')
    end

fun bfnum t =
    let
	val ([t], _) = bfLab (1, [t], 1, [])
    in
	t
    end
*)

val t0 = T ("a", T("b", E, T ("c", E, E)), T ("d", E, E))
val t1 = T ("A", t0, t0)
