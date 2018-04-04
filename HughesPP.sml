structure HughesPP (* : PrettyPrinter *) =
struct

infix <>;
infix $$;
infix cat;
infix <+>;

(* Functional to support sections with an argument to the left *)
fun secl x f y = f (x, y);

(* foldr1, the variant of foldr with no starting value argument *)
fun foldr1 f [x] = x
  | foldr1 f (x :: xs) = f (x, foldr1 f xs);

(* optimized rep of strings: fast length, fast concat *)
type Str = int * (string -> string);
fun len (i, _) = i;
fun (i, s) cat (j, t) = (i + j, s o t);
fun str_ s = (size s, secl s op^);
fun string (i, s) = s "";

datatype Doc =
	 Nil (* text "" *)
       | NilAbove of Doc (* text "" $$ x *)
       | TextBeside of Str * Doc (* text s <> x *)
       | Nest of int * Doc (* nest k x *)
       | Union of Doc * Doc (* x U y *)
       | Empty; (* {} *)

fun text s = TextBeside (str_ s, Nil);

fun nest k x = Nest (k, x);

fun Nil <> (Nest (k, x)) = Nil <> x
  | Nil <> x = x
  | (NilAbove x) <> y = NilAbove (x <> y)
  | (TextBeside (s, x)) <> y = TextBeside (s, x <> y)
  | (Nest (k, x)) <> y = Nest (k, (x <> y))
  | Empty <> y = Empty
  | (Union (x, y)) <> z = Union (x <> z, y <> z);

fun aboveNest Nil k y = NilAbove (nest k y)
  | aboveNest (NilAbove x) k y = NilAbove (aboveNest x k y)
  | aboveNest (TextBeside (s, x)) k y =
    let val k' = k - len s in
	TextBeside (s, aboveNest (Nil <> x) k' y)
    end
  | aboveNest (Nest (k', x)) k y =
    let val k'' = k - k' in
	Nest (k', aboveNest x k'' y)
    end
  | aboveNest (Union (x, y)) k z =
    Union (aboveNest x k z, aboveNest y k z)
  | aboveNest Empty k x = Empty;

fun x $$ y = aboveNest x 0 y;

fun fit Nil = Nil
  | fit (NilAbove x) = Empty
  | fit (TextBeside (s, x)) = TextBeside (s, fit x)
  | fit (Nest (n, x)) = Nest (n, fit x)
  | fit (Union (x, y)) = fit x
  | fit Empty = Empty;

fun vertical x k ys = x $$ nest k (foldr1 (op $$) ys);
fun x <+> y = x <> text " " <> y;

local
    fun sep' Nil k ys = Union (fit (foldl (op <+>) Nil ys),
			       vertical Nil k ys)
      | sep' (NilAbove x) k ys = vertical (NilAbove x) k ys
      | sep' (TextBeside (s, x)) k ys =
	TextBeside (s, sep' (Nil <> x) (k - len s) ys)
      | sep' (Nest (n, x)) k ys = Nest (n, sep' x (k - n) ys)
      | sep' (Union (x, y)) k ys = Union (sep' x k ys, vertical y k ys)
      | sep' Empty k ys = Empty
in
fun sep [x] = x
  | sep (x :: ys) =  sep' x 0 ys
end;

fun fits n k x = if n < k
		 then false
		 else case x of
			  Nil => true
			| NilAbove y => false
			| TextBeside (t, y) => fits n (k + len t) y
			| Empty => false;

fun min w r = if w <= r then w else r;

fun nicest' w r s x y = if fits (min w r) (len s) x then x else y;
fun nicest w r x y = nicest' w r (str_ "") x y;


fun best' w r s Nil = Nil
  | best' w r s (NilAbove x) = NilAbove (best (w - len s) r x)
  | best' w r s (TextBeside (t, x)) =
    TextBeside (t, best' w r (s cat t) x)
  | best' w r s (Nest (k, x)) = best' w r s x
  | best' w r s (Union (x, y)) =
    nicest' w r s (best' w r s x) (best' w r s y)
  | best' w r s Empty = Empty
and best w r Nil = Nil
  | best w r (NilAbove x) = NilAbove (best w r x)
  | best w r (TextBeside (s, x)) = TextBeside (s, best' w r s x)
  | best w r (Nest (k, x)) = Nest (k, best (w - k) r x)
  | best w r (Union (x, y)) = nicest w r (best w r x) (best w r y)
  | best w r Empty = Empty;

fun layout k (Nest (k', x)) = layout (k + k') x
  | layout k x = implode (List.tabulate (k, fn _ => #" ")) ^ layout' k x
and layout' k Nil = "\n"
  | layout' k (NilAbove x) = "\n" ^ layout k x
  | layout' k (TextBeside (s, x)) = string s ^ layout' (k + len s) x;

fun pretty w r d = layout 0 (best w r d);

end;
