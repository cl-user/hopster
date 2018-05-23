signature FUNCTOR = sig
    type 'a t;
    val fmap : ('a -> 'b) -> 'a t -> 'b t
end;

infix <*>;

signature APPLICATIVE = sig
    include FUNCTOR;
    val pure : 'a -> 'a t;
    val <*> : ('a -> 'b) t * 'a t -> 'b t
end;

infix <|>;

signature ALTERNATIVE = sig
    include APPLICATIVE;
    val empty : 'a t;
    val <|> : 'a t * 'a t -> 'a t;
    val many : 'a t -> 'a list t;
    val some : 'a t -> 'a list t;
end;

infix >>=;

signature MONAD = sig
    include ALTERNATIVE;
    (* include APPLICATIVE; *)
    val return : 'a -> 'a t;
    val >>= : 'a t * ('a -> 'b t) -> 'b t
end;

signature PARSER = sig
    include MONAD;
    val parse : 'a t -> string -> ('a * string) list;
    val item : char t;
    val sat : (char -> bool) -> char t;
    val digit : char t;
    val lower : char t;
    val upper : char t;
    val letter : char t;
    val alphanum : char t;
    val char : char -> char t;
    val string : string -> string t;
    val ident : string t;
    val nat : int t;
    val space : unit t
    val int : int t;
    val token : 'a t -> 'a t;
    val identifier : string t;
    val natural : int t;
    val integer : int t;
    val symbol : string -> string t
end;

structure Parser : PARSER =
struct

type 'a t = string -> ('a * string) list;

fun parse p = p;

val item = fn inp => case explode inp of
			 nil => nil
		       | x::xs => [(x, implode xs)];

fun fmap g p = fn inp => case parse p inp of
			     nil => nil
			   | [(v, out)] => [(g v, out)]

fun pure v = fn inp => [(v, inp)];

fun pg <*> px = fn inp => case parse pg inp of
			      nil => nil
			    | [(g, out)] => parse (fmap g px) out;

val return = pure;

fun p >>= f = fn inp => case parse p inp of
			    nil => nil
			  | [(v, out)] => parse (f v) out;

val empty = fn inp => nil;

fun p <|> q = fn inp => case parse p inp of
			    nil => parse q inp
			  | [(v, out)] => [(v, out)];

fun sat p = item >>= (fn x =>
			 if p x then return x else empty);

val digit = sat Char.isDigit;

val lower = sat Char.isLower;

val upper = sat Char.isUpper;

val letter = sat Char.isAlpha;

val alphanum = sat Char.isAlphaNum;

fun char c = sat (fn x => x = c);

fun string "" = return ""
  | string cs =
    let
      val x = String.sub (cs, 0);
      val xs = String.extract (cs, 1, NONE)
    in
	char x >>= (fn _ =>
	string xs >>= (fn _ =>
	return cs))
    end;

(* fun many x = some x <|> pure nil *)

fun many p = (p >>= (fn x => many p >>= (fn xs => return (x :: xs)))) <|> pure nil;

fun some x = let fun g x xs = x :: xs in
		 pure g <*> x <*> many x
	     end;

val ident = lower >>= (fn x =>
	    many alphanum >>= (fn xs =>
	    return (implode (x :: xs))));

val nat = some digit >>= (fn xs => case Int.fromString (implode xs) of
				       SOME n => return n
				     | NONE => empty);

val space = many (sat Char.isSpace) >>= (fn _ => return ());

val int = (char #"-" >>= (fn _ => nat >>= (fn n => return (~ n)))) <|> nat;

fun token p = space >>= (fn _ => p >>= (fn v => space >>= (fn _ => return v)));

val identifier = token ident;

val natural = token nat;

val integer = token int;

fun symbol xs = token (string xs)

end;
