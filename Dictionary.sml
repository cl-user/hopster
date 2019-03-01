signature ORDER = sig
    type t;
    val compare : t * t -> order
end;

functor MakeDict (structure Key : ORDER; type value) :
	sig
	    type ('key, 'value) dict;
	    val create : (Key.t, value) dict;
	    val lookup : (Key.t, value) dict * Key.t -> value option;
	    val insert : (Key.t, value) dict * Key.t * value ->
	    		 (Key.t, value) dict;
	    val merge  : (Key.t, value) dict * (Key.t, value) dict ->
	    		 (Key.t, value) dict;
	    val listItems : (Key.t, value) dict -> (Key.t * value) list
	end
=
struct

type ('key, 'value) dict = (Key.t, value) Redblackmap.dict;

val create = Redblackmap.mkDict Key.compare;
val lookup = Redblackmap.peek;
val insert = Redblackmap.insert;
val listItems = Redblackmap.listItems;

fun merge (d1, d2) =
    Redblackmap.insertList (d2, Redblackmap.listItems d1)

end;

structure OrderedString : ORDER =
struct
type t = string;
val compare = String.compare
end;

structure StringDict = MakeDict (structure Key = OrderedString;
				 type value = string);

signature DICTIONARY = sig
    type dict;

    val hs_constructor : string -> string;
    val hs_variable : string -> string;

    val types : hol_type -> dict;
    val terms : term -> dict
end;

structure Dictionary : DICTIONARY =
struct

type dict = (string, string) StringDict.dict;

fun head s = String.sub (s, 0)
fun tail s = String.extract (s, 1, NONE)
fun cons c s = String.str c ^ s

val symbolicChars =
    Redblackmap.fromList Char.compare
			 [ (#"#", "NumberSign")
			 , (#"?", "QuestionMark")
			 , (#"+", "PlusSign")
			 , (#"*", "Asterisk")
			 , (#"/", "Solidus")
			 , (#"\\", "ReverseSolidus")
			 , (#"=", "EqualsSign")
			 , (#"<", "LessThanSign")
			 , (#">", "GreaterThanSign")
			 , (#"&", "Ampersand")
			 , (#"%", "PercentSign")
			 , (#"@", "CommercialAt")
			 , (#"!", "ExclamationMark")
			 , (#":", "Colon")
			 , (#"|", "VerticalLine")
			 , (#"-", "HyphenMinus")
			 , (#"^", "CircumflexAccent")
			 , (#"'", "Apostrophe")
			 , (#"0", "Zero")
			 , (#"1", "One")
			 , (#"2", "Two")
			 , (#"3", "Three")
			 , (#"4", "Four")
			 , (#"5", "Five")
			 , (#"6", "Six")
			 , (#"7", "Seven")
			 , (#"8", "Eight")
			 , (#"9", "Nine") ];

fun hs_constructor (name : string) =
  let
      val builtins =
          Redblackmap.fromList String.compare
                               [ ("T", "True"),
                                 ("F", "False")];
      fun alphanum_ident () =
	    cons (Char.toUpper (head name))
		 (tail name)
      fun symbolic_ident () =
	let
	    val symNames = List.map ((curry Redblackmap.find) symbolicChars)
				    (explode name)
	in
	    String.concat symNames
	end
      fun is_builtin () =
          Option.isSome (SOME (Redblackmap.findKey (builtins, name)) handle NotFound => NONE);
  in
      if is_builtin ()
      then Redblackmap.find (builtins, name)
      else (if Char.isAlpha (head name)
            then alphanum_ident ()
            else symbolic_ident ())
  end;

local
    val keywords = Redblackset.addList
			  (Redblackset.empty String.compare,
			   ["case", "class", "data", "default"
			    , "deriving", "do", "else", "foreign"
			    , "if", "import", "in", "infix", "infixl"
			    , "infixr", "instance", "let", "module"
			    , "newtype", "of", "then", "type", "where", "_"])
in
fun is_reserved s = Redblackset.member (keywords, s)
end;

val hs_variable =
  let
      fun fix_reserved s = if s = "_"
			   then "underscore"
			   else if is_reserved s
			   then s ^ "'"
			   else s
      val fix_camel_case =
	let fun is_sep c = c = #"-" orelse c = #"_"
	    fun capitalize [] = []
	      | capitalize (c::cs) = Char.toUpper c :: (map Char.toLower cs)
	in
	    concat o map (implode o capitalize o explode) o String.tokens is_sep
	end
      fun fix_first_char s =
	  cons (Char.toLower (head s)) (tail s);
      val fix_sym_chars =
          let
              fun fix sym =
                  if Char.isDigit sym
                  then str sym
                  else (Redblackmap.find (symbolicChars, sym)
                        handle NotFound => str sym)
          in
              concat o map fix o explode
          end
  in
      fix_first_char o fix_camel_case o fix_reserved o fix_sym_chars
  end;

fun types' (t : hol_type, d : dict) =
	if is_vartype t
	then d
	else let val (name, args) = dest_type t in
		 foldr types'
 		       (StringDict.insert (d, hs_constructor name, name))
		       (filter is_type args)
	     end;

fun types (t : hol_type) = types' (t, StringDict.create);

fun terms' (t : term, d : dict) =
    case dest_term t of
	VAR (s, _)          => StringDict.insert (d, hs_variable s, s)
      | CONST {Name=s, ...} => StringDict.insert (d, (if TypeBase.is_constructor t
						      then hs_constructor s
						      else hs_variable s), s)
      | COMB (t1, t2) => StringDict.merge (terms t1,
					   terms t2)
      | LAMB (t1, t2) => StringDict.merge (terms t1,
					   terms t2)

and terms (t : term) = terms' (t, StringDict.create)

end;
