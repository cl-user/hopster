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
	end
=
struct

type ('key, 'value) dict = (Key.t, value) Redblackmap.dict;

val create = Redblackmap.mkDict Key.compare;
val lookup = Redblackmap.peek;
val insert = Redblackmap.insert;

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

    val types : hol_type -> dict;
    val terms : term -> dict
end;

structure Dictionary : DICTIONARY =
struct

type dict = (string, string) StringDict.dict;

fun types' (t : hol_type, d : dict) =
	if is_vartype t
	then d
	else let val (name, args) = dest_type t in
		 foldr types'
 		       (StringDict.insert (d, EmitHaskell.hs_constructor name, name))
		       (filter is_type args)
	     end;

fun types (t : hol_type) = types' (t, StringDict.create);

fun terms' (t : term, d : dict) =
    case dest_term t of
	VAR (s, _)          => StringDict.insert (d, EmitHaskell.hs_variable s, s)
      | CONST {Name=s, ...} => StringDict.insert (d, (if TypeBase.is_constructor t
						      then EmitHaskell.hs_constructor s
						      else EmitHaskell.hs_variable s), s)
      | COMB (t1, t2) => StringDict.merge (terms t1,
					   terms t2)
      | LAMB (t1, t2) => StringDict.merge (terms t1,
					   terms t2)

and terms (t : term) = terms' (t, StringDict.create)

end;
