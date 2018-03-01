structure EmitHaskell (* :> EmitHaskell *) =
struct

open HolKernel boolSyntax Abbrev;

(* Translate a HOL identifier to a Haskell constructor *)
fun pp_constructor (name : string) =
  let
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
			       , (#"9", "Nine") ]
      fun head s = String.sub (s, 0)
      fun tail s = String.extract (s, 1, NONE)
      fun cons c s = String.str c ^ s
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
  in
      if Char.isAlpha (head name)
      then alphanum_ident ()
      else symbolic_ident ()
  end;

(* Translate the name of a type variable from HOL to Haskell
syntax. It drops the apostrophe at the beginning of the name and makes
sure the first alphabetic character is in lower case *)
fun pp_type_variable (name : string) =
  let
      val (#"'"::c::cs) = String.explode name
  in
      String.implode ((Char.toLower c) :: cs)
  end;

fun pp_type_fun (f : hol_type) =
  let
      val (domain, range) = dom_rng f
  in
      pp_type_arg domain
      ^ " "
      ^ "->"
      ^ " "
      ^ (if is_vartype range
	 then pp_type_variable (dest_vartype range)
	 else "(" ^ pp_type_arg range ^ ")")
  end
and pp_type_arg (arg : hol_type) =
    if is_type arg andalso fst (dest_type arg) = "fun"
    then "(" ^ pp_type_fun arg ^ ")"
    else pp_type_variable (dest_vartype arg);

(* pp_type_args = fn : hol_type list -> string *)
val pp_type_args = String.concatWith " " o map pp_type_arg

fun pp_type (t : hol_type) =
  let val (name, args) = dest_type t in
      pp_constructor name
      ^ " "
      ^ pp_type_args args
  end;

fun pp_value_arg (t : hol_type) =
  let
      val arity = List.length o snd o dest_type
  in
      if is_type t
      then (let
	       val (name, args) = dest_type t
	   in
	       if arity t = 0
	       then pp_constructor name
	       else "(" ^ pp_type t ^ ")"
	   end)
      else pp_type_arg t
  end;

val pp_value_args = String.concatWith " " o map pp_value_arg

local
    fun is_funtype t = is_type t andalso (fst o dest_type) t = "fun";

    fun get_args (t : hol_type) =
      if is_funtype t
      then
	  let val (domain, range) = dom_rng t
	  in domain :: get_args range
	  end
      else []
in
fun pp_value_const (t : term) =
  let
      val (term_name, term_type) = dest_const t
      val args = get_args term_type
  in
      pp_constructor term_name
      ^ " "
      ^ pp_value_args args
  end
end;

(* pp_value_consts = fn : term list -> string *)
val pp_value_consts = String.concatWith " | " o map pp_value_const

fun guess_consts (t : hol_type) =
  let
      val {Thy = thy, Tyop = tyop, Args = args} = dest_thy_type t
      val cs = constants thy
      val ds = definitions thy
  in
      []
  end;

fun value_consts (t : hol_type) =
  case TypeBase.fetch t of
      NONE => guess_consts t
    | SOME x => TypeBase.constructors_of t;

(* Returns a string whose value is the definition of 't' in Haskell
   syntax. It is expected that the value of 't' is sensible enough to
   perform the translation. That is to say, it should be a HOL type
   whose arguments are HOL type variables; otherwise the results are
   undefined. *)
fun pp_type_decl (t : hol_type) =
  "data"
  ^ " "
  ^ pp_type t
  ^ let val consts = value_consts t in
	if List.null consts
	then ""
	else " = " ^ pp_value_consts consts
    end;

(*
fun pp_datatype ppstrm (tyvars,decls) =
  let open Portable ParseDatatype
      val {add_break,add_newline,
	   add_string,begin_block,end_block,...} = with_ppstream ppstrm
      fun pp_tyvars [] = ()
       | pp_tyvars [v] = (add_string v; add_break(1,0))
       | pp_tyvars vlist =
          (begin_block CONSISTENT 0;
           pr_list (add_string o pp_type_variable)
		   (fn () => add_break(1,0))
		   (fn ()=>())
		   vlist;
           end_block())
      fun pp_clause r clause =
       (if !r then (add_string "= "; r:=false) else add_string "| ";
        case clause
         of (con,[]) => add_string (fix_cons con)
          | (con,args) =>
              (begin_block INCONSISTENT 0;
                 begin_block CONSISTENT 0;
                   add_string (fix_cons con);
                   add_string " of ";
                 end_block();
               pp_tyl (map ParseDatatype.pretypeToType args);
               end_block()))
      fun pp_decl (tyvars,r) (name,Constructors clauselist) =
        (begin_block CONSISTENT 5;
	 begin_block CONSISTENT 0;
	 add_string "data";
         add_break(1,0);
	 add_string pp_type_constructor name;
	 add_break(1,0);
	 pp_tyvars tyvars;
         end_block();
         add_break(1,0);
         begin_block CONSISTENT 0;
         pr_list (pp_clause (ref true))
                 (fn () => ())
                 (fn () => add_break(1,0)) clauselist;
         end_block(); end_block())
  in
      begin_block CONSISTENT 0
    ; pr_list (pp_decl (tyvars,ref true))
              add_newline
              add_newline
              decls
    ; end_block()
  end;

*)
end;
