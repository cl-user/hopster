(* signature EMITHASKELL = *)
(* sig *)
(*     include HughesPP; *)
(*     val pp_term : term -> Doc; *)
(* end; *)

structure EmitHaskell (* :> EMITHASKELL *) =
struct

open HolKernel boolSyntax Abbrev;

open HughesPP;
infix <>;
infix $$;
infix cat;
infix <+>;


(*---------------------------------------------------------------------------*)
(* TYPES                                                                     *)
(*---------------------------------------------------------------------------*)

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

(*---------------------------------------------------------------------------*)
(* TERMS                                                                     *)
(*---------------------------------------------------------------------------*)

fun same_fn eq1 eq2 = let val f = fst o strip_comb o lhs in
			  same_const (f eq1) (f eq2)
		      end;

fun partitions _ [] = []
  | partitions p (h::t) = let val (l1, l2) = partition (p h) t in
			      (h :: l1) :: partitions p l2
			  end;

fun foldr1 f [x] = x
  | foldr1 f (x :: xs) = f (x, (foldr1 f xs));

local
  val a = mk_var("a",bool)
  val b = mk_var("b",bool)
in
val andalso_tm = list_mk_abs([a,b],mk_conj(a,b))
val orelse_tm = list_mk_abs([a,b],mk_disj(a,b))
end;

fun generic_type_of (t : term) =
  if is_const t
  then let val {Name,Thy,...} = dest_thy_const t in
	   type_of (prim_mk_const{Name=Name,Thy=Thy})
       end
  else type_of t;

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

(* 
 * Returns a Doc representing a variable identifier in Haskell
 * syntax 
 *)
val pp_variable =
  let
      val varid = fst o dest_var
      fun fix_reserved s = if is_reserved s
			   then s ^ "_"
			   else s
      fun fix_first_char s =
	let val c = String.sub (s, 0)
	    val cs = String.extract (s, 1, NONE)
	in
	    if Char.isUpper c
	    then str (Char.toLower c) ^ cs
	    else s
	end
  in
      text o fix_reserved o fix_first_char o varid
  end;

(* Apparently values of type ``:num`` are *arbitrary precision*
natural numbers. A Haskell value of type Numeric.Natural may be needed
here. *)
val pp_number =
    text o Arbnum.toString o Literal.relaxed_dest_numeral

val pp_string =
    text o quote o Literal.relaxed_dest_string_lit

fun pp_conditional (t : term) =
  let val (test_term, then_term, else_term) = dest_cond t in
      text "if" <+> pp_term test_term
	   $$ (text "then" <+> pp_term then_term)
	   $$ (text "else" <+> pp_term else_term)
  end

and pp_arb () = text "undefined"

and pp_list (t : term) =
  let
      val elems = map pp_term (fst (listSyntax.dest_list t))
      infix <++> fun x <++> y = x <> text "," <+> y
  in
      text "["
      <> (if null elems
	  then text ""
	  else foldr1 (op <++>) elems)
      <> text "]"
  end

and pp_cons (t : term) =
    let	val (h, t) = listSyntax.dest_cons t in
	pp_term h <+> text ":" <+> pp_term t
  end

and pp_binop (t : term) =
  let
      val (c, [t1, t2]) = strip_comb t
      fun cmp (t, t') =
	let
	    val {Name=name, Thy=theory, ...} = dest_thy_const t
	    val {Name=name', Thy=theory', ...} = dest_thy_const t'
	in
      	    pair_compare(String.compare,String.compare) ((name,theory),(name',theory'))
	end
      val binops = Redblackmap.fromList cmp [(boolSyntax.equality, "=="),
					     (boolSyntax.conjunction, "&&"),
					     (boolSyntax.disjunction, "||")]
      val operator = case Redblackmap.peek (binops, c) of
			 SOME x => x
		       | NONE => #Name (dest_thy_const c)
  in
      pp_term t1 <+> text operator <+> pp_term t2
  end

and pp_pair (t : term) =
  let val (t1, t2) = pairSyntax.dest_pair t in
      text "(" <> pp_term t1 <> text "," <+> pp_term t2 <> text ")"
  end

and pp_lets (t : term) =
    let
	val (defs, body) = pairSyntax.strip_anylet t
	val defs' = map mk_eq (flatten defs)
    in
      vertical (text "let") 4 (map pp_defns defs') $$ text "in" $$ (nest 4 (pp_term body))
  end

and pp_abs (t : term) =
  let val (p, body) = pairSyntax.dest_pabs t in
      text "(" <> text "\\" <> pp_lhs p <+> text "->" <+> pp_term body <> text ")"
  end

and pp_fail (t : term) =
    let val (f, s, args) = combinSyntax.dest_fail t in
	text "error" <+> text "\"" <> text s <> text "\""
    end

and pp_unit () = text "()"

and pp_case (t : term) =
    let open patternMatchesSyntax
	val (expr, clauses) = TypeBase.strip_case t
	fun toRow (p, rhs) = mk_PMATCH_ROW (p, T, rhs)
	val clauses' = listSyntax.lift_list (type_of PMATCH_ROW_tm) toRow clauses
    in
	pp_case_with_guard (mk_PMATCH expr clauses')
    end

and pp_case_with_guard (t : term) =
    let val (expr, clauses) = patternMatchesSyntax.dest_PMATCH t in
	vertical (text "case" <+> pp_term expr <+> text "of")
		 4
		 (map pp_case_clause clauses)
    end

and pp_case_clause (t : term) =
    let val (_, lhs, guard, rhs) = patternMatchesSyntax.dest_PMATCH_ROW_ABS t in
	pp_lhs lhs <> pp_guard guard <+> text "->" <+> pp_term rhs
    end

and pp_guard (t : term) =
    if (aconv t T)
    then text ""
    else text " | " <> pp_term t

and pp_const (t : term) =
    if same_const t boolSyntax.conjunction
    then pp_abs andalso_tm
    else if same_const t boolSyntax.disjunction
         then pp_abs orelse_tm
         else (text o pp_constructor o fst o dest_const) t
    
and pp_comb (t : term) =
    let
	val (h, args) = strip_comb t
	val (argtys, target) = strip_fun (generic_type_of h)
    in
	if length argtys < length args
	then let val (app, rst) = split_after (length argtys) args in
		 pp_term (list_mk_comb (h, app)) <+> (foldr1 (op <+>) (map pp_term rst))
	     end
	else pp_open_comb t
    end

and pp_open_comb (t : term) =
    let	val (f, args) = strip_comb t in
	foldr1 (op <+>) (map pp_term (f :: args))
    end
	
(* Returns a Doc representing a HOL term as a Haskell expression *)
and pp_term (t : term) : Doc =
  let
      val is_num_literal = Lib.can Literal.relaxed_dest_numeral
      val is_string_literal = Lib.can Literal.relaxed_dest_string_lit
      fun is_infix t = case fixity t of
			   SOME (Infix _) => true
			 | _ => false
      fun is_infix_app t = is_conj t
			   orelse is_disj t
			   orelse is_eq t
			   orelse (is_comb t
				   andalso (is_infix o fst o dest_const o fst o strip_comb) t)
      val is_supported_pmatch = let open patternMatchesLib in
				    is_ocaml_pmatch o analyse_pmatch false
				end
  in
      if is_var t then pp_variable t
      else if is_cond t then pp_conditional t
      else if is_arb t then pp_arb ()
      else if is_num_literal t then pp_number t
      else if is_string_literal t then pp_string t
      else if listSyntax.is_list t then pp_list t
      else if listSyntax.is_cons t then pp_cons t (* unreachable *)
						(* else if listSyntax.is_mem t then  *)
      else if is_infix_app t then pp_binop t
      else if pairSyntax.is_pair t then pp_pair t
      else if boolSyntax.is_let t then pp_lets t
      else if pairSyntax.is_pabs t then pp_abs t
      else if combinSyntax.is_fail t then pp_fail t
      else if oneSyntax.is_one t then pp_unit ()
      (* else if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) *)
      else if is_supported_pmatch t then pp_case_with_guard t
      else if TypeBase.is_case t then pp_case t
					      (* else if is_the_value t then pp_itself t *)
      else if is_const t then pp_const t
      else if is_comb t then pp_comb t
      else raise ERR "pp_term" ("Term with unknown syntax: " ^ Parse.term_to_string t)
  end

and pp_defns (t : term) =
    let
	val equations = map (snd o strip_forall)
			    ((strip_conj o snd o strip_forall) t)
	val clauses = partitions same_fn equations
	infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2
    in
	foldr1 (op $$$) (map pp_defn_clauses clauses)
    end

and pp_defn_clauses (ts : term list) =
    foldr1 (op $$) (map pp_defn_clause ts)

and pp_defn_clause (t : term) =
    let	val (l, r) = dest_eq t in
	pp_lhs l <+> text "=" <+> pp_term r
    end

and pp_lhs (t : term) =
  let
      val is_num_literal = Lib.can Literal.relaxed_dest_numeral
      val is_string_literal = Lib.can Literal.relaxed_dest_string_lit
  in
      if is_var t then pp_variable t
      else if is_arb t then pp_arb ()
      else if is_num_literal t then pp_number t
      else if is_string_literal t then pp_string t
      else if listSyntax.is_list t then pp_list t
      else if listSyntax.is_cons t then pp_cons t (* unreachable *)
						(* else if listSyntax.is_mem t then  *)
      else if pairSyntax.is_pair t then pp_pair t
      else if boolSyntax.is_let t then pp_lets t
      else if pairSyntax.is_pabs t then pp_abs t
      else if combinSyntax.is_fail t then pp_fail t
      else if oneSyntax.is_one t then pp_unit ()
      (* else if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) *)
					      (* else if is_the_value t then pp_itself t *)
      else if is_const t then pp_const t
      else if is_comb t then pp_comb t
      else raise ERR "pp_lhs" ("Term with unknown syntax: " ^ Parse.term_to_string t)
  end
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
