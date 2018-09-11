(* signature EMITHASKELL = *)
(* sig *)
(*     include HughesPP; *)
(*     val pp_term : term -> Doc; *)
(* end; *)

structure EmitHaskell (* :> EMITHASKELL *) =
struct

open HolKernel boolSyntax Abbrev term_grammar Parse;

open HughesPP;
infix <>;
infix $$;
infix cat;
infix <+>;

val ERR = mk_HOL_ERR "EmitHaskell";

fun foldr1 f [x] = x
  | foldr1 f (x :: xs) = f (x, (foldr1 f xs));

(*---------------------------------------------------------------------------*)
(* TYPES                                                                     *)
(*---------------------------------------------------------------------------*)

val pp_constructor = text o Dictionary.hs_constructor;

(* Translate the name of a type variable from HOL to Haskell
syntax. It drops the apostrophe at the beginning of the name and makes
sure the first alphabetic character is in lower case *)
fun pp_type_variable (name : string) =
  let
      val (#"'"::c::cs) = String.explode name
  in
      text (String.implode ((Char.toLower c) :: cs))
  end;

fun pp_type_fun (f : hol_type) =
  let
      val (domain, range) = dom_rng f
  in
      pp_type_arg domain
      <+>
      text "->"
      <+>
      (if is_vartype range
       then pp_type_variable (dest_vartype range)
       else text "(" <> pp_type_arg range <> text ")")
  end
and pp_type_arg (arg : hol_type) =
    if is_type arg andalso fst (dest_type arg) = "fun"
    then text "(" <> pp_type_fun arg <> text ")"
    else pp_type_variable (dest_vartype arg);

fun pp_type_args (ts : hol_type list) =
  case map pp_type_arg ts of
      [] => text ""
    | xs => text " " <> foldr1 (op <+>) xs;

fun pp_type (t : hol_type) =
  let val (name, args) = dest_type t in
      pp_constructor name
      <> pp_type_args args
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
	       else text "(" <> pp_type t <> text ")"
	   end)
      else pp_type_arg t
  end;

fun pp_value_args (ts : hol_type list) =
  case map pp_value_arg ts of
      [] => text ""
   |  xs => text " " <> foldr1 (op <+>) xs;

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
      <> pp_value_args args
  end
end;

fun pp_value_consts (ts : term list) =
  let fun f (d1, d2) = d1 <+> text "|" <+> d2 in
      case map pp_value_const ts of
	  [] => text ""
	| xs => foldr1 f xs
  end;

fun guess_consts (t : hol_type) =
  let
      val {Thy = thy, Tyop = tyop, Args = args} = dest_thy_type t
      val cs = constants thy
      val ds = DB.definitions thy
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
  text "data"
  <+> pp_type t
  <> let val consts = value_consts t in
	if List.null consts
	then text ""
	else text " = " <> pp_value_consts consts
     end;

(*---------------------------------------------------------------------------*)
(* TERMS                                                                     *)
(*---------------------------------------------------------------------------*)

datatype side = Left | Right

type context = (int * HOLgrammars.associativity * side) option

(* A term with extra information from its context necessary to            *)
(* pretty-print it (specifically to determine if it requires parenthesis) *)
type terminfo = term * context;

type emitter = terminfo -> Doc;

fun return doc = fn (_ : terminfo) => doc;

val fail = fn (_ : terminfo) => Empty;

(* fun emit (e : emitter) *)
(* 	 (t : terminfo) = *)
(*   e t; *)

(* fun sat (p : terminfo -> bool) = *)
(*   fn (t : terminfo) => *)
(*      if p t then pp_terminfo else fail; *)

fun choose (p : context -> bool)
	   (e : emitter)
	   (e' : emitter) : emitter =
  fn (t, cxt) =>
     if p cxt then e (t, cxt) else e' (t, cxt);

(* infix +++ *)
(* fun (e : emitter) +++ (e' : emitter) = *)
(*   fn (t : terminfo) => *)
(*      case emit e t of *)
(* 	 Empty => emit e' t *)
(*        | doc => doc; *)

fun parens (e : emitter) =
  fn (t : terminfo) =>
     text "(" <> e t <> text ")";

fun same_fn eq1 eq2 = let val f = fst o strip_comb o lhs in
			  same_const (f eq1) (f eq2)
		      end;

fun partitions _ [] = []
  | partitions p (h::t) = let val (l1, l2) = partition (p h) t in
			      (h :: l1) :: partitions p l2
			  end;

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

val pp_variable : emitter =
    let val varid = fst o dest_var in
	text o Dictionary.hs_variable o varid o fst
    end;

(* Apparently values of type ``:num`` are *arbitrary precision*
natural numbers. A Haskell value of type Numeric.Natural may be needed
here. *)
val pp_number : emitter =
    text o Arbnum.toString o Literal.relaxed_dest_numeral o fst;

val pp_string : emitter =
    text o quote o Literal.relaxed_dest_string_lit o fst;

val pp_arb : emitter = return (text "undefined");

val pp_unit : emitter  = return (text "()");

fun pp_conditional (t, _) =
  let val (test_term, then_term, else_term) = dest_cond t in
      text "if" <+> pp_terminfo (test_term, NONE)
	   $$ (text "then" <+> pp_terminfo (then_term, NONE))
	   $$ (text "else" <+> pp_terminfo (else_term, NONE))
  end

and parenthesize_conditional (e : emitter) =
    let fun needs_parens NONE = false
	  | needs_parens _ = true
    in
	choose needs_parens (parens e) e
    end

and pp_list (t, _) =
    let
	val elems = map (fn t' => (t', NONE)) (fst (listSyntax.dest_list t))
	val docs = map pp_terminfo elems
	infix <++> fun x <++> y = x <> text "," <+> y
    in
	text "["
	<> (case docs of
		[] => text ""
	      | _ => foldr1 (op <++>) docs)
	<> text "]"
    end

and pp_cons (t, _) =
    let
	val SOME (Infix (a, p)) = fixity "::"
	val (l, r) = listSyntax.dest_cons t
    in
	pp_terminfo (l, SOME (p, a, Left))
		    <+> text ":"
		    <+> pp_terminfo (r, SOME (p, a, Right))
    end

and parenthesize_cons (e : emitter) =
    let
	val SOME (Infix (assoc, prec)) = fixity "::"
	fun needs_parens (SOME (p, a, s)) = p > prec orelse (p = prec andalso s = Left)
	  | needs_parens _ = false

    in
	choose needs_parens (parens e) e
    end

and pp_binop (t, _) =
    let
	val (c, [t1, t2]) = strip_comb t
	val (a, p) = case (fixity o #Name o dest_thy_const) c of
			 SOME (Infix x) => x
		       | _ => (NONASSOC, 0)
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
	pp_terminfo (t1, SOME (p, a, Left))
		     <+> text operator
		     <+> pp_terminfo (t2, SOME (p, a, Right))
    end

and parenthesize_binop (e : emitter) =
    fn (t, cxt) =>
       let
	   val (_, prec) = case (fixity o #Name o dest_thy_const o fst o strip_comb) t of
			       SOME (Infix x) => x
			     | _ => (NONASSOC, 0)
	   fun needs_parens (SOME (p, a, s)) = p > prec orelse
					       (p = prec andalso ((a = LEFT andalso s = Right) orelse
								  (a = RIGHT andalso s = Left)))
	     | needs_parens _ = false
       in
	   (choose needs_parens (parens e) e) (t, cxt)
       end

and pp_pair (t, _) =
    let val (t1, t2) = pairSyntax.dest_pair t in
	text "(" <> pp_terminfo (t1, NONE) <>
	text "," <+> pp_terminfo (t2, NONE) <> text ")"
    end

and pp_lets (t, _) =
    let
	val (defs, body) = pairSyntax.strip_anylet t
	val defs' = map mk_eq (flatten defs)
    in
	vertical (text "let") 4 (map pp_defns defs') $$
		 text "in" $$
		 nest 4 (pp_terminfo (body, NONE))
    end

and parenthesize_lets (e : emitter) = parenthesize_conditional e

and pp_abs (t, _) =
    let val (p, body) = pairSyntax.dest_pabs t in
	text "\\" <> pp_lhs (p, NONE) <+> text "->" <+> pp_terminfo (body, NONE)
    end

and parenthesize_abs (e : emitter) = parenthesize_conditional e

and pp_fail (t, _) =
    let val (f, s, args) = combinSyntax.dest_fail t in
	text "error" <+> text "\"" <> text s <> text "\""
    end

and parenthesize_fail (e : emitter) = parenthesize_comb e


and pp_case (t, cxt) =
    let val t' = patternMatchesLib.case2pmatch false t in
	pp_case_with_guard (t', cxt)
    end

and pp_case_with_guard (t, _) =
    let val (expr, clauses) = patternMatchesSyntax.dest_PMATCH t in
	vertical (text "case" <+> pp_terminfo (expr, NONE) <+> text "of")
		 4
		 (map (pp_case_clause o (fn c => (c, NONE))) clauses)
    end

and parenthesize_case (e : emitter) = parenthesize_conditional e
	
and pp_case_clause (t, _) =
    let val (_, lhs, guard, rhs) = patternMatchesSyntax.dest_PMATCH_ROW_ABS t in
	(pp_lhs : emitter) (lhs, NONE) <>
	pp_guard (guard, NONE) <+> text "->" <+> pp_terminfo (rhs, NONE)
    end

and pp_guard (t, _) =
    if (aconv t T)
    then text ""
    else text " | " <> pp_terminfo (t, NONE)

and pp_const (t, _) =
    let
	fun pp_t t =  if TypeBase.is_constructor t
		      then (pp_constructor o fst o dest_const) t
		      else (pp_variable o (fn x => (x, NONE)) o mk_var o dest_const) t
    in
	if same_const t boolSyntax.conjunction
	then pp_abs (andalso_tm, NONE)
	else (if same_const t boolSyntax.disjunction
	      then pp_abs (orelse_tm, NONE)
	      else pp_t t)
    end
    
(* and pp_comb (t, _) = *)
(*     let *)
(* 	val (h, args) = strip_comb t *)
(* 	val (argtys, target) = strip_fun (generic_type_of h) *)
(*     in *)
(* 	if length argtys < length args *)
(* 	then let val (app, rst) = split_after (length argtys) args in *)
(* 		 pp_term (list_mk_comb (h, app)) <+> (foldr1 (op <+>) (map pp_term rst)) *)
(* 	     end *)
(* 	else pp_open_comb t *)
(*     end *)

(* and pp_open_comb (t, _) = *)
(*     let	val (f, args) = strip_comb t in *)
(* 	foldr1 (op <+>) (map pp_term (f :: args)) *)
(*     end *)

and pp_comb (t, _) =
    let
	val (f, args) = strip_comb t
	fun context side = SOME (2000, LEFT, side)
    in
	pp_terminfo (f, context Left) <+>
	foldr1 (op <+>) (map (pp_terminfo o (fn x => (x, context Right))) args)
    end
					 

and parenthesize_comb (e : emitter) =
    let
	val (prec, assoc) = (2000, LEFT)
	fun needs_parens (SOME (p, a, s)) = p > prec orelse
					    (p = prec andalso
					     ((a = RIGHT andalso s = Left) orelse
					      (a = LEFT  andalso s = Right)))
	  | needs_parens _ = false
    in
	choose needs_parens (parens e) e
    end
	   
(* Returns a Doc representing a HOL term as a Haskell expression *)
and pp_terminfo (t, cxt) =
       let
	   val is_num_literal = Lib.can Literal.relaxed_dest_numeral
	   val is_string_literal = Lib.can Literal.relaxed_dest_string_lit
	   fun term_name t = case (dest_term o fst o strip_comb) t of
				 VAR (name, _) => SOME name
			       | CONST {Name=name, ...} => SOME name
			       | _ => NONE
	   fun is_infix t = case term_name t of
				SOME s => (case fixity s of
					       SOME (Infix _) => true
					     | _ => false)
			     |  NONE => false
	   fun is_infix_app t = is_conj t
				orelse is_disj t
				orelse is_eq t
				orelse (is_comb t
					andalso is_infix t)
	   val is_supported_pmatch = let open patternMatchesLib in
					 is_ocaml_pmatch o analyse_pmatch false
				     end
       in
	   if is_var t then pp_variable (t, cxt)
	   else if is_cond t then parenthesize_conditional pp_conditional (t, cxt)
	   else if is_arb t then pp_arb (t, cxt)
	   else if is_num_literal t then pp_number (t, cxt)
	   else if is_string_literal t then pp_string (t, cxt)
	   else if listSyntax.is_list t then pp_list (t, cxt)
	   else if listSyntax.is_cons t then parenthesize_conditional pp_cons (t, cxt)
						     (* else if listSyntax.is_mem t then  *)
	   else if is_infix_app t then parenthesize_binop pp_binop (t, cxt)
	   else if pairSyntax.is_pair t then pp_pair (t, cxt)
	   else if boolSyntax.is_let t then parenthesize_lets pp_lets (t, cxt)
	   else if pairSyntax.is_pabs t then parenthesize_abs pp_abs (t, cxt)
	   else if combinSyntax.is_fail t then parenthesize_fail pp_fail (t, cxt)
	   else if oneSyntax.is_one t then pp_unit (t, cxt)
						   (* else if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) *)
	   else if is_supported_pmatch t then pp_case_with_guard (t, cxt)
	   else if TypeBase.is_case t then pp_case (t, cxt)
						   (* else if is_the_value t then pp_itself t *)
	   else if is_const t then pp_const (t, cxt)
	   else if is_comb t then parenthesize_comb pp_comb (t, cxt)
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
    (foldr1 (op $$) o map pp_defn_clause) ts

and pp_defn_clause (t : term) =
    let val (l, r) = dest_eq t in
	pp_lhs (l, NONE) <+> text "=" <+> pp_terminfo (r, NONE)
    end

and pp_lhs (t, cxt) =
    let
	val is_num_literal = Lib.can Literal.relaxed_dest_numeral
	val is_string_literal = Lib.can Literal.relaxed_dest_string_lit
    in
	if is_var t then pp_variable (t, cxt)
	else if is_arb t then pp_arb (t, cxt)
	else if is_num_literal t then pp_number (t, cxt)
	else if is_string_literal t then pp_string (t, cxt)
	else if listSyntax.is_list t then pp_list (t, cxt)
	else if listSyntax.is_cons t then parenthesize_cons pp_cons (t, cxt)
						       (* else if listSyntax.is_mem t then  *)
	else if pairSyntax.is_pair t then pp_pair (t, cxt)
	else if boolSyntax.is_let t then parenthesize_lets pp_lets (t, cxt)
	else if pairSyntax.is_pabs t then parenthesize_abs pp_abs (t, cxt)
	else if combinSyntax.is_fail t then parenthesize_fail pp_fail (t, cxt)
	else if oneSyntax.is_one t then pp_unit (t, cxt)
						(* else if TypeBase.is_record tm then pp_record i (TypeBase.dest_record tm) *)
						(* else if is_the_value t then pp_itself t *)
	else if is_const t then pp_const (t, cxt)
	else if is_comb t then parenthesize_comb pp_comb (t, cxt)
	else raise ERR "pp_lhs" ("Term with unknown syntax: " ^ Parse.term_to_string t)
    end

(*---------------------------------------------------------------------------*)
(* THEORIES                                                                  *)
(*---------------------------------------------------------------------------*)

fun create_type (name : string, arity : int) =
  let
      val lowercase = ["'a", "'b", "'c", "'d", "'e", "'f", "'g", "'h", "'i",
		       "'j", "'k", "'l", "'m", "'n", "'o", "'p", "'q", "'r",
		       "'s", "'t", "'u", "'v", "'w", "'x", "'y", "'z"]
  in
      mk_type (name, map mk_vartype (List.take (lowercase, arity)))
  end;

fun pp_theory (theory : string) =
  let
      val datatypes = map (pp_type_decl o create_type) (types theory)
      val functions = map (pp_defns o concl o snd) (DB.definitions theory)
      infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2
  in
      text "module" <+> pp_constructor theory <+> text "where"
	   $$$
      (if null datatypes
       then text ""
       else foldr1 (op $$$) datatypes)
	  $$$
	  (if null functions
	   then text ""
	   else foldr1 (op $$$) functions)
  end;

end;
