structure Hopster =
struct

open HolKernel computeLib;

open HughesPP;

infix <+>
infix $$

infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2;

fun secr f y x = f (x, y);

fun id x = x;

fun string_to_term s = Term [QUOTE s];

fun foldr1 f [x] = x
  | foldr1 f (x :: xs) = f (x, (foldr1 f xs));

fun annotate_type (hsname, mlname) =
    text ("{-# ANN type " ^ hsname ^ " (Name \"" ^ mlname ^ "\") #-}");

fun annotate_term (hsname, mlname) =
    text ("{-# ANN " ^ hsname ^ " (Name \"" ^ mlname ^ "\") #-}");

fun pp_datatype (d : hol_type) =
    let
	fun translate mlname = (Dictionary.hs_constructor mlname, mlname)
	val mlname = (fst o dest_type) d;
	val consnames = map (translate o fst o dest_const)
			    (TypeBase.constructors_of d)
    in
	annotate_type (translate mlname)
		      $$
		      foldr1 (op $$) (map annotate_term consnames)
		      $$
		      EmitHaskell.pp_type_decl d
    end;

val name_of_defn =
    let
	val fst_defn = hd o strip_conj;
	val eqn = snd o strip_forall;
	val name = fst o strip_comb
    in
	name o lhs o eqn o fst_defn o concl
    end;

fun pp_defns (defns : thm list) =
    let
	val hs_variable = Dictionary.hs_variable;
	val const_to_string = fst o dest_const;
	val names = map ((fn mlname => (hs_variable mlname, mlname)) o const_to_string o name_of_defn) defns;
    in
	foldr1 (op $$) (map annotate_term names)
	      $$$
	      foldr1 (op $$$) (map (EmitHaskell.pp_defns o concl) defns)
    end;

fun build_haskell_module (name : string)
			 (datatypes : hol_type list)
			 (defns : thm list) =
    text "module" <+> text name <+> text "where"
	 $$$
	 text "import Prelude ()"
	 $$$
	 text "import Tip"
	 $$$
	 foldr1 (op $$$) (map pp_datatype datatypes)
	 $$$
	 pp_defns defns;

fun write_haskell_module (modulename : string)
			 (contents : Doc) =
  let
      val file = TextIO.openOut (modulename ^ ".hs")
      val _ = TextIO.output (file, pretty 80 80 contents)
  in TextIO.closeOut file
  end;

local
    open Parser;
    infix >> fun ma >> mb = ma >>= (fn _ => mb)
in
fun conjecture () = (char #"\n" >> char #"\n" >> return nil) <|>
	            (item >>= (fn x => conjecture () >>= (fn xs => return (x :: xs))));

val conjectures = many (token (conjecture ()))
end;

fun string_to_term s = Term [QUOTE s];

fun parse_conjectures cs =
    let val conjs = case Parser.parse conjectures cs of
			[] => []
		      | [(xs, out)] => map implode xs
    in
	map (fn conj => ([], string_to_term conj)) conjs
    end;

val _ = metisTools.limit := {time = SOME 1.0, infs = NONE};

(* Tactic to prove a single goal *)
fun HARD_TAC lemmas = TRY (TRY (Induct) \\ metis_tac lemmas);

fun EASY_TAC lemmas = fs (map (fn x => Ntimes x 10) lemmas);

fun prove_conjectures_aux (tactic, [], thms, [], _, _) = ([], thms)
  | prove_conjectures_aux (tactic, [], thms, acc, _, false) = (rev acc, thms)
  | prove_conjectures_aux (tactic, [], thms, acc, defns, true) =
    let val _ = print "Finished one loop, will do another...\n" in
	prove_conjectures_aux (tactic, rev acc, thms, [], defns, false)
    end
  | prove_conjectures_aux (tactic, g::gs, thms, acc, defns, status) =
    case tactic (defns @ thms) g of
	([], f) => let val _ = print "Conjecture proven...\n" in
		       prove_conjectures_aux (tactic, gs, f [] :: thms, acc, defns, true)
		   end
      | _ => let val _ = print "Conjecture not proven...\n" in
		 prove_conjectures_aux (tactic, gs, thms, g :: acc, defns, status)
	     end;

fun prove_conjectures (goals, defns) =
    let
	val args = (EASY_TAC, goals, [], [], defns, false);
	val (gs, ls) = prove_conjectures_aux args;
	val args' = (HARD_TAC, gs, [], [], defns @ ls, false)
    in
	prove_conjectures_aux args'
    end;

fun explore_aux (datatypes : hol_type list)
		(defns : thm list) =
    let
      open OS.Process
      val name = "Explore"
      val contents = build_haskell_module name datatypes defns
      val _ = write_haskell_module name contents
      val cmd = "tip-ghc " ^ name ^ ".hs" ^ " | tip-spec | tip --hopster > tip-out.txt"
    in
      if isSuccess (system cmd)
      then
	  let
	      val f = TextIO.openIn "tip-out.txt";
	      val conjs = parse_conjectures (TextIO.inputAll f);
	      val _ = TextIO.closeIn f;
	      val (conjs', lemmas) = prove_conjectures (conjs, defns)
	  in
	      (conjs', lemmas)
	  end
      else raise ERR "explore" "Error while invoking tip tools"
    end;

(* Perform theory exploration on a set of datatypes and function definitions. *)
(* `datatypes` is a list of HOL types.                                        *)
(* `defns` is a list of pairs where the first component is the name of        *)
(* a theory and the second component is the the name under which the          *)
(* function definition is saved in its theory segment.                        *)
(*                                                                            *)
(* EXAMPLE: Hopster.explore [] [("list","REVERSE_DEF"), ("list","APPEND")]    *)
fun explore (datatypes : hol_type list)
	    (defns : (string * string) list) =
    explore_aux datatypes
		(map (uncurry DB.fetch) defns);

(**************)
(* Proof mode *)
(**************)

structure Set = HOLset;

fun is_constructor f =
    let
	fun constructors_of t = TypeBase.constructors_of t handle (HOL_ERR _) => [];
	val cs = (constructors_of o snd o strip_fun o type_of) f
    in
	exists (fn g => f = g) cs
    end;

fun is_proper_fun t =
    let val {Thy=thy, Ty=ty, ...} = dest_thy_const t in
	(fst o dest_type) ty = "fun"
	andalso	not (thy = "min")
	andalso	not (thy = "bool")
    end;

val proper_funs = Set.foldr (fn (x, xs) => if is_const x andalso is_proper_fun x
					      then Set.add (xs, x)
					      else xs)
			       (Set.empty Term.compare)
		  o all_atoms;

val functions =
    let val cmp = pair_compare (String.compare,Term.compare) in
	Set.foldr (fn (x, xs) => Set.add (xs, ((#Thy o dest_thy_const) x, x)))
		  (Set.empty cmp)
	o Set.foldr (fn (x, xs) => if (not o is_constructor) x
				   then Set.add (xs, x)
				   else xs)
		    (Set.empty Term.compare)
	o proper_funs
    end;

val datatypes =
    Set.foldr (fn (x, xs) => Set.add (xs, (snd o strip_fun o type_of) x))
		   (Set.empty Type.compare)
    o proper_funs;

structure ComputeData =
struct

val name = fst o fst;
val theory = snd o fst;
val transform = snd;

end;

fun find_defn (thy, name) =
    let
	val name' = (#Name o dest_thy_const) name
	val is_thy = secr (op =) thy o ComputeData.theory;
	val is_name = secr (op =) name' o ComputeData.name
    in
	computeLib.listItems computeLib.the_compset
			     |> List.find (fn x => is_thy x andalso is_name x)
			     |> valOf
			     |> ComputeData.transform
			     |> foldr (fn (clauses.RRules rules, xs) => rules :: xs) []
			     |> List.concat
			     |> foldr1 (uncurry CONJ)
    end;

fun prove (goal : term list * term) =
    let
	val fs = (functions o snd) goal;
	val fs' = Set.foldr (fn (x, xs) => Set.union (xs, (functions o concl o find_defn) x)) fs fs;
	val ts = (datatypes o snd) goal
    in
	explore_aux (Set.listItems ts)
		    (fs' |> Set.listItems
			 |> map find_defn)
    end;

fun try f arg =
    SOME (f arg) handle (HOL_ERR _) => NONE;

fun defnames (thy : string) =
    let
	val is_thy = secr (op =) thy o ComputeData.theory;
	val to_thm = foldr1 (uncurry CONJ)
		     o List.concat
		     o foldr (fn (clauses.RRules rules, xs) => rules :: xs) []
		     o ComputeData.transform
    in
	computeLib.listItems computeLib.the_compset
			     |> filter is_thy
			     |> filter (not o null o ComputeData.transform)
			     |> map (fn x => (ComputeData.name x, to_thm x))
    end;

val TOP_FUNS_SIZE = 3;

fun top_thy_funs (thy : string) =
    let
	val funs = defnames thy;
	val names = map (string_to_term o fst) funs;
	val matches = map (length o DB.match [thy]) names;
	val cmp = curry (op> o (snd ## snd));
	val top = sort cmp (zip funs matches)
    in
	map fst (List.take (top, TOP_FUNS_SIZE))
    end

end;
