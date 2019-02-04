structure Hopster =
struct

open HolKernel computeLib;

open HughesPP;

val ERR = mk_HOL_ERR "Hopster";

infix <+>
infix $$

infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2;

fun secr f y x = f (x, y);

fun id x = x;

fun string_to_term s = Term [QUOTE s];

fun term_to_quote t = [QUOTE (term_to_string t)];

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
fun conjecture () = (char #"\n" >> (char #"\n" <|> null) >> return nil) <|>
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
fun HARD_TAC lemmas goal =
    let
        val vars = (fst o strip_forall o snd) goal;
        val induct_tacs = map (fn var => Induct_on (term_to_quote var)
                                                   \\ metis_tac lemmas)
                              vars;
        val tacs = induct_tacs @ [metis_tac lemmas]
    in
        TRY (FIRST_PROVE tacs) goal
    end;

fun EASY_TAC lemmas = fs (map (fn x => Ntimes x 10) lemmas);

fun prove_conjectures_aux (tactic, [], thms, [], _, _) = ([], thms)
  | prove_conjectures_aux (tactic, [], thms, acc, _, false) = (rev acc, thms)
  | prove_conjectures_aux (tactic, [], thms, acc, defns, true) =
    let val _ = print "Finished one loop, will do another...\n" in
	prove_conjectures_aux (tactic, rev acc, thms, [], defns, false)
    end
  | prove_conjectures_aux (tactic, g::gs, thms, acc, defns, status) =
    case tactic (defns @ thms) g of
	([], f) => prove_conjectures_aux (tactic, gs, f [] :: thms, acc, defns, true)
      | _ => prove_conjectures_aux (tactic, gs, thms, g :: acc, defns, status);

fun combinations_aux ([] : 'a list)
		     (ys : 'a list) = []
  | combinations_aux (x::xs) ys = (x, ys @ xs) :: combinations_aux xs (ys @ [x]);

fun combinations (xs : 'a list) : ('a * 'a list) list =
    combinations_aux xs [];

fun is_unprovable (tactic, goal) =
    case tactic goal of
	([], _) => false
      | _ => true;

fun impossible_conjectures_aux ([], (us, ps)) = (us, rev ps)
  | impossible_conjectures_aux (x::xs, (us,ps)) =
    let
	val (conj, lemmas) = x;
	val tac = TRY (FIRST_PROVE [EASY_TAC lemmas, HARD_TAC lemmas])
    in
	if is_unprovable (tac, conj)
	then impossible_conjectures_aux(xs, (conj :: us, ps))
	else impossible_conjectures_aux(xs, (us, conj :: ps))
    end;

fun impossible_conjectures (goals : (term list * term) list,
			    defns : thm list) =
    let
	val xs = map (fn (g, cs) => (g, defns @ (map mk_thm cs)))
		     (combinations goals)
    in
	impossible_conjectures_aux (xs, ([],[]))
    end;

fun print_results (conjs, lemmas) =
    let
	val _ = print "** Conjectures found **\n";
	val _ = map (print o (fn x => x ^ "\n") o term_to_string o snd) conjs;
	val _ = print "** Lemmas found **\n";
	val _ = map (print o (fn x => x ^ "\n") o thm_to_string) lemmas
    in
	()
    end;

fun prove_conjectures defns conjs =
    let
	val t = Timer.startRealTimer ();
	val args = (EASY_TAC, conjs, [], [], defns, false);
	val (gs, ls) = prove_conjectures_aux args;
	val t1 = Time.toString (Timer.checkRealTimer t);
	val (us, ps) = impossible_conjectures (gs, defns @ ls);
	val _ = print ("Number of unprovables is: " ^ Int.toString(length us) ^ "\n");
	val t2 = Time.toString (Timer.checkRealTimer t);
	val args' = (HARD_TAC, ps, [], [], defns @ ls, false);
	val (us', ps') = prove_conjectures_aux args';
	val t3 = Time.toString (Timer.checkRealTimer t);
	val _ = print ("Time to find easy lemmas: " ^ t1 ^ "\n"
		       ^ "Time to find impossible lemmas: " ^ t2 ^ "\n"
		       ^ "Time to finish proof loop: " ^ t3 ^ "\n")
    in
	(us @ us', ps')
	(* (us', ps') *)
	(* (gs, ls) *)
    end;

fun quickspec (datatypes : hol_type list)
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
	  in
	      conjs
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
	    (funnames : (string * string) list) =
    let val funs = map (uncurry DB.fetch) funnames in
	quickspec datatypes funs |> prove_conjectures funs
    end;

(**************)
(* Proof mode *)
(**************)

structure Set = HOLset;

fun is_constructor f =
    let
	fun constructors_of t = TypeBase.constructors_of t handle (HOL_ERR _) => [];
	val name_of = #Name o dest_thy_const;
	val theory_of = #Thy o dest_thy_const;
	val cs = (constructors_of o snd o strip_fun o type_of) f
    in
	exists (fn g => name_of f = name_of g andalso
			theory_of f = theory_of g) cs
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


fun destroy_type (t : hol_type) =
    if is_vartype t
    then []
    else let val (name, args) = dest_type t in
	     EmitHaskell.create_type (name, length args) :: List.concat (map destroy_type args)
	 end;

fun all_ground_types (t : hol_type) =
    let val (args, ret) = strip_fun t in
	ret ::
	(if null args
	 then []
	 else List.concat (map all_ground_types args))
    end;

val datatypes =
    Set.foldr (fn (x, xs) => Set.addList(xs, destroy_type x))
	      (Set.empty Type.compare)
    o Set.foldr (fn (x, xs) => Set.addList (xs, (all_ground_types o type_of) x))
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

fun hopster_tac (goal : term list * term) =
    let
	val fs = (functions o snd) goal;
	val fs' = Set.foldr (fn (x, xs) => Set.union (xs, (functions o concl o find_defn) x)) fs fs;
        val funs = map find_defn (Set.listItems fs');
	val types = (Set.listItems o datatypes o snd) goal;
        val (_, lemmas) = prove_conjectures funs (quickspec types funs)
    in
        FIRST_PROVE [EASY_TAC lemmas, HARD_TAC lemmas] goal
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
	val names = map (string_to_term o secl (op ^) "$" o fst) funs;
	val matches = map (length o DB.match [thy]) names;
	val cmp = curry (op> o (snd ## snd));
	val top = sort cmp (zip funs matches)
    in
	map fst (List.take (top, TOP_FUNS_SIZE))
    end

end;
