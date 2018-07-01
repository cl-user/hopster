structure Hopster =
struct

open HolKernel

open HughesPP

infix <+>
infix $$

infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2;

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

val get_defn_name =
    let
	val equations = map (snd o strip_forall) o strip_conj o concl;
	val lhs_ = lhs o hd;
	val name = fst o dest_const o fst o strip_comb
    in
	name o lhs_ o equations
    end;


fun pp_defns (defns : thm list) =
    let
	val hs_variable = Dictionary.hs_variable;
	val names = map ((fn mlname => (hs_variable mlname, mlname)) o get_defn_name) defns;
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
	val args' = (HARD_TAC, gs, [], [], defns @ lemmas, false)
    in
	prove_conjectures_aux args'
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
  let
      open OS.Process
      val _ = metisTools.limit := {time = SOME 1.0, infs = NONE}
      val name = "Explore"
      val ts = map (fn (theory, name) => DB.fetch theory name) defns
      val contents = build_haskell_module name datatypes ts
      val _ = write_haskell_module name contents
      val cmd = "tip-ghc " ^ name ^ ".hs" ^ " | tip-spec | tip --hopster > tip-out.txt"
  in
      if isSuccess (system cmd)
      then
	  let
	      val f = TextIO.openIn "tip-out.txt";
	      val conjs = parse_conjectures (TextIO.inputAll f);
	      val _ = TextIO.closeIn f;
	      val (conjs', lemmas) = prove_conjectures (conjs, ts)
	  in
	      (conjs', lemmas)
	      (* conjs *)
	  end
      else raise ERR "explore" "Error while invoking tip tools"
  end;

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
    let val cmp = pair_compare (String.compare,String.compare) in
	Set.foldr (fn (x, xs) => Set.add (xs, x |> dest_thy_const
						|> (fn {Name=name, Thy=thy, ...} => (thy, name))))
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

fun db_fetch (thy, name) = DB.fetch thy (name ^ !Defn.def_suffix);

fun prove (goal : term list * term) =
    let
	val fs = (functions o snd) goal;
	val fs' = Set.foldr (fn (x, xs) => Set.union (xs, (functions o concl o db_fetch) x)) fs fs;
	val ts = (datatypes o snd) goal
    in
	Hopster.explore (Set.listItems ts)
			(fs' |> Set.listItems
			     |> map (fn (thy, name) => (thy, name ^ !Defn.def_suffix)))
    end;

end;
