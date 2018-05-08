structure Hopster =
struct

open HolKernel

open EmitHaskell

infix <+>
infix $$

fun build_haskell_module (name : string)
			 (datatypes : hol_type list)
			 (defns : (string * string) list) =
  let
      val ds = map pp_type_decl datatypes
      val ts = map (pp_defns o concl o (fn (theory, name) => DB.fetch theory name)) defns
      infix $$$ fun d1 $$$ d2 = d1 $$ text "" $$ d2
  in
      text "module" <+> text name <+> text "where"
	   $$$
	   text "import Prelude ()"
	   $$$
	   foldr (op $$$) (text "") ds
	   $$$
	   foldr (op $$$) (text "") ts
  end;

fun write_haskell_module (modulename : string)
			 (contents : Doc) =
  let
      val file = TextIO.openOut (modulename ^ ".hs")
      val _ = TextIO.output (file, pretty 80 80 contents)
  in TextIO.closeOut file
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
      val name = "Explore"
      val contents = build_haskell_module name datatypes defns
      val _ = write_haskell_module name contents
      val cmd = "tip-ghc " ^ name ^ ".hs" ^ " | tip-spec | tip --hipster > tip-out.txt"
  in
      if isSuccess (system cmd)
      then let val outfile = TextIO.openIn "tip-out.txt" in
	    TextIO.closeIn outfile
	   end
      else raise ERR "explore" "Error while invoking tip tools"
  end;

end;
