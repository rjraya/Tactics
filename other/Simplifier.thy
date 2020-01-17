theory Simplifier
  imports Main
begin
  (* A study of the method for the simplifier in ML *)

  (* Printing the simpset *)}
ML \<open>

val pretty_term = Syntax.pretty_term

fun pretty_terms ctxt trms =
  Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))

fun pretty_thm_no_vars ctxt thm =
  let 
    val ctxt' = Config.put show_question_marks false ctxt
  in
    Syntax.pretty_term ctxt' (Thm.prop_of thm)
  end

fun pretty_thms_no_vars ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thm_no_vars ctxt) thms))

fun print_ss ctxt ss =
  let
    val {simps, congs, procs,...} = Raw_Simplifier.dest_ss ss
  fun name_sthm (nm, thm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
  fun name_cthm ((_, nm), thm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
  fun name_trm (nm, trm) =
    Pretty.enclose (nm ^ ": ") "" [pretty_terms ctxt trm]
    val pps = [Pretty.big_list "Simplification rules:" (map name_sthm simps),
               Pretty.big_list "Congruences rules:" (map name_cthm congs),
               Pretty.big_list "Simproc patterns:" (map name_trm procs)]
  in
    pps |> Pretty.chunks |> Pretty.writeln
end
\<close>

  (* Raw-simplifier provides the functionality to extend the simpset *)

ML \<open>
Raw_Simplifier.simpset_of @{context};
print_ss @{context}
\<close>

definition juan: "juanito = 3"

(* For the empty simp-set we need meta equality *)

ML \<open>
val ctx0 = empty_simpset @{context};
print_ss ctx0;
val ctx1 = ctx0 addsimps [@{thm juan} RS @{thm eq_reflection}];
print_ss ctx1 (Raw_Simplifier.simpset_of ctx1);
\<close>

(* HOL basic simpset *)

ML \<open>           
val ctx0 = put_simpset HOL_basic_ss @{context}; 
val ctx1 = ctx0 addsimps [@{thm juan}];
print_ss ctx1 (Raw_Simplifier.simpset_of ctx1);
\<close>


lemma "juanito = 3"
  by(tactic \<open>simp_tac ((put_simpset HOL_basic_ss @{context}) addsimps [@{thm juan}]) 1\<close>)

end