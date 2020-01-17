theory Parsing
  imports Main
  keywords "foobar" :: thy_decl and
          "foobar_trace" :: thy_decl and
          "foobar_goal" :: thy_goal and
          "foobar_prove" :: thy_goal
begin

ML \<open>
($$ "h") (Symbol.explode "hello")
\<close>

ML \<open>
let
  val do_nothing = Scan.succeed (Local_Theory.background_theory I)
in
  Outer_Syntax.local_theory @{command_keyword "foobar"} "description of foobar" do_nothing
end
\<close>

foobar


(*
function that first parses a proposition (using the parser Parse.prop)
then prints out some tracing information (using the function trace_prop)
finally does nothing.
*)
ML \<open>
let
  fun trace_prop str = Local_Theory.background_theory (fn ctxt => (tracing str; ctxt))
in
  Outer_Syntax.local_theory @{command_keyword "foobar_trace"} "traces a proposition" (Parse.prop >> trace_prop)
end
\<close>


foobar_trace "True \<and> False"


ML \<open>
let
  fun goal_prop str ctxt =
  let
    val prop = Syntax.read_prop ctxt str
  in
    Proof.theorem NONE (K I) [[(prop, [])]] ctxt  
  end
in
  Outer_Syntax.local_theory_to_proof @{command_keyword "foobar_goal"}
   "proves a proposition"
   (Parse.prop >> goal_prop)
 end
\<close>


foobar_goal "True \<and> True"
  apply(rule conjI)
   apply(rule TrueI)+
  done

ML \<open>
structure Result = Proof_Data (
  type T = unit -> term
  fun init thy () = error "Result"
)

val result_cookie = (Result.get, Result.put, "Result.put")
\<close>

ML \<open>
let
 fun after_qed thm_name thms lthy = Local_Theory.note (thm_name, (flat thms)) lthy |> snd

 fun setup_proof (thm_name, src) lthy =
 let
 val (text, _) = Input.source_content src
 val trm = Code_Runtime.value lthy result_cookie ("", text)
 in
 Proof.theorem NONE (after_qed thm_name) [[(trm, [])]] lthy
 end

 val parser = Parse_Spec.opt_thm_name ":" -- Parse.ML_source
 in
 Outer_Syntax.local_theory_to_proof @{command_keyword "foobar_prove"}
 "proving a proposition"
 (parser >> setup_proof)
 end
\<close>

ML \<open>
val prop_true = @{prop "True"}
\<close>

foobar_prove test : prop_true
  apply(rule TrueI)
  done

thm test

print_methods

method_setup foo =
  \<open>Scan.succeed (fn ctxt =>
    (SIMPLE_METHOD ((eresolve_tac ctxt [@{thm conjE}] THEN'
                     resolve_tac ctxt [@{thm conjI}]) 1)))\<close>
"foo method for conjE and conjI"

lemma shows "A \<and> B \<Longrightarrow> C \<and> D"
  apply(foo)
  sorry




end