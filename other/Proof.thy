theory Proof
  imports Main
begin

ML \<open>
val my_thm =
let
  val assm1 = @{cprop "\<And> (x::nat). P x \<Longrightarrow> Q x"}  
  val assm2 = @{cprop "(P::nat \<Rightarrow> bool) t"}
  val Pt_implies_Qt = Thm.assume assm1 |> Thm.forall_elim @{cterm "t::nat"}
  val Qt = Thm.implies_elim Pt_implies_Qt (Thm.assume assm2)
in
  Qt |> Thm.implies_intr assm2 |> Thm.implies_intr assm1
end

val my_thm_vars =
let
  val ctxt0 = @{context}  
  val (_, ctxt1) = Variable.add_fixes ["P", "Q", "t"] ctxt0
in
  singleton (Proof_Context.export ctxt1 ctxt0) my_thm
end



\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "my_thm"}, []), [my_thm_vars]) #> snd 
\<close>

thm my_thm

end