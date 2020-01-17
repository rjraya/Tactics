theory Tactics
 imports Main "HOL-Analysis.Analysis" "HOL.Numeral_Simprocs" "HOL-Number_Theory.Number_Theory"
begin

section \<open>Background theorems\<close>

lemma sin_pi_2: "sin(x + pi/2) \<equiv> cos(x)" 
  by (simp add: sin_cos_eq)

lemma cos_periods:
  fixes k' :: int and k :: real
  assumes "k  \<equiv> 2 * of_int k'" 
  shows "cos (x + k*pi) \<equiv> cos (x)" 
  (is "?cos1 \<equiv> ?cos2")
proof -
  have "cos (x + k*pi) \<equiv> 
        cos (x + k'*(2*pi))"
    using assms by(simp add: algebra_simps)
  also have "... \<equiv> cos (x)" (is "?a \<equiv> ?b")
  proof -
    have "cos (x + k'*(2*pi)) = cos (x)" 
      using sin_cos_eq_iff by fastforce
    then show "?a \<equiv> ?b"
      by auto
  qed
  finally show "cos (x + k*pi) \<equiv> cos (x)"
    by auto
qed

lemma rewrite_sine_1:
  fixes k' :: int and k :: real
  assumes "k  \<equiv> 2 * of_int k'" 
  shows "sin (x + k*pi + pi/2) \<equiv> cos (x)" 
  using assms cos_periods sin_pi_2 by auto

lemma rewrite_sine_2:
  fixes k' :: int and k :: real
  assumes "k  \<equiv> 2 * of_int k'" 
  shows "sin (x + k*pi) \<equiv> sin (x)" 
proof -
  have "sin (x + k*pi) \<equiv> 
        sin (x + k'*(2*pi))"
    using assms by(simp add: algebra_simps)
  also have "... \<equiv> sin (x)" (is "?a \<equiv> ?b")
  proof -
    have "sin (x + k'*(2*pi)) = sin (x)" 
      using sin_cos_eq_iff by fastforce
    then show "?a \<equiv> ?b"
      by auto
  qed
  finally show "sin (x + k*pi) \<equiv> sin (x)"
    by auto
qed

section \<open>Tactic reasoning\<close>

lemma "sin(x+8*pi+pi/2) = cos x" 
  by(tactic \<open>EqSubst.eqsubst_tac @{context} [1] [@{thm sin_pi_2}] 1
             THEN EqSubst.eqsubst_tac @{context} [1] 
                [@{thm cos_periods[of 8 "8 div 2",simplified]}] 1
             THEN simp_tac @{context} 1
             THEN simp_tac @{context} 1\<close>)
  
ML \<open>
let
  val ctxt = @{context}
  val goal = @{prop "sin(x+8*pi+pi/2) = cos x"}
in
  Goal.prove ctxt ["x"] [] goal
    (fn _ => EqSubst.eqsubst_tac @{context} [1] [@{thm sin_pi_2}] 1
             THEN EqSubst.eqsubst_tac @{context} [1] 
                [@{thm cos_periods[of 8 "8 div 2",simplified]}] 1
             THEN simp_tac @{context} 1
             THEN simp_tac @{context} 1) 
end
\<close>

section \<open>Sine pi pi/2\<close>
(* Instead of seeing if there is pi/2 just produce two theorems: one for pi/2 and one
   without pi/2. The real variability is in the coefficient of pi. *)
ML \<open>
fun rewrite_sine ctxt ct =
  let
    val sum = ct |> Thm.term_of |> dest_comb |> snd 
    val x = sum |> dest_comb |> fst |> dest_comb |> snd 
            |> dest_comb |> fst |> dest_comb |> snd
    val k = sum |> dest_comb |> fst |> dest_comb |> snd 
            |> dest_comb |> snd |> dest_comb |> fst
            |> dest_comb |> snd |> dest_comb |> snd |> HOLogic.dest_numeral
    val rk = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.realT k))
    val ik2 = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.intT (k div 2)))
    val cx = SOME( Thm.cterm_of ctxt x)
  in    
    SOME (Thm.instantiate' [] [rk,ik2,cx] @{thm rewrite_sine_1})    
  end
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin(x+8*pi+pi/2)"}
\<close>

simproc_setup sine1 ("sin(x+a*pi+pi/2)") = \<open>K rewrite_sine\<close>

(* this should be handled by sine1 only, but is not *)
lemma "sin(x+8*pi+pi/2) = cos(x)"
  apply simp
  sorry

(* this should be handled by sine1 only, but is not *)
lemma "sin(x+8*pi+pi/2) = cos(x)"
  apply(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>)
  sorry


section \<open>Sine pi\<close>

ML \<open>
fun rewrite_sine' ctxt ct =
  let
    val sum = ct |> Thm.term_of |> dest_comb |> snd 
    val x = sum |> dest_comb |> fst |> dest_comb |> snd 
    val k = sum |> dest_comb |> snd |> dest_comb |> fst 
            |> dest_comb |> snd |> dest_comb |> snd |> HOLogic.dest_numeral
    val rk = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.realT k))
    val ik2 = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.intT (k div 2)))
    val cx = SOME( Thm.cterm_of ctxt x)
  in                                                   
    SOME (Thm.instantiate' [] [rk,ik2,cx] @{thm rewrite_sine_2})    
  end
\<close>

ML \<open>
rewrite_sine' @{context} @{cterm "sin(x+1222222222*pi)"}
\<close>

simproc_setup sine2 ("sin(x+a*pi)") = \<open>K rewrite_sine'\<close>

section \<open>Sine pi/2\<close>
(* Instead of seeing if there is pi/2 just produce two theorems: one for pi/2 and one
   without pi/2. The real variability is in the coefficient of pi. *)
ML \<open>
fun rewrite_sine'' ctxt ct =
  let
    val sum = ct |> Thm.term_of |> dest_comb |> snd 
    val x = sum |> dest_comb |> fst |> dest_comb |> snd 
    val cx = SOME( Thm.cterm_of ctxt x)
  in    
    SOME (Thm.instantiate' [] [cx] @{thm sin_pi_2})    
  end
\<close>

ML \<open>
rewrite_sine'' @{context} @{cterm "sin(x+pi/2)"}
\<close>

simproc_setup sine3 ("sin(x+pi/2)") = \<open>K rewrite_sine''\<close>

section \<open>Experiments\<close>

lemma "sin(x+pi/2) = cos(x)"
  by simp

(* this should be handled by sine1 only, but is not *)
lemma "sin(x+8*pi+pi/2) = cos(x)"
  apply(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>)
  sorry

(* Now we need to study the simplifier *)

ML \<open>
fun rewrite_sine' ctxt ct =
  let
    val sum = ct |> Thm.term_of |> dest_comb |> snd 
    val x = sum |> dest_comb |> fst |> dest_comb |> snd 
    val k = sum |> dest_comb |> snd |> dest_comb |> fst 
            |> dest_comb |> snd |> dest_comb |> snd |> HOLogic.dest_numeral
    val rk = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.realT k))
    val ik2 = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.intT (k div 2)))
    val cx = SOME( Thm.cterm_of ctxt x)
  in                                                   
    SOME (Thm.instantiate' [] [rk,ik2,cx] @{thm rewrite_sine_2})    
  end
\<close>

ML \<open>
rewrite_sine' @{context} @{cterm "sin(x+1222222222*pi)"}
\<close>

simproc_setup sine2 ("sin(x+a*pi)") = \<open>K rewrite_sine'\<close>

lemma "sin(x+8*pi) = sin(x)"
  by simp

(* or just observe to what things the simplifier rewrites useful terms *)



end