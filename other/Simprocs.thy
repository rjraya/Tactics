theory Simprocs
 imports Main "HOL-Analysis.Analysis" "HOL.Numeral_Simprocs" "HOL-Number_Theory.Number_Theory"
begin

section \<open>Introduction to simprocs\<close>

ML \<open>
val pretty_term = Syntax.pretty_term
val pwriteln = Pretty.writeln

fun pretty_cterm ctxt ctrm = 
 pretty_term ctxt (Thm.term_of ctrm)

fun fail_simproc ctxt redex = 
let 
  val _ = pwriteln (Pretty.block [Pretty.str "The redex: ", pretty_cterm ctxt redex])
in 
  NONE
end
\<close>

simproc_setup fail ("Suc n") = \<open>K fail_simproc\<close>

lemma 
  shows "Suc 0 = 1" 
  apply(simp)
  oops

lemma plus_one:
  shows "Suc n \<equiv> n + 1" by simp

ML \<open>
fun plus_one_simproc _ _ redex = 
  case Thm.term_of redex of
    @{term "Suc 0"} => NONE
  | _ => SOME @{thm plus_one}

val plus_one =
 Simplifier.make_simproc @{context} "sproc +1" {lhss = [@{term "Suc n"}], proc = plus_one_simproc}
\<close>

lemma 
  shows "P (Suc (Suc (Suc 0))) (Suc 0)"
  apply(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [plus_one]) 1\<close>)
  oops

text \<open>Simproc for Suc -> n+1\<close>


text \<open>
  When seeing a pattern Suc t add 1 to the number t
\<close>

ML \<open>
fun dest_suc_trm (Const (@{const_name "Suc"}, _) $ t) = 1 + dest_suc_trm t
  | dest_suc_trm t = snd (HOLogic.dest_number t) ;

dest_suc_trm @{term "Suc 1"} ;

fun get_thm ctxt (t,n) = 
let
 val num = HOLogic.mk_number @{typ "nat"} n
 val goal = Logic.mk_equals (t, num)
in 
 Goal.prove ctxt [] [] goal (K (Arith_Data.arith_tac ctxt 1))
end ;

get_thm @{context} (@{term "Suc 0"},1) ;

fun get_thm_alt ctxt (t,n) = 
let
 val num = HOLogic.mk_number @{typ "nat"} n
 val goal = Logic.mk_equals (t, num)
 val num_ss = put_simpset HOL_ss ctxt addsimps @{thms semiring_norm}
in 
 Goal.prove ctxt [] [] goal (K (simp_tac num_ss 1))
end ;

get_thm @{context} (@{term "Suc 1"},2) ;

fun nat_number_simproc _  ctxt ct = 
 SOME (get_thm_alt ctxt (Thm.term_of ct, dest_suc_trm (Thm.term_of ct)))
 handle TERM _ => NONE ;

nat_number_simproc K @{context} @{cterm " 1 :: nat"} ;

val nat_number = 
 Simplifier.make_simproc @{context} "nat_number" {lhss = [@{term "Suc n"}], proc = nat_number_simproc} ;
\<close>

lemma 
  shows "P (Suc (Suc 2)) (Suc 99) (0 :: nat) (Suc 4 + Suc 0) (Suc (0 + 0))"
  apply(tactic \<open>simp_tac (put_simpset HOL_ss @{context} addsimprocs [nat_number]) 1\<close>)
  oops


ML \<open>
fun dest_sum term =
  case term of
    (@{term "(+):: nat \<Rightarrow> nat \<Rightarrow> nat"} $ t1 $ t2) =>
      (snd (HOLogic.dest_number t1),snd (HOLogic.dest_number t2))
  | _ => raise TERM ("dest_sum", [term]) ;

fun get_sum_thm ctxt t (n1, n2) =
let
 val sum = HOLogic.mk_number @{typ "nat"} (n1 + n2)
 val goal = Logic.mk_equals (t, sum)
in
 Goal.prove ctxt [] [] goal (K (Arith_Data.arith_tac ctxt 1))
end ;

get_sum_thm @{context} @{term "1+2::nat"} (1,2);


fun add_sp_aux ctxt t =
let
 val t' = Thm.term_of t
in
 SOME (get_sum_thm ctxt t' (dest_sum t'))
 handle TERM _ => NONE
end 
\<close>

simproc_setup add_sp ("t1+t2") = \<open>K add_sp_aux\<close>

lemma 
  shows "P (Suc (Suc 2)) (Suc 99) (0 :: nat) (Suc 4 + Suc 0) (Suc (0 + 0))"
  apply(tactic \<open>simp_tac (put_simpset HOL_ss @{context} addsimprocs [nat_number]) 1\<close>)
  apply(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc add_sp}]) 1\<close>)
  apply(tactic \<open>simp_tac (put_simpset HOL_ss @{context} addsimprocs [nat_number]) 1\<close>)
  oops

section \<open>Rewrite sin(pi/2-x) to cos(x) tactic\<close>

lemma "sin (pi / 2 - x) = cos(x)" 
  by (simp add: cos_sin_eq)

lemma "sin ((pi - x) / 2) = cos(x / 2)" 
  by (simp add: cos_sin_eq diff_divide_distrib)

text \<open>This version does not work\<close>

lemma "sin (7*pi/2-x) = -cos(x)" 
  
  oops

lemma "sin(x+8*pi+pi/2) = cos x" 
  
  oops


text \<open>A smt proof is not considered sufficiently good\<close>
lemma "sin(x+3*pi) = -sin(x)"
  by (smt sin_periodic_pi)



text \<open>Let's try to prove it to gain intuition in what the simproc should do\<close>

lemma "sin (7*pi/2-x) = -cos(x)" 
proof -
  let ?x = "7*pi/2-x"

  have "a = -x + 7*pi/2"
    apply simp
    sorry

  have "?x - 2*pi = 3*pi/2 - x"
    by(simp add: field_simps)
  moreover have "sin(3*pi/2 - x) = -cos(x)"
    by (metis (no_types, hide_lams) Groups.mult_ac(2) cos_3over2_pi diff_zero mult_1s(1) mult_minus_left mult_zero_left numeral_code(1) sin_3over2_pi sin_diff times_divide_eq_right)

  (* The problem is that here I know the answer, but otherwise it has to be computed *)
  ultimately show ?thesis 
    by (metis cos_2pi_minus diff_zero id_apply mult.commute sin_2pi_minus sin_diff sin_minus_pi sin_pi_minus)

qed

lemma sin_pi_2: "sin(x + pi/2) = cos(x)" 
  by (simp add: sin_cos_eq)

lemma "cos(x+8*pi) = cos x"   
  by (smt cos_periodic)

lemma cos_even: "[k = 0] (mod 2) \<Longrightarrow> cos(x + k*pi) = cos(x)" 
  by (metis (no_types, hide_lams) cong_0_iff cos_add cos_npi_int diff_0 diff_minus_eq_add diff_zero mult.commute mult.right_neutral mult_zero_left of_int_numeral of_nat_numeral sin_cos_eq sin_npi_int)
  
find_theorems "cos (_ + _*pi)"

lemma "sin(x+8*pi+pi/2) = cos x" 
  apply(subst sin_pi_2)
  thm cos_even[of 8 x]
  using cos_even[of 8 x] 
  using [[unify_trace_failure]]
 
proof -
  
  (*
    (* first version of the proof *)
    
    have "sin(x+8*pi+pi/2) = cos(x+8*pi)"
      by (metis Groups.add_ac(2) cos_minus cos_sin_eq diff_minus_eq_add id_apply of_real_eq_id)
    also have "... = cos(x)"
      by (smt cos_periodic)
    
    find_theorems "sin(_ + pi/2)"
    finally show ?thesis
      by blast
 *)
  oops


ML \<open>

(* Takes a term of the form sin(t) and returns t*)
fun dest_sine t =
  case t of
    (@{term "(sin):: real \<Rightarrow> real"} $ t') => t'
  | _ => raise TERM ("dest_sine", [t]) ;

dest_sine @{term "sin (2::real)"} ;

fun rewriter x k k' =
 if (k mod 2 = 0 andalso k' = 0) then @{term "sin::real \<Rightarrow> real"} $ x
 else if (k mod 2 = 0 andalso k' = 1) then @{term "cos::real \<Rightarrow> real"} $ x
 else if (k mod 2 = 1 andalso k' = 0) then @{term "-sin::real \<Rightarrow> real"} $ x
 else @{term "-cos::real \<Rightarrow> real"} $ x ;

(* For the moment assume we are given x k k' *)
fun prover ctxt t x k k' =
let
 val goal = Logic.mk_equals (t, rewriter x k k')
in
 Goal.prove ctxt [] [] goal (K (Arith_Data.arith_tac ctxt 1))
end ;

prover @{context} @{term "sin((x::real)+8*pi+pi/2)"} @{term "(x::real)"} 8 1

\<close>

end