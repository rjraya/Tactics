theory Experiment3
 imports Main "HOL-Analysis.Analysis" "HOL.Numeral_Simprocs" "HOL-Number_Theory.Number_Theory" "HOL-Library.Rewrite"
begin

(* 
Following the answer to this question:

https://stackoverflow.com/questions/58859417/rewriting-sine-using-simprocs-in-isabelle

*)

section \<open>Simproc strategy\<close>

definition "SIN_SIMPROC_ATOM x n = x + of_int n * pi"

lemma ssa_0_n: "SIN_SIMPROC_ATOM 0 n \<equiv> n * pi"
  unfolding SIN_SIMPROC_ATOM_def by simp

lemma ssa_x_0: "SIN_SIMPROC_ATOM x 0 \<equiv> x"
  unfolding SIN_SIMPROC_ATOM_def by simp

subsection \<open>sin_atom_conv\<close>
(* should we pattern match on a numeral or on an int ? *)
ML \<open>
fun sin_atom_conv ctxt ct =
 let 
  val t = ct |> Thm.term_of
  
  val ssa_term = 
    case t of (Const ("Groups.times_class.times", @{typ "real \<Rightarrow> real \<Rightarrow> real"}) $ 
              (Const ("Int.ring_1_class.of_int", @{typ "int \<Rightarrow> real"}) $ t') $
               Const ("Transcendental.pi", @{typ "real"}))  => 
        let 
          val goal = Logic.mk_equals (t, @{term "SIN_SIMPROC_ATOM 0"} $ t' ) 
        in 
          Goal.prove ctxt [] [] goal
                (fn _ => Method.rule_tac ctxt [@{thm ssa_0_n[symmetric]}] [] 1)
        end                 
    | x => 
        let 
          val goal = Logic.mk_equals (t, @{term "SIN_SIMPROC_ATOM"} $ x $ @{term "0::int"}  ) 
        in 
          Goal.prove ctxt [] [] goal
                (fn _ => Method.rule_tac ctxt [@{thm ssa_x_0[symmetric]}] [] 1)
        end
      
 in
 ssa_term
 end
\<close>

subsection \<open>sin_atom_conv tests\<close>

ML \<open>
sin_atom_conv @{context} @{cterm "(2::int)*pi"}  
\<close>

ML \<open>
sin_atom_conv @{context} @{cterm "x+2*pi"}  
\<close>

ML \<open>
sin_atom_conv @{context} @{cterm "(2::int)*pi+x+(2::int)*pi"}  
\<close>


subsection \<open>sin_term_conv\<close>

ML \<open>
fun sin_term_conv ctxt ct =
 let
  val t = ct |> Thm.term_of
  val res =
    case t of (Const ("Groups.plus_class.plus", @{typ "real \<Rightarrow> real \<Rightarrow> real"}) $ t1 $ t2) =>
      let
        val lconv = Thm.prop_of (sin_term_conv ctxt (Thm.cterm_of ctxt t1))

        val rconv = Thm.prop_of (sin_term_conv ctxt (Thm.cterm_of ctxt t2))
        val (_,t1') = Logic.dest_equals lconv
        val (_,t2') = Logic.dest_equals rconv
        val comb =
          case (t1',t2') of 
            (@{term "SIN_SIMPROC_ATOM"} $ x1 $ n1,@{term "SIN_SIMPROC_ATOM"} $ x2 $ n2) =>
              let 
                val farg = 
                  case (x1,x2) of (@{term "0::real"},@{term "0::real"}) => @{term "0::real"}
                               | (x1',@{term "0::real"}) => x1'
                               | (@{term "0::real"},x2') => x2'
                               | (x1',x2') => HOLogic.mk_binop "Groups.plus_class.plus" (x1',x2')
                val sarg = 
                  case (n1,n2) of (@{term "0::int"},@{term "0::int"}) => @{term "0::int"}
                               | (n1',@{term "0::int"}) => n1'
                               | (@{term "0::int"},n2') => n2'
                               | (n1',n2') => HOLogic.mk_binop "Groups.plus_class.plus" (n1',n2')       
              in
                @{term "SIN_SIMPROC_ATOM"} $ farg $ sarg
              end
          | _ => raise TERM ("sin_term_conv outputs a wrong conversion",[lconv,rconv]) 
      in
          Goal.prove ctxt [] [] (Logic.mk_equals (t,comb))
                (fn _ => Method.rule_tac ctxt @{thms HOL.eq_reflection} []  1
                         THEN (simp_tac (put_simpset HOL_basic_ss ctxt addsimps 
                               @{thms SIN_SIMPROC_ATOM_def Int.ring_1_class.of_int_numeral arith_simps}) 1
                              THEN Lin_Arith.simple_tac ctxt 1)
                         ORELSE simp_tac (put_simpset HOL_basic_ss ctxt addsimps 
                               @{thms SIN_SIMPROC_ATOM_def Int.ring_1_class.of_int_numeral arith_simps}) 1)                   
      end
    | _ => sin_atom_conv ctxt ct
 in
  res
 end
\<close>

subsection \<open>sin_term_conv tests\<close>

ML \<open>
sin_term_conv @{context} @{cterm "x+(2::int)*pi"}  
\<close>

ML \<open>
sin_term_conv @{context} @{cterm "(3::int)*pi+x+(2::int)*pi"}  
\<close>

ML \<open>
sin_term_conv @{context} @{cterm "(3::int)*pi+x"}  
\<close>

subsection \<open>Theorems for SIN_SIMPROC_ATOM\<close>

lemma rewrite_sine_even:
  assumes "even k" 
  shows "sin(SIN_SIMPROC_ATOM x k) \<equiv> sin (x)" 
proof(rule HOL.eq_reflection)
  obtain k' where k'_expr: "k = 2 * k'"
    using assms by blast
  have "sin(SIN_SIMPROC_ATOM x k) \<equiv> sin (x + k*pi)"
    unfolding SIN_SIMPROC_ATOM_def by simp
  also have "... \<equiv> sin (x + k'*(2*pi))"
    using k'_expr by(simp add: algebra_simps)
  also have "... \<equiv> sin (x)" (is "?a \<equiv> ?b")
  proof -
    have "sin (x + k'*(2*pi)) = sin (x)" 
      using sin_cos_eq_iff by fastforce
    then show "?a \<equiv> ?b"
      by auto
  qed
  finally show "sin(SIN_SIMPROC_ATOM x k) = sin (x)"
    by simp
qed

lemma rewrite_sine_odd:
  assumes "odd k" 
  shows "sin(SIN_SIMPROC_ATOM x k) \<equiv> -sin (x)" 
proof(rule HOL.eq_reflection)
  obtain k' where k'_expr: "k = 2 * k'+1"
    using assms oddE by blast
  have "sin(SIN_SIMPROC_ATOM x k) \<equiv> sin (x + k*pi)"
    unfolding SIN_SIMPROC_ATOM_def by simp
  also have "... \<equiv> sin (x + k'*(2*pi) + pi)"
    using k'_expr by(simp add: algebra_simps)
  also have "... \<equiv> -sin(x + k'*(2*pi))"
    by simp
  also have "... \<equiv> -sin (x)" (is "?a \<equiv> ?b")
  proof -
    have "sin (x + k'*(2*pi)) = sin (x)" 
      using sin_cos_eq_iff by fastforce
    then show "?a \<equiv> ?b"
      by auto
  qed
  finally show "sin(SIN_SIMPROC_ATOM x k) = -sin (x)"
    by simp
qed

subsection \<open>rewrite_sine\<close>

lemma arg_cong_pure:
  assumes "x \<equiv> y"
  shows "f x \<equiv> f y"
  using assms by simp

lemma truth:
  assumes "a \<equiv> True"
  shows "a"
  using assms by simp

lemma even_to_odd: "even n \<equiv> False \<Longrightarrow> odd n"
  by auto

ML \<open>
fun rewrite_sine ctxt ct =
  let
    val sumt = ct |> Thm.term_of 
    val sum = sumt |> dest_comb |> snd |> Thm.cterm_of ctxt;
    val sum_eq_ssa = sin_term_conv ctxt sum
    val (_,ssa) = Logic.dest_equals (Thm.prop_of sum_eq_ssa)
    val sin_x = @{term "sin::real\<Rightarrow>real"} $ (Thm.term_of sum)
    val sin_ssa = @{term "sin::real\<Rightarrow>real"} $ ssa
    (* sin sum = sin (SIN_SIMPROC_ATOM x n)*)
    val goal1 = Logic.mk_equals (sin_x,sin_ssa)
    val subst_lemma = @{thm arg_cong_pure} OF [sum_eq_ssa]
    val inst_lemma = Thm.instantiate' [SOME @{ctyp "real"}] [SOME @{cterm "sin::real\<Rightarrow>real"}] subst_lemma

    val thm1 = Goal.prove ctxt [] [] goal1
            (fn _ => Method.rule_tac ctxt [inst_lemma] [] 1)
    val (x,k) = case ssa of (@{term SIN_SIMPROC_ATOM} $ x' $ k') => (x',k')
                         | _ => raise TERM ("term should be simproc_atom",[Thm.term_of sum])
    val k_eq_0 = Thm.cterm_of ctxt (HOLogic.mk_eq (k,@{term "0::int"}))
    val (_,is_zro) = Logic.dest_equals(Thm.prop_of (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps 
                      @{thms arith_simps rel_simps Pure.reflexive}) k_eq_0))
    val thm = case is_zro of
      @{term True} => NONE
      | @{term False} =>
        let
          val parity = Thm.cterm_of ctxt (@{term "even::int \<Rightarrow> bool"} $ k)
          val simp = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps 
                      @{thms arith_simps even_numeral even_zero odd_numeral odd_one}) parity
          val (_,truth) = Logic.dest_equals(Thm.prop_of (simp))
          val (thm2,final_term) =  case truth of 
            @{term True} => 
              let 
                val final_term = @{term "sin::real\<Rightarrow>real"} $ x
                val even = @{thm truth} OF [simp]
                val goal2 = Logic.mk_equals (sin_ssa,final_term)   
                val tac = Thm.instantiate' [] [SOME (Thm.cterm_of ctxt k)] @{thm rewrite_sine_even}
                val simp_tac = tac OF [even]
                val thm2 = Goal.prove ctxt [] [] goal2
                          (fn _ => Method.rule_tac ctxt [simp_tac] [] 1)
              in
                (thm2,final_term)
              end
          | @{term False} => 
              let 
                val final_term = @{term "Groups.uminus_class.uminus::real\<Rightarrow>real"} $ (@{term "sin::real\<Rightarrow>real"} $ x)
                val odd = @{thm even_to_odd} OF [simp]
                val goal2 = Logic.mk_equals (sin_ssa,final_term)   
                val tac = Thm.instantiate' [] [SOME (Thm.cterm_of ctxt k)] @{thm rewrite_sine_odd}
                val simp_tac = tac OF [odd]
                val thm2 = Goal.prove ctxt [] [] goal2
                          (fn _ => Method.rule_tac ctxt [simp_tac] [] 1)
              in
                (thm2,final_term)
              end
          | _ => raise TERM ("could not decide parity of term", [k])
      
          val goal = Logic.mk_equals (sin_x,final_term)
          val thm3 = @{thm Pure.transitive} OF [thm1] OF [thm2]
          val thm = Goal.prove ctxt [] [] goal
                  (fn _ => Method.rule_tac ctxt [thm3] [] 1)
        in
          SOME thm
        end
     | _ => raise TERM ("can not determine if k is not zero (to avoid reflexivity)",[x])
  in       
    thm
  end
\<close>

subsection \<open>rewrite_sine tests\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+x)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin(x+(8::int)*pi)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((2::int)*pi+x+(8::int)*pi)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((24::int)*pi+(2::int)*pi+x+(8::int)*pi)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+x+(3::int)*pi)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+(5::int)*pi+x+(y+((3::int)*pi)+(3::int)*pi))"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+(5::int)*pi+x+(y+(3::int)*pi))"}
\<close>


ML \<open>
rewrite_sine @{context} @{cterm "sin(x+(8::int)*pi)"}
\<close>

section \<open>Experiments\<close>

simproc_setup sine1 ("sin(x)") = \<open>K rewrite_sine\<close>

(*
  To ensure that there is no looping, in rewrite_sine we only produce a theorem if the 
  rewriting changes the argument:
  
  SIN x = SIN y

  otherwise the tactic would loop since simproc_setup includes the simproc in the simpset
  of the theory and the following commands would loop.
*)

ML \<open>
rewrite_sine @{context} @{cterm "sin(x+(8::int)*pi)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+(5::int)*pi+x+(y+(3::int)*pi))"}
\<close>

                               
(*
  Some commands showing that now the tactic works on concrete examples. 
  We need to put the basic simpset since otherwise there is no good interaction with the
  other rules in it.
*)

lemma 
  shows "sin(x+(8::int)*pi) = sin(x)"
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>) 
  
lemma 
  shows "sin(x+(8::int)*pi+(8::int)*pi) = sin(x)"  
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>) 
  
lemma 
  shows "sin((8::int)*pi+x+(8::int)*pi) = sin(x)"  
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>) 

lemma 
  shows "sin((10::int)*pi+(8::int)*pi+x+(8::int)*pi) = sin(x)"  
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>)

lemma 
  shows "sin((8::int)*pi+(5::int)*pi+x+(y+((3::int)*pi)+(3::int)*pi)) = -sin(x+y)"
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>)

lemma 
  shows "sin((8::int)*pi+(5::int)*pi+x+(y+((3::int)*pi)+(3::int)*pi)) = -sin(x+y)"
  by(tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [@{simproc sine1}]) 1\<close>)

(*
 TODO: we would like to handle the second equation in practice

*)

lemma "sin((8::int)*pi+(5::int)*pi+x+(y+((3::int)*pi)+(3::int)*pi)) = -sin(x+y)"
  sorry

lemma "sin(8*pi+5*pi+x+(y+(3*pi)+3*pi)) = -sin(x+y)"
  sorry

(*
  I suggest to scan the tree looking for numeral :: num \<Rightarrow> real and substitute it
  for of_int :: int \<Rightarrow> real followed by numeral :: num \<Rightarrow> int. Then implement a conversion
  showing that this does not change the theorem using Int.ring_1_class.of_int_numeral.
*)

lemma "(7::real) = (of_int 7)"
  using [[simp_trace, simp_trace_depth_limit = 100]]
  by linarith

ML \<open>
@{term "(7::real) = (of_int 7)"}
\<close>

ML \<open>
@{term "sin(8*pi) = a"}
\<close>

  

end