theory Experiment3
 imports Main "HOL-Analysis.Analysis" "HOL.Numeral_Simprocs" "HOL-Number_Theory.Number_Theory" 
begin

(* 
Following the answer to this question:

https://stackoverflow.com/questions/58859417/rewriting-sine-using-simprocs-in-isabelle

*)

definition "SIN_SIMPROC_ATOM x n = x + of_int n * pi"

(* should we pattern match on a numeral or on an int ? *)
ML \<open>
fun sin_atom_conv ctxt ct =
 let 
  val t = ct |> Thm.term_of
  (*val _ = @{print} t*)
  
  val ssa_term = 
    case t of (Const ("Groups.times_class.times", @{typ "real \<Rightarrow> real \<Rightarrow> real"}) $ 
              (Const ("Int.ring_1_class.of_int", @{typ "int \<Rightarrow> real"}) $ t') $
               Const ("Transcendental.pi", @{typ "real"}))  => 
        let 
          val goal = Logic.mk_equals (t, @{term "SIN_SIMPROC_ATOM 0"} $ t' ) 
        in 
          Goal.prove ctxt [] [] goal
                (fn _ => simp_tac (ctxt addsimps @{thms SIN_SIMPROC_ATOM_def}) 1)
        end                 
    | x => 
        let 
          val goal = Logic.mk_equals (t, @{term "SIN_SIMPROC_ATOM"} $ x $ @{term "0::int"}  ) 
        in 
          Goal.prove ctxt [] [] goal
                (fn _ => simp_tac (ctxt addsimps @{thms SIN_SIMPROC_ATOM_def}) 1)
        end
      
 in
 ssa_term
 end
\<close>

ML \<open>
sin_atom_conv @{context} @{cterm "(2::int)*pi"}  
\<close>
ML \<open>
sin_atom_conv @{context} @{cterm "x+2*pi"}  
\<close>

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
                (fn _ => asm_full_simp_tac (ctxt addsimps @{thms SIN_SIMPROC_ATOM_def algebra_simps}) 1)
      end
    | _ => sin_atom_conv ctxt ct
 in
  res
 end
\<close>

ML \<open>
sin_term_conv @{context} @{cterm "x+(2::int)*pi"}  
\<close>

ML \<open>
sin_term_conv @{context} @{cterm "(3::int)*pi+x+(2::int)*pi"}  
\<close>

ML \<open>
sin_term_conv @{context} @{cterm "(3::int)*pi+x"}  
\<close>

(* Theorems for SIN_SIMPROC_ATOM *)

lemma rewrite_sine_even:
  fixes k k' :: int 
  assumes "k  \<equiv> 2 * of_int k'" 
  shows "sin(SIN_SIMPROC_ATOM x k) \<equiv> sin (x)" 
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
  finally show "sin(SIN_SIMPROC_ATOM x k) \<equiv> sin (x)"
    unfolding SIN_SIMPROC_ATOM_def
    by auto
qed

lemma arg_cong_pure:
  assumes "x \<equiv> y"
  shows "f x \<equiv> f y"
  using assms by simp

lemma 
  assumes "sin (x + real_of_int 8 * pi) \<equiv> sin x"
  shows "sin (x + 8 * pi) \<equiv> sin x"
  apply(tactic \<open>Method.insert_tac @{context} @{thms assms} 1\<close>)
  by simp

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
            (fn _ => asm_full_simp_tac (ctxt addsimps [inst_lemma] @ @{thms SIN_SIMPROC_ATOM_def add.commute add.assoc}) 1)
    
    val (x,k) = case ssa of (@{term SIN_SIMPROC_ATOM} $ x' $ k') => (x',k')
                         | _ => raise TERM ("term should be simproc_atom",[Thm.term_of sum])
    val (_,kint) = k |> HOLogic.dest_number
    (* even case *)    
    val goal2 = Logic.mk_equals (sin_ssa,@{term "sin::real\<Rightarrow>real"} $ x)
    val tac = Thm.instantiate' [] [SOME (Thm.cterm_of ctxt k), 
                                   SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.intT (kint div 2)))] 
                                   @{thm rewrite_sine_even}
    val thm2 = Goal.prove ctxt [] [] goal2
            (fn _ => Method.rule_tac ctxt [tac] [] 1
                     THEN asm_full_simp_tac ctxt 1)
    (* transitive *)
    val goal = Logic.mk_equals (sin_x,@{term "sin::real\<Rightarrow>real"} $ x)
    val thm3 = @{thm Pure.transitive} OF [thm1] OF [thm2]
    val _ = @{print} thm3
    val thm = Goal.prove ctxt [] [] goal
            (fn _ => Method.insert_tac ctxt [thm3] 1
                     THEN asm_full_simp_tac (ctxt addsimps @{thms algebra_simps}) 1)
  in       
    thm
  end
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((8::int)*pi+x)"}
\<close>

ML \<open>
rewrite_sine @{context} @{cterm "sin((2::int)*pi+x+(8::int)*pi)"}
\<close>


simproc_setup sine1 ("sin(x+a*pi+pi/2)") = \<open>K rewrite_sine\<close>






end