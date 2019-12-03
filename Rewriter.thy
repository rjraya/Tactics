theory Rewriter
  imports Complex_Main "HOL-Library.Rewrite"
begin

section \<open>Examples from file ex\<close>

(* The rewrite method also has an ML interface *)
lemma
  assumes "\<And>a b. P ((a + 1) * (1 + b)) "
  shows "\<And> a b :: nat. P ((a + 1) * (b + 1))"
  apply (tactic \<open>
    let
      (* seems that one fixes the inner term first, so in this case b *)
      val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
      (* Note that the pattern order is reversed *)
      val pat = [
        Rewrite.For [(x, SOME \<^typ>\<open>nat\<close>)],
        Rewrite.In,
        (* therefore here the pattern is for b *)
        Rewrite.Term (@{const plus(nat)} $ Free (x, \<^typ>\<open>nat\<close>) $ \<^term>\<open>1 :: nat\<close>, [])]
      val to = NONE
    in CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute}) 1 end
  \<close>)
  apply (fact assms)
  done

ML \<open>@{term "(\<lambda> x. x)"}\<close>

ML \<open>
Abs ("x", \<^typ>\<open>int\<close>, Bound 0)
\<close>

(*
Finally note that “fixed” versus “schematic” variables as introduced above are
just separate syntactic expressions of the very same formal concept of variables.
The difference is merely one of a policy in certain logical operations to be in-
troduced later on (notably higher-order resolution, see \<section>2.4) [Paulson, 1989]:
schematic variables may get instantiated on the fly, while fixed ones need to be
left unchanged in the present scope.
*)

lemma
  assumes "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. a + b))"
  shows "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. b + a))"
  apply (tactic \<open>
    let
      (* again it seems that they are fixing b with this commands *)
      val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
      val pat = [
        Rewrite.Concl,
        Rewrite.In,
        Rewrite.Term (Free ("Q", (\<^typ>\<open>int\<close> --> TVar (("'b",0), [])) --> \<^typ>\<open>bool\<close>)
          $ Abs ("x", \<^typ>\<open>int\<close>, Rewrite.mk_hole 1 (\<^typ>\<open>int\<close> --> TVar (("'b",0), [])) $ Bound 0), [(x, \<^typ>\<open>int\<close>)]),
        Rewrite.In,
        (* Here they say, please tackle the subterm b + something that can be instantiated *)
        Rewrite.Term (@{const plus(int)} $ Free (x, \<^typ>\<open>int\<close>) $ Var (("c", 0), \<^typ>\<open>int\<close>), [])
        ]
      val to = NONE
    in CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms add.commute}) 1 end
  \<close>)
  apply (fact assms)
  done

lemma
  assumes "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. a + b))"
  shows "Q (\<lambda>b :: int. P (\<lambda>a. a + b) (\<lambda>a. b + a))"
  apply(rewrite at "x + _"  in "Q  (\<lambda> x. \<hole> x)" add.commute) 
  using assms 
  oops

thm add.commute
lemma
  assumes "\<And>a b. P ((a + 1) * (1 + b)) "
  shows "\<And>a b :: nat. P ((a + 1) * (b + 1))"
  apply(rewrite at "y + 1" in for (y) add.commute)
  apply(fact assms)
  done

section \<open>My examples\<close>

lemma "(1::int)+2 = 2+1"
  apply(rewrite add.commute) 
  apply(simp)
  done

lemma "(1::int)+2 = 2+1"
  apply(rewrite add.commute) 
  apply(simp)
  done

lemma "(1::int)+2 = 2+1"
  apply(tactic \<open>
   CCONVERSION (Rewrite.rewrite_conv @{context} ([Rewrite.In], NONE) @{thms add.commute}) 1 
  \<close>)
  apply(simp)
  done

subsection "At"

lemma "(1::int)+x = x+1"
  apply(rewrite at "x+1" add.commute)
  by simp

ML \<open>
writeln (@{make_string} @{term "1 + 1"})
\<close>

lemma "(1::int)+x = x+1"
  apply(tactic \<open>
   let 
    val pat = [     
      Rewrite.Concl,
      Rewrite.In,
      Rewrite.Term (@{const plus(int)} $ @{term x} $ @{term "1::int"}, []),
      Rewrite.At
    ]
    val _ = @{print} @{term x}
    val _ = @{print} @{typ int}
    val _ = @{print} @{context}
    val to = NONE
   in
    CCONVERSION (Rewrite.rewrite_conv @{context} (pat, to) @{thms add.commute}) 1 
   end
  \<close>)
  by simp

lemma "(x::nat)+y = y+x"
  apply(tactic \<open>
   let 
    val (x, ctxt) = yield_singleton Variable.add_fixes "x" \<^context>
    val pat = [     
      Rewrite.Concl,
      Rewrite.In,
      Rewrite.Term (@{const plus(nat)} $ Free(x,\<^typ>\<open>nat\<close>) $ Var((("y",0),\<^typ>\<open>nat\<close>)), []),
      Rewrite.At
    ]
    val to = NONE
   in
    CCONVERSION (Rewrite.rewrite_conv @{context} (pat, to) @{thms add.commute}) 1 
   end
  \<close>)
  by simp

subsection "Others"

definition "juanito = (3::real)"

lemma "1 div juanito = 1 div 3"
  apply(rewrite juanito_def)
  by simp

lemma "1 div juanito = 1 div 3" 
  apply(tactic \<open>
   CCONVERSION (Rewrite.rewrite_conv @{context} ([Rewrite.In], NONE) @{thms juanito_def}) 1 
  \<close>)
  by simp

definition "pepe = (3::real)" 


lemma "juanito / juanito = pepe / (3::real)" 
  (* apply(rewrite at "_ / \<hole>" juanito_def) *)
  apply(tactic \<open>
   let 
    val pat = [
      Rewrite.In,
      Rewrite.Term (@{const divide(real)} $ Var (("c", 0), \<^typ>\<open>real\<close>) $ 
                      Rewrite.mk_hole 1 (\<^typ>\<open>real\<close>), []),
      Rewrite.At
    ]
    val to = NONE
   in
    CCONVERSION (Rewrite.rewrite_conv @{context} (pat, to) @{thms juanito_def}) 1 
   end
  \<close>)
  using juanito_def pepe_def by simp
  
lemma "juanito / (3 * juanito) = pepe / (9::real)" 
  apply(tactic \<open>
   let 
    val pat = [
      Rewrite.In,
      Rewrite.Term (@{const divide(real)} $ Var (("c", 0), \<^typ>\<open>real\<close>) $ 
                      Rewrite.mk_hole 1 (\<^typ>\<open>real\<close>), []),
      Rewrite.In      
    ]
    val to = NONE
   in
    CCONVERSION (Rewrite.rewrite_conv @{context} (pat, to) @{thms juanito_def}) 1 
   end
  \<close>)
  using juanito_def pepe_def by linarith



end