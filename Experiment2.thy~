theory Experiment2
 imports Main "HOL-Analysis.Analysis" "HOL.Numeral_Simprocs" "HOL-Number_Theory.Number_Theory"
begin

ML \<open>
fun extract_sine ctxt ct =
  let 
    val sum = ct |> Thm.term_of |> dest_comb |> snd |> Thm.cterm_of ctxt
  in
    sum 
  end
\<close>

ML \<open>
fun trash ctxt ct =
  let 
    val sum = ct |> Thm.term_of 
  in
    sum 
  end
\<close>

ML \<open>
extract_sine @{context} @{cterm "sin(x+2*pi)"}
\<close>

ML \<open>
extract_sine @{context} @{cterm "sin(x+2*pi)"} |> Thm.term_of |> dest_comb |> snd
\<close>

ML \<open>
case Const ("Transcendental.pi", HOLogic.realT) of  Const (x, y) =>
  Const ("fun", y);
Const ("Transcendental.pi", HOLogic.realT) = Const ("fun", HOLogic.charT);
Thm.cterm_of;
Logic.mk_equals
 
\<close>
(*x + numeral n * pi*)
ML\<open>
fun SIN_SIMPROC_ATOM ctxt x n =
 let 
  val cx = Thm.cterm_of ctxt x
  val cn = Thm.apply @{cterm "of_int::int \<Rightarrow> real"} (Thm.cterm_of ctxt n)
  val sum = Thm.apply (Thm.apply @{cterm "plus::real \<Rightarrow> real \<Rightarrow> real"} cx) cn
 in
  sum
 end
\<close>

(*
  Also use mk_binop for function types 
  Have to use explicit type for num?
  Numerals are STRICTLY positive natural numbers
*)

ML \<open>
fun sin_atom_conv ctxt ct =
 let
  val t = ct |> Thm.term_of
  val pi = t |> dest_comb |> snd
  val times = t |> dest_comb |> fst |> dest_comb |> fst
  val conv = t |> dest_comb |> fst |> dest_comb |> snd |> dest_comb |> fst
  val arg = t |> dest_comb |> fst |> dest_comb |> snd |> dest_comb |> snd 
  val cond = pi = Const ("Transcendental.pi", HOLogic.realT) andalso 
             times = Const ("Groups.times_class.times", 
                            HOLogic.realT --> HOLogic.realT --> HOLogic.realT) andalso
             conv = Const ("Num.numeral_class.numeral", Type ("Num.num", []) --> HOLogic.realT)
  val cres = if cond then SIN_SIMPROC_ATOM ctxt (HOLogic.mk_number HOLogic.realT 0) arg 
             else SIN_SIMPROC_ATOM ctxt t (HOLogic.mk_number HOLogic.intT 0)
  val res = cres |> Thm.term_of
  val goal = Logic.mk_equals (t,res)
 in
  goal
 end
 handle _ => 
  let
   val t = ct |> Thm.term_of
   val cres = SIN_SIMPROC_ATOM ctxt t (HOLogic.mk_number HOLogic.intT 0)
  val _ = @{print} cres

   val res = cres |> Thm.term_of

   val goal = Logic.mk_equals (t,res) 
  in
    goal
  end
\<close>

ML \<open>
sin_atom_conv @{context} @{cterm "2*pi"}  
\<close>
ML \<open>
sin_atom_conv @{context} @{cterm "x+2*pi"}  
\<close>

ML \<open>
(* Gives the first subterm in a term *)
fun first (t $ _) = first t
 | first t = t

fun left ()
\<close>

ML \<open>
first @{term "(1::real)+2"}
\<close>

ML \<open>
if first @{term "(1::real)+2"} = Const ("Groups.plus_class.plus", HOLogic.realT --> HOLogic.realT --> HOLogic.realT) 
then true else false;


\<close>

ML \<open>
fun normalizer ct =
 let
  val t = Thm.term_of
  val sum = Const ("Groups.plus_class.plus", HOLogic.realT --> HOLogic.realT --> HOLogic.realT) 
  if fst t = sum 
  then 
  else
    
 in
 end

\<close>

ML \<open>
fun descend_conv ctxt ct =
  let
    val t = ct |> Thm.term_of 
  in
  end
\<close>

ML \<open>
Pattern.first_order_match;
Pattern.matches
\<close>

ML \<open>
let
val fo_pat = @{term_pat " \<lambda>y. (?X::nat \<Rightarrow>bool) y"}
val trm = @{term " \<lambda>x. (P::nat \<Rightarrow>bool) x"}
val init = (Vartab.empty, Vartab.empty)
in
Pattern.first_order_match @{theory} (fo_pat, trm) init
|> snd
|> pretty_env @{context}
end

\<close>

end