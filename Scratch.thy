theory Scratch
  imports Complex_Main
begin

(*
  These are just some lemmas that we will need.
  The "numeral" thing is a bit tricky, perhaps – the idea is that if you write "2" in Isabelle,
  what you actually get is "numeral (Num.Bit0 Num.One)" (a kind of binary representation of the
  number).

  The type "num" basically represents these binary "numerals", and the function "numeral" allows
  us to turn such a "num" into an actual number, e.g. a natural number, an integer, a complex
  number etc.

  The idea is that if our procedure wants to show that e.g. "sqrt 9 = 3", it simply instantiates
  this theorem with n = 9 and m = 3 and returns it. The simplifier then knows that if it can
  prove that "3 * 3 ≡ 9", then it can rewrite "sqrt 9" to "3".
*)
lemma sqrt_numeral_simproc_aux:
  assumes "m * m ≡ n"
  shows   "sqrt (numeral n :: real) ≡ numeral m"
proof -
  have "numeral n ≡ numeral m * (numeral m :: real)" by (simp add: assms [symmetric])
  moreover have "sqrt … ≡ numeral m" by (subst real_sqrt_abs2) simp
  ultimately show "sqrt (numeral n :: real) ≡ numeral m" by simp
qed

(*
  We could just as well have used this theorem instead. Since we now work on real numbers instead
  of numerals, we also need the precondition "m ≥ 0" and the simplifier will also have to prove
  that (which will be trivial, but still – it's a little bit of unnecessary extra work. That's
  why I didn't do that.).
*)
lemma sqrt_numeral_simproc_aux':
  assumes "n = m * m" and "m ≥ 0"
  shows   "sqrt (n :: real) ≡ m"
  using assms by simp


(* Similar theorems for n-th roots *)
lemma root_numeral_simproc_aux:
  assumes "Num.pow m n ≡ x"
  shows   "root (numeral n) (numeral x :: real) ≡ numeral m"
  by (subst assms [symmetric], subst numeral_pow, subst real_root_pos2) simp_all

lemma powr_numeral_simproc_aux:
  assumes "Num.pow y n = x"
  shows   "numeral x powr (m / numeral n :: real) ≡ numeral y powr m"
  by (subst assms [symmetric], subst numeral_pow, subst powr_numeral [symmetric])
     (simp, subst powr_powr, simp_all)

lemma numeral_powr_inverse_eq:
  "numeral x powr (inverse (numeral n)) = numeral x powr (1 / numeral n :: real)"
  by simp

ML ‹

(*
  Combinator to iterate some function until some condition is met or a threshold for the maximum
  number of iterations is reached.
*)
fun iterate NONE p f x =
      let
        fun go x = if p x then x else go (f x)
      in
        SOME (go x)
      end
  | iterate (SOME threshold) p f x =
      let
        fun go (threshold, x) = 
          if p x then SOME x else if threshold = 0 then NONE else go (threshold - 1, f x)
      in
        go (threshold, x)
      end  

(*
  Computes the n-th root of the given integer using Newton's method with a threshold for the
  maximum number of iterations. For extra speed, first see if the n-th root can be found by
  floating point arithmetic.

  If the input is not an n-th power, will return the floor of the n-th root.
*)
fun nth_root _ 1 x = SOME x
  | nth_root _ _ 0 = SOME 0
  | nth_root _ _ 1 = SOME 1
  | nth_root threshold n x =
  let
    fun newton_step y = ((n - 1) * y + x div Integer.pow (n - 1) y) div n
    fun is_root y = Integer.pow n y <= x andalso x < Integer.pow n (y + 1)
  in
    if x < n then
      SOME 1
    else if x < Integer.pow n 2 then 
      SOME 1 
    else 
      let
        val y = Real.floor (Math.pow (Real.fromInt x, Real.fromInt 1 / Real.fromInt n))
      in
        if is_root y then
          SOME y
        else
          iterate threshold is_root newton_step ((x + n - 1) div n)
      end
  end

(*
  Same as above, but returns NONE if the input is not an n-th power.
*)
fun nth_root' _ 1 x = SOME x
  | nth_root' _ _ 0 = SOME 0
  | nth_root' _ _ 1 = SOME 1
  | nth_root' threshold n x = if x < n then NONE else if x < Integer.pow n 2 then NONE else
      case nth_root threshold n x of
        NONE => NONE
      | SOME y => if Integer.pow n y = x then SOME y else NONE

(*
  Basically the same but for sqrt instead of n-th power.
*)
fun sqrt _ 0 = SOME 0
  | sqrt _ 1 = SOME 1
  | sqrt threshold n =
    let
      fun aux (a, b) = if n >= b * b then aux (b, b * b) else (a, b)
      val (lower_root, lower_n) = aux (1, 2)
      fun newton_step x = (x + n div x) div 2
      fun is_sqrt r = r*r <= n andalso n < (r+1)*(r+1)
      val y = Real.floor (Math.sqrt (Real.fromInt n))
    in
      if is_sqrt y then 
        SOME y
      else
        Option.mapPartial (iterate threshold is_sqrt newton_step o (fn x => x * lower_root)) 
          (sqrt threshold (n div lower_n))
    end

fun sqrt' threshold x =
  case sqrt threshold x of
    NONE => NONE
  | SOME y => if y * y = x then SOME y else NONE

(*
  Simproc to rewrite terms of the form "sqrt (numeral n)" to a single numeral if possible.
*)
fun sqrt_simproc ctxt ct =
  let
    (* extract the number n *)
    val (n : int) = ct |> Thm.term_of |> dest_comb |> snd |> dest_comb |> snd |> HOLogic.dest_numeral
  in
    case sqrt' (SOME 10000) n of (* Check if square root exists *)
      NONE => NONE (* No; do nothing *)
    | SOME m => (* Yes, return theorem of the form "sqrt (numeral n) ≡ numeral m" *)
        SOME (Thm.instantiate' [] (map (SOME o Thm.cterm_of ctxt o HOLogic.mk_numeral) [m, n])
                  @{thm sqrt_numeral_simproc_aux})
    (* most of the "magic" here is to plug m and n into the theorem sqrt_numeral_simproc_aux.*)
  end
    handle TERM _ => NONE

›

(* We can now look at our simproc in action: *)
ML_val ‹
  sqrt_simproc @{context} @{cterm "sqrt 16"}
›

(*
val it =
   SOME
     "num.Bit1 num.One * num.Bit1 num.One ≡ num.Bit1 (num.Bit0 (num.Bit0 num.One)) ⟹
        sqrt 9 ≡ 3" : thm option
*)

(*
  The first part (the precondition) just means "3 * 3 = 9", and the simplifier can solve that
  automatically. That's why you can just write "sqrt 9" and it gets rewritten to "3".
*)


end
