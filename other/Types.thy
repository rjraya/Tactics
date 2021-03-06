theory Types
  imports Main
begin

ML \<open>
local
  fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
  fun pp_list xs = Pretty.list "[" "]" xs
  fun pp_str s = Pretty.str s
  fun pp_qstr s = Pretty.quote (pp_str s)
  fun pp_int i = pp_str (string_of_int i) 
  fun pp_sort S = pp_list (map pp_qstr S)
  fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
in
  fun raw_pp_typ (TVar ((a, i), S)) =
    pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
  | raw_pp_typ (TFree (a, S)) = pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
  | raw_pp_typ (Type (a, tys)) = pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
end
\<close>

ML \<open>
ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)
\<close>

ML \<open>
@{typ "bool"};
@{typ "bool \<Rightarrow> nat"};
\<close>


(* Restore simple printing of types *)

ML \<open>
ML_system_pp
(fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o
Proof_Display.pp_typ Theory.get_pure)
\<close>

ML \<open>
@{typ "bool"};
@{typ "bool \<Rightarrow> nat"};
\<close>

end