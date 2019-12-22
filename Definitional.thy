theory Definitional
  imports Main
begin 

definition "trcl \<equiv> \<lambda>R x y. \<forall> P. (\<forall> x. P x x) \<longrightarrow> (\<forall> x y z. R x y \<longrightarrow> P y z \<longrightarrow> P x z) \<longrightarrow> P x y"

lemma trcl_induct:
  assumes "trcl R x y"
  shows "(\<And> x. P x x) \<Longrightarrow> (\<And> x y z. R x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow> P x y"
  apply(atomize (full))
  apply(cut_tac assms)
  apply(unfold trcl_def)
  apply(drule spec[where x=P])
  apply(assumption)
  done

lemma trcl_base: shows "trcl R x x"
 apply(unfold trcl_def)
 apply(rule allI impI)+
 apply(drule spec)
 apply(assumption)
  done

lemma trcl_step:
shows "R x y \<Longrightarrow> trcl R y z \<Longrightarrow> trcl R x z"
  apply (unfold trcl_def)
  apply (rule allI impI)+
  subgoal premises for P
proof -
  have p1: "R x y" by fact
  have p2: "\<forall> P. (\<forall> x. P x x) \<longrightarrow> (\<forall> x y z. R x y \<longrightarrow> P y z \<longrightarrow> P x z) \<longrightarrow> P y z" by fact
  have r1: "\<forall> x. P x x" by fact
  have r2: "\<forall> x y z. R x y \<longrightarrow> P y z \<longrightarrow> P x z" by fact
  show "P x z"
    apply (rule r2[rule_format])
    apply(rule p1)
    apply(rule p2[THEN spec[where x=P], THEN mp, THEN mp, OF r1, OF r2])
    done
qed
  done


inductive even where
"even 0"
| "even n \<Longrightarrow> even (n+2)"

end