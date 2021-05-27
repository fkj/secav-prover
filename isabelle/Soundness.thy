theory Soundness
  imports Prover
begin

section \<open>Soundness of the prover\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) ([],_) = False\<close>
| \<open>ssemantics (e,f,g) ((p # z),phase) = (semantics e f g p \<or> ssemantics (e,f,g) (z,phase))\<close>

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def RuleSystem_def
proof (safe)
  fix r sequent phase sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
  assume r_enabled: \<open>eff r (sequent, phase) sl\<close>
  assume next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
  proof (induct sequent)
    case Nil
    then show ?case sorry
(* contradiction on the assumption that we can move to a sound state when sequent is empty *)
  next
    case (Cons a sequent)
    then show ?case sorry
  qed
qed

end