theory Soundness
  imports Prover
begin

section \<open>Soundness of the prover\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) ([],_) = False\<close>
| \<open>ssemantics (e,f,g) ((p # z),phase) = (semantics e f g p \<or> ssemantics (e,f,g) (z,phase))\<close>

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def
proof (safe)
  fix r sequent phase sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
  assume r_enabled: \<open>eff r (sequent, phase) sl\<close>
  assume next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
  proof (cases sequent)
    case Nil
    assume empty: \<open>sequent = []\<close>
    show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
    proof (rule ccontr)
      note \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
      have \<open>eff r ([], phase) sl \<Longrightarrow> (\<forall>s'. s' |\<in>| sl \<longrightarrow> fst s' = [])\<close>
        sorry
      moreover have \<open>\<forall>s'. fst s' = [] \<longrightarrow> (\<not> (\<forall>S \<in> UNIV. ssemantics S s'))\<close>
        sorry
      ultimately show \<open>False\<close> using next_sound r_enabled r_rule
        sorry
    qed
  next
    case (Cons p z)
    assume \<open>sequent = p # z\<close>
    show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
      sorry
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>\<forall>i. ssemantics i (fst (root t))\<close>
  sorry

end