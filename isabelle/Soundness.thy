theory Soundness
  imports Prover
begin

section \<open>Soundness of the prover\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> sequent \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e, f, g) z = (\<exists>p \<in> set z. semantics e f g p)\<close>

lemma eff_preserves_Nil:
  assumes \<open>eff r [] sl\<close> \<open>s |\<in>| sl\<close>
  shows \<open>s = []\<close>
  using assms unfolding eff_def effect_def by auto

lemma branches_if_not_Basic:
  assumes \<open>eff r [] sl\<close> \<open>r \<noteq> Basic\<close>
  shows \<open>sl \<noteq> {||}\<close>
  using assms unfolding eff_def effect_def by auto

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def
proof (safe)
  fix r sequent sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
    and r_enabled: \<open>eff r sequent sl\<close>
    and next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) sequent\<close>
  proof (cases sequent)
    case Nil
    show \<open>ssemantics (e, f, g) sequent\<close>
    proof (rule ccontr)
      have \<open>eff r [] sl \<Longrightarrow> (\<forall>s'. s' |\<in>| sl \<longrightarrow> s' = [])\<close>
        using eff_preserves_Nil by blast
      moreover have \<open>\<forall>s'. s' = [] \<longrightarrow> (\<not> (\<forall>S \<in> UNIV. ssemantics S s'))\<close>
        by simp
      ultimately have \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> s' = []\<close>
        using Nil r_enabled by blast
      then have \<open>sl = {||}\<close>
        using next_sound by fastforce
      moreover have \<open>r \<noteq> Basic\<close>
        using r_enabled Nil unfolding eff_def effect_def
          (* this is probably unprovable now *)
        sorry
      ultimately show \<open>False\<close>
        using branches_if_not_Basic Nil r_enabled by blast
    qed
  next
    case (Cons p z)
    then show \<open>ssemantics (e, f, g) sequent\<close>
      sorry
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>(\<exists>p \<in> set (fst (root t)). semantics e f g p)\<close>
  using soundness assms ssemantics.simps UNIV_I
  by metis

end