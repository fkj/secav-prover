theory Completeness
  imports Countermodel "Sequent_Calculus_Verifier" "HOL-Library.BNF_Corec"
begin

section \<open>Completeness of the prover\<close>

text \<open>We start out by specializing the abstract completeness theorem to our prover\<close>
theorem epath_prover_completeness:
  fixes A :: \<open>tm list\<close> and p :: fm
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows
  "(fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t) \<or>
   (\<exists> steps. fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps)" (is "?A \<or> ?B")
proof -
  { assume "\<not> ?A"
    with assms have "\<not> tfinite (mkTree rules (A, [p]))"
      unfolding secavProver_def using wf_mkTree fair_rules by simp
    then obtain steps where "ipath (mkTree rules (A, [p])) steps" using Konig by blast
    with assms have "fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps"
      by (metis UNIV_I fair_rules ipath.cases ipath_mkTree_Saturated mkTree.simps(1) prod.sel(1)
          wf_ipath_epath wf_mkTree)
    hence ?B by blast
  }
  thus ?thesis by blast
qed

section \<open>Generating countermodels from saturated escape paths\<close>

text \<open>We need some lemmas to prove our main theorem\<close>
lemma epath_countermodel:
  assumes \<open>\<exists> steps. fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps\<close>
  shows \<open>\<exists>u (e :: nat \<Rightarrow> tm) f g . \<not> usemantics u e f g p \<and> is_env u e \<and> is_fdenot u f\<close>
proof (rule ccontr)
  assume \<open>\<nexists>u (e :: nat \<Rightarrow> tm) f g. \<not> usemantics u e f g p \<and> is_env u e \<and> is_fdenot u f\<close>
  then have \<open>\<forall>u (e :: nat \<Rightarrow> tm) f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
    by blast
  then show False
  proof -
    assume \<open>\<forall>u (e :: nat \<Rightarrow> tm) f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
    moreover obtain steps
      where steps: \<open>fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps\<close>
      using assms by blast
    then have \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?S\<close>)
      using escape_path_Hintikka assms by simp
    moreover have \<open>p \<in> tree_fms steps\<close>
      using steps shd_sset
      by (metis Pair_inject list.set_intros(1) prod.collapse pseq_def pseq_in_tree_fms)
    then have \<open>\<exists>g. \<not> usemantics (terms ?S) (E ?S) (F ?S) g p\<close>
      using calculation(2) hintikka_counter_model steps by blast
    moreover have \<open>is_env (terms ?S) (E ?S)\<close> \<open>is_fdenot (terms ?S) (F ?S)\<close>
      using is_env_E is_fdenot_F by blast+
    ultimately show False
      by blast
  qed
qed

lemma epath_lem:
  assumes \<open>\<nexists> steps. fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
  using assms epath_prover_completeness t_def by blast

lemma epath_contr:
  assumes \<open>\<forall>(u :: tm set) e f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
  shows \<open>\<nexists> steps. fst (shd steps) = (A, [p]) \<and> epath steps \<and> Saturated steps\<close>
proof (rule ccontr, safe)
  fix steps
  assume \<open>fst (shd steps) = (A, [p])\<close> \<open>epath steps\<close> \<open>Saturated steps\<close>
  then obtain u f g and e :: \<open>nat \<Rightarrow> tm\<close> where
    \<open>\<not> usemantics u e f g p\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
    using epath_countermodel by blast
  with assms show False
    by simp
qed

text \<open>Finally, we arrive at the main theorem\<close>

theorem completeness_usemantics:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<forall>(u :: tm set) e f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
  by (simp add: assms epath_contr epath_lem epath_prover_completeness)

corollary completeness_SeCaV:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<tturnstile> [p]\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>\<forall>(u :: tm set) e f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
    using assms sound_usemantics by fastforce
  then show ?thesis
    using assms completeness_usemantics by blast
qed

corollary completeness_semantics:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>\<tturnstile> [p]\<close>
    using assms complete_sound(1) by blast
  then show ?thesis
    using assms completeness_SeCaV by blast
qed

end
