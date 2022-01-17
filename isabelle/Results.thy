theory Results imports Soundness Completeness Sequent_Calculus_Verifier begin

section \<open>Usemantics\<close>

corollary prover_soundness_usemantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>\<exists>p \<in> set (snd (fst (root t))). usemantics u e f g p\<close>
  using assms prover_soundness_SeCaV sound_usemantics by blast

theorem prover_usemantics:
  fixes A :: \<open>tm list\<close> and ps :: \<open>fm list\<close>
  defines \<open>t \<equiv> secavProver (A, ps)\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (uvalid ps)\<close>
  using assms prover_soundness_usemantics prover_completeness_usemantics
  unfolding secavProver_def by fastforce

corollary
  fixes p :: fm
  defines \<open>t \<equiv> secavProver ([], [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(u :: tm set) e f g.
    is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p)\<close>
  using assms prover_usemantics by simp

section \<open>SeCaV\<close>

corollary prover_completeness_SeCaV:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<tturnstile> ps\<close>
  defines \<open>t \<equiv> secavProver (A, ps)\<close>
  shows \<open>fst (root t) = (A, ps) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>uvalid ps\<close>
    using assms sound_usemantics by blast
  then show ?thesis
    using assms prover_completeness_usemantics by blast
qed

theorem prover_SeCaV:
  fixes A :: \<open>tm list\<close> and ps :: \<open>fm list\<close>
  defines \<open>t \<equiv> secavProver (A, ps)\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<tturnstile> ps)\<close>
  using assms prover_soundness_SeCaV prover_completeness_SeCaV
  unfolding secavProver_def by fastforce

corollary
  fixes p :: fm
  defines \<open>t \<equiv> secavProver ([], [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<tturnstile> [p])\<close>
  using assms prover_SeCaV by blast

section \<open>Semantics\<close>

corollary prover_soundness_semantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close>
  shows \<open>\<exists>p \<in> set (snd (fst (root t))). semantics e f g p\<close>
  using assms prover_soundness_SeCaV sound by blast

corollary
  assumes \<open>tfinite t\<close> \<open>wf t\<close> \<open>snd (fst (root t)) = [p]\<close>
  shows \<open>semantics e f g p\<close>
  using assms prover_soundness_SeCaV complete_sound(2) by metis

corollary prover_completeness_semantics:
  fixes A :: \<open>tm list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p\<close>
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>fst (root t) = (A, [p]) \<and> wf t \<and> tfinite t\<close>
proof -
  have \<open>\<tturnstile> [p]\<close>
    using assms complete_sound(1) by blast
  then show ?thesis
    using assms prover_completeness_SeCaV by blast
qed

theorem prover_semantics:
  fixes A :: \<open>tm list\<close> and p :: fm
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p)\<close>
  using assms prover_soundness_semantics prover_completeness_semantics
  unfolding secavProver_def by fastforce

end
