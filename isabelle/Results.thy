theory Results imports Soundness Completeness begin

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

theorem prover_semantics:
  fixes A :: \<open>tm list\<close> and p :: fm
  defines \<open>t \<equiv> secavProver (A, [p])\<close>
  shows \<open>tfinite t \<and> wf t \<longleftrightarrow> (\<forall>(e :: nat \<Rightarrow> nat hterm) f g. semantics e f g p)\<close>
  using assms prover_soundness_semantics prover_completeness_semantics
  unfolding secavProver_def by fastforce

end
