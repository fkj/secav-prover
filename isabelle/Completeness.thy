theory Completeness
  imports Prover Model "HOL-Library.BNF_Corec"
begin

section \<open>Completeness of the prover\<close>

text \<open>We start out by specializing the abstract completeness theorem to our prover\<close>
theorem epath_prover_completeness:
  assumes "p \<in> (UNIV :: fm set)"
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows
  "(fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t) \<or>
   (\<exists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps)" (is "?A \<or> ?B")
proof -
  { assume "\<not> ?A"
    with assms have "\<not> tfinite (mkTree fenum ([p], PBasic))"
      unfolding secavProver_def using wf_mkTree fair_fenum by simp
    then obtain steps where "ipath (mkTree fenum ([p], PBasic)) steps" using Konig by blast
    with assms have "fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps"
      by (metis UNIV_I fair_fenum ipath.cases ipath_mkTree_Saturated mkTree.simps(1) prod.sel(1)
          wf_ipath_epath wf_mkTree)
    hence ?B by blast
  }
  thus ?thesis by blast
qed

section \<open>Generating countermodels from saturated escape paths\<close>

definition \<open>tree_fms steps \<equiv> \<Union>fms \<in> sset steps. set (fst (fst fms))\<close>

lemma exactly_one_enabled: \<open>\<forall>sequent phase. \<exists>! r. enabled r (sequent, phase)\<close>
  unfolding enabled_def Ex1_def
  using at_least_one_enabled enabled_unique
  by (metis RuleSystem_Defs.enabled_def member_remove remove_def rules_def) 

lemma woop:
  assumes \<open>Dis p q \<in> tree_fms steps\<close>
  shows \<open>\<exists>n. s = shd (sdrop n steps) \<and> (\<exists>z. s = ((Dis p q # z, PABD), AlphaDis))\<close>
  sorry

lemma sset_sdrop: \<open>sset (sdrop n s) \<subseteq> sset s\<close>
  by (induct n arbitrary: s)
    (simp, metis dual_order.trans equalityE insert_subset sdrop.simps(2) stream.collapse stream.simps(8))

lemma escape_path_Hintikka:
  fixes steps
  assumes \<open>fst (fst (shd steps)) = [p] \<and> epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?H\<close>)
proof
  fix n ts
  assume \<open>Pre n ts \<in> tree_fms steps\<close>
  show \<open>Neg (Pre n ts) \<notin> tree_fms steps\<close>
  proof
    assume \<open>Neg (Pre n ts) \<in> tree_fms steps\<close>
    have \<open>\<exists>s \<in> sset steps. enabled Basic (fst s)\<close>
      sorry
    show False
      sorry
  qed
next
  fix p q
  assume dis: \<open>Dis p q \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
  proof -
    obtain s z n where \<open>s = ((Dis p q # z, PABD), AlphaDis)\<close> and \<open>s = shd (sdrop n steps)\<close>
      using dis woop by meson
(* we need that the nxt node contains the decomposed formula as soon as it is enabled *) 
    then have \<open>takenAtStep AlphaDis (shd (sdrop (Suc n) steps))\<close>
      sorry
    then have \<open>\<exists>r. shd (sdrop (Suc n) steps) = ((p # q # z, PBasic), r)\<close>
      sorry
    show \<open>p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
      sorry
  qed
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close>
  show \<open>Neg p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
    sorry
next
  fix p q
  assume \<open>Neg (Con p q) \<in> tree_fms steps\<close>
  show \<open>Neg p \<in> tree_fms steps \<and> Neg q \<in> tree_fms steps\<close>
    sorry
next
  fix p q
  assume \<open>Con p q \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps \<or> q \<in> tree_fms steps\<close>
    sorry
next
  fix p q
  assume \<open>Neg (Imp p q) \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps \<or> Neg q \<in> tree_fms steps\<close>
    sorry
next
  fix p q
  assume \<open>Neg (Dis p q) \<in> tree_fms steps\<close>
  show \<open>Neg p \<in> tree_fms steps \<or> Neg q \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Exi p \<in> tree_fms steps\<close>
  show \<open>\<forall>t\<in>\<Union>f \<in> tree_fms steps. set (subtermFm f). sub 0 t p \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Uni p) \<in> tree_fms steps\<close>
  show \<open>\<forall>t\<in>\<Union>f \<in> tree_fms steps. set (subtermFm f). Neg (sub 0 t p) \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Uni p \<in> tree_fms steps\<close>
  show \<open>\<exists>t \<in> terms (tree_fms steps). sub 0 t p \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Exi p) \<in> tree_fms steps\<close>
  show \<open>\<exists>t \<in> terms (tree_fms steps). Neg (sub 0 t p) \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Neg p) \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps\<close>
    sorry
qed

text \<open>We need some lemmas to prove our main theorem\<close>
lemma epath_countermodel:
  assumes \<open>\<exists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close> \<open>closed 0 p\<close>
  shows \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> (semantics e f g p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>(e :: nat \<Rightarrow> tm) f g. \<not> semantics e f g p\<close>
  then have \<open>\<forall>(e :: nat \<Rightarrow> tm) f g. semantics e f g p\<close>
    by simp
  then show False
  proof -
    assume \<open>\<forall>(e :: nat \<Rightarrow> tm) f g. semantics e f g p\<close>
    moreover obtain steps
      where steps: \<open>fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
      using assms by blast
    then have \<open>Hintikka (tree_fms steps)\<close>
      using escape_path_Hintikka assms by simp
    moreover have \<open>p \<in> tree_fms steps\<close>
      using steps shd_sset unfolding tree_fms_def by force
    then have \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> semantics e f g p\<close>
      using calculation(2) hintikka_counter_model assms(2) steps sorry (* by blast *)
    ultimately show \<open>False\<close>
      by blast
  qed
qed

lemma epath_lem:
  assumes \<open>p \<in> (UNIV :: fm set)\<close> \<open>\<nexists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  using assms(2) epath_prover_completeness t_def by blast

lemma epath_contr:
  assumes \<open>\<tturnstile> [p]\<close> \<open>closed 0 p\<close>
  shows \<open>\<nexists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
proof (rule ccontr, simp)
  show \<open>\<exists> steps. epath steps \<and> fst (fst (shd steps)) = [p] \<and> Saturated steps \<Longrightarrow> False\<close>
  proof -
    assume ep: \<open>\<exists> steps. epath steps \<and> fst (fst (shd steps)) = [p] \<and> Saturated steps\<close>
    have \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> (semantics e f g p)\<close>
      using ep epath_countermodel assms(2) by blast
    with assms show False using sound by fastforce
  qed
qed

text \<open>Finally, we arrive at the main theorem\<close>
theorem completeness:
  assumes \<open>\<tturnstile> [p]\<close> \<open>closed 0 p\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  by (simp add: assms epath_contr epath_lem epath_prover_completeness)

end