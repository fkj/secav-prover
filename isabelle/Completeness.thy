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

lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

lemma effStep_unique: \<open>\<forall>sl sl'. effStep s sl \<longrightarrow> effStep s sl' \<longrightarrow> sl = sl'\<close>
  unfolding eff_def
  by simp

fun index_of :: \<open>sequent \<Rightarrow> fm \<Rightarrow> nat\<close> where
  \<open>index_of [] _ = undefined\<close>
| \<open>index_of (p # z) f = (if p = f then 0 else 1 + index_of z f)\<close>

primrec firstDone :: \<open>sequent \<Rightarrow> fm option\<close> where
  \<open>firstDone [] = None\<close>
| \<open>firstDone (p # z) = (if Neg p \<in> set z then Some p else firstDone z)\<close>

definition basic_measure :: \<open>sequent \<Rightarrow> nat\<close> where
  \<open>basic_measure s = (case firstDone s of None \<Rightarrow> 0 | Some p \<Rightarrow> index_of s p)\<close>

lemma termination_PBasic:
  \<open>branchDone (fst (fst (shd steps))) \<Longrightarrow> ev (holds (\<lambda>s. Neg (hd (fst (fst s))) \<in> set (tl (fst (fst s))))) steps\<close>
proof (induction \<open>steps\<close> rule: wf_induct[where r=\<open>measure (\<lambda>steps. basic_measure (fst (fst (shd steps))))\<close>])
  case 1
  then show ?case ..
next
  case (2 s)
  then show ?case
  proof (cases \<open>Neg (hd (fst (fst (shd s)))) \<in> set (tl (fst (fst (shd s))))\<close>)
    case True
    then show ?thesis using 2 by auto
  next
    case False
    then show ?thesis using 2 sorry
  qed
qed

lemma id_PBasic: \<open>epath steps \<Longrightarrow> alw (holds (\<lambda>s. \<not> branchDone (fst (fst s)))) steps\<close>
proof (coinduction arbitrary: steps)
  case alw
  then show ?case
  proof (auto elim: epath.cases)
    assume *: \<open>epath steps\<close> and \<open>branchDone (fst (fst (shd steps)))\<close>
    then obtain n where \<open>effStep (shd (sdrop n steps)) {||}\<close>
      using termination_PBasic
      sorry
    moreover have \<open>epath (sdrop n steps)\<close>
      using * epath_sdrop by blast
    then have \<open>\<exists>sl. fst (shd (stl (sdrop n steps))) |\<in>| sl \<and> effStep (shd (sdrop n steps)) sl\<close>
      using epath.simps by blast
    ultimately have \<open>fst (shd (stl (sdrop n steps))) |\<in>| {||}\<close>
      using effStep_unique by blast
    then show False
      ..
  qed
qed

lemma woop:
  assumes \<open>Dis p q \<in> tree_fms steps\<close> \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>\<exists>n s. s = shd (sdrop n steps) \<and> (\<exists>z. s = ((Dis p q # z, PABD), AlphaDis))\<close>
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
  assume dis: \<open>Dis p q \<in> ?H\<close>
  obtain s z n where \<open>s = ((Dis p q # z, PABD), AlphaDis)\<close> and \<open>s = shd (sdrop n steps)\<close>
    using dis woop assms by metis
      (* we need that the nxt node contains the decomposed formula as soon as it is enabled *)
  then have \<open>takenAtStep AlphaDis (shd (sdrop n steps))\<close>
    by simp
  have \<open>\<exists>r. shd (sdrop (Suc n) steps) = ((p # q # z, PBasic), r)\<close>
    using assms (* follows from the effStep part of epath steps *)
    sorry
  then show \<open>p \<in> ?H \<and> q \<in> ?H\<close> (* follows from the definition of tree_fms *)
    sorry
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close>
  then have \<open>ev (\<lambda>s. (Imp p q) \<in> set (fst (fst (shd s))) \<and> snd (fst (shd s)) = PABD) steps\<close>
    sorry
  then have \<open>ev (\<lambda>s. hd (fst (fst (shd s))) = Imp p q \<and> snd (fst (shd s)) = PABD) steps\<close>
    sorry
  then have \<open>ev (\<lambda>s. hd (fst (fst (shd s))) = Neg p \<and> hd (tl (fst (fst (shd s)))) = q) steps\<close>
    sorry
  then show \<open>Neg p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
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
  show \<open>\<forall>t\<in>terms (tree_fms steps). sub 0 t p \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Uni p) \<in> tree_fms steps\<close>
  show \<open>\<forall>t\<in>terms (tree_fms steps). Neg (sub 0 t p) \<in> tree_fms steps\<close>
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
  assumes \<open>\<exists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
  shows \<open>\<exists>u (e :: nat \<Rightarrow> tm) f g . \<not> usemantics u e f g p \<and> is_env u e \<and> is_fdenot u f\<close>
proof (rule ccontr)
  assume \<open>\<nexists>u (e :: nat \<Rightarrow> tm) f g. \<not> usemantics u e f g p \<and> is_env u e \<and> is_fdenot u f\<close>
  then have \<open>\<forall>u (e :: nat \<Rightarrow> tm) f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
    by blast
  then show False
  proof -
    assume \<open>\<forall>u (e :: nat \<Rightarrow> tm) f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>
    moreover obtain steps
      where steps: \<open>fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
      using assms by blast
    then have \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?S\<close>)
      using escape_path_Hintikka assms by simp
    moreover have \<open>p \<in> tree_fms steps\<close>
      using steps shd_sset unfolding tree_fms_def by force
    then have \<open>\<exists>g. \<not> usemantics (terms ?S) (E ?S) (F ?S) g p\<close>
      using calculation(2) hintikka_counter_model steps by blast
    moreover have \<open>is_env (terms ?S) (E ?S)\<close> \<open>is_fdenot (terms ?S) (F ?S)\<close>
      using is_env_E is_fdenot_F by blast+
    ultimately show False
      by blast
  qed
qed

lemma epath_lem:
  assumes \<open>p \<in> (UNIV :: fm set)\<close> \<open>\<nexists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  using assms(2) epath_prover_completeness t_def by blast

lemma epath_contr:
  assumes \<open>\<tturnstile> [p]\<close>
  shows \<open>\<nexists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
proof (rule ccontr, simp)
  show \<open>\<exists> steps. epath steps \<and> fst (fst (shd steps)) = [p] \<and> Saturated steps \<Longrightarrow> False\<close>
  proof -
    assume ep: \<open>\<exists> steps. epath steps \<and> fst (fst (shd steps)) = [p] \<and> Saturated steps\<close>
    obtain u f g and e :: \<open>nat \<Rightarrow> tm\<close> where
      \<open>\<not> usemantics u e f g p\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
      using ep epath_countermodel  by blast
    with assms show False using sound_usemantics by fastforce
  qed
qed

text \<open>Finally, we arrive at the main theorem\<close>
theorem completeness:
  assumes \<open>\<tturnstile> [p]\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  by (simp add: assms epath_contr epath_lem epath_prover_completeness)

end