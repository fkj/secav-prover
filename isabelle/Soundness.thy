theory Soundness
  imports ProverLemmas
begin

section \<open>Soundness of the prover\<close>

abbreviation ssemantics
  :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> sequent \<Rightarrow> bool\<close>
  where \<open>ssemantics e f g ps \<equiv> \<exists>p \<in> set ps. semantics e f g p\<close>

lemma eff_preserves_Nil:
  assumes \<open>eff r (A, []) sl\<close> \<open>(B, s) |\<in>| sl\<close>
  shows \<open>s = []\<close>
  using assms unfolding eff_def effect_def by auto

lemma eff_Nil_not_empty:
  assumes \<open>eff r (A, []) sl\<close>
  shows \<open>sl \<noteq> {||}\<close>
  using assms unfolding eff_def effect_def by auto

lemma branchDone_contradiction:
  assumes \<open>branchDone ps\<close>
  shows \<open>\<exists>p. p \<in> set ps \<and> Neg p \<in> set ps\<close>
  using assms by (induct ps rule: branchDone.induct) auto

lemma branchDone_sat:
  assumes \<open>branchDone ps\<close>
  shows \<open>\<exists>p \<in> set ps. semantics e f g p\<close>
proof -
  obtain p where p: \<open>p \<in> set ps\<close> \<open>Neg p \<in> set ps\<close>
    using assms branchDone_contradiction by blast
  then show ?thesis
  proof (cases \<open>semantics e f g p\<close>)
    case True
    then show ?thesis
      using p(1) by blast
  next
    case False
    then have \<open>semantics e f g (Neg p)\<close>
      by simp
    then show ?thesis
      using p(2) by blast
  qed
qed

lemma eff_effect':
  assumes \<open>\<not> branchDone ps\<close> \<open>eff r (A, ps) ss\<close>
  shows \<open>\<forall>qs \<in> set (effect' A r ps). \<exists>B. (B, qs) |\<in>| ss\<close>
  using assms unfolding eff_def by (metis effect.simps fimageI fset_of_list_elem)

lemma paramst_subtermTm:
  \<open>\<forall>i \<in> paramst t. \<exists>l. Fun i l \<in> set (subtermTm t)\<close>
  \<open>\<forall>i \<in> paramsts ts. \<exists>l. Fun i l \<in> (\<Union>t \<in> set ts. set (subtermTm t))\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) fastforce+

lemma params_subtermFm: \<open>\<forall>i \<in> params p. \<exists>l. Fun i l \<in> set (subtermFm p)\<close>
proof (induct p)
  case (Pre x1 x2)
  then show ?case
    using paramst_subtermTm by simp
qed auto

lemma subtermTm_paramst:
  \<open>\<forall>s \<in> set (subtermTm t). s = Fun i l \<longrightarrow> i \<in> paramst t\<close>
  \<open>\<forall>s \<in> (\<Union>t \<in> set ts. set (subtermTm t)). s = Fun i l \<longrightarrow> i \<in> paramsts ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

lemma subtermFm_params: \<open>\<forall>t \<in> set (subtermFm p). t = Fun i l \<longrightarrow> i \<in> params p\<close>
proof (induct p)
  case (Pre x1 x2)
  then show ?case
    using subtermTm_paramst by simp
qed auto

lemma foldr_max:
  fixes xs :: \<open>nat list\<close>
  shows \<open>foldr max xs 0 = (if xs = [] then 0 else Max (set xs))\<close>
  by (induct xs) simp_all

lemma Suc_max_new:
  fixes xs :: \<open>nat list\<close>
  shows \<open>Suc (foldr max xs 0) \<notin> set xs\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons x xs)
  then have \<open>foldr max (x # xs) 0 = Max (set (x # xs))\<close>
    using foldr_max by simp
  then show ?thesis
    using Cons by (metis List.finite_set Max.insert add_0 empty_iff list.set(2) max_0_1(2)
        n_not_Suc_n nat_add_max_left plus_1_eq_Suc remdups.simps(2) set_remdups)
qed

lemma listFunTm_paramst: \<open>set (listFunTm t) = paramst t\<close> \<open>set (listFunTms ts) = paramsts ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

lemma generateNew_new: \<open>Fun (generateNew A) l \<notin> set A\<close>
  unfolding generateNew_def using Suc_max_new listFunTm_paramst(2) by fastforce

lemma soundness_parts:
  assumes \<open>set (subtermFm p) \<subseteq> set A\<close>
    \<open>\<forall>qs \<in> set (parts A r p). \<exists>q \<in> set qs. \<forall>f. semantics e f g q\<close>
  shows \<open>semantics e f g p\<close>
  using assms
proof (cases r)
  case DeltaUni
  then show ?thesis
    using assms
  proof (cases p rule: Neg_exhaust)
    case (6 p)
    let ?i = \<open>generateNew A\<close>
    from 6 have \<open>\<forall>f. semantics e f g (sub 0 (Fun ?i []) p)\<close>
      using DeltaUni assms(2) unfolding parts_def by simp
    then have \<open>\<forall>x. semantics e (f(?i := \<lambda>_. x)) g (sub 0 (Fun ?i []) p)\<close>
      by blast
    moreover have \<open>?i \<notin> params p\<close>
    proof
      assume \<open>?i \<in> params p\<close>
      then have \<open>\<exists>l. Fun ?i l \<in> set (subtermFm p)\<close>
        using params_subtermFm by blast
      moreover have \<open>\<nexists>l. Fun ?i l \<in> set (subtermFm p)\<close>
        using 6 assms(1) generateNew_new by auto
      ultimately show False
        by blast
    qed
    ultimately show ?thesis
      using 6 by simp
  qed (fastforce simp: parts_def)+
next
  case DeltaExi
  then show ?thesis
    using assms
  proof (cases p rule: Neg_exhaust)
    case (11 p)
    let ?i = \<open>generateNew A\<close>
    from 11 have \<open>\<forall>f. \<not> semantics e f g (sub 0 (Fun ?i []) p)\<close>
      using DeltaExi assms(2) unfolding parts_def by simp
    then have \<open>\<forall>x. \<not> semantics e (f(?i := \<lambda>_. x)) g (sub 0 (Fun ?i []) p)\<close>
      by blast
    moreover have \<open>?i \<notin> params p\<close>
    proof
      assume \<open>?i \<in> params p\<close>
      then have \<open>\<exists>l. Fun ?i l \<in> set (subtermFm p)\<close>
        using params_subtermFm by blast
      moreover have \<open>\<nexists>l. Fun ?i l \<in> set (subtermFm p)\<close>
        using 11 assms(1) generateNew_new by auto
      ultimately show False
        by blast
    qed
    ultimately show ?thesis
      using 11 by simp
  qed (fastforce simp: parts_def)+
qed (cases p rule: Neg_exhaust; fastforce simp: parts_def)+

interpretation Soundness eff rules UNIV \<open>\<lambda>(e, f, g) (A, ps). ssemantics e f g ps\<close>
  unfolding Soundness_def
proof safe
  fix r A ps ss f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
    and r_enabled: \<open>eff r (A, ps) ss\<close>
   
  assume \<open>\<forall>s'. s' |\<in>| ss \<longrightarrow> (\<forall>S\<in>(UNIV :: ((nat \<Rightarrow> 'a) \<times> _) set).
      (case S of (e, f, g) \<Rightarrow> \<lambda>(A, ps). ssemantics e f g ps) s')\<close>
  then have next_sound: \<open>\<forall>B qs. (B, qs) |\<in>| ss \<longrightarrow> (\<forall>(e :: nat \<Rightarrow> 'a) f g. ssemantics e f g qs)\<close>
    by simp

  let ?I = \<open>ssemantics e f g\<close>

  show \<open>?I ps\<close>
  proof (cases \<open>branchDone ps\<close>)
    case True
    then show ?thesis
      by (simp add: branchDone_sat)
  next
    case False
    then show ?thesis
    proof (cases r)
      case AlphaDis
      then have \<open>\<forall>qs \<in> set (effect' A r ps). \<exists>B. (B, qs) |\<in>| ss\<close>
        using False r_enabled eff_effect' by blast
      then have \<open>\<forall>qs \<in> set (effect' A r ps). ?I qs\<close>
        using next_sound by blast
      then show ?thesis
        apply (induct ps)
         apply simp
        sorry
    next
      case AlphaImp
      then show ?thesis sorry
    next
      case AlphaCon
      then show ?thesis sorry
    next
      case BetaCon
      then show ?thesis sorry
    next
      case BetaImp
      then show ?thesis sorry
    next
      case BetaDis
      then show ?thesis sorry
    next
      case DeltaUni
      then show ?thesis sorry
    next
      case DeltaExi
      then show ?thesis sorry
    next
      case NegNeg
      then show ?thesis sorry
    next
      case GammaExi
      then show ?thesis sorry
    next
      case GammaUni
      then show ?thesis sorry
    qed
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>\<exists>p \<in> set (snd (fst (root t))). semantics e f g p\<close>
  using soundness assms prod.exhaust by force

end