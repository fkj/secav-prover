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

lemma (* TODO: needs lemmas about sub and params I think *)
  assumes \<open>qs \<in> set (parts A r p)\<close> \<open>q \<in> set qs\<close> \<open>r \<noteq> DeltaUni\<close> \<open>r \<noteq> DeltaExi\<close>
  shows \<open>params q \<subseteq> paramsts A \<union> params p\<close>
  using assms
(*
proof (cases r)
  case GammaExi
  then show ?thesis
    using assms
  proof (cases p rule: Neg_exhaust)
    case (5 p)
    then show ?thesis
      using GammaExi assms unfolding parts_def
      apply simp
      apply (induct A)
       apply simp
      sorry
  qed (auto simp: parts_def)
next
  case GammaUni
  then show ?thesis sorry
qed (cases p rule: Neg_exhaust; auto simp: parts_def)
*)
  oops

lemma SeCaV_effect'_pre:
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs)\<close>
   (* \<open>(\<Union>p \<in> set (pre @ ps). set (subtermFm p)) \<subseteq> set A\<close> *)
  shows \<open>\<tturnstile> pre @ ps\<close>
  using assms
proof (induct ps arbitrary: pre)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then have ih: \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs) \<Longrightarrow> (\<tturnstile> pre @ ps)\<close>
(*    if \<open>(\<Union>p \<in> set pre. set (subtermFm p)) \<subseteq> set A\<close> *) for pre
   (* using that *) by simp

  have **: \<open>\<tturnstile> pre @ p # ps\<close>
    if *: \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # qs)\<close>
(*    and p: \<open>set (subtermFm p) \<subseteq> set A\<close>
    and pre: \<open>(\<Union>p \<in> set pre. set (subtermFm p)) \<subseteq> set A\<close> *)
    for p
  proof -
    have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      using * by simp
    then have \<open>\<tturnstile> pre @ p # ps\<close>
      using ih[where pre=\<open>pre @ [p]\<close>] (* p pre *) by simp
    then show ?thesis
      by blast
  qed

  have \<open>\<forall>qs \<in> set (list_prod (parts A r p) (effect' A r ps)). (\<tturnstile> pre @ qs)\<close>
    using Cons by simp
  then have \<open>\<forall>qs \<in> {hs @ ts |hs ts. hs \<in> set (parts A r p) \<and> ts \<in> set (effect' A r ps)}.
      (\<tturnstile> pre @ qs)\<close>
    using list_prod_is_cartesian by blast
  then have *: \<open>\<forall>hs \<in> set (parts A r p). \<forall>ts \<in> set (effect' A r ps). (\<tturnstile> pre @ hs @ ts)\<close>
    by blast
  then show ?case
  proof (cases r)
    case AlphaDis
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (3 p q)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # q # qs)\<close>
        using AlphaDis * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p, q]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ p # q # ps\<close>
        using 3 ih by fastforce
      then have \<open>\<tturnstile> p # q # pre @ ps\<close>
        using Ext by simp
      then have \<open>\<tturnstile> Dis p q # pre @ ps\<close>
        using SeCaV.AlphaDis by blast
      then show ?thesis
        using 3 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case AlphaImp
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (2 p q)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg p # q # qs)\<close>
        using AlphaImp * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg p, q]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ Neg p # q # ps\<close>
        using 2 ih by fastforce
      then have \<open>\<tturnstile> Neg p # q # pre @ ps\<close>
        using Ext by simp
      then have \<open>\<tturnstile> Imp p q # pre @ ps\<close>
        using SeCaV.AlphaImp by blast
      then show ?thesis
        using 2 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case AlphaCon
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (10 p q)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg p # Neg q # qs)\<close>
        using AlphaCon * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg p, Neg q]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ Neg p # Neg q # ps\<close>
        using 10 ih by fastforce
      then have \<open>\<tturnstile> Neg p # Neg q # pre @ ps\<close>
        using Ext by simp
      then have \<open>\<tturnstile> Neg (Con p q) # pre @ ps\<close>
        using SeCaV.AlphaCon by blast
      then show ?thesis
        using 10 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case BetaCon
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (4 p q)
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ q # qs)\<close>
        using BetaCon * unfolding parts_def by simp_all
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [q]) @ qs)\<close>
        by simp_all
      then have \<open>\<tturnstile> pre @ p # ps\<close> \<open>\<tturnstile> pre @ q # ps\<close>
        using 4 ih by fastforce+
      then have \<open>\<tturnstile> p # pre @ ps\<close> \<open>\<tturnstile> q # pre @ ps\<close>
        using Ext by simp_all
      then have \<open>\<tturnstile> Con p q # pre @ ps\<close>
        using SeCaV.BetaCon by blast
      then show ?thesis
        using 4 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case BetaImp
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (8 p q)
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg q # qs)\<close>
        using BetaImp * unfolding parts_def by simp_all
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg q]) @ qs)\<close>
        by simp_all
      then have \<open>\<tturnstile> pre @ p # ps\<close> \<open>\<tturnstile> pre @ Neg q # ps\<close>
        using 8 ih by fastforce+
      then have \<open>\<tturnstile> p # pre @ ps\<close> \<open>\<tturnstile> Neg q # pre @ ps\<close>
        using Ext by simp_all
      then have \<open>\<tturnstile> Neg (Imp p q) # pre @ ps\<close>
        using SeCaV.BetaImp by blast
      then show ?thesis
        using 8 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case BetaDis
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (9 p q)
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg p # qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg q # qs)\<close>
        using BetaDis * unfolding parts_def by simp_all
      then have
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg p]) @ qs)\<close>
        \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg q]) @ qs)\<close>
        by simp_all
      then have \<open>\<tturnstile> pre @ Neg p # ps\<close> \<open>\<tturnstile> pre @ Neg q # ps\<close>
        using 9 ih by fastforce+
      then have \<open>\<tturnstile> Neg p # pre @ ps\<close> \<open>\<tturnstile> Neg q # pre @ ps\<close>
        using Ext by simp_all
      then have \<open>\<tturnstile> Neg (Dis p q) # pre @ ps\<close>
        using SeCaV.BetaDis by blast
      then show ?thesis
        using 9 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case DeltaUni
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (6 p)
      let ?i = \<open>generateNew A\<close>
      from 6 have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ sub 0 (Fun ?i []) p # qs)\<close>
        using DeltaUni * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [sub 0 (Fun ?i []) p]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ sub 0 (Fun ?i []) p # ps\<close>
        using 6 ih by fastforce
      then have \<open>\<tturnstile> sub 0 (Fun ?i []) p # pre @ ps\<close>
        using Ext by simp
      moreover have \<open>news ?i (p # pre @ ps)\<close>
        sorry (* TODO: need to ensure this *)
      ultimately have \<open>\<tturnstile> Uni p # pre @ ps\<close>
        using SeCaV.DeltaUni by blast
      then show ?thesis
        using 6 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case DeltaExi
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (11 p)
      let ?i = \<open>generateNew A\<close>
      from 11 have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # qs)\<close>
        using DeltaExi * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [Neg (sub 0 (Fun ?i []) p)]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # ps\<close>
        using 11 ih by fastforce
      then have \<open>\<tturnstile> Neg (sub 0 (Fun ?i []) p) # pre @ ps\<close>
        using Ext by simp
      moreover have \<open>news ?i (p # pre @ ps)\<close>
        sorry (* TODO: need to ensure this *)
      ultimately have \<open>\<tturnstile> Neg (Exi p) # pre @ ps\<close>
        using SeCaV.DeltaExi by blast
      then show ?thesis
        using 11 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case NegNeg
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (13 p)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # qs)\<close>
        using NegNeg * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
        by simp
      then have \<open>\<tturnstile> pre @ p # ps\<close>
        using 13 ih by fastforce
      then have \<open>\<tturnstile> p # pre @ ps\<close>
        using Ext by simp
      then have \<open>\<tturnstile> Neg (Neg p) # pre @ ps\<close>
        using SeCaV.Neg by blast
      then show ?thesis
        using 13 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case GammaExi
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (5 p)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ qs)\<close>
        using GammaExi * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> ((pre @ Exi p # map (\<lambda>t. sub 0 t p) A) @ qs))\<close>
        by simp
      then have \<open>\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ ps\<close>
        using 5 ih by fastforce
      moreover have \<open>ext (map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ ps)
          (pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ ps)\<close>
        by auto
      ultimately have \<open>\<tturnstile> map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ ps\<close>
        using Ext by blast
      then have \<open>\<tturnstile> Exi p # pre @ ps\<close>
      proof (induct A)
        case Nil
        then show ?case
          by simp
      next
        case (Cons a A)
        then have \<open>\<tturnstile> Exi p # map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ ps\<close>
          using SeCaV.GammaExi by simp
        then have \<open>\<tturnstile> map (\<lambda>t. sub 0 t p) A @ Exi p # pre @ ps\<close>
          using Ext by simp
        then show ?case
          using Cons.hyps by blast
      qed
      then show ?thesis
        using 5 Ext by simp
    qed (simp_all add: ** parts_def)
  next
    case GammaUni
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (12 p)
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ qs)\<close>
        using GammaUni * unfolding parts_def by simp
      then have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> ((pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A) @ qs))\<close>
        by simp
      then have \<open>\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ ps\<close>
        using 12 ih by fastforce
      moreover have \<open>ext (map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ ps)
          (pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ ps)\<close>
        by auto
      ultimately have \<open>\<tturnstile> map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ ps\<close>
        using Ext by blast
      then have \<open>\<tturnstile> Neg (Uni p) # pre @ ps\<close>
      proof (induct A)
        case Nil
        then show ?case
          by simp
      next
        case (Cons a A)
        then have \<open>\<tturnstile> Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ ps\<close>
          using SeCaV.GammaUni by simp
        then have \<open>\<tturnstile> map (\<lambda>t. Neg (sub 0 t p)) A @ Neg (Uni p) # pre @ ps\<close>
          using Ext by simp
        then show ?case
          using Cons.hyps by blast
      qed
      then show ?thesis
        using 12 Ext by simp
    qed (simp_all add: ** parts_def)
  qed
qed

corollary SeCaV_effect':
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> qs)\<close>
  shows \<open>\<tturnstile> ps\<close>
  using SeCaV_effect'_pre assms by (metis append_Nil)

interpretation Soundness eff rules UNIV \<open>\<lambda>_ (A, ps). (\<tturnstile> ps)\<close>
  unfolding Soundness_def
proof safe
  fix r A ps ss S
  assume r_rule: \<open>r \<in> R\<close> and r_enabled: \<open>eff r (A, ps) ss\<close>

  assume \<open>\<forall>s'. s' |\<in>| ss \<longrightarrow> (\<forall>S \<in> UNIV. case s' of (A, ps) \<Rightarrow> \<tturnstile> ps)\<close>
  then have next_sound: \<open>\<forall>B qs. (B, qs) |\<in>| ss \<longrightarrow> (\<tturnstile> qs)\<close>
    by simp

  have A: \<open>(\<Union>p \<in> set ps. set (subtermFm p)) \<subseteq> set A\<close>
    sorry

  show \<open>\<tturnstile> ps\<close>
  proof (cases \<open>branchDone ps\<close>)
    case True
    then obtain p where \<open>p \<in> set ps\<close> \<open>Neg p \<in> set ps\<close>
      using branchDone_contradiction by blast
    then show ?thesis
      using Ext Basic by fastforce
  next
    case False
    then show ?thesis
      using False r_enabled eff_effect' next_sound SeCaV_effect' by metis
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>ssemantics e f g (snd (fst (root t)))\<close>
proof -
  have \<open>\<tturnstile> (snd (fst (root t)))\<close>
    using soundness assms prod.exhaust by fastforce
  then show ?thesis
    using sound by blast
qed

(*************** SEMANTIC APPROACH *************)


(*
  This assumption is too strong in a sense.
  I'm not going to know the "validity" of parts, but something larger where parts is a head.
*)
lemma soundness_parts:
  assumes \<open>set (subtermFm p) \<subseteq> set A\<close> \<open>\<forall>qs \<in> set (parts A r p). \<forall>f. ssemantics e f g qs\<close>
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

(*
  Paper proof:

  Alpha: p, q, ... \<Longrightarrow> Dis p q, ...
  Either p or q is sat and then Dis p q is, or the shared tail is.

  Beta: p, ... \<Longrightarrow> q, ... \<Longrightarrow> Con p q, ...
  Either p and q is sat or the shared tail is sat in one branch.

  Delta: p[i/0], ... \<Longrightarrow> i new \<Longrightarrow> Uni p, ...
  Case:
  - if p[i/0] holds for all assignments of i, then Uni p holds
  - otherwise consider some assignment x of i where p[i/0] does not hold.
      Then Uni p does not hold, so we need to show the tail is sat.
      Apply the induction hypothesis at i := x.
      Since p[i/0] does not hold under this assignment, we can reduce this
        to some part of the tail holding under i := x.
      But i does not occur in the tail.
      Which proves the thesis.

  Gamma: p[i/0], ... for some i in A \<Longrightarrow> Exi p, ...
  Either p[i/0] is sat and so Exi p is, or the shared tail is.

  In @thm\<open>sound\<close> we have stuff like \<open>\<exists>a\<in>set (sub 0 (Fun i []) p # z). semantics e ?f g a\<close> as IH.
*)

lemma soundness_effect':
  assumes \<open>(\<Union>p \<in> set ps. set (subtermFm p)) \<subseteq> set A\<close>
    (* This quantifier doesn't work with the disjunction that appears in the induction *)
    \<open>\<forall>qs \<in> set (effect' A r ps). \<forall>f. ssemantics e f g qs\<close>
   (* Maybe I need a more local perspective such that instead of
        - all effects are valid \<Longrightarrow> sequent is valid
      we do
        - all parts are valid \<Longrightarrow> glue \<Longrightarrow> sequent is valid *)
  shows \<open>ssemantics e f g ps\<close>
  using assms
proof (induct ps arbitrary: f)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then have ih: \<open>\<forall>qs \<in> set (effect' A r ps). ssemantics e f g qs \<Longrightarrow> ssemantics e f g ps\<close> for f
    sorry

  moreover have \<open>\<forall>qs \<in> set (effect' A r (p # ps)). ssemantics e f g qs\<close>
    sorry
  then have \<open>\<forall>qs \<in> set (list_prod (parts A r p) (effect' A r ps)). ssemantics e f g qs\<close>
    by simp
  then have \<open>\<forall>qs \<in> {hs @ ts |hs ts. hs \<in> set (parts A r p) \<and> ts \<in> set (effect' A r ps)}.
      ssemantics e f g qs\<close>
    using list_prod_is_cartesian by blast
  then have *: \<open>\<forall>hs \<in> set (parts A r p). \<forall>ts \<in> set (effect' A r ps).
      ssemantics e f g hs \<or> ssemantics e f g ts\<close>
    by force
  then show ?case
  proof (cases r)
    case AlphaDis
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case AlphaImp
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case AlphaCon
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case BetaCon
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case BetaImp
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case BetaDis
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case DeltaUni
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (6 p')      
      let ?i = \<open>generateNew A\<close>
      have i: \<open>news ?i (p' # ps)\<close>
        (* TODO: if this is not provable we have a problem but it will require coupling
          new and params if not done so already in SeCaV.thy *)
        sorry

      (* TODO: this one needs to be over an ?f I can change *)
(*
      have ih': \<open>semantics e f g (sub 0 (Fun ?i []) p') \<or>
          (\<forall>ts\<in>set (effect' A DeltaUni ps). ssemantics e f g ts)\<close>
        using 6 DeltaUni * unfolding parts_def by simp
*)

      have *: \<open>\<forall>hs \<in> set (parts A r p). \<forall>ts \<in> set (effect' A r ps).
          \<forall>f. ssemantics e f g hs \<or> ssemantics e f g ts\<close>
        sorry
      then have **: \<open>semantics e f g (sub 0 (Fun ?i []) p') \<or>
          (\<forall>ts\<in>set (effect' A DeltaUni ps). ssemantics e f g ts)\<close> for f
        using 6 DeltaUni unfolding parts_def by auto

      have thesis: \<open>?thesis = (semantics e f g p \<or> ssemantics e f g ps)\<close>
        using DeltaUni * unfolding parts_def by simp

      show ?thesis
      proof (cases \<open>\<forall>x. semantics e (f(?i := \<lambda>_. x)) g (sub 0 (Fun ?i []) p')\<close>)
        case True
        then have \<open>semantics e f g (Uni p')\<close>
          using i by simp
        then show ?thesis
          using 6 thesis by blast
      next
        case False
        then have \<open>\<not> semantics e f g (Uni p')\<close>
          using i by simp
        then have thesis': \<open>?thesis = ssemantics e f g ps\<close>
          using 6 thesis by blast
        note False
        then obtain x where \<open>\<not> semantics e (f(?i := \<lambda>_. x)) g (sub 0 (Fun ?i []) p')\<close>
          by blast
        then have \<open>\<forall>ts \<in> set (effect' A DeltaUni ps). ssemantics e (f(?i := \<lambda>_. x)) g ts\<close>
          using ** by blast
        then have \<open>\<forall>ts \<in> set (effect' A DeltaUni ps). ssemantics e f g ts\<close>
          using i upd_lemma sorry
              (* This is a bit annoying but should just be induction
                  We need that parts does not introduce ?i to any of the results
                  (and that it doesn't appear there in the first place). *)
        then show ?thesis
          using DeltaUni ih by simp
      qed
    qed (auto simp: ih parts_def)
  next
    case DeltaExi
    then show ?thesis
      using *
    proof (cases p rule: Neg_exhaust)
      case (11 p')
      then show ?thesis sorry
    qed (auto simp: ih parts_def)
  next
    case NegNeg
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case GammaExi
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  next
    case GammaUni
    then show ?thesis
      using * by (cases p rule: Neg_exhaust; auto simp: ih parts_def)
  qed

(*
  proof (cases \<open>\<forall>hs \<in> set (parts A r p). \<forall>f. ssemantics e f g hs\<close>)
    case True
    then show ?thesis
      using Cons apply simp by (meson soundness_parts)
  next
    case False
    then obtain hs f where hs: \<open>hs \<in> set (parts A r p)\<close> \<open>\<not> ssemantics e f g hs\<close>
      by blast
    then have \<open>\<forall>ts \<in> set (effect' A r ps). ssemantics e f g ts\<close>
      using * by blast
    then have \<open>\<forall>ts \<in> set (effect' A r ps). \<forall>f. ssemantics e f g ts\<close>
      sorry (* I only know this for a particular f but the ih requires all f... *)
    then have \<open>\<forall>f. ssemantics e f g ps\<close>
      using ih by blast
    then show ?thesis
      by simp
  qed
*)
qed

(*
interpretation Soundness eff rules UNIV \<open>\<lambda>(e, f, g) (A, ps). ssemantics e f g ps\<close>
  unfolding Soundness_def
proof safe
  fix r A ps ss f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close> and r_enabled: \<open>eff r (A, ps) ss\<close>
   
  assume \<open>\<forall>s'. s' |\<in>| ss \<longrightarrow> (\<forall>S \<in> (UNIV :: ((nat \<Rightarrow> 'a) \<times> _) set).
      (case S of (e, f, g) \<Rightarrow> \<lambda>(A, ps). ssemantics e f g ps) s')\<close>
  then have next_sound: \<open>\<forall>B qs. (B, qs) |\<in>| ss \<longrightarrow> (\<forall>f. ssemantics e f g qs)\<close>
    by simp

  have A: \<open>(\<Union>p \<in> set ps. set (subtermFm p)) \<subseteq> set A\<close>
    using r_enabled unfolding eff_def
    sorry (* TODO: how do I get this assumption in here? I think I need to change an interpretation
      in Prover.thy such that UNIV is replaced by the set of valid states. *)

  show \<open>ssemantics e f g ps\<close>
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
      then have \<open>\<forall>qs \<in> set (effect' A r ps). \<forall>f. ssemantics e f g qs\<close>
        using next_sound by blast
      then show ?thesis
        using soundness_effect' A by blast
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
*)

end