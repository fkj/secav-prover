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
  shows \<open>\<forall>qs \<in> set (effect' (remdups (A @ subtermFms ps)) r ps). \<exists>B. (B, qs) |\<in>| ss\<close>
  using assms unfolding eff_def using fset_of_list_elem by fastforce

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

(* These kind of belong in a SeCaVLemmas.thy. Probably along with usemantics and stuff. *)
lemma paramst_liftt [simp]:
  \<open>paramst (liftt t) = paramst t\<close> \<open>paramsts (liftts ts) = paramsts ts\<close>
  by (induct t and ts rule: liftt.induct liftts.induct) auto

lemma paramst_sub_term:
  \<open>paramst (sub_term m s t) \<subseteq> paramst s \<union> paramst t\<close>
  \<open>paramsts (sub_list m s l) \<subseteq> paramst s \<union> paramsts l\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) auto

lemma params_sub: \<open>params (sub m t p) \<subseteq> paramst t \<union> params p\<close>
proof (induct p arbitrary: m t)
  case (Pre x1 x2)
  then show ?case
    using paramst_sub_term(2) by simp
qed fastforce+

abbreviation \<open>paramss A \<equiv> \<Union>p \<in> set A. params p\<close>

lemma news_paramss: \<open>news i ps \<longleftrightarrow> i \<notin> paramss ps\<close>
  by (induct ps) auto

lemma paramsts_subset: \<open>set A \<subseteq> set B \<Longrightarrow> paramsts A \<subseteq> paramsts B\<close>
  by (induct A) auto

lemma subtermFm_subset_params: \<open>set (subtermFm p) \<subseteq> set A \<Longrightarrow> params p \<subseteq> paramsts A\<close>
  using params_subtermFm by force

lemma SeCaV_effect'_pre:
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs)\<close> \<open>paramss (pre @ ps) \<subseteq> paramsts A\<close> 
  shows \<open>\<tturnstile> pre @ ps\<close>
  using assms
proof (induct ps arbitrary: pre A)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then have ih: \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs) \<Longrightarrow> (\<tturnstile> pre @ ps)\<close>
    if \<open>paramss (pre @ ps) \<subseteq> paramsts A\<close>
    for pre A
    using that by simp

  let ?parts = \<open>parts A r p\<close>
  let ?A = \<open>remdups (A @ subtermFms (concat (parts A r p)))\<close>

  have A: \<open>paramss (pre @ p # ps) \<subseteq> paramsts ?A\<close>
    using paramsts_subset Cons.prems(2) by fastforce

  have \<open>\<forall>qs \<in> set (list_prod ?parts (effect' ?A r ps)). (\<tturnstile> pre @ qs)\<close>
    using Cons.prems by simp
  then have \<open>\<forall>qs \<in> {hs @ ts |hs ts. hs \<in> set ?parts \<and> ts \<in> set (effect' ?A r ps)}. (\<tturnstile> pre @ qs)\<close>
    using list_prod_is_cartesian by blast
  then have *: \<open>\<forall>hs \<in> set ?parts. \<forall>ts \<in> set (effect' ?A r ps). (\<tturnstile> pre @ hs @ ts)\<close>
    by blast
  then show ?case
  proof (cases r p rule: parts_exhaust)
    case (AlphaDis p q)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ p # q # qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [p, q]) @ qs)\<close>
      by simp
    then have \<open>\<tturnstile> pre @ p # q # ps\<close>
      using AlphaDis ih[where pre=\<open>pre @ [p, q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> p # q # pre @ ps\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Dis p q # pre @ ps\<close>
      using SeCaV.AlphaDis by blast
    then show ?thesis
      using AlphaDis Ext by simp
  next
    case (AlphaImp p q)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg p # q # qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg p, q]) @ qs)\<close>
      by simp
    then have \<open>\<tturnstile> pre @ Neg p # q # ps\<close>
      using AlphaImp ih[where pre=\<open>pre @ [Neg p, q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg p # q # pre @ ps\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Imp p q # pre @ ps\<close>
      using SeCaV.AlphaImp by blast
    then show ?thesis
      using AlphaImp Ext by simp
  next
    case (AlphaCon p q)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg p # Neg q # qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg p, Neg q]) @ qs)\<close>
      by simp
    then have \<open>\<tturnstile> pre @ Neg p # Neg q # ps\<close>
      using AlphaCon ih[where pre=\<open>pre @ [Neg p, Neg q]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg p # Neg q # pre @ ps\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Neg (Con p q) # pre @ ps\<close>
      using SeCaV.AlphaCon by blast
    then show ?thesis
      using AlphaCon Ext by simp
  next
    case (BetaCon p q)
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ p # qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ q # qs)\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [q]) @ qs)\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ p # ps\<close> \<open>\<tturnstile> pre @ q # ps\<close>
      using BetaCon ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> p # pre @ ps\<close> \<open>\<tturnstile> q # pre @ ps\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Con p q # pre @ ps\<close>
      using SeCaV.BetaCon by blast
    then show ?thesis
      using BetaCon Ext by simp
  next
    case (BetaImp p q)
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ p # qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg q # qs)\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg q]) @ qs)\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ p # ps\<close> \<open>\<tturnstile> pre @ Neg q # ps\<close>
      using BetaImp ih ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> p # pre @ ps\<close> \<open>\<tturnstile> Neg q # pre @ ps\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Neg (Imp p q) # pre @ ps\<close>
      using SeCaV.BetaImp by blast
    then show ?thesis
      using BetaImp Ext by simp
  next
    case (BetaDis p q)
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg p # qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg q # qs)\<close>
      using * unfolding parts_def by simp_all
    then have
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg p]) @ qs)\<close>
      \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg q]) @ qs)\<close>
      by simp_all
    then have \<open>\<tturnstile> pre @ Neg p # ps\<close> \<open>\<tturnstile> pre @ Neg q # ps\<close>
      using BetaDis ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp_all
    then have \<open>\<tturnstile> Neg p # pre @ ps\<close> \<open>\<tturnstile> Neg q # pre @ ps\<close>
      using Ext by simp_all
    then have \<open>\<tturnstile> Neg (Dis p q) # pre @ ps\<close>
      using SeCaV.BetaDis by blast
    then show ?thesis
      using BetaDis Ext by simp
  next
    case (DeltaUni p)
    let ?i = \<open>generateNew A\<close>
    have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ sub 0 (Fun ?i []) p # qs)\<close>
      using DeltaUni * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [sub 0 (Fun ?i []) p]) @ qs)\<close>
      by simp
    moreover have \<open>set (subtermFm (sub 0 (Fun ?i []) p)) \<subseteq> set ?A\<close>
      using DeltaUni unfolding parts_def by simp
    then have \<open>params (sub 0 (Fun ?i []) p) \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by blast
    ultimately have \<open>\<tturnstile> pre @ sub 0 (Fun ?i []) p # ps\<close>
      using DeltaUni ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp 
    then have \<open>\<tturnstile> sub 0 (Fun ?i []) p # pre @ ps\<close>
      using Ext by simp
    moreover have \<open>?i \<notin> paramsts A\<close>
      by (induct A) (metis Suc_max_new generateNew_def listFunTm_paramst(2) plus_1_eq_Suc)+
    then have \<open>news ?i (p # pre @ ps)\<close>
      using DeltaUni Cons.prems(2) news_paramss by auto
    ultimately have \<open>\<tturnstile> Uni p # pre @ ps\<close>
      using SeCaV.DeltaUni by blast
    then show ?thesis
      using DeltaUni Ext by simp
  next
    case (DeltaExi p)
    let ?i = \<open>generateNew A\<close>
    have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # qs)\<close>
      using DeltaExi * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [Neg (sub 0 (Fun ?i []) p)]) @ qs)\<close>
      by simp
    moreover have \<open>set (subtermFm (sub 0 (Fun ?i []) p)) \<subseteq> set ?A\<close>
      using DeltaExi unfolding parts_def by simp
    then have \<open>params (sub 0 (Fun ?i []) p) \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by blast
    ultimately have \<open>\<tturnstile> pre @ Neg (sub 0 (Fun ?i []) p) # ps\<close>
      using DeltaExi ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> Neg (sub 0 (Fun ?i []) p) # pre @ ps\<close>
      using Ext by simp
    moreover have \<open>?i \<notin> paramsts A\<close>
      by (induct A) (metis Suc_max_new generateNew_def listFunTm_paramst(2) plus_1_eq_Suc)+
    then have \<open>news ?i (p # pre @ ps)\<close>
      using DeltaExi Cons.prems(2) news_paramss by auto
   ultimately have \<open>\<tturnstile> Neg (Exi p) # pre @ ps\<close>
      using SeCaV.DeltaExi by blast
    then show ?thesis
      using DeltaExi Ext by simp
  next
    case (NegNeg p)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ p # qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      by simp
    then have \<open>\<tturnstile> pre @ p # ps\<close>
      using NegNeg ih[where pre=\<open>pre @ [_]\<close> and A=\<open>?A\<close>] A by simp
    then have \<open>\<tturnstile> p # pre @ ps\<close>
      using Ext by simp
    then have \<open>\<tturnstile> Neg (Neg p) # pre @ ps\<close>
      using SeCaV.Neg by blast
    then show ?thesis
      using NegNeg Ext by simp
  next
    case (GammaExi p)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> ((pre @ Exi p # map (\<lambda>t. sub 0 t p) A) @ qs))\<close>
      by simp
    moreover have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts A \<union> params p\<close>
      using params_sub by fastforce
    then have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts ?A\<close>
        using GammaExi A by fastforce
    then have \<open>paramss (map (\<lambda>t. sub 0 t p) A) \<subseteq> paramsts ?A\<close>
      by auto
    ultimately have \<open>\<tturnstile> pre @ Exi p # map (\<lambda>t. sub 0 t p) A @ ps\<close>
      using GammaExi ih[where pre=\<open>pre @ Exi p # map _ A\<close> and A=\<open>?A\<close>] A by simp
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
      using GammaExi Ext by simp
  next
    case (GammaUni p)
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ qs)\<close>
      using * unfolding parts_def by simp
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> ((pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A) @ qs))\<close>
      by simp
    moreover have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts A \<union> params p\<close>
      using params_sub by fastforce
    then have \<open>\<forall>t \<in> set A. params (sub 0 t p) \<subseteq> paramsts ?A\<close>
        using GammaUni A by fastforce
    then have \<open>paramss (map (\<lambda>t. sub 0 t p) A) \<subseteq> paramsts ?A\<close>
      by auto
    ultimately have \<open>\<tturnstile> pre @ Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A @ ps\<close>
      using GammaUni ih[where pre=\<open>pre @ Neg (Uni p) # map _ A\<close> and A=\<open>?A\<close>] A by simp
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
      using GammaUni Ext by simp
  next
    case Other
    then have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      using * by simp
    then have \<open>\<tturnstile> pre @ p # ps\<close>
      using ih[where pre=\<open>pre @ [p]\<close> and A=\<open>?A\<close>] A by simp
    then show ?thesis
      by blast
  qed
qed

corollary SeCaV_effect':
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> qs)\<close> \<open>paramss ps \<subseteq> paramsts A\<close>
  shows \<open>\<tturnstile> ps\<close>
  using SeCaV_effect'_pre assms by (metis append_Nil)

interpretation Soundness eff rules UNIV \<open>\<lambda>_ (A, ps). (\<tturnstile> ps)\<close>
  unfolding Soundness_def
proof safe
  fix r A ps ss S
  assume r_enabled: \<open>eff r (A, ps) ss\<close>

  assume \<open>\<forall>s'. s' |\<in>| ss \<longrightarrow> (\<forall>S \<in> UNIV. case s' of (A, ps) \<Rightarrow> \<tturnstile> ps)\<close>
  then have next_sound: \<open>\<forall>B qs. (B, qs) |\<in>| ss \<longrightarrow> (\<tturnstile> qs)\<close>
    by simp

  show \<open>\<tturnstile> ps\<close>
  proof (cases \<open>branchDone ps\<close>)
    case True
    then obtain p where \<open>p \<in> set ps\<close> \<open>Neg p \<in> set ps\<close>
      using branchDone_contradiction by blast
    then show ?thesis
      using Ext Basic by fastforce
  next
    case False
    let ?A = \<open>remdups (A @ subtermFms ps)\<close>
    have \<open>\<forall>qs \<in> set (effect' ?A r ps). (\<tturnstile> qs)\<close>
      using False r_enabled eff_effect' next_sound by blast
    moreover have \<open>set (subtermFms ps) \<subseteq> set ?A\<close>
      by simp
    then have \<open>paramss ps \<subseteq> paramsts ?A\<close>
      using subtermFm_subset_params by fastforce
    ultimately show \<open>\<tturnstile> ps\<close>
      using SeCaV_effect' by blast
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

end
