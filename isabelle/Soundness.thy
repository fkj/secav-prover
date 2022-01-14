theory Soundness
  imports ProverLemmas Usemantics
begin

section \<open>Soundness of the prover\<close>

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

theorem prover_soundness_SeCaV:
  assumes \<open>tfinite t\<close> \<open>wf t\<close>
  shows \<open>\<tturnstile> (snd (fst (root t)))\<close>
  using assms soundness prod.exhaust by fastforce

corollary prover_soundness_usemantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>\<exists>p \<in> set (snd (fst (root t))). usemantics u e f g p\<close>
  using assms prover_soundness_SeCaV sound_usemantics by blast

corollary prover_soundness_semantics:
  assumes \<open>tfinite t\<close> \<open>wf t\<close>
  shows \<open>\<exists>p \<in> set (snd (fst (root t))). semantics e f g p\<close>
  using assms prover_soundness_SeCaV sound by blast

end
