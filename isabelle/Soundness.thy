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

(* These three kind of belong in SeCaV.thy *)
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

(* I can modify effect' to add stuff to A so I know directly that it's there *)
(*
  I'm using pre to make the ih apply to more than just ps, since parts p adds formulas in front.
 
  I need to know in the Delta cases that ?i (currently \<open>generateNew A\<close>)
    is new to pre, p and ps.
 
  What does pre look like?
  - In Alpha and Beta cases, I add direct subformulas to pre
  - In Gamma cases I add Exi p (Neg (Uni p)) and instances p[t/0] for all t in A
  - In Delta cases I add p[i/0] for an i not in A.

  In the Delta case, I introduce a new param, so I can't assume
    that pre only contains subformulas of ps.
  I can assume that it only contains subformulas and instances but this does not help me,
    as it tells me nothing about params.
*)

lemma SeCaV_effect'_pre:
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs)\<close> \<open>paramss ps \<subseteq> paramsts A\<close> 
  shows \<open>\<tturnstile> pre @ ps\<close>
  using assms
proof (induct ps arbitrary: pre)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  then have ih: \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ qs) \<Longrightarrow> (\<tturnstile> pre @ ps)\<close> for pre
    by simp

  have **: \<open>\<tturnstile> pre @ p # ps\<close> if *: \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> pre @ p # qs)\<close> for p
  proof -
    have \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> (pre @ [p]) @ qs)\<close>
      using * by simp
    then have \<open>\<tturnstile> pre @ p # ps\<close>
      using ih[where pre=\<open>pre @ [p]\<close>] Cons.prems by simp
    then show ?thesis
      by blast
  qed

  have \<open>\<forall>qs \<in> set (list_prod (parts A r p) (effect' A r ps)). (\<tturnstile> pre @ qs)\<close>
    using Cons.prems by simp
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
        using 3 ih[where pre=\<open>pre @ [p, q]\<close>] by simp
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
        using 2 ih[where pre=\<open>pre @ [Neg p, q]\<close>] by simp
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
        using 10 ih[where pre=\<open>pre @ [Neg p, Neg q]\<close>] by simp
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
        using 4 ih[where pre=\<open>pre @ [_]\<close>] by simp_all
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
        using 8 ih ih[where pre=\<open>pre @ [_]\<close>] by simp_all
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
        using 9 ih[where pre=\<open>pre @ [_]\<close>] by simp_all
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
        using 6 ih[where pre=\<open>pre @ [_]\<close>] by simp (* Right here pre must be allowed to contain ?i *)
      then have \<open>\<tturnstile> sub 0 (Fun ?i []) p # pre @ ps\<close>
        using Ext by simp
      moreover have \<open>?i \<notin> paramsts A\<close>
        by (induct A) (metis Suc_max_new generateNew_def listFunTm_paramst(2) plus_1_eq_Suc)+
      then have \<open>news ?i (p # ps)\<close> (* Right here pre must not *)
        using 6 Cons.prems(2) news_paramss by auto
      then have \<open>news ?i (p # pre @ ps)\<close>
        using Cons.prems
        sorry (* TODO: pre fucks me up *)
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
        using 11 ih[where pre=\<open>pre @ [_]\<close>] sorry (* TODO *)
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
        using 13 ih[where pre=\<open>pre @ [_]\<close>] by simp
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
        using 5 ih[where pre=\<open>pre @ Exi p # map _ A\<close>] by simp
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
        using 12 ih[where pre=\<open>pre @ Neg (Uni p) # map _ A\<close>] by simp
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
  assumes \<open>\<forall>qs \<in> set (effect' A r ps). (\<tturnstile> qs)\<close> \<open>paramss ps \<subseteq> paramsts A\<close>
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

  have \<open>(\<Union>p \<in> set ps. set (subtermFm p)) \<subseteq> set A\<close>
    sorry
  then have A: \<open>paramss ps \<subseteq> paramsts A\<close>
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
      using False A r_enabled eff_effect' next_sound SeCaV_effect' by metis
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