theory Hintikka
  imports Prover
begin

section \<open>Definition of a Hintikka set for SeCaV\<close>

definition
  \<open>terms H \<equiv> if (\<Union>f \<in> H. set (subtermFm f)) = {} then {Fun 0 []} else (\<Union>f \<in> H. set (subtermFm f))\<close>

locale Hintikka =
  fixes H :: \<open>fm set\<close>
  assumes
    Basic: \<open>Pre n ts \<in> H \<Longrightarrow> Neg (Pre n ts) \<notin> H\<close> and
    AlphaDis: \<open>Dis p q \<in> H \<Longrightarrow> p \<in> H \<and> q \<in> H\<close> and
    AlphaImp: \<open>Imp p q \<in> H \<Longrightarrow> Neg p \<in> H \<and> q \<in> H\<close> and
    AlphaCon: \<open>Neg (Con p q) \<in> H \<Longrightarrow> Neg p \<in> H \<and> Neg q \<in> H\<close> and
    BetaCon: \<open>Con p q \<in> H \<Longrightarrow> p \<in> H \<or> q \<in> H\<close> and
    BetaImp: \<open>Neg (Imp p q) \<in> H \<Longrightarrow> p \<in> H \<or> Neg q \<in> H\<close> and
    BetaDis: \<open>Neg (Dis p q) \<in> H \<Longrightarrow> Neg p \<in> H \<or> Neg q \<in> H\<close> and
    GammaExi: \<open>Exi p \<in> H \<Longrightarrow> \<forall>t \<in> terms H. sub 0 t p \<in> H\<close> and
    GammaUni: \<open>Neg (Uni p) \<in> H \<Longrightarrow> \<forall>t \<in> terms H. Neg (sub 0 t p) \<in> H\<close> and
    DeltaUni: \<open>Uni p \<in> H \<Longrightarrow> \<exists>t \<in> terms H. sub 0 t p \<in> H\<close> and
    DeltaExi: \<open>Neg (Exi p) \<in> H \<Longrightarrow> \<exists>t \<in> terms H. Neg (sub 0 t p) \<in> H\<close> and
    Neg: \<open>Neg (Neg p) \<in> H \<Longrightarrow> p \<in> H\<close>

section \<open>Various facts about the "flow" in the prover\<close>
definition prule :: \<open>sequent \<times> rule \<Rightarrow> rule\<close> where
  \<open>prule x = snd x\<close>

definition pseq :: \<open>state \<times> rule \<Rightarrow> sequent\<close> where
  \<open>pseq x = snd (fst x)\<close>

definition ptms :: \<open>state \<times> rule \<Rightarrow> tm list\<close> where
  \<open>ptms x = fst (fst x)\<close>

lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

text \<open>Transformation of formulas on an epath\<close>

lemma epath_eff:
  assumes \<open>epath steps\<close> \<open>eff (snd (shd steps)) (fst (shd steps)) ss\<close>
  shows \<open>fst (shd (stl steps)) |\<in>| ss\<close>
  using assms by (metis (mono_tags, lifting) epath.simps eff_def)

lemma effect_tms:
  assumes \<open>(B, qs) |\<in>| effect r (A, ps)\<close>
  shows \<open>B = remdups (A @ subterms ps)\<close>
  using assms by (metis (mono_tags, lifting) effect.simps fempty_iff fimageE fst_conv)

lemma epath_effect:
  assumes \<open>epath steps\<close> \<open>shd steps = ((A, ps), r)\<close>
  shows \<open>\<exists>B qs r'. (B, qs) |\<in>| effect r (A, ps) \<and> shd (stl steps) = ((B, qs), r') \<and>
          (B = remdups (A @ subterms ps))\<close>
  using assms epath_eff effect_tms
  by (metis (mono_tags, lifting) eff_def fst_conv prod.collapse snd_conv)

lemma epath_stl_ptms:
  assumes \<open>epath steps\<close>
  shows \<open>ptms (shd (stl steps)) = remdups (ptms (shd steps) @ subterms (pseq (shd steps)))\<close>
  using assms epath_effect by (metis fst_conv prod.exhaust_sel pseq_def ptms_def)

lemma epath_sdrop_ptms:
  assumes \<open>epath steps\<close>
  shows \<open>set (ptms (shd steps)) \<subseteq> set (ptms (shd (sdrop n steps)))\<close>
  using assms
proof (induct n)
  case (Suc n)
  then have \<open>epath (sdrop n steps)\<close>
    using epath_sdrop by blast
  then show ?case
    using Suc epath_stl_ptms by fastforce
qed simp

lemma epath_sdrop_Suc_ptms:
  assumes \<open>epath steps\<close>
  shows \<open>set (ptms (shd steps) @ subterms (pseq (shd steps))) \<subseteq>
         set (ptms (shd (sdrop (n + 1) steps)))\<close>
  using assms
proof (induct n)
  case 0
  then show ?case
    by (simp add: epath_stl_ptms)
  next
    case (Suc n)
  then have \<open>epath (sdrop (n + 1) steps)\<close>
    using epath_sdrop by blast
  then show ?case
    using Suc epath_stl_ptms by fastforce
qed

(* TODO: rules should be in a nicer order in the datatype... *)

text \<open>Unaffected formulas\<close>

definition affects :: \<open>rule \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>affects r p \<equiv> case (r, p) of
    (AlphaDis, Dis _ _) \<Rightarrow> True
  | (AlphaImp, Imp _ _) \<Rightarrow> True
  | (AlphaCon, Neg (Con _ _)) \<Rightarrow> True
  | (BetaCon, Con _ _) \<Rightarrow> True
  | (BetaImp, Neg (Imp _ _)) \<Rightarrow> True
  | (BetaDis, Neg (Dis _ _)) \<Rightarrow> True
  | (DeltaUni, Uni _) \<Rightarrow> True
  | (DeltaExi, Neg (Exi _)) \<Rightarrow> True
  | (NegNeg, Neg (Neg _)) \<Rightarrow> True
  | (GammaExi, Exi _) \<Rightarrow> False
  | (GammaUni, Neg (Uni _)) \<Rightarrow> False
  | (_,  _) \<Rightarrow> False\<close>
                      
lemma Neg_exhaust:
  \<open>(\<And>i ts. x = Pre i ts \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Imp p q \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Dis p q \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Con p q \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p. x = Exi p \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p. x = Uni p \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i ts. x = Neg (Pre i ts) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Neg (Imp p q) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Neg (Dis p q) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p q. x = Neg (Con p q) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p. x = Neg (Exi p) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p. x = Neg (Uni p) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>p. x = Neg (Neg p) \<Longrightarrow> P) \<Longrightarrow>
  P\<close>
proof (induct x)
  case (Neg p)
  then show ?case
    by (cases p) simp_all
qed simp_all

lemma parts_preserves_unaffected:
  assumes \<open>\<not> affects r p\<close> \<open>qs \<in> set (parts A r p)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms unfolding parts_def affects_def
  by (cases r; cases p rule: Neg_exhaust) simp_all

lemma parts_not_Nil: \<open>parts A r p \<noteq> []\<close>
  unfolding parts_def by (cases r; cases p rule: Neg_exhaust) auto

lemma parts_all_inhabited: \<open>[] \<notin> set (parts A r p)\<close>
  unfolding parts_def by (cases r; cases p rule: Neg_exhaust) auto

lemma set_effect'_Cons:
  \<open>set (effect' A r (p # ps)) =
    {hs @ ts |hs ts. hs \<in> set (parts A r p) \<and> ts \<in> set (effect' A r ps)}\<close>
  using list_prod_is_cartesian by (metis effect'.simps(2))

lemma effect'_preserves_unaffected:
  assumes \<open>p \<in> set ps\<close> \<open>\<not> affects r p\<close> \<open>qs \<in> set (effect' A r ps)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms parts_preserves_unaffected set_effect'_Cons
  by (induct ps arbitrary: qs) auto

lemma effect_preserves_unaffected:
  assumes \<open>p \<in> set ps\<close> \<open>\<not> affects r p\<close> \<open>(B, qs) |\<in>| effect r (A, ps)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms effect'_preserves_unaffected
  unfolding effect_def
  by (smt (verit, best) Pair_inject femptyE fimageE fset_of_list_elem old.prod.case)

text \<open>Affected formulas\<close>

lemma parts_in_effect':
  assumes \<open>p \<in> set ps\<close> \<open>qs \<in> set (effect' A r ps)\<close>
  shows \<open>\<exists>xs \<in> set (parts A r p). set xs \<subseteq> set qs\<close>
  using assms
proof (induct ps arbitrary: qs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
  proof (cases \<open>a = p\<close>)
    case True
    then show ?thesis
      using Cons(3) set_effect'_Cons by auto
  next
    case False
    then show ?thesis
      using Cons set_effect'_Cons
      by simp (metis Un_iff set_append subsetD subsetI)
  qed
qed 

lemma parts_in_effect:
  assumes \<open>p \<in> set ps\<close> \<open>(B, qs) |\<in>| effect r (A, ps)\<close> \<open>\<not> branchDone ps\<close>
  shows \<open>\<exists>xs \<in> set (parts A r p). set xs \<subseteq> set qs\<close>
  using assms parts_in_effect' by (auto simp: fset_of_list_elem)

corollary \<open>\<not> branchDone ps \<Longrightarrow> Neg (Neg p) \<in> set ps \<Longrightarrow>
    (B, qs) |\<in>| effect NegNeg (A, ps) \<Longrightarrow> p \<in> set qs\<close>
  using parts_in_effect unfolding parts_def by fastforce
   
corollary \<open>\<not> branchDone ps \<Longrightarrow> Neg (Uni p) \<in> set ps \<Longrightarrow> (B, qs) |\<in>| effect GammaUni (A, ps) \<Longrightarrow>
    set (map (\<lambda>t. Neg (sub 0 t p)) A) \<subseteq> set qs\<close>
  using parts_in_effect unfolding parts_def by fastforce

text \<open>Preservation on epath\<close>

lemma ev_prefix_sdrop:
  assumes \<open>ev (holds P) xs\<close>
  shows \<open>\<exists>pre suf n. list_all (not P) pre \<and> holds P suf \<and> pre = stake n xs \<and> suf = sdrop n xs\<close>
  using assms
proof (induct xs)
  case (base xs)
  then show ?case
    by (metis list.pred_inject(1) sdrop.simps(1) stake.simps(1))
next
  case (step xs)
  then show ?case
    by (metis holds.elims(1) list.pred_inject(2) list_all_simps(2) sdrop.simps(1-2) stake.simps(1-2))
qed

lemma ev_prefix:
  assumes \<open>ev (holds P) xs\<close>
  shows \<open>\<exists>pre suf. list_all (not P) pre \<and> holds P suf \<and> xs = pre @- suf\<close>
  using assms ev_prefix_sdrop by (metis stake_sdrop)

lemma always_enabledAtStep: \<open>enabledAtStep r xs\<close>
  by (simp add: RuleSystem_Defs.enabled_def eff_def)

lemma epath_preserves_unaffected:
  assumes \<open>p \<in> set (pseq (shd steps))\<close> \<open>epath steps\<close> \<open>steps = pre @- suf\<close>
    \<open>list_all (not (\<lambda>step. affects (snd step) p)) pre\<close>
  shows \<open>p \<in> set (pseq (shd suf))\<close>
  using assms
proof (induct pre arbitrary: steps)
  case Nil
  then show ?case
    by simp
next
  case (Cons q pre)
  from this(3) show ?case
  proof cases
    case (epath sl)
    then show ?thesis
      using Cons effect_preserves_unaffected unfolding eff_def pseq_def
      by simp (metis (no_types, lifting) effect_preserves_unaffected prod.exhaust_sel)
  qed
qed

section \<open>Proving that the formulas on an escape path form a Hintikka set\<close>

definition \<open>tree_fms steps \<equiv> \<Union>ss \<in> sset steps. set (pseq ss)\<close>

lemma pseq_in_tree_fms: \<open>\<lbrakk>x \<in> sset steps; p \<in> set (pseq x)\<rbrakk> \<Longrightarrow> p \<in> tree_fms steps\<close>
  using pseq_def tree_fms_def by blast

lemma tree_fms_in_pseq: \<open>p \<in> tree_fms steps \<Longrightarrow> \<exists>n. p \<in> set (pseq (steps !! n))\<close>
  unfolding pseq_def tree_fms_def using sset_range[of steps] by simp

lemma sset_sdrop: \<open>sset (sdrop n s) \<subseteq> sset s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  then show ?case
    by (metis in_mono sdrop_simps(2) stl_sset subsetI)
qed simp

lemma Saturated_sdrop: \<open>Saturated steps \<Longrightarrow> Saturated (sdrop n steps)\<close>
  by (simp add: RuleSystem_Defs.Saturated_def alw_iff_sdrop saturated_def)

lemma Saturated_ev_rule:
  assumes \<open>Saturated steps\<close>
  shows \<open>ev (holds (\<lambda>step. snd step = r)) (sdrop n steps)\<close>
proof -
  have \<open>Saturated (sdrop n steps)\<close>
    using \<open>Saturated steps\<close> Saturated_sdrop by fast
  moreover have \<open>r \<in> Prover.R\<close>
    by (metis rules_repeat snth_sset)
  ultimately have \<open>saturated r (sdrop n steps)\<close>
    unfolding Saturated_def by fast
  then show ?thesis
    unfolding saturated_def using always_enabledAtStep holds.elims(3) by blast
qed

abbreviation \<open>is_rule r step \<equiv> snd step = r\<close>

lemma list_prod_nil: \<open>list_prod [] ts = []\<close>
  by (induct ts) simp_all

lemma epath_never_branchDone:
  assumes \<open>epath steps\<close>
  shows \<open>alw (holds (not (branchDone o pseq))) steps\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have \<open>ev (holds (branchDone o pseq)) steps\<close>
    by (simp add: alw_iff_sdrop ev_iff_sdrop)
  then obtain n where n: \<open>holds (branchDone o pseq) (sdrop n steps)\<close>
    using sdrop_wait by blast
  let ?suf = \<open>sdrop n steps\<close>
  have \<open>\<forall>r A. effect r (A, pseq (shd ?suf)) = {||}\<close>
    unfolding effect_def using n by simp
  moreover have \<open>epath ?suf\<close>
    using \<open>epath steps\<close> epath_sdrop by blast
  then have \<open>\<forall>r A. \<exists>qs r'. qs |\<in>| effect r (A, pseq (shd ?suf)) \<and> shd (stl ?suf) = (qs, r')\<close>
    using epath_effect by (metis calculation prod.exhaust_sel pseq_def)
  ultimately show False
    by blast
qed

lemma sub_term_const_transfer:
  \<open>Fun a [] \<notin> set (subtermTm (sub_term m (Fun a []) t)) \<Longrightarrow>
    sub_term m (Fun a []) t = sub_term m s t\<close>
  \<open>Fun a [] \<notin> (\<Union>t \<in> set (sub_list m (Fun a []) l). set (subtermTm t)) \<Longrightarrow>
    sub_list m (Fun a []) l = sub_list m s l\<close>
 by (induct t and l rule: sub_term.induct sub_list.induct) auto

lemma sub_const_transfer:
  assumes \<open>Fun a [] \<notin> set (subtermFm (sub m (Fun a []) p))\<close>
  shows \<open>sub m (Fun a []) p = sub m t p\<close>
  using assms
proof (induct p arbitrary: m t)
  case (Pre i l)
  then have \<open>Fun a [] \<notin> (\<Union>t \<in> set (sub_list m (Fun a []) l). set (subtermTm t))\<close>
    by simp
  then show ?case
    using sub_term_const_transfer(2) by (metis sub.simps(1))
next
  case (Imp p q)
  then show ?case
    by (metis Un_iff set_append sub.simps(2) subtermFm.simps(2))
next
  case (Dis p1 p2)
  then show ?case
    by (metis Un_iff set_append sub.simps(3) subtermFm.simps(3))
next
  case (Con p1 p2)
  then show ?case
    by (metis Un_iff set_append sub.simps(4) subtermFm.simps(4))
next
  case (Exi p)
  then show ?case
    by (metis inc_list.simps(1) inc_term.simps(2) sub.simps(5) subtermFm.simps(5))
next
  case (Uni p)
  then show ?case
    by (metis inc_list.simps(1) inc_term.simps(2) sub.simps(6) subtermFm.simps(6))
next
  case (Neg p)
  then show ?case
    by (metis sub.simps(7) subtermFm.simps(7))
qed

lemma set_subterms:
  fixes ps
  defines \<open>ts \<equiv> \<Union>p \<in> set ps. set (subtermFm p)\<close>
  shows \<open>set (subterms ps) = (if ts = {} then {Fun 0 []} else ts)\<close>
proof -
  have *: \<open>set (remdups (concat (map subtermFm ps))) = (\<Union>p \<in> set ps. set (subtermFm p))\<close>
    by (induct ps) auto
  then show ?thesis
  proof (cases \<open>ts = {}\<close>)
    case True
    then show ?thesis
      by simp (metis * True list.simps(15) list.simps(4) set_empty2 ts_def)
  next
    case False
    then show ?thesis
      by simp (metis * empty_set list.exhaust list.simps(5) ts_def)
  qed
qed

lemma escape_path_Hintikka:
  fixes steps
  assumes \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?H\<close>)
proof
  fix n ts
  assume pre: \<open>Pre n ts \<in> ?H\<close>
  then obtain m where m: \<open>Pre n ts \<in> set (pseq (shd (sdrop m steps)))\<close>
    using tree_fms_in_pseq by auto

  show \<open>Neg (Pre n ts) \<notin> ?H\<close>
  proof
    assume \<open>Neg (Pre n ts) \<in> ?H\<close>
    then obtain k where k: \<open>Neg (Pre n ts) \<in> set (pseq (shd (sdrop k steps)))\<close>
      using tree_fms_in_pseq by auto

    let ?pre = \<open>stake (m + k) steps\<close>
    let ?suf = \<open>sdrop (m + k) steps\<close>
    
    have
      1: \<open>\<not> affects r (Pre n ts)\<close> and
      2: \<open>\<not> affects r (Neg (Pre n ts))\<close> for r
      unfolding affects_def by (cases r, simp_all)+
    
    have \<open>list_all (not (\<lambda>step. affects (snd step) (Pre n ts))) ?pre\<close>
      unfolding list_all_def using 1 by (induct ?pre) simp_all
    then have p: \<open>Pre n ts \<in> set (pseq (shd ?suf))\<close>
      using \<open>epath steps\<close> epath_preserves_unaffected m epath_sdrop
      by (metis (no_types, lifting) list.pred_mono_strong list_all_append
          sdrop_add stake_add stake_sdrop)

    have \<open>list_all (not (\<lambda>step. affects (snd step) (Neg (Pre n ts)))) ?pre\<close>
      unfolding list_all_def using 2 by (induct ?pre) simp_all
    then have np: \<open>Neg (Pre n ts) \<in> set (pseq (shd ?suf))\<close>
      using \<open>epath steps\<close> epath_preserves_unaffected k epath_sdrop
      (* TODO: smt *)
      by (smt (verit, best) add.commute list.pred_mono_strong list_all_append sdrop_add
          stake_add stake_sdrop)

    have \<open>holds (branchDone o pseq) ?suf\<close>
      using p np branchDone by simp
    moreover have \<open>\<not> holds (branchDone o pseq) ?suf\<close>
      using \<open>epath steps\<close> epath_never_branchDone by (simp add: alw_iff_sdrop)
    ultimately show False
      by blast
  qed
next
  fix p q
  assume \<open>Dis p q \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaDis
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>p \<in> set qs\<close> \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>p \<in> ?H \<and> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaImp
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>Neg p \<in> set qs\<close> \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Con p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaCon
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>Neg p \<in> set qs\<close> \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Con p q \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaCon
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>p \<in> set qs\<close> | \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Imp p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaImp
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>p \<in> set qs\<close> | \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Dis p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaDis
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>Neg p \<in> set qs\<close> | \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>Neg p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p
  assume \<open>Exi p \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto

  let ?r = GammaExi

  show \<open>\<forall>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
  proof
    fix t
    assume t: \<open>t \<in> terms ?H\<close>
    show \<open>sub 0 t p \<in> ?H\<close>
    proof -
      have \<open>\<exists>m. t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
      proof (cases \<open>(\<Union>f \<in> ?H. set (subtermFm f)) = {}\<close>)
        case True
        moreover have \<open>\<forall>p \<in> set (pseq (shd steps)). p \<in> ?H\<close>
          unfolding tree_fms_def by (metis pseq_in_tree_fms shd_sset tree_fms_def)
        ultimately have \<open>\<forall>p \<in> set (pseq (shd steps)). subtermFm p = []\<close>
          by simp
        then have \<open>concat (map subtermFm (pseq (shd steps))) = []\<close>
          by (induct \<open>pseq (shd steps)\<close>) simp_all
        then have \<open>subterms (pseq (shd steps)) = [Fun 0 []]\<close>
          by (metis list.simps(4) remdups_eq_nil_iff subterms.simps)
        then show ?thesis
          using True t unfolding terms_def
          by (metis empty_iff insert_iff list.set_intros(1) sdrop.simps(1))
      next
        case False
        then obtain pt where pt: \<open>t \<in> set (subtermFm pt)\<close> \<open>pt \<in> ?H\<close>
          using t unfolding terms_def by (metis (no_types, lifting) UN_E)
        then obtain m where m: \<open>pt \<in> set (pseq (shd (sdrop m steps)))\<close>
          using tree_fms_in_pseq by auto
        then show ?thesis
          using pt(1) set_subterms by fastforce
      qed
      then obtain m where \<open>t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
        by blast
      then have \<open>t \<in> set (ptms (shd (stl (sdrop m steps))))\<close>
        using epath_stl_ptms epath_sdrop \<open>epath steps\<close> by (metis set_remdups Un_iff set_append)
      moreover have \<open>epath (stl (sdrop m steps))\<close>
        using epath_sdrop \<open>epath steps\<close> by (meson epath.cases)
      ultimately have \<open>\<forall>k \<ge> m. t \<in> set (ptms (shd (stl (sdrop k steps))))\<close>
        using epath_sdrop_ptms by (metis (no_types, lifting) le_Suc_ex sdrop_add sdrop_stl subsetD)
      then have above: \<open>\<forall>k > m. t \<in> set (ptms (shd (sdrop k steps)))\<close>
        by (metis Nat.lessE less_irrefl_nat less_trans_Suc linorder_not_less sdrop_simps(2))

      let ?pre = \<open>stake (n + m + 1) steps\<close>
      let ?suf = \<open>sdrop (n + m + 1) steps\<close>

      have *: \<open>\<not> affects r ?f\<close> for r
        unfolding affects_def by (cases r, simp_all)+

      have \<open>ev (holds (is_rule ?r)) ?suf\<close>
        using \<open>Saturated steps\<close> Saturated_ev_rule by blast
      then obtain pre suf k where
        pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
        suf: \<open>holds (is_rule ?r) suf\<close> and
        ori: \<open>pre = stake k ?suf\<close> \<open>suf = sdrop k ?suf\<close>
        using ev_prefix_sdrop by blast

      have k: \<open>\<exists>k > m. suf = sdrop k steps\<close>
        using ori by (meson le_add2 less_add_one order_le_less_trans sdrop_add trans_less_add1)

      have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) ?pre\<close>
        unfolding list_all_def using * by (induct ?pre) simp_all
      then have \<open>?f \<in> set (pseq (shd ?suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop
        by (metis (no_types, lifting) list.pred_mono_strong list_all_append
            sdrop_add stake_add stake_sdrop)
      then have \<open>?f \<in> set (pseq (shd suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop * ori
        by (metis (no_types, lifting) list.pred_mono_strong pre stake_sdrop)
      moreover have \<open>epath suf\<close>
        using \<open>epath steps\<close> epath_sdrop ori by blast
      then obtain B qs r' where
        qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close>
        \<open>shd (stl suf) = ((B, qs), r')\<close>
        using suf epath_effect unfolding pseq_def ptms_def
        by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)

      moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
        using \<open>epath suf\<close> epath_never_branchDone by blast
      moreover have \<open>t \<in> set (ptms (shd suf))\<close>
        using above k by (meson le_add2 less_add_one order_le_less_trans)
      ultimately have \<open>sub 0 t p \<in> set qs\<close>
        using parts_in_effect[where A=\<open>ptms (shd suf)\<close>] unfolding parts_def by fastforce
      then show ?thesis
        using k pseq_in_tree_fms qs(2)
        by (metis Pair_inject in_mono prod.collapse pseq_def shd_sset sset_sdrop stl_sset)
    qed
  qed 
next
  fix p
  assume \<open>Neg (Uni p) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto

  let ?r = GammaUni

  show \<open>\<forall>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
  proof
    fix t
    assume t: \<open>t \<in> terms ?H\<close>
    show \<open>Neg (sub 0 t p) \<in> ?H\<close>
    proof -
      have \<open>\<exists>m. t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
      proof (cases \<open>(\<Union>f \<in> ?H. set (subtermFm f)) = {}\<close>)
        case True
        moreover have \<open>\<forall>p \<in> set (pseq (shd steps)). p \<in> ?H\<close>
          unfolding tree_fms_def by (metis pseq_in_tree_fms shd_sset tree_fms_def)
        ultimately have \<open>\<forall>p \<in> set (pseq (shd steps)). subtermFm p = []\<close>
          by simp
        then have \<open>concat (map subtermFm (pseq (shd steps))) = []\<close>
          by (induct \<open>pseq (shd steps)\<close>) simp_all
        then have \<open>subterms (pseq (shd steps)) = [Fun 0 []]\<close>
          by (metis list.simps(4) remdups_eq_nil_iff subterms.simps)
        then show ?thesis
          using True t unfolding terms_def
          by (metis empty_iff insert_iff list.set_intros(1) sdrop.simps(1))
      next
        case False
        then obtain pt where pt: \<open>t \<in> set (subtermFm pt)\<close> \<open>pt \<in> ?H\<close>
          using t unfolding terms_def by (metis (no_types, lifting) UN_E)
        then obtain m where m: \<open>pt \<in> set (pseq (shd (sdrop m steps)))\<close>
          using tree_fms_in_pseq by auto
        then show ?thesis
          using pt(1) set_subterms by fastforce
      qed
      then obtain m where \<open>t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
        by blast
      then have \<open>t \<in> set (ptms (shd (stl (sdrop m steps))))\<close>
        using epath_stl_ptms epath_sdrop \<open>epath steps\<close> by (metis set_remdups Un_iff set_append)
      moreover have \<open>epath (stl (sdrop m steps))\<close>
        using epath_sdrop \<open>epath steps\<close> by (meson epath.cases)
      ultimately have \<open>\<forall>k \<ge> m. t \<in> set (ptms (shd (stl (sdrop k steps))))\<close>
        using epath_sdrop_ptms by (metis (no_types, lifting) le_Suc_ex sdrop_add sdrop_stl subsetD)
      then have above: \<open>\<forall>k > m. t \<in> set (ptms (shd (sdrop k steps)))\<close>
        by (metis Nat.lessE less_irrefl_nat less_trans_Suc linorder_not_less sdrop_simps(2))

      let ?pre = \<open>stake (n + m + 1) steps\<close>
      let ?suf = \<open>sdrop (n + m + 1) steps\<close>

      have *: \<open>\<not> affects r ?f\<close> for r
        unfolding affects_def by (cases r, simp_all)+

      have \<open>ev (holds (is_rule ?r)) ?suf\<close>
        using \<open>Saturated steps\<close> Saturated_ev_rule by blast
      then obtain pre suf k where
        pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
        suf: \<open>holds (is_rule ?r) suf\<close> and
        ori: \<open>pre = stake k ?suf\<close> \<open>suf = sdrop k ?suf\<close>
        using ev_prefix_sdrop by blast

      have k: \<open>\<exists>k > m. suf = sdrop k steps\<close>
        using ori by (meson le_add2 less_add_one order_le_less_trans sdrop_add trans_less_add1)

      have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) ?pre\<close>
        unfolding list_all_def using * by (induct ?pre) simp_all
      then have \<open>?f \<in> set (pseq (shd ?suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop
        by (metis (no_types, lifting) list.pred_mono_strong list_all_append
            sdrop_add stake_add stake_sdrop)
      then have \<open>?f \<in> set (pseq (shd suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop * ori
        by (metis (no_types, lifting) list.pred_mono_strong pre stake_sdrop)
      moreover have \<open>epath suf\<close>
        using \<open>epath steps\<close> epath_sdrop ori by blast
      then obtain B qs r' where
        qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close>
        \<open>shd (stl suf) = ((B, qs), r')\<close>
        using suf epath_effect unfolding pseq_def ptms_def
        by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)

      moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
        using \<open>epath suf\<close> epath_never_branchDone by blast
      moreover have \<open>t \<in> set (ptms (shd suf))\<close>
        using above k by (meson le_add2 less_add_one order_le_less_trans)
      ultimately have \<open>Neg (sub 0 t p) \<in> set qs\<close>
        using parts_in_effect[where A=\<open>ptms (shd suf)\<close>] unfolding parts_def by fastforce
      then show ?thesis
        using k pseq_in_tree_fms qs(2)
        by (metis Pair_inject in_mono prod.collapse pseq_def shd_sset sset_sdrop stl_sset)
    qed
  qed 
next
  fix p
  assume \<open>Uni p \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = DeltaUni
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast
  ultimately have \<open>sub 0 (Fun (new_name (ptms (shd suf))) []) p \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce
  then have *: \<open>sub 0 (Fun (new_name (ptms (shd suf))) []) p \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
  let ?t = \<open>Fun (new_name (ptms (shd suf))) []\<close>
  show \<open>\<exists>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
  proof (cases \<open>?t \<in> set (subtermFm (sub 0 ?t p))\<close>)
    case True
    then have \<open>?t \<in> terms ?H\<close>
      unfolding terms_def using * by (metis UN_I empty_iff)
    then show ?thesis
      using * by blast
  next
    case False
    then have \<open>sub 0 t p = sub 0 ?t p\<close> for t
      using sub_const_transfer by metis
    moreover have \<open>terms ?H \<noteq> {}\<close>
      unfolding terms_def by simp
    then have \<open>\<exists>t. t \<in> terms ?H\<close>
      by blast
    ultimately show ?thesis
      using * by metis
  qed
next
  fix p
  assume \<open>Neg (Exi p) \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = DeltaExi
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast
  ultimately have \<open>Neg (sub 0 (Fun (new_name (ptms (shd suf))) []) p) \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce
  then have *: \<open>Neg (sub 0 (Fun (new_name (ptms (shd suf))) []) p) \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
  let ?t = \<open>Fun (new_name (ptms (shd suf))) []\<close>
  show \<open>\<exists>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
  proof (cases \<open>?t \<in> set (subtermFm (Neg (sub 0 ?t p)))\<close>)
    case True
    then have \<open>?t \<in> terms ?H\<close>
      unfolding terms_def using * by (metis UN_I empty_iff)
    then show ?thesis
      using * by blast
  next
    case False
    then have \<open>Neg (sub 0 t p) = Neg (sub 0 ?t p)\<close> for t
      using sub_const_transfer by (metis subtermFm.simps(7))
    moreover have \<open>terms ?H \<noteq> {}\<close>
      unfolding terms_def by simp
    then have \<open>\<exists>t. t \<in> terms ?H\<close>
      by blast
    ultimately show ?thesis
      using * by metis
  qed
next
  fix p
  assume \<open>Neg (Neg p) \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = NegNeg
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B qs r' where
    qs: \<open>(B, qs) |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, qs), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>p \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
qed

end
