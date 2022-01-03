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

definition pseq :: \<open>sequent \<times> rule \<Rightarrow> sequent\<close> where
  \<open>pseq x = fst x\<close>

definition phd :: \<open>sequent \<times> rule \<Rightarrow> fm\<close> where
  \<open>phd x = hd (fst x)\<close>

lemma phd_in_pseq: \<open>pseq s \<noteq> [] \<Longrightarrow> phd s = p \<Longrightarrow> p \<in> set (pseq s)\<close>
  by (cases, cases, cases, auto simp add: phd_def pseq_def)

definition ptl :: \<open>sequent \<times> rule \<Rightarrow> fm list\<close> where
  \<open>ptl x = tl (fst x)\<close>

lemma hd_ptl_in_pseq: \<open>tl (pseq s) \<noteq> [] \<Longrightarrow> hd (ptl s) = p \<Longrightarrow> p \<in> set (pseq s)\<close>
  by (cases s, cases \<open>fst s\<close>, auto simp add: pseq_def ptl_def)

lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

text \<open>Transformation of formulas on an epath\<close>

lemma epath_eff:
  assumes \<open>epath steps\<close> \<open>eff (snd (shd steps)) (fst (shd steps)) A\<close>
  shows \<open>fst (shd (stl steps)) |\<in>| A\<close>
  using assms by (metis (mono_tags, lifting) RuleSystem_Defs.epath.simps eff_def)

lemma epath_effect:
  assumes \<open>epath steps\<close> \<open>shd steps = (ps, r)\<close>
  shows \<open>\<exists>qs r'. qs |\<in>| effect r ps \<and> shd (stl steps) = (qs, r')\<close>
  using assms epath_eff by (metis (mono_tags, lifting) eff_def fst_conv prod.collapse snd_conv)

lemma epath_effect_next_step:
  assumes \<open>epath steps\<close> \<open>steps !! n = (ps, r)\<close>
  shows \<open>\<exists>qs r'. qs |\<in>| effect r ps \<and> steps !! (n + 1) = (qs, r')\<close>
  using assms epath_effect
  by (metis One_nat_def add.right_neutral add_Suc_right epath_sdrop sdrop_simps(1) sdrop_simps(2))

(* I want to get
  - Preservation until the first occurrence
      (cut down an ev P xs into xs = pre @ suf s.t. no element in pre satisfies P and shd suf does) 
  - I never encounter both a predicate and its negation
      (should be a simple proof by contradiction using fairness and the effect of Basic)
  + Preservation under other rules
  + Effect of the (first) occurrence

  Notes:
  epath throws away too much information to prove anything about which rule is next
*)
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
  | (GammaExi, Exi _) \<Rightarrow> True
  | (GammaUni, Neg (Uni _)) \<Rightarrow> True
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
  assumes \<open>p \<in> set ps\<close> \<open>\<not> affects r p\<close> \<open>qs |\<in>| effect r ps\<close>
  shows \<open>p \<in> set qs\<close>
  using assms effect'_preserves_unaffected by (metis fempty_iff effect_def fset_of_list_elem)

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
  assumes \<open>p \<in> set ps\<close> \<open>qs |\<in>| effect r ps\<close> \<open>\<not> branchDone ps\<close>
  shows \<open>\<exists>xs \<in> set (parts (subterms ps) r p). set xs \<subseteq> set qs\<close>
  using assms parts_in_effect' by (simp add: effect_def fset_of_list_elem)

corollary \<open>\<not> branchDone ps \<Longrightarrow> Neg (Neg p) \<in> set ps \<Longrightarrow> qs |\<in>| effect NegNeg ps \<Longrightarrow> p \<in> set qs\<close>
  using parts_in_effect unfolding parts_def by fastforce
   
corollary \<open>\<not> branchDone ps \<Longrightarrow> Neg (Uni p) \<in> set ps \<Longrightarrow> qs |\<in>| effect GammaUni ps \<Longrightarrow>
    set (map (\<lambda>t. Neg (subst p t 0)) (subterms ps)) \<subseteq> set qs\<close>
  using parts_in_effect unfolding parts_def by fastforce

text \<open>Preservation on epath\<close>

lemma ev_prefix:
  assumes \<open>ev (holds P) xs\<close>
  shows \<open>\<exists>pre suf. list_all (not P) pre \<and> holds P suf \<and> xs = pre @- suf\<close>
  using assms
proof (induct xs)
  case (base xs)
  then show ?case
    by (metis list_all_simps(2) shift.simps(1))
next
  case (step xs)
  then show ?case
    by (metis holds.elims(1) list.pred_inject(2) list_all_simps(2) shift.simps(1-2) stream.collapse)
qed

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
      by (metis list.pred_inject(2) list.sel(1) shift.simps(2) shift_simps(1) stream.sel(2))
  qed
qed

section \<open>Proving that the formulas on an escape path form a Hintikka set\<close>

definition \<open>tree_fms steps \<equiv> \<Union>fms \<in> sset steps. set (fst fms)\<close>

lemma pseq_in_tree_fms: \<open>\<lbrakk>x \<in> sset steps; p \<in> set (pseq x)\<rbrakk> \<Longrightarrow> p \<in> tree_fms steps\<close>
  using pseq_def tree_fms_def by fastforce

lemma tree_fms_in_pseq: \<open>p \<in> tree_fms steps \<Longrightarrow> \<exists>n. p \<in> set (pseq (steps !! n))\<close>
  unfolding pseq_def tree_fms_def
proof (simp)
  assume \<open>\<exists>x \<in> sset steps. p \<in> set (fst x)\<close>
  then obtain x where \<open>x \<in> sset steps\<close> \<open>p \<in> set (fst x)\<close>
    by blast
  then show \<open>\<exists>n. p \<in> set (fst (steps !! n))\<close>
    using sset_range[of steps] by auto
qed

lemma sset_sdrop: \<open>sset (sdrop n s) \<subseteq> sset s\<close>
  by (induct n arbitrary: s)
    (simp, metis dual_order.trans equalityE insert_subset sdrop.simps(2) stream.collapse stream.simps(8))

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
    unfolding saturated_def using always_enabledAtStep by auto
qed

abbreviation \<open>is_rule r step \<equiv> snd step = r\<close>

lemma list_prod_nil: \<open>list_prod [] ts = []\<close>
  by (induct ts) simp_all

(*
  I don't think we should have a Basic rule as \<open>effect\<close> does not preserve \<open>branchDone\<close>:

  Neg (Dis p q), Dis p q
  === AlphaDis ==>
  Neg (Dis p q), p, q

  This makes it tricky to show that we never hit \<open>branchDone\<close> as I do below.
  It's easier and more efficient to just drop sequents that are axioms.
*)

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
  have \<open>\<forall>r. effect r (pseq (shd ?suf)) = {||}\<close>
    unfolding effect_def using n by simp
  moreover have \<open>epath ?suf\<close>
    using \<open>epath steps\<close> epath_sdrop by blast
  then have \<open>\<forall>r. \<exists>qs r'. qs |\<in>| effect r (pseq (shd ?suf)) \<and> shd (stl ?suf) = (qs, r')\<close>
    using epath_effect by (metis calculation prod.exhaust_sel pseq_def)
  ultimately show False
    by blast
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>p \<in> set qs\<close> \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>p \<in> ?H \<and> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>Neg p \<in> set qs\<close> \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>Neg p \<in> set qs\<close> \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>p \<in> set qs\<close> | \<open>q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>p \<in> set qs\<close> | \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately consider \<open>Neg p \<in> set qs\<close> | \<open>Neg q \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>Neg p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
next
  fix p
  assume \<open>Exi p \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = GammaExi
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>\<forall>t \<in> set (subterms (pseq (shd suf))). subst p t 0 \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>\<forall>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    sorry (* TODO: I need that suf contains all terms on the branch *)
next
  fix p
  assume \<open>Neg (Uni p) \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = GammaUni
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>\<forall>t \<in> set (subterms (pseq (shd suf))). Neg (sub 0 t p) \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>\<forall>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    sorry (* TODO: I need that suf contains all terms on the branch *)
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast
  ultimately have \<open>sub 0 (Fun (new_name (subterms (pseq (shd suf)))) []) p \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce
  then have *: \<open>sub 0 (Fun (new_name (subterms (pseq (shd suf)))) []) p \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
  moreover have \<open>Fun (new_name (subterms (pseq (shd suf)))) [] \<in> terms ?H\<close>
    sorry (* TODO: does this hold? *)
  ultimately show \<open>\<exists>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
    by blast
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast
  ultimately have \<open>Neg (sub 0 (Fun (new_name (subterms (pseq (shd suf)))) []) p) \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce
  then have *: \<open>Neg (sub 0 (Fun (new_name (subterms (pseq (shd suf)))) []) p) \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
  moreover have \<open>Fun (new_name (subterms (pseq (shd suf)))) [] \<in> terms ?H\<close>
    sorry (* TODO: does this hold? *)
  ultimately show \<open>\<exists>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
    by blast
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
  then obtain qs r' where qs: \<open>qs |\<in>| effect ?r (pseq (shd suf))\<close> \<open>shd (stl suf) = (qs, r')\<close>
    using suf epath_effect by (metis (mono_tags, lifting) holds.elims(2) prod.collapse pseq_def)
  moreover have \<open>holds (not (branchDone o pseq)) suf\<close>
    using \<open>epath suf\<close> epath_never_branchDone by blast

  ultimately have \<open>p \<in> set qs\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H\<close>
    using qs(2) ori pseq_in_tree_fms
    by (metis Un_iff fst_conv pseq_def shd_sset sset_sdrop sset_shift stl_sset subset_eq)
qed

end