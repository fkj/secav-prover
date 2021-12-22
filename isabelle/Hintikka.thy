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
  - Preservation under other rules
  - Preservation until the first occurrence
      (cut down an ev P xs into xs = pre @ suf s.t. no element in pre satisfies P and shd suf does) 
  - I never encounter both a predicate and its negation
      (should be a simple proof by contradiction using fairness and the effect of Basic)
  + Effect of the (first) occurrence

  Notes:
  epath throws away too much information to prove anything about which rule is next
*)
(* TODO: rules should be in a nicer order in the datatype... *)

definition affects :: \<open>rule \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>affects r p \<equiv> case (r, p) of
    (Basic, _) \<Rightarrow> True
  | (AlphaDis, Dis _ _) \<Rightarrow> True
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
  assumes \<open>\<not> affects r p\<close> \<open>qs \<in> set (parts A b r p)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms unfolding parts_def affects_def
  by (cases r; cases p rule: Neg_exhaust) simp_all

lemma parts_non_empty: \<open>r \<noteq> Basic \<Longrightarrow> parts A b r p \<noteq> []\<close>
  unfolding parts_def by (cases r; cases p rule: Neg_exhaust) simp_all

lemma Basic_affects_all: \<open>\<not> affects r p \<Longrightarrow> r \<noteq> Basic\<close>
  unfolding affects_def by auto

lemma split_maps:
  assumes \<open>A \<noteq> []\<close> \<open>xs \<in> set (List.maps (\<lambda>tail. map (\<lambda>ps. ps @ tail) A) B)\<close>
  shows \<open>\<exists>a rest. a \<in> set A \<and> xs = a @ rest\<close>
  using assms by (induct B) (auto simp: maps_simps)

thm effect'_def

lemma
  assumes \<open>r \<noteq> Basic\<close>
  shows \<open>set (effect' A r (p # ps)) = {qs @ ih |qs ih.
    qs \<in> set (parts A (branchDone (p # ps)) r p) \<and> ih \<in> set (effect' A r (p # ps))}\<close>
  using assms sorry

lemma
  assumes \<open>r \<noteq> Basic\<close> \<open>qs \<in> set (effect' A r ps)\<close> \<open>qs' \<in> set (effect' A r (p # ps))\<close>
  shows \<open>set qs \<subseteq> set qs'\<close>
  using assms
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
    apply simp
    sorry
qed

lemma
  assumes \<open>p \<in> set ps\<close> \<open>\<not> affects r p\<close> \<open>qs \<in> set (effect' A r ps)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms
proof (induct ps arbitrary: qs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  show ?case
  proof (cases \<open>p = a\<close>)
    case True
    let ?pss = \<open>parts A (branchDone (a # ps)) r a\<close>
    have \<open>\<forall>ps \<in> set ?pss. p \<in> set ps\<close>
      using Cons True parts_preserves_unaffected by blast
    moreover have \<open>\<exists>ps rest. ps \<in> set ?pss \<and> qs = ps @ rest\<close>
      using Cons(3, 4) parts_non_empty Basic_affects_all split_maps[where xs=qs] by simp
    ultimately show ?thesis
      by auto
  next
    case False
    then have \<open>p \<in> set qs'\<close> if \<open>qs' \<in> set (effect' A r ps)\<close> for qs'
      using Cons that by simp
    moreover have \<open>set qs' \<subseteq> set qs\<close> if \<open>qs' \<in> set (effect' A r ps)\<close> for qs'
      using Cons that
      apply simp
      sorry
    ultimately show ?thesis
      by (metis Cons.prems(3) effect'.simps(2) list.set_sel(1) maps_simps(2) subsetD)
  qed
qed


(************** rest of the stuff *********************)

(* TODO: not usable I think, as an epath loses information about the order of rules *)
definition rule_dist :: \<open>rule \<Rightarrow> rule \<Rightarrow> nat\<close> where
  \<open>rule_dist r1 r2 = nat \<bar>int (rule_index r1) - int (rule_index r2)\<bar>\<close>

lemma rule_dist_id[simp]: \<open>rule_dist r r = 0\<close>
  unfolding rule_dist_def by simp

lemma rule_dist_rule:
  \<open>\<lbrakk>epath steps; Saturated steps\<rbrakk> \<Longrightarrow> prule (steps !! (n + rule_dist (prule (steps !! n)) r)) = r\<close>
  sorry

lemma eff_step:
  \<open>epath steps \<Longrightarrow> eff (prule (steps !! n)) (pseq (steps !! n)) ss \<Longrightarrow> pseq (steps !! (n + 1)) |\<in>| ss\<close>
  sorry

subsection \<open>Facts about the NegNeg rule\<close>
text \<open>Similar lemmas are needed about all of the other rules.
I don't see how to generalize the lemmas since their statements vary quite a lot...\<close>

lemma p_in_NegNeg_branches:
  fixes steps n
  defines \<open>sequent \<equiv> pseq (steps !! (n + rule_dist (prule (steps !! n)) NegNeg))\<close>
  assumes
    \<open>epath steps\<close>
    \<open>Saturated steps\<close>
    \<open>eff NegNeg sequent ss\<close>
    \<open>Neg (Neg p) \<in> set sequent\<close>
    \<open>x |\<in>| ss\<close>
  shows \<open>member p x\<close>
  using assms
(* this is true because Neg (Neg p) is in the sequent and we are applying the NegNeg rule,
        which means the parts function will return a list of lists containing only a single list
        containing p when NegNeg is applied to Neg (Neg p).
       this list is then added to the sequent of step n + ?d, which means that p is in the only branch in ss.
       actually proving this probably needs some sublemmas about the parts and effect functions... *)
  sorry

lemma steps_preserve_NegNeg:
  assumes \<open>epath steps\<close> \<open>Saturated steps\<close> \<open>Neg (Neg p) \<in> set (pseq (steps !! n))\<close> \<open>rule_dist (prule (steps !! n)) NegNeg = k\<close> \<open>m \<le> k\<close>
  shows \<open>Neg (Neg p) \<in> set (pseq (steps !! (n + m)))\<close>
  using assms
  sorry

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

lemma escape_path_Hintikka:
  fixes steps
  assumes \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>Hintikka (tree_fms steps)\<close> (is \<open>Hintikka ?H\<close>)
proof
  fix n ts
  assume pre: \<open>Pre n ts \<in> tree_fms steps\<close>
  show \<open>Neg (Pre n ts) \<notin> tree_fms steps\<close>
  proof
    assume \<open>Neg (Pre n ts) \<in> tree_fms steps\<close>
    then obtain m where *: \<open>Pre n ts \<in> set (pseq (steps !! m))\<close> \<open>Neg (Pre n ts) \<in> set (pseq (steps !! m))\<close>
      using tree_fms_in_pseq pre sorry
    let ?r = \<open>prule (steps !! m)\<close>
    let ?d = \<open>rule_dist ?r Basic\<close>
    have \<open>prule (steps !! (m + ?d)) = Basic\<close>
      by (simp add: rule_dist_rule assms)
    moreover obtain ss where **: \<open>eff Basic (pseq (steps !! (m + ?d))) ss\<close>
      by (simp add: eff_def effect_def)
    moreover have \<open>Pre n ts \<in> set (pseq (steps !! (m + ?d)))\<close> \<open>Neg (Pre n ts) \<in> set (pseq (steps !! (m + ?d)))\<close>
      using * assms sorry
    then have \<open>branchDone (pseq (steps !! (m + ?d)))\<close>
      sorry
    then have \<open>ss = {||}\<close>
      sorry
    ultimately show False
      using assms eff_step ex_fin_conv
      by metis
  qed
next
  fix p q
  assume \<open>Dis p q \<in> ?H\<close>
  show \<open>p \<in> ?H \<and> q \<in> ?H\<close>
    sorry
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close>
  show \<open>Neg p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
    sorry
next
  fix p q
  assume \<open>Neg (Con p q) \<in> tree_fms steps\<close>
  then obtain n where *: \<open>Neg (Con p q) \<in> set (pseq (steps !! n))\<close>
    using tree_fms_in_pseq by auto
  let ?r = \<open>prule (steps !! n)\<close>
  let ?d = \<open>rule_dist ?r AlphaCon\<close>
  have \<open>prule (steps !! (n + ?d)) = AlphaCon\<close>
    by (simp add: rule_dist_rule assms)
  moreover obtain ss where **: \<open>eff AlphaCon (pseq (steps !! (n + ?d))) ss\<close>
    by (simp add: eff_def effect_def)
  ultimately have \<open>pseq (steps !! (n + ?d + 1)) |\<in>| ss\<close>
    using eff_step assms by simp
  moreover have \<open>Neg (Con p q) \<in> (set (pseq (steps !! (n + ?d))))\<close>
    using * assms sorry
  then have \<open>\<forall>x. x |\<in>| ss \<longrightarrow> member (Neg p) x \<and> member (Neg q) x\<close>
    using ** assms sorry
  ultimately have \<open>Neg p \<in> set (pseq (steps !! (n + ?d + 1)))\<close> \<open>Neg q \<in> set (pseq (steps !! (n + ?d + 1)))\<close>
    by blast+
  then show \<open>Neg p \<in> tree_fms steps \<and> Neg q \<in> tree_fms steps\<close>
    using pseq_in_tree_fms snth_sset by blast
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
  then obtain n where *: \<open>Neg (Dis p q) \<in> set (pseq (steps !! n))\<close>
    using tree_fms_in_pseq by auto
  let ?r = \<open>prule (steps !! n)\<close>
  let ?d = \<open>rule_dist ?r BetaDis\<close>
  have \<open>prule (steps !! (n + ?d)) = BetaDis\<close>
    by (simp add: rule_dist_rule assms)
  moreover obtain ss where **: \<open>eff BetaDis (pseq (steps !! (n + ?d))) ss\<close>
    by (simp add: eff_def effect_def)
  ultimately have ****: \<open>pseq (steps !! (n + ?d + 1)) |\<in>| ss\<close>
    using eff_step assms by simp
  moreover have \<open>Neg (Dis p q) \<in> (set (pseq (steps !! (n + ?d))))\<close>
    using * assms sorry
  then have ***: \<open>\<forall>x. x |\<in>| ss \<longrightarrow> member (Neg p) x \<or> member (Neg q) x\<close>
    using ** assms sorry
  ultimately show \<open>Neg p \<in> tree_fms steps \<or> Neg q \<in> tree_fms steps\<close>
    using pseq_in_tree_fms snth_sset
  proof (cases \<open>member (Neg p) (pseq (steps !! (n + ?d + 1)))\<close>)
    case True
    then have \<open>Neg p \<in> set (pseq (steps !! (n + ?d + 1)))\<close>
      by simp
    then show ?thesis
      using pseq_in_tree_fms snth_sset by blast
  next
    case False
    then have \<open>Neg q \<in> set (pseq (steps !! (n + ?d + 1)))\<close>
      using *** **** by auto
    then show ?thesis
      using pseq_in_tree_fms snth_sset by blast
  qed
next
  fix p
  assume \<open>Exi p \<in> tree_fms steps\<close>
  then obtain n where *: \<open>Exi p \<in> set (pseq (steps !! n))\<close>
    using tree_fms_in_pseq by auto
  let ?r = \<open>prule (steps !! n)\<close>
  let ?d = \<open>rule_dist ?r DeltaExi\<close>
  have \<open>prule (steps !! (n + ?d)) = DeltaExi\<close>
    by (simp add: rule_dist_rule assms)
  moreover obtain ss where **: \<open>eff DeltaExi (pseq (steps !! (n + ?d))) ss\<close>
    by (simp add: eff_def effect_def)
  ultimately have \<open>pseq (steps !! (n + ?d + 1)) |\<in>| ss\<close>
    using eff_step assms by simp
  moreover have \<open>Exi p \<in> set (pseq (steps !! (n + ?d)))\<close>
    using assms * sorry
  then have \<open>\<forall>x. x |\<in>| ss \<longrightarrow> (\<forall>t \<in> terms (tree_fms steps). member (sub 0 t p) x)\<close>
    using ** assms sorry
  ultimately have \<open>\<forall>t \<in> terms (tree_fms steps). sub 0 t p \<in> set (pseq (steps !! (n + ?d + 1)))\<close>
    by blast
  then show \<open>\<forall>t \<in> terms (tree_fms steps). sub 0 t p \<in> tree_fms steps\<close>
    using pseq_in_tree_fms snth_sset by blast
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
  then obtain n where *: \<open>Neg (Neg p) \<in> set (pseq (steps !! n))\<close>
    using tree_fms_in_pseq by auto
  let ?r = \<open>prule (steps !! n)\<close>
  let ?d = \<open>rule_dist ?r NegNeg\<close>
  have \<open>prule (steps !! (n + ?d)) = NegNeg\<close>
    by (simp add: rule_dist_rule assms)
  moreover obtain ss where **: \<open>eff NegNeg (pseq (steps !! (n + ?d))) ss\<close>
    by (simp add: eff_def effect_def)
  ultimately have \<open>pseq (steps !! (n + ?d + 1)) |\<in>| ss\<close>
    using eff_step assms by simp
  moreover have \<open>Neg (Neg p) \<in> set (pseq (steps !! (n + ?d)))\<close>
    by (simp add: assms * steps_preserve_NegNeg)
  then have \<open>\<forall>x. x |\<in>| ss \<longrightarrow> member p x\<close>
    using ** assms p_in_NegNeg_branches by blast
  ultimately have \<open>p \<in> set (pseq (steps !! (n + ?d + 1)))\<close>
    by blast
  then show \<open>p \<in> tree_fms steps\<close>
    using pseq_in_tree_fms snth_sset by blast
qed

end