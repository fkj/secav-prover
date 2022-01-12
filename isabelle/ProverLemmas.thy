theory ProverLemmas imports Prover begin

text \<open>Fairness\<close>

primrec next_rule :: \<open>rule \<Rightarrow> rule\<close> where
  \<open>next_rule NegNeg = AlphaImp\<close>
| \<open>next_rule AlphaImp = AlphaDis\<close>
| \<open>next_rule AlphaDis = AlphaCon\<close>
| \<open>next_rule AlphaCon = DeltaExi\<close>
| \<open>next_rule DeltaExi = DeltaUni\<close>
| \<open>next_rule DeltaUni = BetaImp\<close>
| \<open>next_rule BetaImp = BetaDis\<close>
| \<open>next_rule BetaDis = BetaCon\<close>
| \<open>next_rule BetaCon = GammaExi\<close>
| \<open>next_rule GammaExi = GammaUni\<close>
| \<open>next_rule GammaUni = NegNeg\<close>

primrec rule_index :: \<open>rule \<Rightarrow> nat\<close> where
  \<open>rule_index NegNeg = 0\<close>
| \<open>rule_index AlphaImp = 1\<close>
| \<open>rule_index AlphaDis = 2\<close>
| \<open>rule_index AlphaCon = 3\<close>
| \<open>rule_index DeltaExi = 4\<close>
| \<open>rule_index DeltaUni = 5\<close>
| \<open>rule_index BetaImp = 6\<close>
| \<open>rule_index BetaDis = 7\<close>
| \<open>rule_index BetaCon = 8\<close>
| \<open>rule_index GammaExi = 9\<close>
| \<open>rule_index GammaUni = 10\<close>

lemma distinct_rulesList: \<open>distinct rulesList\<close>
  unfolding rulesList_def by simp

lemma cycle_nth: \<open>xs \<noteq> [] \<Longrightarrow> cycle xs !! n = xs ! (n mod length xs)\<close>
  by (metis cycle.sel(1) hd_rotate_conv_nth rotate_conv_mod sdrop_cycle sdrop_simps(1))

lemma nth_rule_index: \<open>rulesList ! (rule_index r) = r\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma rule_index_bnd: \<open>rule_index r < length rulesList\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma unique_rule_index:
  assumes \<open>n < length rulesList\<close> \<open>rulesList ! n = r\<close>
  shows \<open>n = rule_index r\<close>
  using assms nth_rule_index distinct_rulesList rule_index_bnd nth_eq_iff_index_eq by metis

lemma rule_index_mod:
  assumes \<open>rules !! n = r\<close>
  shows \<open>n mod length rulesList = rule_index r\<close>
proof -
  have *: \<open>rulesList ! (n mod length rulesList) = r\<close>
    using assms cycle_nth unfolding rules_def rulesList_def by (metis list.distinct(1))
  then show ?thesis
    using distinct_rulesList * unique_rule_index
    by (cases r) (metis length_greater_0_conv list.discI rulesList_def
        unique_euclidean_semiring_numeral_class.pos_mod_bound)+
qed

lemma mod_hit:
  fixes k :: nat
  assumes \<open>0 < k\<close>
  shows \<open>\<forall>i < k. \<exists>n > m. n mod k = i\<close>
proof safe
  fix i
  let ?n = \<open>(1 + m) * k + i\<close>
  assume \<open>i < k\<close>
  then have \<open>?n mod k = i\<close>
    by (metis mod_less mod_mult_self3)
  moreover have \<open>?n > m\<close>
    using assms
    by (metis One_nat_def Suc_eq_plus1_left Suc_leI add.commute add_lessD1 less_add_one
        mult.right_neutral nat_mult_less_cancel1 order_le_less trans_less_add1 zero_less_one)
  ultimately show \<open>\<exists>n > m. n mod k = i\<close>
    by fast
qed

lemma mod_suff:
  assumes \<open>\<forall>(n :: nat) > m. P (n mod k)\<close> \<open>0 < k\<close>
  shows \<open>\<forall>i < k. P i\<close>
  using assms mod_hit by blast

lemma rules_repeat: \<open>\<exists>n > m. rules !! n = r\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<exists>n > m. rules !! n = r)\<close>
  then have \<open>\<not> (\<exists>n > m. n mod length rulesList = rule_index r)\<close>
    using rule_index_mod nth_rule_index by metis
  then have \<open>\<forall>n > m. n mod length rulesList \<noteq> rule_index r\<close>
    by blast
  moreover have \<open>length rulesList > 0\<close>
    unfolding rulesList_def by simp
  ultimately have \<open>\<forall>k < length rulesList. k \<noteq> rule_index r\<close>
    using mod_suff[where P=\<open>\<lambda>a. a \<noteq> rule_index r\<close>] by blast
  then show False
    using rule_index_bnd by blast
qed

lemma rules_repeat_sdrop: \<open>\<exists>n. (sdrop k rules) !! n = r\<close>
  using rules_repeat by (metis less_imp_add_positive sdrop_snth)

lemma fair_rules: \<open>fair rules\<close>
proof -
  { fix r assume \<open>r \<in> R\<close>
    then obtain m where r: \<open>r = rules !! m\<close> unfolding sset_range by blast
    { fix n :: nat and rs let ?rules = \<open>\<lambda>n. sdrop n rules\<close>
      assume \<open>n > 0\<close>
      hence \<open>alw (ev (holds ((=) r))) (rs @- ?rules n)\<close>
      proof (coinduction arbitrary: n rs)
        case alw
        show ?case
        proof (rule exI[of _ \<open>rs @- ?rules n\<close>], safe)
          show \<open>\<exists>n' rs'. stl (rs @- ?rules n) = rs' @- ?rules n' \<and> n' > 0\<close>
          proof (cases rs)
            case Nil thus ?thesis unfolding alw
              by (metis sdrop_simps(2) shift.simps(1) zero_less_Suc)
          qed (auto simp: alw intro: exI[of _ n])
        next
          have \<open>ev (holds ((=) r)) (sdrop n rules)\<close>
            unfolding ev_holds_sset using rules_repeat_sdrop by (metis snth_sset)
          then show \<open>ev (holds ((=) r)) (rs @- sdrop n rules)\<close>
            unfolding ev_holds_sset by simp
        qed
      qed
    }
  }
  thus \<open>fair rules\<close> unfolding fair_def
    by (metis (full_types) alw_iff_sdrop ev_holds_sset neq0_conv order_refl sdrop.simps(1)
        stake_sdrop)
qed

text \<open>Substitution\<close>

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

lemma parts_exhaust
  [case_names AlphaDis AlphaImp AlphaCon BetaDis BetaImp BetaCon
    DeltaUni DeltaExi NegNeg GammaExi GammaUni Other]:
  assumes
    \<open>\<And>p q. r = AlphaDis \<Longrightarrow> x = Dis p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = AlphaImp \<Longrightarrow> x = Imp p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = AlphaCon \<Longrightarrow> x = Neg (Con p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaDis \<Longrightarrow> x = Neg (Dis p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaImp \<Longrightarrow> x = Neg (Imp p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaCon \<Longrightarrow> x = Con p q \<Longrightarrow> P\<close>
    \<open>\<And>p. r = DeltaUni \<Longrightarrow> x = Uni p \<Longrightarrow> P\<close>
    \<open>\<And>p. r = DeltaExi \<Longrightarrow> x = Neg (Exi p) \<Longrightarrow> P\<close>
    \<open>\<And>p. r = NegNeg \<Longrightarrow> x = Neg (Neg p) \<Longrightarrow> P\<close>
    \<open>\<And>p. r = GammaExi \<Longrightarrow> x = Exi p \<Longrightarrow> P\<close>
    \<open>\<And>p. r = GammaUni \<Longrightarrow> x = Neg (Uni p) \<Longrightarrow> P\<close>
    \<open>\<forall>A. parts A r x = [[x]] \<Longrightarrow> P\<close>
  shows P
  using assms
proof (cases r)
  case BetaCon
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (4 p q)
    then show ?thesis
      using BetaCon assms by blast
  qed (simp_all add: parts_def)
next
  case BetaImp
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (8 p q)
    then show ?thesis
      using BetaImp assms by blast
  qed (simp_all add: parts_def)
next
  case DeltaUni
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (6 p)
    then show ?thesis
      using DeltaUni assms by fast
  qed (simp_all add: parts_def)
next
  case DeltaExi
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (11 p)
    then show ?thesis
      using DeltaExi assms by fast
  qed (simp_all add: parts_def)
next
  case NegNeg
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (13 p)
    then show ?thesis
      using NegNeg assms by fast
  qed (simp_all add: parts_def)
next
  case GammaExi
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (5 p)
    then show ?thesis
      using GammaExi assms by fast
  qed (simp_all add: parts_def)
next
  case GammaUni
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (12 p)
    then show ?thesis
      using GammaUni assms by fast
  qed (simp_all add: parts_def)
qed (cases x rule: Neg_exhaust, simp_all add: parts_def)+

lemma parts_preserves_unaffected:
  assumes \<open>\<not> affects r p\<close> \<open>qs \<in> set (parts A r p)\<close>
  shows \<open>p \<in> set qs\<close>
  using assms unfolding affects_def
  by (cases r p rule: parts_exhaust) (simp_all add: parts_def)

lemma parts_not_Nil: \<open>parts A r p \<noteq> []\<close>
  by (cases r p rule: parts_exhaust) (simp_all add: parts_def)

lemma parts_all_inhabited: \<open>[] \<notin> set (parts A r p)\<close>
  by (cases r p rule: parts_exhaust) (simp_all add: parts_def)

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

end