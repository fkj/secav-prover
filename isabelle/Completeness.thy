theory Completeness
  imports Prover "HOL-Library.BNF_Corec"
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
    GammaExi: \<open>Exi p \<in> H \<Longrightarrow> \<forall>t \<in> \<Union>f \<in> H. set (subtermFm 0 f). sub 0 t p \<in> H\<close> and
    GammaUni: \<open>Neg (Uni p) \<in> H \<Longrightarrow> \<forall>t \<in> \<Union>f \<in> H. set (subtermFm 0 f). Neg (sub 0 t p) \<in> H\<close> and
    DeltaUni: \<open>Uni p \<in> H \<Longrightarrow> \<exists>t. sub 0 t p \<in> H\<close> and
    DeltaExi: \<open>Neg (Exi p) \<in> H \<Longrightarrow> \<exists>t. Neg (sub 0 t p) \<in> H\<close> and
    Neg: \<open>Neg (Neg p) \<in> H \<Longrightarrow> p \<in> H\<close>

lemma exactly_one_enabled: \<open>\<forall>sequent phase. \<exists>! r. enabled r (sequent, phase)\<close>
  unfolding enabled_def Ex1_def
  using at_least_one_enabled enabled_unique
  by (metis RuleSystem_Defs.enabled_def member_remove remove_def rules_def) 

lemma woop:
  assumes \<open>Dis p q \<in> tree_fms steps\<close>
  shows \<open>\<exists>n. s = shd (sdrop n steps) \<and> (\<exists>z. s = ((Dis p q # z, PABD), AlphaDis))\<close>
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
  assume dis: \<open>Dis p q \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
  proof -
    obtain s z n where \<open>s = ((Dis p q # z, PABD), AlphaDis)\<close> and \<open>s = shd (sdrop n steps)\<close>
      using dis woop by meson
(* we need that the nxt node contains the decomposed formula as soon as it is enabled *) 
    then have \<open>takenAtStep AlphaDis (shd (sdrop (Suc n) steps))\<close>
      sorry
    then have \<open>\<exists>r. shd (sdrop (Suc n) steps) = ((p # q # z, PBasic), r)\<close>
      sorry
    show \<open>p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
      sorry
  qed
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close>
  show \<open>Neg p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
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
  show \<open>\<forall>t\<in>\<Union>f \<in> tree_fms steps. set (subtermFm 0 f). sub 0 t p \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Uni p) \<in> tree_fms steps\<close>
  show \<open>\<forall>t\<in>\<Union>f \<in> tree_fms steps. set (subtermFm 0 f). Neg (sub 0 t p) \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Uni p \<in> tree_fms steps\<close>
  show \<open>\<exists>t. sub 0 t p \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Exi p) \<in> tree_fms steps\<close>
  show \<open>\<exists>t. Neg (sub 0 t p) \<in> tree_fms steps\<close>
    sorry
next
  fix p
  assume \<open>Neg (Neg p) \<in> tree_fms steps\<close>
  show \<open>p \<in> tree_fms steps\<close>
    sorry
qed

datatype htm = HFun nat \<open>htm list\<close>

fun tm_to_htm :: \<open>tm \<Rightarrow> htm\<close> where
  \<open>tm_to_htm (Var _) = undefined\<close>
| \<open>tm_to_htm (Fun n ts) = HFun n (map tm_to_htm ts)\<close>

fun htm_to_tm :: \<open>htm \<Rightarrow> tm\<close> where
  \<open>htm_to_tm (HFun n hts) = Fun n (map htm_to_tm hts)\<close>


lemma \<open>tm_to_htm (htm_to_tm t) = t\<close>
  sorry  

lemma
  assumes \<open>closedt t\<close>
  shows \<open>htm_to_tm (tm_to_htm t) = t\<close>
  sorry

abbreviation (input) \<open>sat S n ts \<equiv> Neg (Pre n ts) \<in> S\<close>

lemma semantics_id [simp]:
  \<open>semantics_term Var Fun t = t\<close>
  \<open>semantics_list Var Fun ts = ts\<close>
  by (induct t and ts rule: semantics_term.induct semantics_list.induct) simp_all

lemma size_sub [simp]: \<open>size (sub i t p) = size p\<close>
  by (induct p arbitrary: i t) auto

lemma
  assumes
    \<open>\<forall>e. \<forall>t \<in> {Fun i []} \<union> set (subtermFm 0 p). semantics e f g (sub 0 t p)\<close>
    \<open>i \<notin> params p\<close>
  shows \<open>semantics e f g (sub 0 t p)\<close>
proof (cases \<open>t \<in> set (subtermFm 0 p)\<close>)
  case True
  then show ?thesis
    using assms by blast
next
  case False
  let ?x = \<open>semantics_term e f t\<close>
  let ?y = \<open>f i []\<close>

  (* t = f(g(a)) *)

  have \<open>semantics (SeCaV.shift e 0 ?y) f g p\<close>
    using assms by simp
  then have \<open>\<forall>x. semantics (SeCaV.shift e 0 x) f g p\<close>
    using \<open>i \<notin> params p\<close> sorry
  then have \<open>semantics (SeCaV.shift e 0 ?x) f g p\<close>
    by simp
  then show ?thesis
    using subst_lemma by simp
qed

lemma hintikka_counter_model:
  assumes \<open>Hintikka S\<close>
  shows \<open>(p \<in> S \<longrightarrow> \<not> semantics Var Fun (sat S) p) \<and> (Neg p \<in> S \<longrightarrow> semantics Var Fun (sat S) p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  fix x
  assume wf: \<open>\<forall>q. (q, x) \<in> measure size \<longrightarrow>
      (q \<in> S \<longrightarrow> \<not> semantics Var Fun (sat S) q) \<and>
      (Neg q \<in> S \<longrightarrow> semantics Var Fun (sat S) q)\<close>

  show \<open>(x \<in> S \<longrightarrow> \<not> semantics Var Fun (sat S) x) \<and>
        (Neg x \<in> S \<longrightarrow> semantics Var Fun (sat S) x)\<close>
  proof (cases x)
    case (Pre n ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg (Pre n ts) \<notin> S\<close>
        using assms Pre Hintikka.Basic by blast
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using Pre by simp
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>sat S n ts\<close>
        using assms Pre Hintikka.Basic by blast
      then show \<open>semantics Var Fun (sat S) x\<close>
        using Pre by simp
    qed
  next
    case (Imp p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>q \<in> S\<close>
        using Imp assms Hintikka.AlphaImp by blast+
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using wf Imp by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S \<or> Neg q \<in> S\<close>
        using Imp assms Hintikka.BetaImp by blast
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Imp by fastforce
    qed
  next
    case (Dis p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S\<close> \<open>q \<in> S\<close>
        using Dis assms Hintikka.AlphaDis by blast+
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using wf Dis by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S \<or> Neg q \<in> S\<close>
        using Dis assms Hintikka.BetaDis by blast
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Dis by fastforce
    qed
  next
    case (Con p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S \<or> q \<in> S\<close>
        using Con assms Hintikka.BetaCon by blast
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using wf Con by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>Neg q \<in> S\<close>
        using Con assms Hintikka.AlphaCon by blast+
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Con by fastforce
    qed
  next
    case (Exi p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>\<forall>t \<in> \<Union>f \<in> S. set (subtermFm 0 f). sub 0 t p \<in> S\<close>
        using Exi assms Hintikka.GammaExi by blast
      then have \<open>\<forall>t \<in> \<Union>f \<in> S. set (subtermFm 0 f). \<not> semantics Var Fun (sat S) (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(12) in_measure lessI)
      (* NEW THOUGHTS: Need to restrict the model so that the universe only contains
            terms that occur in S.
            We cannot do this easily with the Isabelle logic.
            Maybe we can define a semantics a la FEval here:
              https://www.isa-afp.org/browser_info/current/AFP/Verified-Prover/Prover.html *)

      (* Assume formula is closed and be arbitrary over e *)    

      (* Need a lemma that proves that quantifying over Fun 0 [] and the subterms is enough
         to generalize to all terms *)

      (* e :: nat \<Rightarrow> {t :: tm. t \<in> \<Union>f \<in> H. set (subtermFm 0 f)}

          e S
         (f S) n ts : 'a

          datatype htm = HFun nat htm list | Other
          if Fun n ts \<in> S then HFun n ts else Other

          f :: filter


          Sig at t er en subterm af S.
          Så f t = t og det holder induktivt.

          Sig at t ikke er en subterm af S.
          Så f t = Fun 0 []
          Så skal vi vise \<not> semantics Var f (sat S) (sub 0 (Fun 0 []) p)
            Hvordan gør vi det?
       *)
      have \<open>\<forall>t. \<not> semantics Var Fun (sat S) (sub 0 t p)\<close>
        sorry
      then have \<open>\<forall>t. \<not> semantics (SeCaV.shift Var 0 t) Fun (sat S) p\<close>
        using subst_lemma by simp
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using Exi by simp
    next
      assume \<open>Neg x \<in> S\<close>
      then obtain t where \<open>Neg (sub 0 t p) \<in> S\<close>
        using Exi assms Hintikka.DeltaExi by blast
      then have \<open>semantics Var Fun (sat S) (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis Nat.add_0_right add_Suc_right fm.size(12) in_measure less_Suc_eq)
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Exi by fastforce
    qed
  next
    case (Uni p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then obtain t where \<open>sub 0 t p \<in> S\<close>
        using Uni assms Hintikka.DeltaUni by blast
      then have \<open>\<not> semantics Var Fun (sat S) (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis Nat.add_0_right add_Suc_right fm.size(13) in_measure less_Suc_eq)
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using Uni by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>\<forall>t \<in> \<Union>f \<in> S. set (subtermFm 0 f). Neg (sub 0 t p) \<in> S\<close>
        using Uni assms Hintikka.GammaUni by blast
      then have \<open>\<forall>t \<in> \<Union>f \<in> S. set (subtermFm 0 f). semantics Var Fun (sat S) (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(13) in_measure lessI)

(* SEE ABOVE *)
      have \<open>\<forall>t. semantics Var Fun (sat S) (sub 0 t p)\<close>
        sorry
      then have \<open>\<forall>t. semantics (SeCaV.shift Var 0 t) Fun (sat S) p\<close>
        using subst_lemma by simp
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Uni by fastforce
    qed
  next
    case (Neg p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then show \<open>\<not> semantics Var Fun (sat S) x\<close>
        using wf Neg by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S\<close>
        using Neg assms Hintikka.Neg by blast
      then show \<open>semantics Var Fun (sat S) x\<close>
        using wf Neg by fastforce
    qed
  qed
qed

text \<open>We need some lemmas to prove our main theorem\<close>
lemma epath_countermodel:
  assumes \<open>\<exists> steps. fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
  shows \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> (semantics e f g p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>(e :: nat \<Rightarrow> tm) f g. \<not> semantics e f g p\<close>
  then have \<open>\<forall>(e :: nat \<Rightarrow> tm) f g. semantics e f g p\<close>
    by simp
  then show False
  proof -
    assume \<open>\<forall>(e :: nat \<Rightarrow> tm) f g. semantics e f g p\<close>
    moreover obtain steps
      where steps: \<open>fst (fst (shd steps)) = [p] \<and> epath steps \<and> Saturated steps\<close>
      using assms by blast
    then have \<open>Hintikka (tree_fms steps)\<close>
      using escape_path_Hintikka assms by simp
    moreover have \<open>p \<in> tree_fms steps\<close>
      using steps shd_sset unfolding tree_fms_def by force
    then have \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> semantics e f g p\<close>
      using calculation(2) hintikka_counter_model steps by blast
    ultimately show \<open>False\<close>
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
    have \<open>\<exists>(e :: nat \<Rightarrow> tm) f g . \<not> (semantics e f g p)\<close>
      using ep epath_countermodel by blast
    with assms show False using sound by fastforce
  qed
qed

text \<open>Finally, we arrive at the main theorem\<close>
theorem completeness:
  assumes \<open>\<tturnstile> [p]\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  by (simp add: assms epath_contr epath_lem epath_prover_completeness)

end