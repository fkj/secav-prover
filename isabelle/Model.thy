theory Model imports Prover begin

section \<open>Alternative Semantics\<close>

primrec usemantics where
  \<open>usemantics u e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>usemantics u e f g (Imp p q) = (usemantics u e f g p \<longrightarrow> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Dis p q) = (usemantics u e f g p \<or> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Con p q) = (usemantics u e f g p \<and> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Exi p) = (\<exists>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close> |
  \<open>usemantics u e f g (Uni p) = (\<forall>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close> |
  \<open>usemantics u e f g (Neg p) = (\<not> usemantics u e f g p)\<close>

definition is_env :: \<open>'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>is_env u e \<equiv> \<forall>n. e n \<in> u\<close>

definition uvalid :: \<open>'a set \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>uvalid u p \<equiv> \<forall>e f g. is_env u e \<longrightarrow> usemantics u e f g p\<close>

lemma usemantics_UNIV: \<open>usemantics UNIV e f g p \<longleftrightarrow> semantics e f g p\<close>
  by (induct p arbitrary: e) auto

lemma is_env_UNIV: \<open>is_env UNIV e\<close>
  unfolding is_env_def by blast

lemma uvalid_semantics:
  fixes e :: \<open>nat \<Rightarrow> 'a\<close>
  assumes \<open>\<forall>(u :: 'a set). uvalid u p\<close>
  shows \<open>semantics e f g p\<close>
  using assms is_env_UNIV usemantics_UNIV unfolding uvalid_def
  by blast

section \<open>Machinery\<close>

primrec closedt where
  \<open>closedt m (Var n) = (n < m)\<close>
| \<open>closedt m (Fun _ ts) = list_all (closedt m) ts\<close>

primrec closed where
  \<open>closed m (Pre _ ts) = list_all (closedt m) ts\<close>
| \<open>closed m (Imp p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Dis p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Con p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Exi p) = (closed (Suc m) p)\<close>
| \<open>closed m (Uni p) = (closed (Suc m) p)\<close>
| \<open>closed m (Neg p) = closed m p\<close>

lemma closedt_usemantics_id [simp]:
  assumes \<open>closedt 0 t\<close> \<open>list_all (closedt 0) ts\<close>
  shows
  \<open>semantics_term e Fun t = t\<close>
  \<open>semantics_list e Fun ts = ts\<close>
  using assms by (induct t and ts rule: semantics_term.induct semantics_list.induct)
    (simp_all add: assms)

lemma usubst_lemma [iff]:
  \<open>usemantics u e f g (subst a t i) \<longleftrightarrow> usemantics u (SeCaV.shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

lemma subtermTm_Fun: \<open>t \<in> set ts \<Longrightarrow> t \<in> set (subtermTm 0 (Fun i ts))\<close>
  sorry

(* This thing is downwards closed *)
value \<open>subtermTm 0 (Fun 0 [Var 0, Fun 1 [Var 1]])\<close>
value \<open>subtermFm 0 (Pre 0 [Var 0, Fun 1 [Var 1]])\<close>

abbreviation \<open>terms H \<equiv> \<Union>f \<in> H. set (subtermFm 0 f)\<close>

lemma woop: \<open>t \<in> terms S \<Longrightarrow> s \<in> set (subtermTm 0 t) \<Longrightarrow> s \<in> terms S\<close>
  sorry

section \<open>The Good Stuff\<close>

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

abbreviation (input) \<open>sat S n ts \<equiv> Neg (Pre n ts) \<in> S\<close>

abbreviation \<open>E S n \<equiv> if Var n \<in> terms S then Var n else SOME t. t \<in> terms S\<close>

lemma usemantics_E:
  assumes \<open>t \<in> terms S\<close> \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
  shows
    \<open>semantics_term (E S) Fun t = t\<close>
    \<open>semantics_list (E S) Fun ts = ts\<close>
  using assms
proof (induct t and ts arbitrary: ts rule: semantics_term.induct semantics_list.induct)
  case (Fun i ts')
  moreover have \<open>\<forall>t' \<in> set ts'. t' \<in> set (subtermTm 0 (Fun i ts'))\<close>
    using subtermTm_Fun by blast
  ultimately have \<open>list_all (\<lambda>t. t \<in> terms S) ts'\<close>
    using woop by (metis (no_types, lifting) Ball_set_list_all)
  then show ?case
    using Fun assms(1) by simp
next
  case (Var x)
  then show ?case
    by fastforce
next
  case Nil_tm
  then show ?case
    by simp
next
  case (Cons_tm x1 x2)
  then show ?case
    using assms(2) by simp
qed
    
lemma size_sub [simp]: \<open>size (sub i t p) = size p\<close>
  by (induct p arbitrary: i t) auto

lemma is_env_E:
  assumes \<open>terms S \<noteq> {}\<close>
  shows \<open>is_env (terms S) (E S)\<close>
  unfolding is_env_def
proof
  fix n
  show \<open>E S n \<in> terms S\<close>
  proof (cases \<open>Var n \<in> terms S\<close>)
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using assms by (metis someI equals0I)
  qed
qed

lemma hintikka_counter_model:
  assumes \<open>Hintikka S\<close> \<open>\<forall>p \<in> S. closed 0 p\<close> \<open>closed 0 p\<close>
  shows
    \<open>(p \<in> S \<longrightarrow> \<not> usemantics (terms S) (E S) Fun (sat S) p) \<and>
 (Neg p \<in> S \<longrightarrow> usemantics (terms S) (E S) Fun (sat S) p)\<close>
  using assms(3)
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  fix x

  let ?s = \<open>usemantics (terms S) (E S) Fun (sat S)\<close>

  assume wf: \<open>\<forall>q. (q, x) \<in> measure size \<longrightarrow> closed 0 q \<longrightarrow>
    (q \<in> S \<longrightarrow> \<not> ?s q) \<and> (Neg q \<in> S \<longrightarrow> ?s q)\<close>
  assume cl: \<open>closed 0 x\<close>

  show \<open>(x \<in> S \<longrightarrow> \<not> ?s x) \<and> (Neg x \<in> S \<longrightarrow> ?s x)\<close>
  proof (cases x)
    case (Pre n ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg (Pre n ts) \<notin> S\<close>
        using assms Pre Hintikka.Basic by blast
      then show \<open>\<not> ?s x\<close>
        using Pre cl closedt_usemantics_id
        by (metis (no_types, lifting) closed.simps(1) closedt.simps(2) usemantics.simps(1))
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>sat S n ts\<close>
        using assms Pre Hintikka.Basic by blast
      then show \<open>?s x\<close>
        using Pre cl closedt_usemantics_id
        by (metis (no_types, lifting) closed.simps(1) closedt.simps(2) usemantics.simps(1))
    qed
  next
    case (Imp p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>q \<in> S\<close>
        using Imp assms Hintikka.AlphaImp by blast+
      then show \<open>\<not> ?s x\<close>
        using wf Imp cl by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S \<or> Neg q \<in> S\<close>
        using Imp assms Hintikka.BetaImp by blast
      then show \<open>?s x\<close>
        using wf Imp cl by fastforce
    qed
  next
    case (Dis p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S\<close> \<open>q \<in> S\<close>
        using Dis assms Hintikka.AlphaDis by blast+
      then show \<open>\<not> ?s x\<close>
        using wf Dis cl by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S \<or> Neg q \<in> S\<close>
        using Dis assms Hintikka.BetaDis by blast
      then show \<open>?s x\<close>
        using wf Dis cl by fastforce
    qed
  next
    case (Con p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S \<or> q \<in> S\<close>
        using Con assms Hintikka.BetaCon by blast
      then show \<open>\<not> ?s x\<close>
        using wf Con cl by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>Neg q \<in> S\<close>
        using Con assms Hintikka.AlphaCon by blast+
      then show \<open>?s x\<close>
        using wf Con cl by fastforce
    qed
  next
    case (Exi p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. sub 0 t p \<in> S\<close>
        using Exi assms Hintikka.GammaExi by blast
      moreover from this have \<open>\<forall>t \<in> terms S. closed 0 (sub 0 t p)\<close>
        using assms(2) by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> ?s (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(12) in_measure lessI)
      then have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S)
          (SeCaV.shift (E S) 0 (semantics_term (E S) Fun t)) Fun (sat S) p\<close>
        by simp
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) Fun t = t\<close>
        using usemantics_E(1) woop unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) Fun (sat S) p\<close>
        by simp
      then show \<open>\<not> ?s x\<close>
        using Exi by simp
    next
      assume \<open>Neg x \<in> S\<close>
      then obtain t where \<open>t \<in> terms S\<close> \<open>Neg (sub 0 t p) \<in> S\<close>
        using Exi cl assms Hintikka.DeltaExi by metis
      moreover from this have \<open>closed 0 (sub 0 t p)\<close>
        using assms(2) by auto
      ultimately have \<open>?s (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(12) in_measure lessI)
      moreover have \<open>semantics_term (E S) Fun t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) woop unfolding list_all_def by blast
      ultimately show \<open>?s x\<close>
        using wf Exi \<open>t \<in> terms S\<close> by auto
    qed
  next
    case (Uni p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then obtain t where \<open>t \<in> terms S\<close> \<open>sub 0 t p \<in> S\<close>
        using Uni assms Hintikka.DeltaUni by metis
      moreover from this have \<open>closed 0 (sub 0 t p)\<close>
        using assms(2) by blast
      ultimately have \<open>\<not> ?s (sub 0 t p)\<close>
        using wf Uni cl size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(13) in_measure lessI)
      moreover have \<open>semantics_term (E S) Fun t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) woop unfolding list_all_def by blast
      ultimately show \<open>\<not> ?s x\<close>
        using Uni cl \<open>t \<in> terms S\<close> by auto
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. Neg (sub 0 t p) \<in> S\<close>
        using Uni assms Hintikka.GammaUni by blast
      moreover from this have \<open>\<forall>t \<in> terms S. closed 0 (Neg (sub 0 t p))\<close>
        using assms(2) by blast
      ultimately have \<open>\<forall>t \<in> terms S. ?s (sub 0 t p)\<close>
        using wf Uni cl size_sub
        by (metis (no_types, lifting) Nat.add_0_right add_Suc_right closed.simps(7)
            fm.size(13) in_measure lessI)
      then have \<open>\<forall>t \<in> terms S. usemantics (terms S)
          (SeCaV.shift (E S) 0 (semantics_term (E S) Fun t)) Fun (sat S) p\<close>
        by simp
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) Fun t = t\<close>
        using usemantics_E(1) woop unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) Fun (sat S) (Neg p)\<close>
        by simp
      then show \<open>?s x\<close>
        using wf Uni by fastforce
    qed
  next
    case (Neg p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then show \<open>\<not> ?s x\<close>
        using wf Neg cl by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S\<close>
        using Neg assms Hintikka.Neg by blast
      then show \<open>?s x\<close>
        using wf Neg cl by fastforce
    qed
  qed
qed

end