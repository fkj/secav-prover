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

lemma usubst_lemma [iff]:
  \<open>usemantics u e f g (subst a t i) \<longleftrightarrow> usemantics u (SeCaV.shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

lemma subtermTm_Fun: \<open>t \<in> set ts \<longrightarrow> t \<in> set (subtermTm (Fun i ts))\<close>
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts')
  then show ?case
  proof (safe)
    assume \<open>t \<in> set (t' # ts')\<close> \<open>t \<notin> set ts'\<close>
    from this have \<open>t = t'\<close> by simp
    moreover have \<open>t' \<in> set (subtermTm (Fun i (t' # ts')))\<close>
    proof (simp)
      have \<open>t' \<in> set (subtermTm t')\<close>
        by (cases t') simp_all
      then show \<open>t' = Fun i (t' # ts') \<or> t' \<in> set (subtermTm t') \<or> (\<exists>x\<in>set ts'. t' \<in> set (subtermTm x))\<close>
        by simp
    qed
    ultimately show \<open>t \<in> set (subtermTm (Fun i (t' # ts')))\<close> by simp
  next
    assume \<open>t \<in> set (t' # ts')\<close> \<open>t \<in> set (subtermTm (Fun i ts'))\<close>
    then show \<open>t \<in> set (subtermTm (Fun i (t' # ts')))\<close>
    proof (simp)
      assume *: \<open>t = t' \<or> t \<in> set ts'\<close>
      assume \<open>t = Fun i ts' \<or> (\<exists>x\<in>set ts'. t \<in> set (subtermTm x))\<close>
      then show \<open>t = Fun i (t' # ts') \<or> t \<in> set (subtermTm t') \<or> (\<exists>x\<in>set ts'. t \<in> set (subtermTm x))\<close>
      proof (cases \<open>\<exists>x\<in>set ts'. t \<in> set (subtermTm x)\<close>)
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
        proof (cases \<open>t = t'\<close>)
          case True
          then show ?thesis
          proof (simp)
            have \<open>t' \<in> set (subtermTm t')\<close>
              by (cases t') simp_all
            then show \<open>t' = Fun i (t' # ts') \<or> t' \<in> set (subtermTm t') \<or> (\<exists>x\<in>set ts'. t' \<in> set (subtermTm x))\<close>
              by simp
          qed
        next
          case False
          then show ?thesis
          proof -
            have \<open>t \<in> set ts'\<close>
              using * False by simp
            moreover have \<open>t \<in> set (subtermTm t)\<close>
              by (cases t) simp_all
            ultimately have \<open>\<exists>x \<in> set ts'. t \<in> set (subtermTm x)\<close>
              by blast
            then show \<open>t = Fun i (t' # ts') \<or> t \<in> set (subtermTm t') \<or> (\<exists>x\<in>set ts'. t \<in> set (subtermTm x))\<close>
              by simp
          qed
        qed
      qed
    qed
  qed
qed

(* This thing is downwards closed *)
value \<open>subtermTm (Fun 0 [Var 0, Fun 1 [Var 1]])\<close>
value \<open>subtermFm (Pre 0 [Var 0, Fun 1 [Var 1]])\<close>

abbreviation \<open>terms H \<equiv> \<Union>f \<in> H. set (subtermFm f)\<close>

lemma subtermTm_refl [simp]: \<open>t \<in> set (subtermTm t)\<close>
  by (induct t) simp_all

lemma subterm_Pre_refl: \<open>set ts \<subseteq> set (subtermFm (Pre n ts))\<close>
  by (induct ts) auto

lemma subterm_Fun_refl: \<open>set ts \<subseteq> set (subtermTm (Fun n ts))\<close>
  by (induct ts) auto

lemma detherlemma: \<open>t \<in> terms S \<Longrightarrow> \<exists>p \<in> S. t \<in> set (subtermFm p)\<close>
  by blast

primrec preds :: \<open>fm \<Rightarrow> fm set\<close> where
  \<open>preds (Pre n ts) = {Pre n ts}\<close>
| \<open>preds (Imp f1 f2) = preds f1 \<union> preds f2\<close>
| \<open>preds (Dis f1 f2) = preds f1 \<union> preds f2\<close>
| \<open>preds (Con f1 f2) = preds f1 \<union> preds f2\<close>
| \<open>preds (Exi f) = preds f\<close>
| \<open>preds (Uni f) = preds f\<close>
| \<open>preds (Neg f) = preds f\<close>

lemma subtermFm_preds: \<open>t \<in> set (subtermFm p) \<longleftrightarrow> (\<exists>pre \<in> preds p. t \<in> set (subtermFm pre))\<close>
  by (induct p) auto

lemma preds_shape: \<open>pre \<in> preds p \<Longrightarrow> \<exists>n ts. pre = Pre n ts\<close>
  by (induct p) auto

lemma subtermTm_le: \<open>t \<in> set (subtermTm s) \<Longrightarrow> set (subtermTm t) \<subseteq> set (subtermTm s)\<close>
  by (induct s) auto

lemma ogdether:
  assumes \<open>Fun n ts \<in> set (subtermFm p)\<close>
  shows \<open>set ts \<subseteq> set (subtermFm p)\<close>
proof -
  obtain pre where pre: \<open>pre \<in> preds p\<close> \<open>Fun n ts \<in> set (subtermFm pre)\<close>
    using assms subtermFm_preds by blast
  then obtain n' ts' where \<open>pre = Pre n' ts'\<close>
    using preds_shape by blast
  then have \<open>set ts \<subseteq> set (subtermFm pre)\<close>
    using subtermTm_le pre by force
  then have \<open>set ts \<subseteq> set (subtermFm p)\<close>
    using pre subtermFm_preds by blast
  then show ?thesis
    by blast
qed

lemma woop: \<open>t \<in> terms S \<Longrightarrow> set (subtermTm t) \<subseteq> terms S\<close>
proof (induct t)
  case (Fun n ts)
  moreover have \<open>\<forall>t \<in> set ts. t \<in> set ts\<close>
    by simp
  moreover have \<open>\<forall>t \<in> set ts. t \<in> terms S\<close>
  proof
    fix t
    assume \<open>t \<in> set ts\<close>
    moreover obtain p where p: \<open>p \<in> S\<close> \<open>Fun n ts \<in> set (subtermFm p)\<close>
      using Fun(2) detherlemma by blast
    ultimately show \<open>t \<in> terms S\<close>
      using ogdether by fast
  qed
  ultimately have \<open>\<forall>t \<in> set ts. set (subtermTm t) \<subseteq> terms S\<close>
    using Fun by meson
  moreover note \<open>Fun n ts \<in> terms S\<close>
  ultimately show ?case
    by auto
next
  case (Var x)
  then show ?case
    by simp
qed

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
  shows
    \<open>t \<in> terms S \<Longrightarrow> semantics_term (E S) Fun t = t\<close>
    \<open>list_all (\<lambda>t. t \<in> terms S) ts \<Longrightarrow> semantics_list (E S) Fun ts = ts\<close>
proof (induct t and ts arbitrary: ts rule: semantics_term.induct semantics_list.induct)
  case (Fun i ts')
  moreover have \<open>\<forall>t' \<in> set ts'. t' \<in> set (subtermTm (Fun i ts'))\<close>
    using subtermTm_Fun by blast
  ultimately have \<open>list_all (\<lambda>t. t \<in> terms S) ts'\<close>
    using woop unfolding list_all_def by (metis (no_types, lifting) subsetD)
  then show ?case
    using Fun by simp
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
    by simp
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
  assumes \<open>Hintikka S\<close>
  shows
    \<open>(p \<in> S \<longrightarrow> \<not> usemantics (terms S) (E S) Fun (sat S) p) \<and>
 (Neg p \<in> S \<longrightarrow> usemantics (terms S) (E S) Fun (sat S) p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  fix x

  let ?s = \<open>usemantics (terms S) (E S) Fun (sat S)\<close>

  assume wf: \<open>\<forall>q. (q, x) \<in> measure size \<longrightarrow>
    (q \<in> S \<longrightarrow> \<not> ?s q) \<and> (Neg q \<in> S \<longrightarrow> ?s q)\<close>

  show \<open>(x \<in> S \<longrightarrow> \<not> ?s x) \<and> (Neg x \<in> S \<longrightarrow> ?s x)\<close>
  proof (cases x)
    case (Pre n ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg (Pre n ts) \<notin> S\<close>
        using assms Pre Hintikka.Basic by blast
      moreover have \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
        using \<open>x \<in> S\<close> Pre subterm_Pre_refl unfolding list_all_def by fast
      ultimately show \<open>\<not> ?s x\<close>
        using Pre usemantics_E
        by (metis (no_types, lifting) usemantics.simps(1))
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>sat S n ts\<close>
        using assms Pre Hintikka.Basic by blast
      moreover have \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
        using \<open>Neg x \<in> S\<close> Pre subterm_Pre_refl unfolding list_all_def by force
      ultimately show \<open>?s x\<close>
        using Pre usemantics_E
        by (metis (no_types, lifting) usemantics.simps(1))
    qed
  next
    case (Imp p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>q \<in> S\<close>
        using Imp assms Hintikka.AlphaImp by blast+
      then show \<open>\<not> ?s x\<close>
        using wf Imp by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S \<or> Neg q \<in> S\<close>
        using Imp assms Hintikka.BetaImp by blast
      then show \<open>?s x\<close>
        using wf Imp by fastforce
    qed
  next
    case (Dis p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S\<close> \<open>q \<in> S\<close>
        using Dis assms Hintikka.AlphaDis by blast+
      then show \<open>\<not> ?s x\<close>
        using wf Dis by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S \<or> Neg q \<in> S\<close>
        using Dis assms Hintikka.BetaDis by blast
      then show \<open>?s x\<close>
        using wf Dis by fastforce
    qed
  next
    case (Con p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S \<or> q \<in> S\<close>
        using Con assms Hintikka.BetaCon by blast
      then show \<open>\<not> ?s x\<close>
        using wf Con by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>Neg q \<in> S\<close>
        using Con assms Hintikka.AlphaCon by blast+
      then show \<open>?s x\<close>
        using wf Con by fastforce
    qed
  next
    case (Exi p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. sub 0 t p \<in> S\<close>
        using Exi assms Hintikka.GammaExi by blast
      then have \<open>\<forall>t \<in> terms S. \<not> ?s (sub 0 t p)\<close>
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
        using Exi assms Hintikka.DeltaExi by metis
      then have \<open>?s (sub 0 t p)\<close>
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
      then have \<open>\<not> ?s (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(13) in_measure lessI)
      moreover have \<open>semantics_term (E S) Fun t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) woop unfolding list_all_def by blast
      ultimately show \<open>\<not> ?s x\<close>
        using Uni \<open>t \<in> terms S\<close> by auto
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. Neg (sub 0 t p) \<in> S\<close>
        using Uni assms Hintikka.GammaUni by blast
      then have \<open>\<forall>t \<in> terms S. ?s (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis (no_types, lifting) Nat.add_0_right add_Suc_right
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
        using wf Neg by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S\<close>
        using Neg assms Hintikka.Neg by blast
      then show \<open>?s x\<close>
        using wf Neg by fastforce
    qed
  qed
qed

end