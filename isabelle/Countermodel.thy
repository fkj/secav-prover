theory Countermodel
  imports Hintikka
begin

section \<open>Alternative Semantics\<close>

text \<open>We define an alternate semantics where the quantifiers refer to a specific set\<close>
primrec usemantics where
  \<open>usemantics u e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>usemantics u e f g (Imp p q) = (usemantics u e f g p \<longrightarrow> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Dis p q) = (usemantics u e f g p \<or> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Con p q) = (usemantics u e f g p \<and> usemantics u e f g q)\<close> |
  \<open>usemantics u e f g (Exi p) = (\<exists>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close> |
  \<open>usemantics u e f g (Uni p) = (\<forall>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close> |
  \<open>usemantics u e f g (Neg p) = (\<not> usemantics u e f g p)\<close>

text \<open>An environment is only defined if the variables are actually in the quantifier set u\<close>
definition is_env :: \<open>'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>is_env u e \<equiv> \<forall>n. e n \<in> u\<close>

definition is_fdenot :: \<open>'a set \<Rightarrow> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>is_fdenot u f \<equiv> \<forall>i l. list_all (\<lambda>x. x \<in> u) l \<longrightarrow> f i l \<in> u\<close>

text \<open>A formula only needs to be valid for the "real" environments\<close>
(* TODO: change this *)
definition uvalid :: \<open>'a set \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>uvalid u p \<equiv> \<forall>e f g. is_env u e \<longrightarrow> is_fdenot u f \<longrightarrow> usemantics u e f g p\<close>

text \<open>If we choose to quantify over the universal set, we obtain the usual semantics\<close>
lemma usemantics_UNIV: \<open>usemantics UNIV e f g p \<longleftrightarrow> semantics e f g p\<close>
  by (induct p arbitrary: e) auto

text \<open>If we choose the universal set, any environment is defined\<close>
lemma is_env_UNIV: \<open>is_env UNIV e\<close>
  unfolding is_env_def by blast

text \<open>If a formula is valid for any quantifier set, it is valid for the universal set in particular,
and we thus obtain that it is also valid in the usual semantics\<close>
lemma uvalid_semantics:
  fixes e :: \<open>nat \<Rightarrow> 'a\<close>
  assumes \<open>\<forall>(u :: 'a set) e f g. usemantics u e f g p\<close>
  shows \<open>semantics e f g p\<close>
  using assms is_env_UNIV usemantics_UNIV by blast

lemma uupd_lemma [iff]: \<open>n \<notin> params p \<Longrightarrow> usemantics u e (f(n := z)) g p \<longleftrightarrow> usemantics u e f g p\<close>
  by (induct p arbitrary: e) simp_all

text \<open>The semantics of substituting variable i by term t in formula a are well-defined\<close>
lemma usubst_lemma [iff]:
  \<open>usemantics u e f g (subst a t i) \<longleftrightarrow> usemantics u (SeCaV.shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

subsection \<open>Soundness of SeCaV\<close>

lemma usemantics_term [simp]:
  assumes \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>semantics_term e f t \<in> u\<close> \<open>list_all (\<lambda>x. x \<in> u) (semantics_list e f l)\<close>
  using assms by (induct t and l rule: semantics_term.induct semantics_list.induct)
    (simp_all add: is_env_def is_fdenot_def)

lemma is_env_shift [simp]: \<open>is_env u e \<Longrightarrow> x \<in> u \<Longrightarrow> is_env u (SeCaV.shift e v x)\<close>
  unfolding is_env_def SeCaV.shift_def by simp                  

lemma is_fdenot_shift [simp]: \<open>is_fdenot u f \<Longrightarrow> x \<in> u \<Longrightarrow> is_fdenot u (f(i := \<lambda>_. x))\<close>
  unfolding is_fdenot_def SeCaV.shift_def by simp

theorem sound_usemantics:
  assumes \<open>\<tturnstile> z\<close> \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>\<exists>p \<in> set z. usemantics u e f g p\<close>
  using assms
proof (induct arbitrary: f rule: sequent_calculus.induct)
  case (10 i p z)
  then show ?case
  proof (cases \<open>\<forall>x \<in> u. usemantics u e (f(i := \<lambda>_. x)) g (sub 0 (Fun i []) p)\<close>)
    case False
    moreover have \<open>\<forall>x \<in> u. \<exists>p \<in> set (sub 0 (Fun i []) p # z). usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      using 10 is_fdenot_shift by metis
    ultimately have \<open>\<exists>x \<in> u. \<exists>p \<in> set z. usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      by fastforce
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 10 by simp
    ultimately show ?thesis
      using 10 Ball_set insert_iff list.set(2) uupd_lemma by metis
  qed simp
next
  case (11 i p z)
  then show ?case
  proof (cases \<open>\<forall>x \<in> u. usemantics u e (f(i := \<lambda>_. x)) g (Neg (sub 0 (Fun i []) p))\<close>)
    case False
    moreover have
      \<open>\<forall>x \<in> u. \<exists>p \<in> set (Neg (sub 0 (Fun i []) p) # z). usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      using 11 is_fdenot_shift by metis
    ultimately have \<open>\<exists>x \<in> u. \<exists>p \<in> set z. usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      by fastforce
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 11 by simp
    ultimately show ?thesis
      using 11 Ball_set insert_iff list.set(2) uupd_lemma by metis
  qed simp
qed fastforce+

section \<open>Machinery\<close>

text \<open>If t is a term in some argument list ts, t is also in the list of subterms of a function
applied to those arguments\<close>
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

lemma subtermTm_refl [simp]: \<open>t \<in> set (subtermTm t)\<close>
  by (induct t) simp_all

lemma subterm_Pre_refl: \<open>set ts \<subseteq> set (subtermFm (Pre n ts))\<close>
  by (induct ts) auto

lemma subterm_Fun_refl: \<open>set ts \<subseteq> set (subtermTm (Fun n ts))\<close>
  by (induct ts) auto

lemma terms_cases: \<open>t \<in> terms S \<Longrightarrow> t = Fun 0 [] \<or> (\<exists>p \<in> S. t \<in> set (subtermFm p))\<close>
  unfolding terms_def by (simp split: if_splits)

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

lemma fun_arguments_subterm:
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

lemma terms_downwards_closed: \<open>t \<in> terms S \<Longrightarrow> set (subtermTm t) \<subseteq> terms S\<close>
proof (induct t)
  case (Fun n ts)
  moreover have \<open>\<forall>t \<in> set ts. t \<in> set ts\<close>
    by simp
  moreover have \<open>\<forall>t \<in> set ts. t \<in> terms S\<close>
  proof
    fix t
    assume *: \<open>t \<in> set ts\<close>
    then show \<open>t \<in> terms S\<close>
    proof (cases \<open>terms S = {Fun 0 []}\<close>)
      case True
      then show ?thesis
        using Fun * by simp
    next
      case False
      moreover obtain p where p: \<open>p \<in> S\<close> \<open>Fun n ts \<in> set (subtermFm p)\<close>
        using Fun(2) terms_cases * by fastforce
      then have \<open>set ts \<subseteq> set (subtermFm p)\<close>
        using fun_arguments_subterm by blast
      ultimately show \<open>t \<in> terms S\<close>
        unfolding terms_def using * p(1) by (metis UN_iff in_mono)
    qed
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

section \<open>Countermodels from Hintikka sets\<close>

text \<open>A predicate is satisfied in a set of formulas S if its negation is also in S\<close>
abbreviation (input) \<open>sat S n ts \<equiv> Neg (Pre n ts) \<in> S\<close>

text \<open>Alternate interpretation for environments: if a variable is not present, we interpret it as some existing term\<close>
abbreviation \<open>E S n \<equiv> if Var n \<in> terms S then Var n else SOME t. t \<in> terms S\<close>

abbreviation \<open>F S i l \<equiv> if Fun i l \<in> terms S then Fun i l else SOME t. t \<in> terms S\<close>

lemma terms_ne [simp]: \<open>terms S \<noteq> {}\<close>
  unfolding terms_def by simp

text \<open>If terms are actually in a set of formulas, interpreting the environment over these formulas
allows for a Herbrand interpretation\<close>
lemma usemantics_E:
  shows
    \<open>t \<in> terms S \<Longrightarrow> semantics_term (E S) (F S) t = t\<close>
    \<open>list_all (\<lambda>t. t \<in> terms S) ts \<Longrightarrow> semantics_list (E S) (F S) ts = ts\<close>
proof (induct t and ts arbitrary: ts rule: semantics_term.induct semantics_list.induct)
  case (Fun i ts')
  moreover have \<open>\<forall>t' \<in> set ts'. t' \<in> set (subtermTm (Fun i ts'))\<close>
    using subtermTm_Fun by blast
  ultimately have \<open>list_all (\<lambda>t. t \<in> terms S) ts'\<close>
    using terms_downwards_closed unfolding list_all_def by (metis (no_types, lifting) subsetD)
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

text \<open>Substituting a variable by a term does not change the depth of a formula
(only the term size changes)\<close>
lemma size_sub [simp]: \<open>size (sub i t p) = size p\<close>
  by (induct p arbitrary: i t) auto

text \<open>As long as some formulas exist, our alternate interpretation of environments is defined\<close>
lemma is_env_E: \<open>is_env (terms S) (E S)\<close>
  unfolding is_env_def
proof
  fix n
  show \<open>E S n \<in> terms S\<close>
    by (cases \<open>Var n \<in> terms S\<close>) (simp_all add: some_in_eq)
qed

lemma is_fdenot_F: \<open>is_fdenot (terms S) (F S)\<close>
  unfolding is_fdenot_def
proof (intro allI impI)
  fix i l
  assume \<open>list_all (\<lambda>x. x \<in> terms S) l\<close>
  then show \<open>F S i l \<in> terms S\<close>
    by (cases \<open>\<forall>n. Var n \<in> terms S\<close>) (simp_all add: some_in_eq)
qed

text \<open>If S is a Hintikka set containing only closed formulas, then we can construct a countermodel
for any closed formula using our alternate semantics and a Herbrand interpretation\<close>
lemma hintikka_counter_model:
  assumes \<open>Hintikka S\<close>
  shows
    \<open>(p \<in> S \<longrightarrow> \<not> usemantics (terms S) (E S) (F S) (sat S) p) \<and>
 (Neg p \<in> S \<longrightarrow> usemantics (terms S) (E S) (F S) (sat S) p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  fix x

  let ?s = \<open>usemantics (terms S) (E S) (F S) (sat S)\<close>

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
        using \<open>x \<in> S\<close> Pre subterm_Pre_refl unfolding terms_def list_all_def by force
      ultimately show \<open>\<not> ?s x\<close>
        using Pre usemantics_E
        by (metis (no_types, lifting) usemantics.simps(1))
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>sat S n ts\<close>
        using assms Pre Hintikka.Basic by blast
      moreover have \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
        using \<open>Neg x \<in> S\<close> Pre subterm_Pre_refl unfolding terms_def list_all_def by force
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
          (SeCaV.shift (E S) 0 (semantics_term (E S) (F S) t)) (F S) (sat S) p\<close>
        by simp
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) (F S) t = t\<close>
        using usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) (F S) (sat S) p\<close>
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
      moreover have \<open>semantics_term (E S) (F S) t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
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
      moreover have \<open>semantics_term (E S) (F S) t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
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
          (SeCaV.shift (E S) 0 (semantics_term (E S) (F S) t)) (F S) (sat S) p\<close>
        by simp
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) (F S) t = t\<close>
        using usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) (F S) (sat S) (Neg p)\<close>
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