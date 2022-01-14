theory Usemantics imports SeCaV begin

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

end
