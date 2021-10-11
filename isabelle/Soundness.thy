theory Soundness
  imports Prover
begin

section \<open>Soundness of the prover\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e, f, g) (z, _) = (\<exists>p \<in> set z. semantics e f g p)\<close>

lemma eff_preserves_Nil:
  assumes \<open>eff r ([], phase) sl\<close> \<open>s |\<in>| sl\<close>
  shows \<open>fst s = []\<close>
  using assms unfolding eff_def
proof (induct r)
  case Rotate
  moreover have \<open>effect Rotate ([], PInstGamma n ots ts b) = Some sl \<Longrightarrow>
       s |\<in>| sl \<Longrightarrow> fst s = []\<close> for n ots ts b
    by (induct b) simp_all
  ultimately show ?case
    by (induct phase) simp_all
next
  case Next
  moreover have \<open>effect Next ([], PInstGamma n ots ts b) = Some sl \<Longrightarrow>
       s |\<in>| sl \<Longrightarrow> fst s = []\<close> for n ots ts b
    by (induct ts) (induct b, auto)+
  ultimately show ?case
    by (induct phase) auto
qed (induct phase, simp_all)

lemma branches_if_not_Basic:
  assumes \<open>eff r ([], phase) sl\<close> \<open>r \<noteq> Basic\<close>
  shows \<open>sl \<noteq> {||}\<close>
  using assms unfolding eff_def
proof (induct r)
  case Rotate
  moreover have \<open>effect Rotate ([], PInstGamma n ots ts b) = Some sl \<Longrightarrow>
       Rotate \<noteq> Basic \<Longrightarrow> sl \<noteq> {||}\<close> for n ots ts b
    by (induct b) simp_all
  ultimately show ?case
    by (induct phase) auto
next
  case Next
  moreover have \<open>effect Next ([], PInstGamma n ots ts b) = Some sl \<Longrightarrow>
       Next \<noteq> Basic \<Longrightarrow> sl \<noteq> {||}\<close> for n ots ts b
    by (induct ts) (induct b, auto)+
  ultimately show ?case
    by (induct phase) auto
qed (induct phase, auto)

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def
proof (safe)
  fix r sequent phase sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
    and r_enabled: \<open>eff r (sequent, phase) sl\<close>
    and next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
  proof (cases sequent)
    case Nil
    show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
    proof (rule ccontr)
      have \<open>eff r ([], phase) sl \<Longrightarrow> (\<forall>s'. s' |\<in>| sl \<longrightarrow> fst s' = [])\<close>
        using eff_preserves_Nil by blast
      moreover have \<open>\<forall>s'. fst s' = [] \<longrightarrow> (\<not> (\<forall>S \<in> UNIV. ssemantics S s'))\<close>
        by simp
      ultimately have \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> fst s' = []\<close>
        using Nil r_enabled by blast
      then have \<open>sl = {||}\<close>
        using next_sound by fastforce
      moreover have \<open>r \<noteq> Basic\<close>
        using r_enabled Nil unfolding eff_def by auto
      ultimately show \<open>False\<close>
        using branches_if_not_Basic Nil r_enabled by blast
    qed
  next
    case (Cons p z)
    then show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
    proof (induct phase)
      case PBasic
      then show ?case
      proof (cases p)
        case (Pre n ts)
        then show ?thesis
        proof (cases \<open>branchDone (p # z)\<close>)
          case True
          then show ?thesis
          proof (cases \<open>Neg p \<notin> set z\<close>)
            case True
            then have \<open>r = Rotate\<close>
              sorry
            then show ?thesis
              sorry
          next
            case False
            then show ?thesis sorry
          qed
        next
          case False
          then show ?thesis sorry
        qed 
      next
        case (Imp x21 x22)
        then show ?thesis sorry
      next
        case (Dis x31 x32)
        then show ?thesis sorry
      next
        case (Con x41 x42)
        then show ?thesis sorry
      next
        case (Exi x5)
        then show ?thesis sorry
      next
        case (Uni x6)
        then show ?thesis sorry
      next
        case (Neg x7)
        then show ?thesis sorry
      qed  
    next
      case PABD
      then show ?case sorry
    next
      case (PPrepGamma x1 x2)
      then show ?case sorry
    next
      case (PInstGamma x1 x2 x3 x4)
      then show ?case sorry
    qed
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>(\<exists>p \<in> set (fst (fst (root t))). semantics e f g p)\<close>
  using soundness assms ssemantics.simps UNIV_I eq_fst_iff
  by metis

end