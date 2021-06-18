theory Soundness
  imports Prover
begin

section \<open>Soundness of the prover\<close>

(*
fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) ([],_) = False\<close>
| \<open>ssemantics (e,f,g) ((p # z),phase) = (semantics e f g p \<or> ssemantics (e,f,g) (z,phase))\<close>
*)

definition ssemantics' where \<open>ssemantics' e f g state \<equiv> \<exists>p \<in> set (fst state). semantics e f g p\<close>
definition ssemantics where \<open>ssemantics i state \<equiv> ssemantics' (fst i) (fst (snd i)) (snd (snd i)) state\<close>

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def
proof (safe)
  fix r sequent phase sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
  assume r_enabled: \<open>eff r (sequent, phase) sl\<close>
  assume next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) (sequent, phase)\<close> unfolding ssemantics_def ssemantics'_def
  proof (cases sequent)
    case Nil
    assume empty: \<open>sequent = []\<close>
    show \<open>\<exists>p\<in>set (fst (sequent, phase)). semantics (fst (e, f, g)) (fst (snd (e, f, g))) (snd (snd (e, f, g))) p\<close>
    proof (rule ccontr)
      note \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
      have \<open>eff r ([], phase) sl \<Longrightarrow> (\<forall>s'. s' |\<in>| sl \<longrightarrow> fst s' = [])\<close> sorry
      moreover have \<open>\<forall>s'. fst s' = [] \<longrightarrow> (\<not> (\<forall>S \<in> UNIV. ssemantics S s'))\<close> sorry
      ultimately show \<open>False\<close> using next_sound r_enabled r_rule
      proof (simp)
        assume eff_empty: \<open>(eff r ([], phase) sl \<Longrightarrow> \<forall>s. (\<exists>p. (s, p) |\<in>| sl) \<longrightarrow> s = [])\<close>
        assume empty_invalid: \<open> \<forall>phase. \<exists>e f g. \<not> ssemantics (e, f, g) ([], phase)\<close>
        assume enabled_valid: \<open>\<forall>s p. (s, p) |\<in>| sl \<longrightarrow> (\<forall>e f g. ssemantics (e, f, g) (s, p))\<close>
        assume eff: \<open>eff r (sequent, phase) sl\<close>
        assume r: \<open>r \<in> R\<close>
        have \<open>eff r ([], phase) sl\<close> using empty eff by simp
        then have \<open>\<forall>s. (\<exists>p. (s, p) |\<in>| sl) \<longrightarrow> s = []\<close> using eff_empty by simp
        then show False
          sorry
      qed
    qed
  next
    case (Cons p z)
    assume \<open>sequent = p # z\<close>
    show \<open>\<exists>p\<in>set (fst (sequent, phase)). semantics (fst (e, f, g)) (fst (snd (e, f, g))) (snd (snd (e, f, g))) p\<close>
    proof (simp)
      show \<open>\<exists>p\<in>set sequent. semantics e f g p\<close>
        sorry
    qed
  qed
qed

theorem prover_soundness:
  fixes t
  assumes f: \<open>tfinite t\<close> and w: \<open>wf t\<close>
  shows \<open>\<forall>i. ssemantics i (fst (root t))\<close>
proof (safe)
  fix t :: \<open>((fm list \<times> phase) \<times> PseudoRule) tree\<close>
  fix e f and g :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  show \<open>ssemantics (e,f,g) (fst (root t))\<close>
    using assms soundness
    sorry
qed

end