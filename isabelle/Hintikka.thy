theory Hintikka
  imports Prover
begin

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

definition \<open>tree_fms steps \<equiv> \<Union>fms \<in> sset steps. set (fst (fst fms))\<close>

lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

lemma effStep_unique: \<open>\<forall>sl sl'. effStep s sl \<longrightarrow> effStep s sl' \<longrightarrow> sl = sl'\<close>
  unfolding eff_def
  by simp

fun index_of :: \<open>sequent \<Rightarrow> fm \<Rightarrow> nat\<close> where
  \<open>index_of [] _ = undefined\<close>
| \<open>index_of (p # z) f = (if p = f then 0 else 1 + index_of z f)\<close>

primrec firstDone :: \<open>sequent \<Rightarrow> fm option\<close> where
  \<open>firstDone [] = None\<close>
| \<open>firstDone (p # z) = (if Neg p \<in> set z then Some p else firstDone z)\<close>

definition basic_measure :: \<open>sequent \<Rightarrow> nat\<close> where
  \<open>basic_measure s = (case firstDone s of None \<Rightarrow> 0 | Some p \<Rightarrow> index_of s p)\<close>

lemma termination_PBasic:
  \<open>branchDone (fst (fst (shd steps))) \<Longrightarrow> ev (holds (\<lambda>s. Neg (hd (fst (fst s))) \<in> set (tl (fst (fst s))))) steps\<close>
proof (induction \<open>steps\<close> rule: wf_induct[where r=\<open>measure (\<lambda>steps. basic_measure (fst (fst (shd steps))))\<close>])
  case 1
  then show ?case ..
next
  case (2 s)
  then show ?case
  proof (cases \<open>Neg (hd (fst (fst (shd s)))) \<in> set (tl (fst (fst (shd s))))\<close>)
    case True
    then show ?thesis using 2 by auto
  next
    case False
    then show ?thesis using 2 sorry
  qed
qed

lemma id_PBasic: \<open>epath steps \<Longrightarrow> alw (holds (\<lambda>s. \<not> branchDone (fst (fst s)))) steps\<close>
proof (coinduction arbitrary: steps)
  case alw
  then show ?case
  proof (auto elim: epath.cases)
    assume *: \<open>epath steps\<close> and \<open>branchDone (fst (fst (shd steps)))\<close>
    then obtain n where \<open>effStep (shd (sdrop n steps)) {||}\<close>
      using termination_PBasic
      sorry
    moreover have \<open>epath (sdrop n steps)\<close>
      using * epath_sdrop by blast
    then have \<open>\<exists>sl. fst (shd (stl (sdrop n steps))) |\<in>| sl \<and> effStep (shd (sdrop n steps)) sl\<close>
      using epath.simps by blast
    ultimately have \<open>fst (shd (stl (sdrop n steps))) |\<in>| {||}\<close>
      using effStep_unique by blast
    then show False
      ..
  qed
qed

lemma woop:
  assumes \<open>Dis p q \<in> tree_fms steps\<close> \<open>epath steps\<close> \<open>Saturated steps\<close>
  shows \<open>\<exists>n s. s = shd (sdrop n steps) \<and> (\<exists>z. s = ((Dis p q # z, PABD), AlphaDis))\<close>
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
  assume dis: \<open>Dis p q \<in> ?H\<close>
  obtain s z n where \<open>s = ((Dis p q # z, PABD), AlphaDis)\<close> and \<open>s = shd (sdrop n steps)\<close>
    using dis woop assms by metis
      (* we need that the nxt node contains the decomposed formula as soon as it is enabled *)
  then have \<open>takenAtStep AlphaDis (shd (sdrop n steps))\<close>
    by simp
  have \<open>\<exists>r. shd (sdrop (Suc n) steps) = ((p # q # z, PBasic), r)\<close>
    using assms (* follows from the effStep part of epath steps *)
    sorry
  then show \<open>p \<in> ?H \<and> q \<in> ?H\<close> (* follows from the definition of tree_fms *)
    sorry
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close>
  then have \<open>ev (\<lambda>s. (Imp p q) \<in> set (fst (fst (shd s))) \<and> snd (fst (shd s)) = PABD) steps\<close>
    sorry
  then have \<open>ev (\<lambda>s. hd (fst (fst (shd s))) = Imp p q \<and> snd (fst (shd s)) = PABD) steps\<close>
    sorry
  then have \<open>ev (\<lambda>s. hd (fst (fst (shd s))) = Neg p \<and> hd (tl (fst (fst (shd s)))) = q) steps\<close>
    sorry
  then show \<open>Neg p \<in> tree_fms steps \<and> q \<in> tree_fms steps\<close>
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
  show \<open>\<forall>t \<in> terms (tree_fms steps). sub 0 t p \<in> tree_fms steps\<close>
    sorry
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
  show \<open>p \<in> tree_fms steps\<close>
    sorry
qed


end