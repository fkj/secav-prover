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

end
