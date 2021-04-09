theory SeCaV_Enum
  imports SeCaV
          "HOL-Library.Stream"
          Abstract_Completeness
          Finite_Proof_Soundness
          "HOL-Library.Countable"
          "HOL-Library.Code_Lazy"
begin

text \<open>In this file, we want to obtain streams containing all lists of terms and formulas\<close>

section \<open>Terms\<close>
text \<open>Isabelle can generate a countability proof for our type of terms\<close>
instance tm :: countable
  by countable_datatype

text \<open>
We can encode a term either as the identifier of the variable or as the product of the identifier
of the function and the recursively encoded list of arguments of the function
\<close>
fun term_encode where
  "term_encode (Var n) = sum_encode (Inl n)"
| "term_encode (Fun n ts) = sum_encode (Inr (prod_encode (n, list_encode (map term_encode ts))))"


text \<open>
The decoding of a term is just the inverse of the term_encode function above, but termination is a
bit more involved here, and we use the above lemmas "in order" with the transitivity of less than
\<close>
function term_decode where
  "term_decode m = (case sum_decode m of
    Inl n \<Rightarrow> Var n
  | Inr p \<Rightarrow> case prod_decode p of (n, ts) \<Rightarrow> Fun n (map term_decode (list_decode ts)))"
  by auto

text \<open>
We need a few lemmas about ordering of the decodings to ensure termination of the decoding
\<close>
lemma sum_decode_le: \<open>sum_decode m = Inr p \<Longrightarrow> p < m\<close>
  using odd_pos by (simp add: sum_decode_def split: if_splits, auto)

lemma prod_decode_le: \<open>(n, ts) = prod_decode p \<Longrightarrow> ts \<le> p\<close>
  apply (simp add: prod_decode_def prod_decode_aux.simps)
  apply (induct ts, simp_all add: prod_decode_def)
  by (metis le_prod_encode_2 le_zero_eq prod_decode_aux.simps prod_decode_def prod_decode_inverse)  

text \<open>I am a bit unsure about how to prove this one\<close>
lemma list_decode_le: \<open>l \<in> set (list_decode ts) \<Longrightarrow> l \<le> ts\<close>
proof (induct ts rule: list_decode.induct)
  case 1
  then show ?case
    by simp
next
  case (2 n)
  then show ?case
  proof -
    assume l1:  \<open>\<And>x y . (x, y) = prod_decode n \<Longrightarrow> l \<in> set (list_decode y) \<Longrightarrow> l \<le> y\<close>
    assume l2: \<open>l \<in> set (list_decode (Suc n))\<close>
    note \<open>\<And>x . (x, Suc n) = prod_decode n \<Longrightarrow> l \<in> set (list_decode (Suc n)) \<Longrightarrow> l \<le> Suc n\<close>
    show \<open>l \<le> Suc n\<close>
      sorry
  qed
qed

termination
proof (relation "measure size", auto)
  fix m p n ts l
  assume p_m: \<open>sum_decode m = Inr p\<close>
  assume ts_p: \<open>(n, ts) = prod_decode p\<close>
  assume l_ts: \<open>l \<in> set (list_decode ts)\<close>
  then show \<open>l < m\<close>
    using p_m ts_p l_ts
    by (meson le_less_trans list_decode_le prod_decode_le sum_decode_le)
qed

text \<open>
This decoding is the inverse of the encoding, and vice versa
\<close>

lemma term_encode_inverse [simp]: \<open>term_decode (term_encode t) = t\<close>
proof (induct t rule: term_encode.induct)
  case (1 n)
  then show ?case
    by simp
next
  case (2 n ts)
  then show ?case
    sorry
qed

lemma term_decode_inverse [simp]: \<open>term_encode (term_decode x) = x\<close>
proof (induct x rule: term_decode.induct)
  case (1 m)
  then show ?case
    sorry
qed

text \<open>
  Which gives rise to a bijection between nat and tm
\<close>
lemma bij_term_decode: \<open>bij term_decode\<close>
  by (metis bijI' term_decode_inverse term_encode_inverse)

text \<open>
We then define a stream of all possible terms as the mapping of the stream of all natural
numbers to the stream of lists of terms
\<close>
definition single_terms: \<open>single_terms \<equiv> smap term_decode nats\<close>

lemma UNIV_single_terms: \<open>sset single_terms = (UNIV :: tm set)\<close>
proof (intro equalityI subsetI UNIV_I)
  fix t
  assume t: \<open>t \<in> (UNIV :: tm set)\<close>
  show \<open>t \<in> sset single_terms\<close>
    unfolding single_terms
    using bij_term_decode
    sorry
qed

definition terms: \<open>terms \<equiv> smap (map term_decode \<circ> list_decode) nats\<close>

text \<open>We now need to prove that this stream actually contains every possible list of terms\<close>
lemma UNIV_term_decode: \<open>t \<in> (UNIV :: tm set) \<Longrightarrow> \<exists>x . term_decode x = t\<close>
  using term_encode_inverse by blast

lemma UNIV_list_decode: \<open>l \<in> (UNIV :: nat list set) \<Longrightarrow> \<exists>x . list_decode x = l\<close>
  using list_encode_inverse by blast

lemma UNIV_list_term_decode: \<open>l \<in> (UNIV :: tm list set) \<Longrightarrow> \<exists>x . (map term_decode \<circ> list_decode) x = l\<close>
  sorry

lemma countable_terms: \<open>countable (sset terms)\<close> ..

lemma UNIV_terms: "sset terms = (UNIV :: tm list set)"
proof (intro equalityI subsetI UNIV_I)
  fix t
  assume t: \<open>t \<in> (UNIV :: tm list set)\<close>
  show \<open>t \<in> sset terms\<close>
    unfolding sset_def terms
    sorry
qed

text \<open>stream.set_induct

Unfold sset
prove UNIV list_decode

\<close>

section \<open>Rules\<close>

text \<open>A proof state in SeCaV is a list of formulas (a sequent)\<close>
type_synonym sequent = \<open>fm list\<close>

text \<open>
We now have to define the rule application we will use in the prover.
We will start by defining the possible rules.
\<close>
datatype rule = Basic
  | AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | GammaExi tm | GammaUni tm
  | DeltaUni | DeltaExi
  | NegNeg
  | ExtRotate

text \<open>We now need to define what the rules do\<close>
fun maxFunTm :: \<open>tm \<Rightarrow> nat\<close> where
  \<open>maxFunTm (Fun n ts) = max n (foldl max 0 (map maxFunTm ts))\<close>
| \<open>maxFunTm (Var n) = 0\<close>

fun maxFun :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>maxFun (Pre n ts) = foldl max 0 (map maxFunTm ts)\<close>
| \<open>maxFun (Imp f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Dis f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Con f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Exi f) = maxFun f\<close>
| \<open>maxFun (Uni f) = maxFun f\<close>
| \<open>maxFun (Neg f) = maxFun f\<close>

fun generate_new :: \<open>fm \<Rightarrow> fm list \<Rightarrow> nat\<close> where
\<open>generate_new p z = 1 + max (maxFun p) (foldl max 0 (map maxFun z))\<close>

(* this takes a while to check *)
fun eff' :: \<open>rule \<Rightarrow> sequent \<Rightarrow> sequent fset option\<close> where
  \<open>eff' Basic (p # z) = (if Neg p \<in> set z then Some {||} else None)\<close>
| \<open>eff' Basic [] = None\<close>
| \<open>eff' AlphaDis (Dis p q # z) = Some {| p # q # z|}\<close>
| \<open>eff' AlphaDis _ = None\<close>
| \<open>eff' AlphaImp (Imp p q # z) = Some {| Neg p # q # z|}\<close>
| \<open>eff' AlphaImp _ = None\<close>
| \<open>eff' AlphaCon (Neg (Con p q) # z) = Some {| Neg p # Neg q # z|}\<close>
| \<open>eff' AlphaCon _ = None\<close>
| \<open>eff' BetaCon (Con p q # z) = Some {| p # z, q # z |}\<close>
| \<open>eff' BetaCon _ = None\<close>
| \<open>eff' BetaImp (Neg (Imp p q) # z) = Some {| p # z, Neg q # z |}\<close>
| \<open>eff' BetaImp _ = None\<close>
| \<open>eff' BetaDis (Neg (Dis p q) # z) = Some {| Neg p # z, Neg q # z |}\<close>
| \<open>eff' BetaDis _ = None\<close>
| \<open>eff' (GammaExi t) (Exi p # z) = (if t \<noteq> Var 0 then Some {| sub 0 t p # z @ [(Exi p)]|} else None)\<close>
| \<open>eff' (GammaExi t) _ = None\<close>
| \<open>eff' (GammaUni t) (Neg (Uni p) # z) = (if t \<noteq> Var 0 then Some {| Neg (sub 0 t p) # z @ [(Neg (Uni p))]|} else None)\<close>
| \<open>eff' (GammaUni t) _ = None\<close>
| \<open>eff' DeltaUni (Uni p # z) = Some {| sub 0 (Fun (generate_new p z) []) p # z|}\<close>
| \<open>eff' DeltaUni _ = None\<close>
| \<open>eff' DeltaExi (Neg (Exi p) # z) = Some {| Neg (sub 0 (Fun (generate_new p z) []) p) # z|}\<close>
| \<open>eff' DeltaExi _ = None\<close>
| \<open>eff' NegNeg (Neg (Neg p) # z) = Some {| p # z |}\<close>
| \<open>eff' NegNeg _ = None\<close>
| \<open>eff' ExtRotate (Pre n ts # z) = (if Neg (Pre n ts) \<in> set z then None else Some {| z @ [Pre n ts] |})\<close>
| \<open>eff' ExtRotate (Neg (Pre n ts) # z) = Some {| z @ [Neg (Pre n ts)] |}\<close>
| \<open>eff' ExtRotate _ = None\<close>

text \<open>It should be enough to instantiate gamma rules with existing terms, so we need to extract those\<close>
fun subterm_tm :: \<open>tm \<Rightarrow> tm set\<close> where
  \<open>subterm_tm (Fun n ts) = insert (Fun n ts) (\<Union> (set (map subterm_tm ts)))\<close>
| \<open>subterm_tm (Var n) = {Var n}\<close>

fun subterm_fm :: \<open>fm \<Rightarrow> tm set\<close> where
  \<open>subterm_fm (Pre _ ts) = \<Union> (set (map subterm_tm ts))\<close>
| \<open>subterm_fm (Imp f1 f2) = subterm_fm f1 \<union> subterm_fm f2\<close>
| \<open>subterm_fm (Dis f1 f2) = subterm_fm f1 \<union> subterm_fm f2\<close>
| \<open>subterm_fm (Con f1 f2) = subterm_fm f1 \<union> subterm_fm f2\<close>
| \<open>subterm_fm (Exi f) = subterm_fm f\<close>
| \<open>subterm_fm (Uni f) = subterm_fm f\<close>
| \<open>subterm_fm (Neg f) = subterm_fm f\<close>

fun subterms :: \<open>sequent \<Rightarrow> tm set\<close> where
\<open>subterms s = \<Union> (set (map subterm_fm s))\<close>

text \<open>mkGamma maps a (Gamma) rule over all possible terms\<close>
abbreviation \<open>mkGamma f \<equiv> smap f single_terms\<close>

text \<open>
We will now define a stream containing the rules that the prover
will attempt to apply.
This definition is the actual proof strategy used by the prover.
\<close>
abbreviation \<open>sinterleaves \<equiv> fold sinterleave\<close>

text \<open>This does not work because each Gamma rule is only tried with a specific term once
But the same term might be needed for several Gamma rules e.g. in nested universal quantifiers\<close>
definition rules where
  \<open>rules = sinterleaves [
            sconst AlphaDis, sconst AlphaImp, sconst AlphaCon,
            sconst BetaCon, sconst BetaImp, sconst BetaDis,
            mkGamma GammaExi, mkGamma GammaUni,
            sconst DeltaUni, sconst DeltaExi,
            sconst NegNeg,
            sconst ExtRotate
           ] (sconst Basic)\<close>

text \<open>We need to prove that the prover will try every possible rule application\<close>
text \<open>This is actually unprovable right now... (see above)\<close>
lemma rules_UNIV: \<open>sset rules = (UNIV :: rule set)\<close>
  unfolding rules_def
  sorry

section \<open>Completeness\<close>

interpretation RuleSystem \<open>\<lambda>r s ss. eff' r s = Some ss\<close> rules UNIV
  unfolding rules_def RuleSystem_def
  sorry

interpretation PersistentRuleSystem \<open>\<lambda> r s ss. eff' r s = Some ss\<close> rules UNIV
  unfolding rules_def PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  sorry

definition \<open>rho \<equiv> i.fenum rules\<close>
definition \<open>secavTree \<equiv> i.mkTree eff' rho\<close>

theorem completeness:
  assumes \<open>s \<in> (UNIV :: fm list set)\<close>
  shows
    \<open>(\<exists> t. fst (root t) = s \<and> wf t \<and> tfinite t)\<or>
      (\<exists> steps. fst (shd steps) = s \<and> epath steps \<and> Saturated steps)\<close>
  by (simp add: epath_completeness_Saturated)

(*
section \<open>Soundness\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> sequent \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) [] = False\<close>
| \<open>ssemantics (e,f,g) (p # z) = semantics e f g p \<or> ssemantics (e,f,g) z\<close>

interpretation Soundness \<open>\<lambda>r s ss. eff' r s = Some ss\<close> rules UNIV ssemantics
  unfolding rules_def Soundness_def RuleSystem_def
  sorry

theorem soundness:
  assumes f: "tfinite t" and w: "wf t"
  shows "ssat (fst (root t))"

*)

end