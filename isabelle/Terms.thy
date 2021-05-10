theory Terms
  imports SeCaV
          "HOL-Library.Stream"
          "HOL-Library.Countable"
          "HOL-Library.Code_Lazy"
          Abstract_Completeness.Abstract_Completeness
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

end