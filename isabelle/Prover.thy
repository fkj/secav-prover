theory Prover
  imports SeCaV
          "HOL-Library.Stream"
          Abstract_Completeness.Abstract_Completeness
          Abstract_Soundness.Finite_Proof_Soundness
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

text \<open>It should be enough to instantiate gamma rules with existing terms, so we need to extract those\<close>
primrec flatten :: \<open>'a list list \<Rightarrow> 'a list\<close> where
  \<open>flatten [] = []\<close>
| \<open>flatten (l # ls) = l @ flatten ls\<close>

fun subterm_tm :: \<open>tm \<Rightarrow> tm list\<close> where
  \<open>subterm_tm (Fun n ts) = (Fun n ts) # (remdups (flatten (map subterm_tm ts)))\<close>
| \<open>subterm_tm (Var n) = [Var n]\<close>

fun subterm_fm :: \<open>fm \<Rightarrow> tm list\<close> where
  \<open>subterm_fm (Pre _ ts) = remdups (flatten (map subterm_tm ts))\<close>
| \<open>subterm_fm (Imp f1 f2) = remdups (subterm_fm f1 @ subterm_fm f2)\<close>
| \<open>subterm_fm (Dis f1 f2) = remdups (subterm_fm f1 @ subterm_fm f2)\<close>
| \<open>subterm_fm (Con f1 f2) = remdups (subterm_fm f1 @ subterm_fm f2)\<close>
| \<open>subterm_fm (Exi f) = subterm_fm f\<close>
| \<open>subterm_fm (Uni f) = subterm_fm f\<close>
| \<open>subterm_fm (Neg f) = subterm_fm f\<close>

fun subterms :: \<open>sequent \<Rightarrow> tm list\<close> where
\<open>subterms s = remdups (flatten (map subterm_fm s))\<close>

(*

Algorithm 7.40 adapted for SeCaV:

A proof tree is a tree where each node is labeled by a sequent consisting of a list of formulas.

Initially, the proof tree consists of a single node, the root, labeled with the formula we wish to prove.

The proof tree is built by repeatedly selecting the left-most open branch of the tree, labeled with
the list of formulas \<Gamma>, and applying the first applicable rule in the following list:

* If \<Gamma> contains a complementary pair, use the Basic rule to close the branch
* If \<Gamma> is not a set of literals, choose the first formula A in \<Gamma>
  - If A is an \<alpha>-formula, create a new node l' on the branch and label it with
         (\<Gamma> - A) \<union> {\<alpha>\<^sub>1, \<alpha>\<^sub>2}
    (we treat the Neg rule as an \<alpha>-rule with no \<alpha>\<^sub>2)

  - If A is a \<beta>-formula, create two new nodes l' and l'' on the branch and label them with
     \<Gamma>' = (\<Gamma> - A) \<union> {\<beta>\<^sub>1}
    \<Gamma>'' = (\<Gamma> - A) \<union> {\<beta>\<^sub>2}

  - If A is a \<delta>-formula, create a new node l' on the branch and label it with
         \<Gamma>' = (\<Gamma> - A) \<union> {sub 0 a' A}
    where a' is some constant that does not appear in \<Gamma> 

  - Let {\<gamma>\<^sub>1, ..., \<gamma>\<^sub>m} \<in> \<Gamma> be all of the \<gamma>-formulas in \<Gamma>.
    Let {c\<^sub>1, ..., c\<^sub>k} be all of the constants appearing in \<Gamma>.
    Create a new node l' on the branch and label it with
         \<Gamma>' = \<Gamma> \<union> {\<Union>\<^sub>i\<^sub>=\<^sub>1\<^sup>m \<Union>\<^sub>j\<^sub>=\<^sub>1\<^sup>k sub 0 c\<^sub>j \<gamma>\<^sub>i}
    However, if \<Gamma> consists only of literals and \<gamma>-formulas and if \<Gamma>' as constructed would be the
    same as \<Gamma>, do not create node l', and instead mark the branch as open.

Using meta-rules:

- Basic:
  - Applies Basic, ExtRotate until we have applied Basic to every formula in the sequent
  - After this we know that no Basic rules can be applied to any formula

- ABD:
  - For each formula in the sequent:
     - While any Alpha, Beta or Delta rule can be applied:
        - Tries to apply an Alpha rule - if this succeeds, it also applies a MBasic rule
        - Tries to apply a Beta rule - if this succeeds, it also applies a MBasic rule
        - Tries to apply a Delta rule - if this succeeds, it also applies a MBasic rule
  - After this we know that no Basic, Alpha, Beta or Delta rules can be applied to any formula

- Gamma:
  - For each formula in the sequent:
     - For each term in the sequent:
        - Tries to apply a Gamma rule instantiated with the current term

Then the rule stream goes: Basic, ABD, Gamma, \<dots>

*)

(*
  We model this algorithm by keeping track of the current phase in the proof state.
  The phase is not necessary for the actual proof, only for the search procedure.
  We introduce a new pseudo-rule Next which advances the phase, but is not part of the actual proof.

  Additionally, we collect all Gamma-rule applications into a single meta-rule called Gamma.
  This is necessary because we do not have term information at hand when constructing the rule stream.
  The Gamma meta-rule applies Gamma-rules instantiated with all existing terms to all Gamma-formulas.

  We also introduce the pseudo-rule Rotate, which is just a special case of the Ext rule, in that it
  moves the first formula in a sequent to the end.
  Multiple applications of Rotate following each other can be collapsed to a single application of
  the Ext rule.
*)

datatype phase = PBasic | PABD | PPreGamma nat \<open>tm list\<close> | PInstGamma nat \<open>tm list\<close> \<open>tm list\<close> bool

type_synonym psequent = \<open>sequent \<times> phase\<close>

datatype PseudoRule = Basic
  | AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | DeltaUni | DeltaExi
  | NegNeg
  | GammaExi | GammaUni
  | Rotate
  | Duplicate
  | Next

(*
Ideas/questions:

integrate Gamma instantiation terms into state so we know when we are done trying the actual terms
and can go on to trying the infinite stream of all terms
 - A Gamma phase should apply every term to every Gamma formula if there are any terms
 - If there are no terms left, we can move on to the infinite stream of all terms

Is it necessary to do a "full rotation" of Basic rules after every successful ABD rule?
 - For shorter proofs this is best, and we also know this to be complete from Ben-Ari's book
How can this be done?
 - We just transition back to the Basic phase after each successful application of an ABD-rule

How do we know when to advance phase with the Next rule?
Is it necessary to keep other state than the current phase and sequent?
 - Yes, we probably need to keep track of the progress through the sequent so we know when we have gone through all formulas in it for the Basic step
 - For the ABD-phase, we advance when there are no more ABD-formulas left
 - For the Gamma-phase we advance when all terms have been applied to every formula (progress needed again)
 - We introduce a counter on the Basic and Gamma phases to keep track of how many formulas are left
 - We initially set the phase counter to the length of the sequent, then count down for every application of Rotate
 - When the phase counter hits 0, we disable every other rule and enable the Next rule

In the ABD phase, how do we know when to move to the next formula? (e.g. when is Rotate allowed?)
 - When the current formula is not an ABD-formula

*)

text \<open>We need to be able to detect when no further ABD-rules can be applied so we know when to end
      an ABD phase\<close>
fun abdDone :: \<open>sequent \<Rightarrow> bool\<close> where
  \<open>abdDone (Dis _ _ # _) = False\<close>
| \<open>abdDone (Imp _ _ # _) = False\<close>
| \<open>abdDone (Neg (Con _ _) # _) = False\<close>
| \<open>abdDone (Con _ _ # _) = False\<close>
| \<open>abdDone (Neg (Imp _ _) # _) = False\<close>
| \<open>abdDone (Neg (Dis _ _) # _) = False\<close>
| \<open>abdDone (Neg (Neg _) # _) = False\<close>
| \<open>abdDone (Uni _ # _) = False\<close>
| \<open>abdDone (Neg (Exi _) # _) = False\<close>
| \<open>abdDone (_ # z) = abdDone z\<close>
| \<open>abdDone [] = True\<close>

fun branchDone :: \<open>sequent \<Rightarrow> bool\<close> where
  \<open>branchDone [] = False\<close>
| \<open>branchDone (Neg p # z) = (p \<in> set z \<or> branchDone z)\<close>
| \<open>branchDone (p # z) = (Neg p \<in> set z \<or> branchDone z)\<close>

(*
  The Gamma phase is divided into a number of iterations of two subphases.
  First is a PreGamma subphase in which the Rotate and Duplicate pseudo-rules are used to set up
  a InstGamma subphase in which the actual GammaExi and GammaUni rules are used in conjunction with
  Rotate rules to instantiate the quantified formulas in the sequent with every term in the sequent.

  In the PreGamma subphase, if we encounter a non-quantified formula, we rotate it to the back,
  while decrementing a counter to ensure that we do not instantiate the newly generated formulas.
  If we encounter a quantified formula, we instead apply a Duplicate rule to add a copy of the first
  formula in the sequent for each term in the list of terms to instantiate with and move to an InstGamma subphase.
  We also need to preserve a copy for later instantiation, and it is useful to place this at the
  end of the sequent.

  In the InstGamma subphase, we are now ready to instantiate all of the terms into a single
  quantified formula.
  We need to do this in a quite particular fashion due to the design of the GammaExi and GammaUni
  rules.
  To perform a single instantiation, we must first do the actual instantiation by applying a GammaExi or GammaUni rule.
  This will result in e.g.
    Exi p # z \<Longrightarrow> p[0/a] # z
  We then need to move the newly instantiated formula away, which we accomplish by a Rotate rule.
  This will continue a set number of times which is determined by the amount of terms we need to
  instantiate (the formulas to instantiate will have already been created in the PreGamma subphase).
  This "countdown" can be done by simply recursing on the list of terms, which then also provides
  a simple way to obtain the next term to instantiate with (always the head of the list).
  At the end of this, we will have the other formulas in the original sequent followed by the
  formula we just instantiated, followed by all of the instantiations.
  We then go back to the PreGamma subphase, decrementing the counter by one.
  
  This cycle will continue until all of the quantified formulas in the original sequent have been
  instantiated with every term, at which point the counter reaches 0.
  When this happens, we go to a Basic phase.

  Info needed for PreGamma subphase: list of terms in the original sequent, counter
  Info needed for InstGamma subphase: list of terms yet to instantiate, boolean to know if we are rotating or instantiating, counter (just for returning to the PreGamma subphase)
  
*)

(* this takes a while to check *)
fun peff' :: \<open>PseudoRule \<Rightarrow> psequent \<Rightarrow> psequent fset option\<close> where
(* Basic phase *)
(* The Basic rule is only enabled if it completes the proof branch *)
  \<open>peff' Basic ((p # z), PBasic) = (if Neg p \<in> set z then Some {||} else None)\<close>
(* Empty sequents are unprovable, so we just disable the rule *)
| \<open>peff' Basic ([], PBasic) = None\<close>
| \<open>peff' Basic (_, _) = None\<close>
(* The Rotate pseudo-rule is only enabled if the Basic rule will eventually become enabled by rotating *)
(* It moves the first formula to the end of the sequent *)
| \<open>peff' Rotate ((p # z), PBasic) = (if branchDone (p # z) \<and> Neg p \<notin> set z then Some {| (z @ [p], PBasic) |} else None)\<close>
(* Empty sequents are unprovable, so we just disable the rule *)
| \<open>peff' Rotate ([], _) = None\<close>
(* The Next pseudo-rule advances to an ABD phase if the Basic rule can not be applied even after rotations *)
(* The rule is disabled if it is possible to end the branch here *)
| \<open>peff' Next (s, PBasic) = (if branchDone s then None else Some {| (s, PABD) |})\<close>
(* ABD phase *)
(* Each ABD rule is enabled if the current first formula matches its pattern and disabled otherwise*)
(* The ABD rule patterns are all mutually exclusive, so the order does not matter *)
(* After each ABD rule we move back to the Basic phase to check whether we are done with the proof branch *) 
| \<open>peff' AlphaDis ((Dis p q # z), PABD) = Some {| (p # q # z, PBasic) |}\<close>
| \<open>peff' AlphaDis (_,_) = None\<close>
| \<open>peff' AlphaImp ((Imp p q # z), PABD) = Some {| (Neg p # q # z, PBasic) |}\<close>
| \<open>peff' AlphaImp (_,_) = None\<close>
| \<open>peff' AlphaCon ((Neg (Con p q) # z), PABD) = Some {| (Neg p # Neg q # z, PBasic) |}\<close>
| \<open>peff' AlphaCon (_,_) = None\<close>
| \<open>peff' BetaCon ((Con p q # z), PABD) = Some {| (p # z, PBasic) , (q # z, PBasic) |}\<close>
| \<open>peff' BetaCon (_,_) = None\<close>
| \<open>peff' BetaImp ((Neg (Imp p q) # z), PABD) = Some {| (p # z, PBasic) , (Neg q # z, PBasic) |}\<close>
| \<open>peff' BetaImp (_,_) = None\<close>
| \<open>peff' BetaDis ((Neg (Dis p q) # z), PABD) = Some {| (Neg p # z, PBasic), (Neg q # z, PBasic) |}\<close>
| \<open>peff' BetaDis (_,_) = None\<close>
| \<open>peff' DeltaUni ((Uni p # z), PABD) = Some {| (sub 0 (Fun (generate_new p z) []) p # z, PBasic) |}\<close>
| \<open>peff' DeltaUni (_,_) = None\<close>
| \<open>peff' DeltaExi ((Neg (Exi p) # z), PABD) = Some {| (Neg (sub 0 (Fun (generate_new p z) []) p) # z, PBasic) |}\<close>
| \<open>peff' DeltaExi (_,_) = None\<close>
| \<open>peff' NegNeg ((Neg (Neg p) # z), PABD) = Some {| (p # z, PBasic) |}\<close>
| \<open>peff' NegNeg (_,_) = None\<close>
(* The Rotate pseudo-rule is enabled if none of the ABD rules match the current first formula, but some other formulas do *)
(* It is disabled if no more ABD rules match anywhere in the sequent, as computed by the predicate abdDone *)
(* It is also disabled if any ABD rule matches the current first formula, which can be computed by the abdDone predicate with the "sequent" consisting only of p *)
(* The pseudo-rule simply moves the first formula to the end of the sequent *)
| \<open>peff' Rotate (p # z, PABD) = (if abdDone (p # z) then None else
                                    (if abdDone [p] then Some {| (z @ [p], PABD) |} else None))\<close>
(* The Next pseudo-rule advances to a Gamma phase if no more ABD rules can be applied to the sequent, as computed by the predicate abdDone *)
(* When we advance, we start off with the length of the sequent as fuel count and put the current existing terms into the state as well *)
(* The rule is disabled as long as it is still possible to apply an ABD rule somewhere in the sequent *)
| \<open>peff' Next (s, PABD) = (if abdDone s then Some {| (s, PPreGamma (length s) (subterms s)) |} else None)\<close>
(* PreGamma phase *)
| \<open>peff' Rotate ((Exi p) # _, PPreGamma _ _ ) = None\<close>
| \<open>peff' Rotate ((Neg (Uni p)) # _, PPreGamma _ _) = None\<close>
| \<open>peff' Rotate (p # z, PPreGamma n ts) = (if n = 0 then None else Some {| (z @ [p], PPreGamma (n - 1) ts) |})\<close>
| \<open>peff' Duplicate ((Exi p) # z, PPreGamma n ts) = (if n = 0 then None else Some {| (replicate (length ts) (Exi p) @ z @ [Exi p], PInstGamma n ts ts False) |})\<close>
| \<open>peff' Duplicate ((Neg (Uni p)) # z, PPreGamma n ts) = (if n = 0 then None else Some {| (replicate (length ts) (Neg (Uni p)) @ z @ [Neg (Uni p)], PInstGamma n ts ts False) |})\<close>
| \<open>peff' Duplicate _ = None\<close>
| \<open>peff' Next (s, PPreGamma n _) = (if n = 0 then Some {| (s, PBasic) |} else None)\<close>
(* InstGamma phase *)
(* The bool is used to know whether we have just instantiated and need to rotate (true) or need to instantiate (false) *)
| \<open>peff' Rotate (p # z, PInstGamma n ots ts True) = Some {| (z @ [p], PInstGamma n ots ts False) |}\<close>
| \<open>peff' Rotate (_, PInstGamma _ _ _ False) = None\<close>
| \<open>peff' GammaExi (Exi p # z, PInstGamma n ots (t # ts) False) = Some {| (sub 0 t p # z, PInstGamma n ots ts True) |}\<close>
| \<open>peff' GammaExi (_, _) = None\<close>
| \<open>peff' GammaUni (Neg (Uni p) # z, PInstGamma n ots (t # ts) False) = Some {| (Neg (sub 0 t p) # z, PInstGamma n ots ts True) |}\<close>
| \<open>peff' GammaUni (_, _) = None\<close>
| \<open>peff' Next (s, PInstGamma n ots [] False) = Some {| (s, PPreGamma (n - 1) ots) |}\<close>
| \<open>peff' Next (_, PInstGamma _ _ _ _) = None\<close>

text \<open>Then the rule stream is just all rules in any order (since the actual order is enforced by the effect relation):\<close>
definition rules where
  \<open>rules = cycle [
      Basic,
      AlphaDis, AlphaImp, AlphaCon, BetaCon, BetaImp, BetaDis, DeltaUni, DeltaExi, NegNeg,
      GammaExi, GammaUni,
      Rotate, Duplicate, Next]\<close>

section \<open>Completeness\<close>

interpretation RuleSystem \<open>\<lambda>r s ss. peff' r s = Some ss\<close> rules UNIV
  unfolding rules_def RuleSystem_def
  sorry

interpretation PersistentRuleSystem \<open>\<lambda> r s ss. peff' r s = Some ss\<close> rules UNIV
  unfolding rules_def PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  sorry

definition \<open>rho \<equiv> i.fenum rules\<close>
definition \<open>secavTree \<equiv> i.mkTree peff' rho\<close>
definition \<open>secavProver \<equiv> \<lambda>x . secavTree (x, PBasic)\<close>

lemma tree_completeness:
  assumes \<open>s \<in> (UNIV :: fm list set)\<close>
  shows
    \<open>(\<exists> t. fst (fst (root t)) = s \<and> wf t \<and> tfinite t) \<or>
      (\<exists> steps. fst (fst (shd steps)) = s \<and> epath steps \<and> Saturated steps)\<close>
  using epath_completeness_Saturated fstI by fastforce


section \<open>Soundness\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> psequent \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) ([],_) = False\<close>
| \<open>ssemantics (e,f,g) ((p # z),phase) = (semantics e f g p \<or> ssemantics (e,f,g) (z,phase))\<close>

interpretation Soundness \<open>\<lambda>r s ss. peff' r s = Some ss\<close> rules UNIV ssemantics
  unfolding rules_def Soundness_def RuleSystem_def
  sorry

(*

From here, we proceed to our main result which states that any provable formula in SeCaV
gives rise to a finite proof tree which will be found by the prover.

*)

theorem completeness:
  assumes \<open>\<tturnstile> [p]\<close> \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  sorry


end