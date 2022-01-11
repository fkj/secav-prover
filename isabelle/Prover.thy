theory Prover
  imports SeCaV
    "HOL-Library.Stream"
    Abstract_Completeness.Abstract_Completeness
    Abstract_Soundness.Finite_Proof_Soundness
    "HOL-Library.Countable"
    "HOL-Library.Code_Lazy"
begin

section \<open>Datatypes\<close>

text \<open>A sequent is a list of formulas\<close>
type_synonym sequent = \<open>fm list\<close>

text \<open>We introduce a number of rules to move between sequents\<close>
datatype rule
  = AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | DeltaUni | DeltaExi
  | NegNeg
  | GammaExi | GammaUni

section \<open>Auxiliary functions\<close>

text \<open>
Before defining what the rules do, we need to define a number of auxiliary functions needed for the
semantics of the rules.\<close>

text \<open>listFunTm is a list of function and constant names in a term\<close>
primrec listFunTm :: \<open>tm \<Rightarrow> nat list\<close>
  and listFunTms :: \<open>tm list \<Rightarrow> nat list\<close>where
  \<open>listFunTm (Fun n ts) = n # listFunTms ts\<close>
| \<open>listFunTm (Var n) = []\<close>
| \<open>listFunTms [] = []\<close>
| \<open>listFunTms (t # ts) = listFunTm t @ listFunTms ts\<close>

text \<open>generateNew uses the \<open>listFunTms\<close> function to obtain a fresh function index\<close>
definition generateNew :: \<open>tm list \<Rightarrow> nat\<close> where
  \<open>generateNew z \<equiv> 1 + foldr max (listFunTms z) 0\<close>

fun flatten :: \<open>'a list option list \<Rightarrow> 'a list option\<close> where
  \<open>flatten [] = Some []\<close>
| \<open>flatten (None # _) = None\<close>
| \<open>flatten (Some x # xs) = (case flatten xs of
                             None \<Rightarrow> None
                           | Some ys \<Rightarrow> Some (x @ ys))\<close>

text \<open>subtermTm returns a list of all terms occurring within a term\<close>
primrec subtermTm :: \<open>tm \<Rightarrow> tm list\<close> where
  \<open>subtermTm (Fun n ts) = Fun n ts # remdups (concat (map subtermTm ts))\<close>
| \<open>subtermTm (Var n) = []\<close>

text \<open>subtermFm returns a list of all terms occurring within a formula\<close>
primrec subtermFm :: \<open>fm \<Rightarrow> tm list\<close> where
  \<open>subtermFm (Pre _ ts) = concat (map subtermTm ts)\<close>
| \<open>subtermFm (Imp f1 f2) = subtermFm f1 @ subtermFm f2\<close>
| \<open>subtermFm (Dis f1 f2) = subtermFm f1 @ subtermFm f2\<close>
| \<open>subtermFm (Con f1 f2) = subtermFm f1 @ subtermFm f2\<close>
| \<open>subtermFm (Exi f) = subtermFm f\<close>
| \<open>subtermFm (Uni f) = subtermFm f\<close>
| \<open>subtermFm (Neg f) = subtermFm f\<close>

text \<open>subterms returns a list of all terms occurring within a sequent.
      This is used to determine which terms to instantiate Gamma-formulas with.
      We must always be able to instantiate Gamma-formulas, so if there are no terms in the sequent,
      the function simply returns a list containing the first function.\<close>
  (* This needs to do even more: functions of bound variables should also not be instantiated - I think?
   Check Grandfather proof to see why - it creates new free variables
   We have functions unlike Ben-Ari, so we need to handle functions of bound variables as well *)
fun subterms :: \<open>sequent \<Rightarrow> tm list\<close> where
  \<open>subterms s = (case remdups (concat (map subtermFm s)) of
                [] \<Rightarrow> [Fun 0 []]
              | ts \<Rightarrow> ts)\<close>

text \<open>We need to be able to detect if a branch can be closed by the Basic rule so we know whether
to do anything in a Basic phase or just skip it.
The section \<open>Neg (Neg p) \<in> set z\<close> is not necessary for the prover, but allows us to prove the lemma
below.\<close>
fun branchDone :: \<open>sequent \<Rightarrow> bool\<close> where
  \<open>branchDone [] = False\<close>
| \<open>branchDone (Neg p # z) = (p \<in> set z \<or> Neg (Neg p) \<in> set z \<or> branchDone z)\<close>
| \<open>branchDone (p # z) = (Neg p \<in> set z \<or> branchDone z)\<close>

lemma pinz_done: \<open>Neg p \<in> set z \<Longrightarrow> branchDone (p # z)\<close>
  by (cases p; simp)

lemma branchDone: \<open>p \<in> set ps \<Longrightarrow> Neg p \<in> set ps \<Longrightarrow> branchDone ps\<close>
  by (induct ps rule: branchDone.induct) auto

section \<open>Effects of rules\<close>

(* TODO: do this on fsets instead if we convert at the end anyway? *)
definition parts :: \<open>tm list \<Rightarrow> rule \<Rightarrow> fm \<Rightarrow> fm list list\<close> where
  \<open>parts A r f = (case (r, f) of
      (NegNeg, Neg (Neg p)) \<Rightarrow> [[p]]
    | (AlphaImp, Imp p q) \<Rightarrow> [[Neg p, q]]
    | (AlphaDis, Dis p q) \<Rightarrow> [[p, q]]
    | (AlphaCon, Neg (Con p q)) \<Rightarrow> [[Neg p, Neg q]]
    | (BetaImp, Neg (Imp p q)) \<Rightarrow> [[p], [Neg q]]
    | (BetaDis, Neg (Dis p q)) \<Rightarrow> [[Neg p], [Neg q]]
    | (BetaCon, Con p q) \<Rightarrow> [[p], [q]]
    | (DeltaExi, Neg (Exi p)) \<Rightarrow> [[Neg (sub 0 (Fun (generateNew A) []) p)]]
    | (DeltaUni, Uni p) \<Rightarrow> [[sub 0 (Fun (generateNew A) []) p]]
    | (GammaExi, Exi p) \<Rightarrow> [Exi p # map (\<lambda>t. sub 0 t p) A]
    | (GammaUni, Neg (Uni p)) \<Rightarrow> [Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A]
    | _ \<Rightarrow> [[f]])\<close>

primrec list_prod :: \<open>'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close> where
  \<open>list_prod _ [] = []\<close>
| \<open>list_prod hs (t # ts) = map (\<lambda>h. h @ t) hs @ list_prod hs ts\<close>

lemma list_prod_is_cartesian: \<open>set (list_prod hs ts) = {h @ t |h t. h \<in> set hs \<and> t \<in> set ts}\<close>
  by (induct ts) auto

primrec effect' :: \<open>tm list \<Rightarrow> rule \<Rightarrow> sequent \<Rightarrow> sequent list\<close> where
  \<open>effect' _ _ [] = [[]]\<close>
| \<open>effect' A r (f # z) = list_prod (parts A r f) (effect' A r z)\<close>

type_synonym state = \<open>tm list \<times> sequent\<close>

primrec effect :: \<open>rule \<Rightarrow> state \<Rightarrow> state fset\<close> where
  \<open>effect r (A, s) =
  (if branchDone s then {||} else
    fimage (\<lambda>s'. (remdups (A @ subterms s @ subterms s'), s')) (fset_of_list (effect' A r s)))\<close>

section \<open>The rule stream\<close>

text \<open>Then the rule stream is just all rules in the order: Alpha, Delta, Beta, Gamma (with Basic rules in between each Alpha, Delta and Beta rule).\<close>
definition \<open>rulesList \<equiv> [
  NegNeg, AlphaImp, AlphaDis, AlphaCon,
  DeltaExi, DeltaUni,
  BetaImp, BetaDis, BetaCon,
  GammaExi, GammaUni
]\<close>

text \<open>By cycling the list of all rules we obtain an infinite stream with every rule occurring
infinitely often.\<close>
definition rules where
  \<open>rules = cycle rulesList\<close>

section \<open>Abstract completeness\<close>

definition eff where
  \<open>eff \<equiv> \<lambda>r s ss. effect r s = ss\<close>

definition \<open>valid_states \<equiv> {(A, ps) |A ps. (\<Union>p \<in> set ps. set (subtermFm p)) \<subseteq> set A}\<close>

lemma all_rules_enabled: \<open>\<forall>st. \<forall>r \<in> i.R (cycle rulesList). \<exists>sl. eff r st sl\<close>
  unfolding eff_def by blast

lemma woop: \<open>st |\<in>| effect r (A, ps) \<Longrightarrow> st \<in> valid_states\<close>
  unfolding valid_states_def oops

interpretation RuleSystem eff rules UNIV (* valid_states *)
  unfolding rules_def RuleSystem_def
  using all_rules_enabled stream.set_sel(1)
  (* oops by (metis (full_types) eff_def prod.collapse) *)
  by blast

interpretation PersistentRuleSystem eff rules UNIV
  unfolding PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  by (metis all_rules_enabled enabled_def fair_fenum iso_tuple_UNIV_I per_def rules_def trim_in_R)

section \<open>The prover function\<close>
definition \<open>secavProver \<equiv> mkTree rules\<close>

end
