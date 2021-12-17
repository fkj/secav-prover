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
datatype rule =
  Basic
  | AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | DeltaUni | DeltaExi
  | NegNeg
  | GammaExi | GammaUni

section \<open>Auxiliary functions\<close>

text \<open>
Before defining what the rules do, we need to define a number of auxiliary functions needed for the
semantics of the rules.\<close>

text \<open>maxFunTm is the largest index used for functions in a term\<close>
fun maxFunTm :: \<open>tm \<Rightarrow> nat\<close> where
  \<open>maxFunTm (Fun n ts) = max n (foldl max 0 (map maxFunTm ts))\<close>
| \<open>maxFunTm (Var n) = 0\<close>

text \<open>maxFun is the largest index used for functions in a formula\<close>
fun maxFun :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>maxFun (Pre n ts) = foldl max 0 (map maxFunTm ts)\<close>
| \<open>maxFun (Imp f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Dis f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Con f1 f2) = max (maxFun f1) (maxFun f2)\<close>
| \<open>maxFun (Exi f) = maxFun f\<close>
| \<open>maxFun (Uni f) = maxFun f\<close>
| \<open>maxFun (Neg f) = maxFun f\<close>

text \<open>generateNew uses the maxFun function to obtain a fresh function index\<close>
fun generateNew :: \<open>fm \<Rightarrow> fm list \<Rightarrow> nat\<close> where
  \<open>generateNew p z = 1 + max (maxFun p) (foldl max 0 (map maxFun z))\<close>

fun flatten :: \<open>'a list option list \<Rightarrow> 'a list option\<close> where
  \<open>flatten [] = Some []\<close>
| \<open>flatten (None # _) = None\<close>
| \<open>flatten (Some x # xs) = (case flatten xs of
                             None \<Rightarrow> None
                           | Some ys \<Rightarrow> Some (x @ ys))\<close>

text \<open>subtermTm returns a list of all terms occurring within a term\<close>
fun subtermTm :: \<open>tm \<Rightarrow> tm list\<close> where
  \<open>subtermTm (Fun n ts) = Fun n ts # remdups (concat (map subtermTm ts))\<close>
| \<open>subtermTm (Var n) = [Var n]\<close>

text \<open>subtermFm returns a list of all terms occurring within a formula\<close>
fun subtermFm :: \<open>fm \<Rightarrow> tm list\<close> where
  \<open>subtermFm (Pre _ ts) = remdups (concat (map subtermTm ts))\<close>
| \<open>subtermFm (Imp f1 f2) = remdups (subtermFm f1 @ subtermFm f2)\<close>
| \<open>subtermFm (Dis f1 f2) = remdups (subtermFm f1 @ subtermFm f2)\<close>
| \<open>subtermFm (Con f1 f2) = remdups (subtermFm f1 @ subtermFm f2)\<close>
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

section \<open>Effects of rules\<close>

definition new_name :: \<open>tm list \<Rightarrow> nat\<close> where
  \<open>new_name A \<equiv> 1 + foldl max 0 (map maxFunTm A)\<close>

(* TODO: do this on fsets instead if we convert at the end anyway? *)
definition parts :: \<open>tm list \<Rightarrow> bool \<Rightarrow> rule \<Rightarrow> fm \<Rightarrow> sequent list\<close> where
  \<open>parts A b r f = (case (r, f) of
      (Basic, p) \<Rightarrow> (if b then [] else [[p]])
    | (NegNeg, Neg (Neg p)) \<Rightarrow> [[p]]
    | (AlphaImp, Imp p q) \<Rightarrow> [[Neg p, q]]
    | (AlphaDis, Dis p q) \<Rightarrow> [[p, q]]
    | (AlphaCon, Neg (Con p q)) \<Rightarrow> [[Neg p, Neg q]]
    | (BetaImp, Neg (Imp p q)) \<Rightarrow> [[p], [Neg q]]
    | (BetaDis, Neg (Dis p q)) \<Rightarrow> [[Neg p], [Neg q]]
    | (BetaCon, Con p q) \<Rightarrow> [[p], [q]]
    | (DeltaExi, Neg (Exi p)) \<Rightarrow> [[Neg (subst p (Fun (new_name A) []) 0)]]
    | (DeltaUni, Uni p) \<Rightarrow> [[subst p (Fun (new_name A) []) 0]]
    | (GammaExi, Exi p) \<Rightarrow> [Exi p # map (\<lambda>t. subst p t 0) A]
    | (GammaUni, Neg (Uni p)) \<Rightarrow> [Neg (Uni p) # map (\<lambda>t. Neg (subst p t 0)) A]
    | _ \<Rightarrow> [[f]])\<close>

primrec effect' :: \<open>tm list \<Rightarrow> rule \<Rightarrow> sequent \<Rightarrow> sequent list\<close> where
  \<open>effect' _ _ [] = [[]]\<close>
| \<open>effect' A r (f # z) = (let rest = effect' A r z; pss = parts A (branchDone (f # z)) r f in
    List.maps (\<lambda>s. map (\<lambda>ps. ps @ s) pss) rest)\<close>

definition effect :: \<open>rule \<Rightarrow> sequent \<Rightarrow> sequent fset option\<close> where
  \<open>effect r s = Some (fset_of_list (effect' (subterms s) r s))\<close>

section \<open>The rule stream\<close>

text \<open>Then the rule stream is just all rules in the order: Alpha, Delta, Beta, Gamma (with Basic rules in between each Alpha, Delta and Beta rule).\<close>
definition \<open>rulesList \<equiv> [
  Basic, NegNeg, AlphaImp, AlphaDis, AlphaCon,
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
  \<open>eff \<equiv> \<lambda>r s ss. effect r s = Some ss\<close>

lemma all_rules_enabled: \<open>\<forall>sequent. \<forall>r \<in> i.R (cycle rulesList). \<exists>sl. eff r sequent sl\<close>
  by (meson eff_def effect_def stream.set_sel(1))

interpretation RuleSystem eff rules UNIV
  unfolding rules_def RuleSystem_def
  using all_rules_enabled stream.set_sel(1)
  by blast

interpretation PersistentRuleSystem eff rules UNIV
  unfolding PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  by (metis all_rules_enabled enabled_def fair_fenum iso_tuple_UNIV_I per_def rules_def trim_in_R)

primrec next_rule :: \<open>rule \<Rightarrow> rule\<close> where
  \<open>next_rule Basic = NegNeg\<close>
| \<open>next_rule NegNeg = AlphaImp\<close>
| \<open>next_rule AlphaImp = AlphaDis\<close>
| \<open>next_rule AlphaDis = AlphaCon\<close>
| \<open>next_rule AlphaCon = DeltaExi\<close>
| \<open>next_rule DeltaExi = DeltaUni\<close>
| \<open>next_rule DeltaUni = BetaImp\<close>
| \<open>next_rule BetaImp = BetaDis\<close>
| \<open>next_rule BetaDis = BetaCon\<close>
| \<open>next_rule BetaCon = GammaExi\<close>
| \<open>next_rule GammaExi = GammaUni\<close>
| \<open>next_rule GammaUni = Basic\<close>

primrec rule_index :: \<open>rule \<Rightarrow> nat\<close> where
  \<open>rule_index Basic = 0\<close>
| \<open>rule_index NegNeg = 1\<close>
| \<open>rule_index AlphaImp = 2\<close>
| \<open>rule_index AlphaDis = 3\<close>
| \<open>rule_index AlphaCon = 4\<close>
| \<open>rule_index DeltaExi = 5\<close>
| \<open>rule_index DeltaUni = 6\<close>
| \<open>rule_index BetaImp = 7\<close>
| \<open>rule_index BetaDis = 8\<close>
| \<open>rule_index BetaCon = 9\<close>
| \<open>rule_index GammaExi = 10\<close>
| \<open>rule_index GammaUni = 11\<close>

lemma distinct_rulesList: \<open>distinct rulesList\<close>
  unfolding rulesList_def by simp

lemma cycle_nth: \<open>xs \<noteq> [] \<Longrightarrow> cycle xs !! n = xs ! (n mod length xs)\<close>
  by (metis cycle.sel(1) hd_rotate_conv_nth rotate_conv_mod sdrop_cycle sdrop_simps(1))

lemma nth_rule_index: \<open>rulesList ! (rule_index r) = r\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma rule_index_bnd: \<open>rule_index r < length rulesList\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma unique_rule_index:
  assumes \<open>n < length rulesList\<close> \<open>rulesList ! n = r\<close>
  shows \<open>n = rule_index r\<close>
  using assms nth_rule_index distinct_rulesList rule_index_bnd nth_eq_iff_index_eq by metis

lemma rule_index_mod:
  assumes \<open>rules !! n = r\<close>
  shows \<open>n mod length rulesList = rule_index r\<close>
proof -
  have *: \<open>rulesList ! (n mod length rulesList) = r\<close>
    using assms cycle_nth unfolding rules_def rulesList_def by (metis list.distinct(1))
  then show ?thesis
    using distinct_rulesList * unique_rule_index
    by (cases r) (metis length_greater_0_conv list.discI rulesList_def
        unique_euclidean_semiring_numeral_class.pos_mod_bound)+
qed

lemma mod_hit:
  fixes k :: nat
  assumes \<open>0 < k\<close>
  shows \<open>\<forall>i < k. \<exists>n > m. n mod k = i\<close>
proof safe
  fix i
  let ?n = \<open>(1 + m) * k + i\<close>
  assume \<open>i < k\<close>
  then have \<open>?n mod k = i\<close>
    by (metis mod_less mod_mult_self3)
  moreover have \<open>?n > m\<close>
    using assms
    by (metis One_nat_def Suc_eq_plus1_left Suc_leI add.commute add_lessD1 less_add_one
        mult.right_neutral nat_mult_less_cancel1 order_le_less trans_less_add1 zero_less_one)
  ultimately show \<open>\<exists>n > m. n mod k = i\<close>
    by fast
qed

lemma mod_suff:
  assumes \<open>\<forall>(n :: nat) > m. P (n mod k)\<close> \<open>0 < k\<close>
  shows \<open>\<forall>i < k. P i\<close>
  using assms mod_hit by blast

lemma rules_repeat: \<open>\<exists>n > m. rules !! n = r\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<exists>n > m. rules !! n = r)\<close>
  then have \<open>\<not> (\<exists>n > m. n mod length rulesList = rule_index r)\<close>
    using rule_index_mod nth_rule_index by metis
  then have \<open>\<forall>n > m. n mod length rulesList \<noteq> rule_index r\<close>
    by blast
  moreover have \<open>length rulesList > 0\<close>
    unfolding rulesList_def by simp
  ultimately have \<open>\<forall>k < length rulesList. k \<noteq> rule_index r\<close>
    using mod_suff[where P=\<open>\<lambda>a. a \<noteq> rule_index r\<close>] by blast
  then show False
    using rule_index_bnd by blast
qed

lemma rules_repeat_sdrop: \<open>\<exists>n. (sdrop k rules) !! n = r\<close>
  using rules_repeat by (metis less_imp_add_positive sdrop_snth)

lemma fair_rules: \<open>fair rules\<close>
proof -
  { fix r assume \<open>r \<in> R\<close>
    then obtain m where r: \<open>r = rules !! m\<close> unfolding sset_range by blast
    { fix n :: nat and rs let ?rules = \<open>\<lambda>n. sdrop n rules\<close>
      assume \<open>n > 0\<close>
      hence \<open>alw (ev (holds ((=) r))) (rs @- ?rules n)\<close>
      proof (coinduction arbitrary: n rs)
        case alw
        show ?case
        proof (rule exI[of _ \<open>rs @- ?rules n\<close>], safe)
          show \<open>\<exists>n' rs'. stl (rs @- ?rules n) = rs' @- ?rules n' \<and> n' > 0\<close>
          proof (cases rs)
            case Nil thus ?thesis unfolding alw
              by (metis sdrop_simps(2) shift.simps(1) zero_less_Suc)
          qed (auto simp: alw intro: exI[of _ n])
        next
          have \<open>ev (holds ((=) r)) (sdrop n rules)\<close>
            unfolding ev_holds_sset using rules_repeat_sdrop by (metis snth_sset)
          then show \<open>ev (holds ((=) r)) (rs @- sdrop n rules)\<close>
            unfolding ev_holds_sset by simp
        qed
      qed
    }
  }
  thus \<open>fair rules\<close> unfolding fair_def
    by (metis (full_types) alw_iff_sdrop ev_holds_sset neq0_conv order_refl sdrop.simps(1) stake_sdrop)
qed

section \<open>The prover function\<close>
definition \<open>secavProver \<equiv> mkTree rules\<close>

end
