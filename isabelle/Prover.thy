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

text \<open>Our prover will work in a number of phases, which we define here and explain later\<close>
datatype phase = PBasic | PABD | PPrepGamma nat \<open>tm list\<close> | PInstGamma nat \<open>tm list\<close> \<open>tm list\<close> bool

text \<open>A proof state is a pair containing a sequent and a phase\<close>
type_synonym state = \<open>sequent \<times> phase\<close>

text \<open>We introduce a number of pseudo-rules to move between proof states\<close>
datatype PseudoRule =
  Basic
  | AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | DeltaUni | DeltaExi
  | NegNeg
  | GammaExi | GammaUni
  | Rotate
  | Duplicate
  | Next

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

text \<open>This function simply flattens a list of lists into a list\<close>
primrec flatten :: \<open>'a list list \<Rightarrow> 'a list\<close> where
  \<open>flatten [] = []\<close>
| \<open>flatten (l # ls) = l @ flatten ls\<close>

text \<open>subtermTm returns a list of all terms occurring within a term\<close>
fun subtermTm :: \<open>nat \<Rightarrow> tm \<Rightarrow> tm list\<close> where
  \<open>subtermTm q (Fun n ts) = (Fun n ts) # (remdups (flatten (map (subtermTm q) ts)))\<close>
| \<open>subtermTm q (Var n) = (if n \<ge> q then [Var n] else [])\<close>

text \<open>subtermFm returns a list of all terms occurring within a formula\<close>
fun subtermFm :: \<open>nat \<Rightarrow> fm \<Rightarrow> tm list\<close> where
  \<open>subtermFm q (Pre _ ts) = remdups (flatten (map (subtermTm q) ts))\<close>
| \<open>subtermFm q (Imp f1 f2) = remdups (subtermFm q f1 @ subtermFm q f2)\<close>
| \<open>subtermFm q (Dis f1 f2) = remdups (subtermFm q f1 @ subtermFm q f2)\<close>
| \<open>subtermFm q (Con f1 f2) = remdups (subtermFm q f1 @ subtermFm q f2)\<close>
| \<open>subtermFm q (Exi f) = subtermFm (q + 1) f\<close>
| \<open>subtermFm q (Uni f) = subtermFm (q + 1) f\<close>
| \<open>subtermFm q (Neg f) = subtermFm q f\<close>

text \<open>subterms returns a list of all terms occurring within a sequent.
      This is used to determine which terms to instantiate Gamma-formulas with.
      We must always be able to instantiate Gamma-formulas, so if there are no terms in the sequent,
      the function simply returns a list containing the first function.\<close>
  (* This needs to do even more: functions of bound variables should also not be instantiated - I think?
   Check Grandfather proof to see why - it creates new free variables
   We have functions unlike Ben-Ari, so we need to handle functions of bound variables as well *)
fun subterms :: \<open>sequent \<Rightarrow> tm list\<close> where
  \<open>subterms s = (case remdups (flatten (map (subtermFm 0) s)) of
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

section \<open>Effects of pseudo-rules\<close>

text \<open>The effect function specifies the effect of each pseudo-rule\<close>
fun effect :: \<open>PseudoRule \<Rightarrow> state \<Rightarrow> state fset option\<close> where
  (* Basic phase *)
  (* The Basic rule is only enabled if it completes the proof branch *)
  \<open>effect Basic state = (case state of
                          ((p # z), PBasic) \<Rightarrow> (if Neg p \<in> set z then Some {||} else None)
                        | (_, _) \<Rightarrow> None)\<close>
  (* The Rotate pseudo-rule is only enabled if the Basic rule will eventually become enabled by rotating *)
  (* It moves the first formula to the end of the sequent *)

(* The Rotate pseudo-rule is enabled if none of the ABD rules match the current first formula, but some other formulas do *)
(* It is disabled if no more ABD rules match anywhere in the sequent, as computed by the predicate abdDone *)
(* It is also disabled if any ABD rule matches the current first formula, which can be computed by the abdDone predicate with the "sequent" consisting only of p *)
(* The pseudo-rule simply moves the first formula to the end of the sequent *)

(* Empty sequents are unprovable, so we just disable the rule *)
| \<open>effect Rotate state = (case state of
                           (p # z, PBasic) \<Rightarrow> (if branchDone (p # z) \<and> Neg p \<notin> set z
                                               then Some {| (z @ [p], PBasic) |} else None)
                         | (p # z, PABD) \<Rightarrow> (if abdDone (p # z) then None else
                                              (if abdDone [p]
                                               then Some {| (z @ [p], PABD) |} else None))
                         | ((Exi p) # _, PPrepGamma _ _) \<Rightarrow> None
                         | ((Neg (Uni p)) # _, PPrepGamma _ _) \<Rightarrow> None
                         | (p # z, PPrepGamma n ts) \<Rightarrow>
                              (if n = 0 then None else Some {| (z @ [p], PPrepGamma (n - 1) ts) |})
                         | (p # z, PInstGamma n ots ts True) \<Rightarrow>
                              Some {| (z @ [p], PInstGamma n ots ts False) |}
                         | (_, PInstGamma _ _ _ False) \<Rightarrow> None
                         | ([], _) \<Rightarrow> None)\<close>
  (* The Next pseudo-rule advances to an ABD phase if the Basic rule can not be applied even after rotations *)
  (* The rule is disabled if it is possible to end the branch here *)

(* The Next pseudo-rule advances to a Gamma phase if no more ABD rules can be applied to the sequent, as computed by the predicate abdDone *)
(* When we advance, we start off with the length of the sequent as fuel count and put the current existing terms into the state as well *)
(* The rule is disabled as long as it is still possible to apply an ABD rule somewhere in the sequent *)
(* If the sequent is empty, we just go to the next phase immediately (this is only relevant for the completeness proof) *)
(* The patterns with specific formulas will never be used, and are just for the completeness proof *)
| \<open>effect Next state = (case state of
                         (s, PBasic) \<Rightarrow> (if branchDone s then None else Some {| (s, PABD) |})
                       | (s, PABD) \<Rightarrow> (if abdDone s
                                       then Some {| (s, PPrepGamma (length s) (subterms s)) |}
                                       else None)
                       | ([], PPrepGamma n _) \<Rightarrow> Some {| ([], PBasic) |}
                       | (s, PPrepGamma n _) \<Rightarrow> (if n = 0 then Some {| (s, PBasic) |} else None)
                       | (s, PInstGamma n ots [] False) \<Rightarrow> Some {| (s, PPrepGamma (n - 1) ots) |}
                       | (Pre _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Imp _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Dis _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Con _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Uni _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Pre _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Imp _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Dis _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Con _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Exi _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Neg _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow>
                            Some {| ([], PPrepGamma (n - 1) ots) |}
                       | ([], PInstGamma n ots _ _) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (_, PInstGamma _ _ _ _) \<Rightarrow> None)\<close>
  (* ABD phase *)
  (* Each ABD rule is enabled if the current first formula matches its pattern and disabled otherwise*)
  (* The ABD rule patterns are all mutually exclusive, so the order does not matter *)
  (* After each ABD rule we move back to the Basic phase to check whether we are done with the proof branch *) 
| \<open>effect AlphaDis state = (case state of
                             ((Dis p q # z), PABD) \<Rightarrow> Some {| (p # q # z, PBasic) |}
                           |(_, _) \<Rightarrow> None)\<close>
| \<open>effect AlphaImp state = (case state of
                             ((Imp p q # z), PABD) \<Rightarrow> Some {| (Neg p # q # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect AlphaCon state = (case state of
                             ((Neg (Con p q) # z), PABD) \<Rightarrow> Some {| (Neg p # Neg q # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect BetaCon state = (case state of
                            ((Con p q # z), PABD) \<Rightarrow> Some {| (p # z, PBasic) , (q # z, PBasic) |}
                          | (_, _) \<Rightarrow> None)\<close>
| \<open>effect BetaImp state = (case state of
                            ((Neg (Imp p q) # z), PABD) \<Rightarrow>
                                Some {| (p # z, PBasic) , (Neg q # z, PBasic) |}
                          | (_, _) \<Rightarrow> None)\<close>
| \<open>effect BetaDis state = (case state of
                            ((Neg (Dis p q) # z), PABD) \<Rightarrow>
                                Some {| (Neg p # z, PBasic), (Neg q # z, PBasic) |}
                          | (_, _) \<Rightarrow> None)\<close>
| \<open>effect DeltaUni state = (case state of
                             ((Uni p # z), PABD) \<Rightarrow>
                                Some {| (sub 0 (Fun (generateNew p z) []) p # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect DeltaExi state = (case state of
                             ((Neg (Exi p) # z), PABD) \<Rightarrow>
                                Some {| (Neg (sub 0 (Fun (generateNew p z) []) p) # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect NegNeg state = (case state of
                           ((Neg (Neg p) # z), PABD) \<Rightarrow> Some {| (p # z, PBasic) |}
                         | (_, _) \<Rightarrow> None)\<close>
  (* PreGamma phase *)
| \<open>effect Duplicate state = (case state of
                              (Exi p # z, PPrepGamma n ts) \<Rightarrow> (if n = 0 then None else
                                Some {| (replicate (length ts) (Exi p) @ z @ [Exi p],
                                        PInstGamma n ts ts False) |})
                            | ((Neg (Uni p)) # z, PPrepGamma n ts) \<Rightarrow> (if n = 0 then None else
                                Some {| (replicate (length ts) (Neg (Uni p)) @ z @ [Neg (Uni p)],
                                        PInstGamma n ts ts False) |})
                            | _ \<Rightarrow> None)\<close>
  (* InstGamma phase *)
  (* The bool is used to know whether we have just instantiated and need to rotate (true) or need to instantiate (false) *)
| \<open>effect GammaExi state = (case state of
                             (Exi p # z, PInstGamma n ots (t # ts) False) \<Rightarrow>
                                Some {| (sub 0 t p # z, PInstGamma n ots ts True) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect GammaUni state = (case state of
                             (Neg (Uni p) # z, PInstGamma n ots (t # ts) False) \<Rightarrow>
                                Some {| (Neg (sub 0 t p) # z, PInstGamma n ots ts True) |}
                           | (_, _) \<Rightarrow> None)\<close>

section \<open>The rule stream\<close>

text \<open>Then the rule stream is just all rules in any order (since the actual order is enforced by the effect relation).\<close>
definition rulesList where
  \<open>rulesList = [ Basic,
      AlphaDis, AlphaImp, AlphaCon, BetaCon, BetaImp, BetaDis, DeltaUni, DeltaExi, NegNeg,
      GammaExi, GammaUni,
      Rotate, Duplicate, Next]\<close>

text \<open>By cycling the list of all rules we obtain an infinite stream with every rule occurring
infinitely often.\<close>
definition rules where
  \<open>rules = cycle rulesList\<close>

section \<open>Abstract completeness\<close>

definition eff where
  \<open>eff \<equiv> \<lambda>r s ss. effect r s = Some ss\<close>

lemma at_least_one_enabled: \<open>\<forall>sequent phase. \<exists>r \<in> i.R (cycle rulesList). \<exists>sl. eff r (sequent,phase) sl\<close>
proof (intro allI)
  fix sequent phase
  show \<open>\<exists>r\<in>i.R (cycle rulesList). \<exists>sl. eff r (sequent, phase) sl\<close>
  proof (induct phase)
    case PBasic
    then show ?case unfolding eff_def
    proof (induct sequent)
      case Nil
      then show ?case unfolding rulesList_def by simp
    next
      case (Cons p z)
      then show ?case
      proof (cases \<open>branchDone (p # z)\<close>)
        case bd: True
        show ?thesis
        proof (cases \<open>Neg p \<notin> set z\<close>)
          case neg: True
          then show ?thesis
          proof -
            have \<open>Rotate \<in> i.R (cycle rulesList)\<close>
              unfolding rulesList_def by simp
            moreover have \<open>effect Rotate (p # z, PBasic) = Some {| (z @ [p], PBasic) |}\<close>
              using bd neg
            proof (cases p)
              case (Neg q)
              with neg bd show ?thesis by (cases q) simp_all
            qed simp_all
            ultimately show ?thesis unfolding rulesList_def by simp
          qed
        next
          case False
          then show ?thesis unfolding rulesList_def by simp
        qed
      next
        case False
        then show ?thesis unfolding rulesList_def
          by (simp split: fm.splits)
      qed
    qed
  next
    case PABD
    then show ?case unfolding rulesList_def eff_def
    proof (induct sequent)
      case Nil
      show ?case by simp
    next
      case (Cons p z)
      show ?case
      proof (cases p)
        case (Neg q)
        then show ?thesis
          by (cases q) simp_all
      qed simp_all
    qed
  next
    case (PPrepGamma n ts)
    then show ?case unfolding eff_def
    proof (induct n)
      case 0
      then show ?case unfolding rulesList_def
        by (cases sequent; simp split: fm.splits)
    next
      case n': (Suc n')
      then show ?case
      proof (cases sequent)
        case p: Nil
        then show ?thesis unfolding p rulesList_def by simp
      next
        case (Cons p z)
        then show ?thesis
        proof simp
          show \<open>\<exists>r\<in>i.R (cycle rulesList).
                    \<exists>sl. effect r (p # z, PPrepGamma (Suc n') ts) = Some sl\<close>
          proof (cases p)
            case p: (Neg q)
            then show ?thesis unfolding rulesList_def
              by (cases q) simp_all
          qed (unfold rulesList_def, simp_all)
        qed
      qed
    qed
  next
    case (PInstGamma n ots ts b)
    then show ?case unfolding eff_def
    proof (induct ts)
      case Nil
      then show ?case unfolding rulesList_def
        by (cases b; cases sequent; simp split: list.splits fm.splits bool.splits)
    next
      case (Cons t ts')
      then show ?case
      proof (cases b)
        case bt: True
        then show ?thesis unfolding rulesList_def
          by (cases sequent; simp add: bt split: fm.splits)
      next
        case bf: False
        then show ?thesis
        proof (cases sequent)
          case Nil
          then show ?thesis unfolding rulesList_def
            by (simp add: bf)
        next
          case ss: (Cons p z)
          then show ?thesis
          proof (cases p)
            case pneg: (Neg q)
            then show ?thesis unfolding rulesList_def
              by (cases q; simp add: bf ss pneg)
          qed (unfold rulesList_def, simp_all add: bf ss)
        qed
      qed
    qed
  qed
qed

interpretation RuleSystem eff rules UNIV
  unfolding rules_def RuleSystem_def
  using at_least_one_enabled
  by simp

lemma enabled_unique:
  \<open>\<forall>r sequent phase. enabled r (sequent, phase) \<longrightarrow> (\<forall>r' \<in> R - {r}. \<not> enabled r' (sequent, phase))\<close>
proof (intro allI impI)
  fix r sequent phase
  assume \<open>enabled r (sequent, phase)\<close>
  then show \<open>\<forall>r' \<in> R - {r}. \<not> enabled r' (sequent, phase)\<close>
  proof (induct phase)
    case pb: PBasic
    then show ?case
    proof (cases sequent)
      case sn: Nil
      assume r_enabled: \<open>enabled r (sequent, PBasic)\<close>
      assume \<open>sequent = []\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume empty: \<open>sequent = []\<close>
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PBasic)\<close>
        proof (rule ccontr, simp)
          assume r'_enabled: \<open>enabled r' (sequent, PBasic)\<close>
          have \<open>enabled r' ([], PBasic) \<Longrightarrow> r' = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r') simp_all
          then have \<open>r' = Next\<close> using r'_enabled empty by simp
          moreover have \<open>enabled r ([], PBasic) \<Longrightarrow> r = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r) simp_all
          ultimately show False using not_eq r_enabled empty by simp
        qed
      qed
    next
      case (Cons p z)
      fix p z
      assume r_enabled: \<open>enabled r (sequent, PBasic)\<close>
      assume content: \<open>sequent = p # z\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PBasic)\<close>
        proof (cases \<open>branchDone (p # z)\<close>)
          case bd: True
          then show ?thesis
          proof (cases \<open>Neg p \<notin> set z\<close>)
            case neg: True
            then show ?thesis
            proof -
              show \<open>\<not> enabled r' (sequent, PBasic)\<close>
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PBasic)\<close>
                have \<open>enabled r' (p # z, PBasic) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using bd neg by (induct r'; cases p; simp split: fm.splits)
                then have \<open>r' = Rotate\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PBasic) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using neg bd by (induct r; cases p; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            qed
          next
            case neg: False
            then show ?thesis
            proof -
              show \<open>\<not> enabled r' (sequent, PBasic)\<close>
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PBasic)\<close>
                have \<open>enabled r' (p # z, PBasic) \<Longrightarrow> r' = Basic\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using bd neg
                  by (induct r'; simp split: fm.splits)
                then have \<open>r' = Basic\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PBasic) \<Longrightarrow> r = Basic\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using neg bd by (induct r; cases p; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            qed
          qed
        next
          case bd: False
          then show ?thesis
          proof (cases \<open>Neg p \<notin> set z\<close>)
            case neg: True
            then show ?thesis
            proof -
              show \<open>\<not> enabled r' (sequent, PBasic)\<close>
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PBasic)\<close>
                have \<open>enabled r' (p # z, PBasic) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using bd neg by (induct r'; simp split: fm.splits)
                then have \<open>r' = Next\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PBasic) \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using neg bd by (induct r; cases p; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            qed
          next
            case neg: False
            then show ?thesis
            proof -
              show \<open>\<not> enabled r' (sequent, PBasic)\<close>
              proof (rule ccontr)
                show False using pinz_done bd neg by simp
              qed
            qed
          qed
        qed
      qed
    qed
  next
    case pabd: PABD
    then show ?case
    proof (cases sequent)
      case sn: Nil
      assume r_enabled: \<open>enabled r (sequent, PABD)\<close>
      assume \<open>sequent = []\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume empty: \<open>sequent = []\<close>
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PABD)\<close>
        proof (rule ccontr, simp)
          assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
          have \<open>enabled r' ([], PABD) \<Longrightarrow> r' = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r') simp_all
          then have \<open>r' = Next\<close> using r'_enabled empty by simp
          moreover have \<open>enabled r ([], PABD) \<Longrightarrow> r = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r) simp_all
          ultimately show False using not_eq r_enabled empty by simp
        qed
      qed
    next
      case (Cons p z)
      fix p z
      assume r_enabled: \<open>enabled r (sequent, PABD)\<close>
      assume content: \<open>sequent = p # z\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PABD)\<close>
        proof (cases p)
          case pre: (Pre n ts)
          then show ?thesis
          proof (cases \<open>abdDone (p # z)\<close>)
            case d: True
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                using d by (induct r'; simp split: fm.splits)
              then have \<open>r' = Next\<close> using r'_enabled content by simp
              moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                using d by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content by simp
            qed
          next
            case d: False
            then show ?thesis
            proof (cases \<open>abdDone [p]\<close>)
              case pd: True
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d pd by (induct r'; simp split: fm.splits)
                hence \<open>r' = Rotate\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d pd by (induct r; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            next
              case pd: False
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have notdone: \<open>\<not> abdDone [p]\<close> using pd by simp
                have \<open>abdDone [Pre n ts]\<close> by simp
                have \<open>p = Pre n ts\<close> using pre content by simp
                then have \<open>abdDone [p]\<close> by simp
                then show False using notdone by simp
              qed
            qed
          qed
        next
          case p: (Imp a b)
          show ?thesis
          proof (rule ccontr, simp)
            assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
            have \<open>enabled r' (Imp a b # z, PABD) \<Longrightarrow> r' = AlphaImp\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits)
            then have \<open>r' = AlphaImp\<close> using r'_enabled content p by simp
            moreover have \<open>enabled r (Imp a b # z, PABD) \<Longrightarrow> r = AlphaImp\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits)
            ultimately show False using not_eq r_enabled content p by simp
          qed
        next
          case p: (Dis a b)
          show ?thesis
          proof (rule ccontr, simp)
            assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
            have \<open>enabled r' (Dis a b # z, PABD) \<Longrightarrow> r' = AlphaDis\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits)
            then have \<open>r' = AlphaDis\<close> using r'_enabled content p by simp
            moreover have \<open>enabled r (Dis a b # z, PABD) \<Longrightarrow> r = AlphaDis\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits)
            ultimately show False using not_eq r_enabled content p by simp
          qed
        next
          case p: (Con a b)
          show ?thesis
          proof (rule ccontr, simp)
            assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
            have \<open>enabled r' (Con a b # z, PABD) \<Longrightarrow> r' = BetaCon\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits)
            then have \<open>r' = BetaCon\<close> using r'_enabled content p by simp
            moreover have \<open>enabled r (Con a b # z, PABD) \<Longrightarrow> r = BetaCon\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits)
            ultimately show False using not_eq r_enabled content p by simp
          qed
        next
          case p: (Exi q)
          then show ?thesis
          proof (cases \<open>abdDone (p # z)\<close>)
            case d: True
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                using d by (induct r'; simp split: fm.splits)
              then have \<open>r' = Next\<close> using r'_enabled content by simp
              moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                using d by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content by simp
            qed
          next
            case d: False
            then show ?thesis
            proof (cases \<open>abdDone [p]\<close>)
              case pd: True
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d pd by (induct r'; simp split: fm.splits)
                hence \<open>r' = Rotate\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d pd by (induct r; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            next
              case pd: False
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have notdone: \<open>\<not> abdDone [p]\<close> using pd by simp
                have \<open>abdDone [Exi q]\<close> by simp
                have \<open>p = Exi q\<close> using content p by simp
                then have \<open>abdDone [p]\<close> by simp
                then show False using notdone by simp
              qed
            qed
          qed
        next
          case p: (Uni q)
          show ?thesis
          proof (rule ccontr, simp)
            assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
            have \<open>enabled r' (Uni q # z, PABD) \<Longrightarrow> r' = DeltaUni\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits)
            then have \<open>r' = DeltaUni\<close> using r'_enabled content p by simp
            moreover have \<open>enabled r (Uni q # z, PABD) \<Longrightarrow> r = DeltaUni\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits)
            ultimately show False using not_eq r_enabled content p by simp
          qed
        next
          case p: (Neg q)
          then show ?thesis
          proof (cases q)
            case q: (Pre n ts)
            then show ?thesis
            proof (cases \<open>abdDone (p # z)\<close>)
              case d: True
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d by (induct r'; simp split: fm.splits)
                then have \<open>r' = Next\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d by (induct r; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            next
              case d: False
              then show ?thesis
              proof (cases \<open>abdDone [p]\<close>)
                case pd: True
                show ?thesis
                proof (rule ccontr, simp)
                  assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                  have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Rotate\<close>
                    unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                    using d pd by (induct r'; simp split: fm.splits)
                  hence \<open>r' = Rotate\<close> using r'_enabled content by simp
                  moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Rotate\<close>
                    unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                    using d pd by (induct r; simp split: fm.splits)
                  ultimately show False using not_eq r_enabled content by simp
                qed
              next
                case pd: False
                show ?thesis
                proof (rule ccontr, simp)
                  assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                  have notdone: \<open>\<not> abdDone [p]\<close> using pd by simp
                  have \<open>abdDone [Pre n ts]\<close> by simp
                  have \<open>p = Neg (Pre n ts)\<close> using p q content by simp
                  then have \<open>abdDone [p]\<close> by simp
                  then show False using notdone by simp
                qed
              qed
            qed
          next
            case q: (Imp a b)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (Neg (Imp a b) # z, PABD) \<Longrightarrow> r' = BetaImp\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits)
              then have \<open>r' = BetaImp\<close> using r'_enabled content p q by simp
              moreover have \<open>enabled r (Neg (Imp a b) # z, PABD) \<Longrightarrow> r = BetaImp\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content p q by simp
            qed
          next
            case q: (Dis a b)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (Neg (Dis a b) # z, PABD) \<Longrightarrow> r' = BetaDis\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits)
              then have \<open>r' = BetaDis\<close> using r'_enabled content p q by simp
              moreover have \<open>enabled r (Neg (Dis a b) # z, PABD) \<Longrightarrow> r = BetaDis\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content p q by simp
            qed
          next
            case q: (Con a b)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (Neg (Con a b) # z, PABD) \<Longrightarrow> r' = AlphaCon\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits)
              then have \<open>r' = AlphaCon\<close> using r'_enabled content p q by simp
              moreover have \<open>enabled r (Neg (Con a b) # z, PABD) \<Longrightarrow> r = AlphaCon\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content p q by simp
            qed
          next
            case q: (Exi a)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (Neg (Exi a) # z, PABD) \<Longrightarrow> r' = DeltaExi\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits)
              then have \<open>r' = DeltaExi\<close> using r'_enabled content p q by simp
              moreover have \<open>enabled r (Neg (Exi a) # z, PABD) \<Longrightarrow> r = DeltaExi\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content p q by simp
            qed
          next
            case q: (Uni a)
            then show ?thesis
            proof (cases \<open>abdDone (p # z)\<close>)
              case d: True
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d by (induct r'; simp split: fm.splits)
                then have \<open>r' = Next\<close> using r'_enabled content by simp
                moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  using d by (induct r; simp split: fm.splits)
                ultimately show False using not_eq r_enabled content by simp
              qed
            next
              case d: False
              then show ?thesis
              proof (cases \<open>abdDone [p]\<close>)
                case pd: True
                show ?thesis
                proof (rule ccontr, simp)
                  assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                  have \<open>enabled r' (p # z, PABD) \<Longrightarrow> r' = Rotate\<close>
                    unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                    using d pd by (induct r'; simp split: fm.splits)
                  hence \<open>r' = Rotate\<close> using r'_enabled content by simp
                  moreover have \<open>enabled r (p # z, PABD) \<Longrightarrow> r = Rotate\<close>
                    unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                    using d pd by (induct r; simp split: fm.splits)
                  ultimately show False using not_eq r_enabled content by simp
                qed
              next
                case pd: False
                show ?thesis
                proof (rule ccontr, simp)
                  assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
                  have notdone: \<open>\<not> abdDone [p]\<close> using pd by simp
                  have \<open>abdDone [Neg (Uni a)]\<close> by simp
                  have \<open>p = Neg (Uni a)\<close> using p q content by simp
                  then have \<open>abdDone [p]\<close> by simp
                  then show False using notdone by simp
                qed
              qed
            qed
          next
            case q: (Neg a)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PABD)\<close>
              have \<open>enabled r' (Neg (Neg a) # z, PABD) \<Longrightarrow> r' = NegNeg\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits)
              then have \<open>r' = NegNeg\<close> using r'_enabled content p q by simp
              moreover have \<open>enabled r (Neg (Neg a) # z, PABD) \<Longrightarrow> r = NegNeg\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits)
              ultimately show False using not_eq r_enabled content p q by simp
            qed
          qed
        qed
      qed
    qed
  next
    case pprep: (PPrepGamma n ts)
    then show ?case
    proof (cases sequent)
      case sn: Nil
      assume r_enabled: \<open>enabled r (sequent, PPrepGamma n ts)\<close>
      assume \<open>sequent = []\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume empty: \<open>sequent = []\<close>
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PPrepGamma n ts)\<close>
        proof (rule ccontr, simp)
          assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
          have \<open>enabled r' ([], PPrepGamma n ts) \<Longrightarrow> r' = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r') simp_all
          then have \<open>r' = Next\<close> using r'_enabled empty by simp
          moreover have \<open>enabled r ([], PPrepGamma n ts) \<Longrightarrow> r = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r) simp_all
          ultimately show False using not_eq r_enabled empty by simp
        qed
      qed
    next
      case (Cons p z)
      assume r_enabled: \<open>enabled r (sequent, PPrepGamma n ts)\<close>
      assume \<open>sequent = p # z\<close>
      then show ?thesis
      proof (intro ballI)
        fix r'
        assume content: \<open>sequent = p # z\<close>
        assume not_eq: \<open>r' \<in> R - {r}\<close>
        show \<open>\<not> enabled r' (sequent, PPrepGamma n ts)\<close>
        proof (cases n)
          case 0
          assume n0: \<open>n = 0\<close>
          show ?thesis
          proof (rule ccontr, simp)
            assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
            have \<open>enabled r' (sequent, PPrepGamma 0 ts) \<Longrightarrow> r' = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits list.splits)
            moreover have \<open>enabled r' (sequent, PPrepGamma 0 ts)\<close> using r'_enabled n0 by simp
            ultimately have \<open>r' = Next\<close> using content r'_enabled n0 by simp
            moreover have \<open>enabled r (sequent, PPrepGamma 0 ts) \<Longrightarrow> r = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits list.splits)
            ultimately show False using not_eq r_enabled content n0 by simp
          qed
        next
          case n': (Suc n')
          then show ?thesis
          proof (cases p)
            case p: (Pre pn pts)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Pre pn pts # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Pre pn pts # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Pre pn pts # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Pre pn pts # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Imp f1 f2)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Imp f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Imp f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Imp f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Imp f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Dis f1 f2)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Dis f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Dis f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Dis f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Dis f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Con f1 f2)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Con f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Con f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Con f1 f2 # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Con f1 f2 # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Exi q)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Exi q # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Duplicate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Exi q # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Duplicate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Exi q # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Duplicate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Exi q # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Uni q)
            show ?thesis
            proof (rule ccontr, simp)
              assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
              have \<open>enabled r' (Uni q # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r') simp_all
              moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                using r'_enabled n' content by simp
              then have \<open>enabled r' (Uni q # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
              moreover have \<open>enabled r (Uni q # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r) simp_all
              moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                using r_enabled n' content by simp
              then have \<open>enabled r (Uni q # z, PPrepGamma (Suc n') ts)\<close>
                using p by simp
              ultimately show False using not_eq r_enabled content n' by simp
            qed
          next
            case p: (Neg q)
            then show ?thesis
            proof (cases q)
              case q: (Pre pn pts)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Pre pn pts) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Pre pn pts) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Pre pn pts) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Pre pn pts) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
            qed
            next
              case q: (Imp a b)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Imp a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Imp a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Imp a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Imp a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            next
              case q: (Dis a b)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Dis a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Dis a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Dis a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Dis a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            next
              case q: (Con a b)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Con a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Con a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Con a b) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Con a b) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            next
              case q: (Exi a)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Exi a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Exi a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Exi a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Exi a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            next
              case q: (Uni a)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Uni a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Duplicate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Uni a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Duplicate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Uni a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Duplicate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Uni a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            next
              case q: (Neg a)
              show ?thesis
              proof (rule ccontr, simp)
                assume r'_enabled: \<open>enabled r' (sequent, PPrepGamma n ts)\<close>
                have \<open>enabled r' (Neg (Neg a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r' = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r') simp_all
                moreover have \<open>enabled r' (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r'_enabled n' content by simp
                then have \<open>enabled r' (Neg (Neg a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately have \<open>r' = Rotate\<close> using content r'_enabled n' by simp
                moreover have \<open>enabled r (Neg (Neg a) # z, PPrepGamma (Suc n') ts) \<Longrightarrow> r = Rotate\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r) simp_all
                moreover have \<open>enabled r (p # z, PPrepGamma (Suc n') ts)\<close>
                  using r_enabled n' content by simp
                then have \<open>enabled r (Neg (Neg a) # z, PPrepGamma (Suc n') ts)\<close>
                  using p q by simp
                ultimately show False using not_eq r_enabled content n' by simp
              qed
            qed
          qed
        qed
      qed
    qed
  next
    case (PInstGamma n ots ts b)
    then show ?case
    proof (cases sequent)
      case Nil
      assume r_enabled: \<open>enabled r (sequent, PInstGamma n ots ts b)\<close>
      assume empty: \<open>sequent = []\<close>
      show ?thesis
      proof (cases b)
        case b: True
        show ?thesis
        proof (rule ccontr, safe)
          fix r'
          assume not_eq: \<open>r' \<noteq> r\<close>
          assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
          have \<open>enabled r' ([], PInstGamma n ots ts True) \<Longrightarrow> r' = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r'; simp split: fm.splits list.splits)
          then have \<open>r' = Next\<close> using r'_enabled empty b by simp
          moreover have \<open>enabled r ([], PInstGamma n ots ts True) \<Longrightarrow> r = Next\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r; simp split: fm.splits list.splits)
          ultimately show False using not_eq r_enabled empty b by simp
        qed
      next
        case b: False
        show ?thesis
        proof (cases ts)
          case Nil
          assume ts_empty: \<open>ts = []\<close>
          show ?thesis
          proof (rule ccontr, safe)
            fix r'
            assume not_eq: \<open>r' \<noteq> r\<close>
            assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
            have \<open>enabled r' ([], PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits list.splits)
            then have \<open>r' = Next\<close> using r'_enabled empty ts_empty b
              by simp
            moreover have \<open>enabled r ([], PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits list.splits)
            ultimately show False using not_eq r_enabled empty ts_empty b
              by simp
          qed
        next
          case (Cons t' ts')
          fix t' ts'
          assume ts: \<open>ts = t' # ts'\<close>
          show ?thesis
          proof (rule ccontr, safe)
            fix r'
            assume not_eq: \<open>r' \<noteq> r\<close>
            assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
            have \<open>enabled r' ([], PInstGamma n ots ts False) \<Longrightarrow> r' = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r'; simp split: fm.splits list.splits)
            then have \<open>r' = Next\<close> using r'_enabled empty ts b
              by simp
            moreover have \<open>enabled r ([], PInstGamma n ots ts False) \<Longrightarrow> r = Next\<close>
              unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
              by (induct r; simp split: fm.splits list.splits)
            ultimately show False using not_eq r_enabled empty ts b
              by simp
          qed
        qed
      qed
    next
      case (Cons p z)
      fix p z
      assume r_enabled: \<open>enabled r (sequent, PInstGamma n ots ts b)\<close>
      assume content: \<open>sequent = p # z\<close>
      then show ?thesis
      proof (cases b)
        case b: True
        show ?thesis
        proof (rule ccontr, safe)
          fix r'
          assume not_eq: \<open>r' \<noteq> r\<close>
          assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
          have \<open>enabled r' (p # z, PInstGamma n ots ts True) \<Longrightarrow> r' = Rotate\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r'; simp split: fm.splits list.splits)
          then have \<open>r' = Rotate\<close> using r'_enabled content b by simp
          moreover have \<open>enabled r (p # z, PInstGamma n ots ts True) \<Longrightarrow> r = Rotate\<close>
            unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
            by (induct r; simp split: fm.splits list.splits)
          ultimately show False using not_eq r_enabled content b by simp
        qed
      next
        case b: False
        show ?thesis
        proof (cases ts)
          case Nil
          assume ts: \<open>ts = []\<close>
          show ?thesis
          proof (induct p)
            case (Pre f1 f2)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Imp f1 f2)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Dis f1 f2)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Con f1 f2)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Exi f)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Uni f)
            show ?case
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (p # z, PInstGamma n ots [] False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts by simp
              moreover have \<open>enabled r (p # z, PInstGamma n ots [] False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts by simp
            qed
          next
            case (Neg f)
            then show ?case by (induct f) simp_all
          qed
        next
          case (Cons t' ts')
          assume ts: \<open>ts = t' # ts'\<close>
          then show ?thesis
          proof (cases p)
            case p: (Pre pn pts)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Pre pn pts # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Pre pn pts # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Imp f1 f2)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Imp f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Imp f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Dis f1 f2)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Dis f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Dis f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Con f1 f2)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Con f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Con f1 f2 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Exi f1)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Exi f1 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = GammaExi\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = GammaExi\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Exi f1 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = GammaExi\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Uni f1)
            show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Uni f1 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = Next\<close> using r'_enabled content b ts p by simp
              moreover have \<open>enabled r (Uni f1 # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p by simp
            qed
          next
            case p: (Neg q)
            then show ?thesis
            proof (cases q)
              case q: (Pre pn pts)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Pre pn pts) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Pre pn pts) # z, PInstGamma n ots (t' # ts') False)
                                  \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            next
              case q: (Imp f1 f2)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Imp f1 f2) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Imp f1 f2) # z, PInstGamma n ots (t' # ts') False)
                                  \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            next
              case q: (Dis f1 f2)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Dis f1 f2) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Dis f1 f2) # z, PInstGamma n ots (t' # ts') False)
                                  \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            next
              case q: (Con f1 f2)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Con f1 f2) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Con f1 f2) # z, PInstGamma n ots (t' # ts') False)
                                  \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            next
              case q: (Exi f1)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Exi f1) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Exi f1) # z, PInstGamma n ots (t' # ts') False)
                                  \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            next
              case q: (Uni f1)
              show ?thesis
            proof (rule ccontr, safe)
              fix r'
              assume not_eq: \<open>r' \<noteq> r\<close>
              assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
              have \<open>enabled r' (Neg (Uni f1) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = GammaUni\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r'; simp split: fm.splits list.splits)
              then have \<open>r' = GammaUni\<close> using r'_enabled content b ts p q by simp
              moreover have \<open>enabled r (Neg (Uni f1) # z, PInstGamma n ots (t' # ts') False)
                                \<Longrightarrow> r = GammaUni\<close>
                unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                by (induct r; simp split: fm.splits list.splits)
              ultimately show False using not_eq r_enabled content b ts p q by simp
            qed
            next
              case q: (Neg f1)
              show ?thesis
              proof (rule ccontr, safe)
                fix r'
                assume not_eq: \<open>r' \<noteq> r\<close>
                assume r'_enabled: \<open>enabled r' (sequent, PInstGamma n ots ts b)\<close>
                have \<open>enabled r' (Neg (Neg f1) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r' = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r'; simp split: fm.splits list.splits)
                then have \<open>r' = Next\<close> using r'_enabled content b ts p q by simp
                moreover have \<open>enabled r (Neg (Neg f1) # z, PInstGamma n ots (t' # ts') False) \<Longrightarrow> r = Next\<close>
                  unfolding enabled_def eff_def RuleSystem_Defs.enabled_def
                  by (induct r; simp split: fm.splits list.splits)
                ultimately show False using not_eq r_enabled content b ts p q by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

interpretation PersistentRuleSystem eff rules UNIV
  unfolding PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
proof (safe)
  fix sequent phase
  show \<open>\<exists>r \<in> R. \<exists>sl. eff r (sequent, phase) sl\<close>
    using enabled_R rules_def by fastforce
  fix r
  assume r_rule: \<open>r \<in> R\<close>
  show \<open>per r\<close> unfolding per_def
  proof (safe)
    fix sequent phase r' sl' sequent' phase'
    assume st: \<open>(sequent, phase) \<in> (UNIV :: state set)\<close>
    assume r_enabled: \<open>enabled r (sequent, phase)\<close>
    assume r': \<open>r' \<in> R\<close>
    assume r_not_enabled: \<open>\<not> enabled r (sequent', phase')\<close>
    assume r'_real: \<open>r' \<notin> {}\<close>
    assume r'_enabled: \<open>eff r' (sequent, phase) sl'\<close>
    assume st'_follows: \<open>(sequent', phase') |\<in>| sl'\<close>
    show \<open>r' = r\<close>
    proof (rule ccontr)
      assume noteq: \<open>r' \<noteq> r\<close>
      from r'_enabled have \<open>enabled r' (sequent, phase)\<close>
        unfolding enabled_def by fastforce
      moreover have \<open>\<forall>r' \<in> R - {r}. \<not> enabled r' (sequent, phase)\<close>
        using r_enabled enabled_unique by simp
      ultimately show False using noteq r'
        by simp
    qed
  qed
  fix sl sequent' phase'
  assume \<open>(sequent, phase) \<in> (UNIV :: state set)\<close>
  assume \<open>eff r (sequent, phase) sl\<close>
  assume \<open>(sequent', phase') |\<in>| sl\<close>
  show \<open>(sequent', phase') \<in> UNIV\<close>
    by simp
qed

section \<open>The prover function\<close>
definition \<open>secavProver \<equiv> \<lambda>x . mkTree fenum (x, PBasic)\<close>

end