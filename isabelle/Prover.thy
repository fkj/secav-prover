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

text \<open>maxFunTm is the largest de Bruijn index used for functions in a term\<close>
fun maxFunTm :: \<open>tm \<Rightarrow> nat\<close> where
  \<open>maxFunTm (Fun n ts) = max n (foldl max 0 (map maxFunTm ts))\<close>
| \<open>maxFunTm (Var n) = 0\<close>

text \<open>maxFun is the largest de Bruijn index used for functions in a formula\<close>
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
to do anything in a Basic phase or just skip it.\<close>
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

section \<open>Semantics of pseudo-rules\<close>

(* this takes a while to check *)
text \<open>The effect function specifies the semantics of each pseudo-rule\<close>
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
                           (p # z, PBasic) \<Rightarrow> (if branchDone (p # z) \<and> Neg p \<notin> set z then Some {| (z @ [p], PBasic) |} else None)
                         | (p # z, PABD) \<Rightarrow> (if abdDone (p # z) then None else
                                              (if abdDone [p] then Some {| (z @ [p], PABD) |} else None))
                         | ((Exi p) # _, PPrepGamma _ _) \<Rightarrow> None
                         | ((Neg (Uni p)) # _, PPrepGamma _ _) \<Rightarrow> None
                         | (p # z, PPrepGamma n ts) \<Rightarrow> (if n = 0 then None else Some {| (z @ [p], PPrepGamma (n - 1) ts) |})
                         | (p # z, PInstGamma n ots ts True) \<Rightarrow> Some {| (z @ [p], PInstGamma n ots ts False) |}
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
                       | (s, PABD) \<Rightarrow> (if abdDone s then Some {| (s, PPrepGamma (length s) (subterms s)) |} else None)
                       | ([], PPrepGamma n _) \<Rightarrow> Some {| ([], PBasic) |}
                       | (s, PPrepGamma n _) \<Rightarrow> (if n = 0 then Some {| (s, PBasic) |} else None)
                       | (s, PInstGamma n ots [] False) \<Rightarrow> Some {| (s, PPrepGamma (n - 1) ots) |}
                       | (Pre _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Imp _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Dis _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Con _ _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Uni _ # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Pre _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Imp _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Dis _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Con _ _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Exi _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
                       | (Neg (Neg _) # z, PInstGamma n ots (_ # _) False) \<Rightarrow> Some {| ([], PPrepGamma (n - 1) ots) |}
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
                            ((Neg (Imp p q) # z), PABD) \<Rightarrow> Some {| (p # z, PBasic) , (Neg q # z, PBasic) |}
                          | (_, _) \<Rightarrow> None)\<close>
| \<open>effect BetaDis state = (case state of
                            ((Neg (Dis p q) # z), PABD) \<Rightarrow> Some {| (Neg p # z, PBasic), (Neg q # z, PBasic) |}
                          | (_, _) \<Rightarrow> None)\<close>
| \<open>effect DeltaUni state = (case state of
                             ((Uni p # z), PABD) \<Rightarrow> Some {| (sub 0 (Fun (generateNew p z) []) p # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect DeltaExi state = (case state of
                             ((Neg (Exi p) # z), PABD) \<Rightarrow> Some {| (Neg (sub 0 (Fun (generateNew p z) []) p) # z, PBasic) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect NegNeg state = (case state of
                           ((Neg (Neg p) # z), PABD) \<Rightarrow> Some {| (p # z, PBasic) |}
                         | (_, _) \<Rightarrow> None)\<close>
(* PreGamma phase *)
| \<open>effect Duplicate state = (case state of
                              (Exi p # z, PPrepGamma n ts) \<Rightarrow> (if n = 0 then None else Some {| (replicate (length ts) (Exi p) @ z @ [Exi p], PInstGamma n ts ts False) |})
                            | ((Neg (Uni p)) # z, PPrepGamma n ts) \<Rightarrow> (if n = 0 then None else Some {| (replicate (length ts) (Neg (Uni p)) @ z @ [Neg (Uni p)], PInstGamma n ts ts False) |})
                            | _ \<Rightarrow> None)\<close>
(* InstGamma phase *)
(* The bool is used to know whether we have just instantiated and need to rotate (true) or need to instantiate (false) *)
| \<open>effect GammaExi state = (case state of
                             (Exi p # z, PInstGamma n ots (t # ts) False) \<Rightarrow> Some {| (sub 0 t p # z, PInstGamma n ots ts True) |}
                           | (_, _) \<Rightarrow> None)\<close>
| \<open>effect GammaUni state = (case state of
                             (Neg (Uni p) # z, PInstGamma n ots (t # ts) False) \<Rightarrow> Some {| (Neg (sub 0 t p) # z, PInstGamma n ots ts True) |}
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

interpretation RuleSystem eff rules UNIV
  unfolding rules_def RuleSystem_def
  sorry

interpretation PersistentRuleSystem \<open>\<lambda> r s ss. effect r s = Some ss\<close> rules UNIV
  unfolding rules_def PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  sorry

lemma tree_completeness:
  assumes \<open>s \<in> (UNIV :: sequent set)\<close>
  shows
    \<open>(\<exists> t. fst (fst (root t)) = s \<and> wf t \<and> tfinite t) \<or>
      (\<exists> steps. fst (fst (shd steps)) = s \<and> epath steps \<and> Saturated steps)\<close>
  using epath_completeness_Saturated fstI by fastforce


section \<open>The prover function\<close>

definition \<open>rho \<equiv> i.fenum rules\<close>
definition \<open>secavTree \<equiv> i.mkTree effect rho\<close>
definition \<open>secavProver \<equiv> \<lambda>x . secavTree (x, PBasic)\<close>


section \<open>Soundness of the prover\<close>

fun ssemantics :: \<open>(nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool\<close>
  where
  \<open>ssemantics (e,f,g) ([],_) = False\<close>
| \<open>ssemantics (e,f,g) ((p # z),phase) = (semantics e f g p \<or> ssemantics (e,f,g) (z,phase))\<close>

interpretation Soundness eff rules UNIV ssemantics
  unfolding Soundness_def RuleSystem_def
proof (safe)
  fix r sequent phase sl f g and e :: \<open>nat \<Rightarrow> 'a\<close>
  assume r_rule: \<open>r \<in> R\<close>
  assume r_enabled: \<open>eff r (sequent, phase) sl\<close>
  assume next_sound: \<open>\<forall>s'. s' |\<in>| sl \<longrightarrow> (\<forall>S \<in> UNIV. ssemantics S s')\<close>
  show \<open>ssemantics (e, f, g) (sequent, phase)\<close>
  proof (induct sequent)
    case Nil
    then show ?case sorry
(* contradiction on the assumption that we can move to a sound state when sequent is empty *)
  next
    case (Cons a sequent)
    then show ?case sorry
  qed
qed

section \<open>Completeness of the prover\<close>

(*

From here, we proceed to our main result which states that any provable formula in SeCaV
gives rise to a finite proof tree which will be found by the prover.

*)

theorem completeness:
  assumes \<open>\<tturnstile> [p]\<close>
  defines \<open>t \<equiv> secavProver [p]\<close>
  shows \<open>fst (fst (root t)) = [p] \<and> wf t \<and> tfinite t\<close>
  sorry

(*

If we have an escape path, we can obtain a countermodel which falsifies every sequent on the path <-- this is the hard part
This contradicts soundness because \<tturnstile> [p] implies that every interpretation is a model, including the interpretation which is the countermodel obtained above.
This means there cannot be an escape path, so by tree_completeness, we obtain the result.

*)

(*

Make a function that checks if a tree is finite and turns it into an inductive tree if it is.
Then the Haskell post-processing can be moved into Isabelle and maybe we can prove it sound.

*)


end