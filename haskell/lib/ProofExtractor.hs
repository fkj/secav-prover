{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module ProofExtractor where

import Arith ( Nat(Nat), zero_nat )
import qualified Data.Bimap as Map
import Control.Monad.State (evalState, get, modify)
import Data.List (genericReplicate, intercalate)
import FSet ( Fset(Abs_fset) )
import Prover ( Rule(..), Tree(..), generateNew)
import ProverInstances()
import SeCaV ( Fm(..), Tm(..), sub )
import Set ( Set(Set, Coset) )
import ShortAST (funCount, NameGen,  NameState(existingFuns, existingPres) )

-- These are the "real" rules of SeCaV that we want to end up with
data SeCaVRule
  = RBasic
  | RAlphaDis
  | RAlphaImp
  | RAlphaCon
  | RBetaCon
  | RBetaImp
  | RBetaDis
  | RGammaExi Tm
  | RGammaUni Tm
  | RDeltaUni
  | RDeltaExi
  | RNeg
  | RExt
  deriving (Show)

instance Show (Set (Tree ([Fm], SeCaVRule))) where
  show (Set s) = show s
  show (Coset s) = show s

instance Show (Fset (Tree ([Fm], SeCaVRule))) where
  show (Abs_fset s) = show s

instance Show (Tree ([Fm], SeCaVRule)) where
  show (Node (fs, r) t) = show fs <> " " <> show r <> "\n" <> show t

-- These functions get every first and every second element of a list, respectively
-- They are used to split the cartesian product of branches from Beta rules into binary trees
first :: [a] -> [a]
first [] = []
first (x : xs) = x : second xs

second :: [a] -> [a]
second [] = []
second (x : xs) = first xs

-- Expansion of AlphaDis rule
expandAlphaDis :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandAlphaDis (Node ((terms, (f : fs)), AlphaDis) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Dis p q -> [p, q]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandAlphaDis (Node ((terms, (fs ++ applied)), AlphaDis) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RAlphaDis) (Abs_fset (Set [extRule]))

-- Expansion of AlphaCon rule
expandAlphaCon :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandAlphaCon (Node ((terms, (f : fs)), AlphaCon) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Neg (Con p q) -> [Neg p, Neg q]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandAlphaCon (Node ((terms, (fs ++ applied)), AlphaCon) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RAlphaCon) (Abs_fset (Set [extRule]))

-- Expansion of AlphaImp rule
expandAlphaImp :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandAlphaImp (Node ((terms, (f : fs)), AlphaImp) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Imp p q -> [Neg p, q]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandAlphaImp (Node ((terms, (fs ++ applied)), AlphaImp) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RAlphaImp) (Abs_fset (Set [extRule]))

-- Expansion of NegNeg rule
expandNegNeg :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandNegNeg (Node ((terms, (f : fs)), NegNeg) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Neg (Neg p) -> [p]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandNegNeg (Node ((terms, (fs ++ applied)), NegNeg) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RNeg) (Abs_fset (Set [extRule]))

-- Expansion of BetaCon rule
-- The prover creates the product of all beta rules as branches, so we need to reassemble the branches into a binary tree
expandBetaCon :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandBetaCon (Node ((terms, (Con p q : fs)), BetaCon) (Abs_fset (Set [b1, b2]))) 1 =
  let branch1 = (Node (p : fs, RExt) (Abs_fset (Set [expandMultiRules b1]))) in
  let branch2 = (Node (q : fs, RExt) (Abs_fset (Set [expandMultiRules b2]))) in
  Node (Con p q : fs, RBetaCon) (Abs_fset (Set [branch1, branch2]))
expandBetaCon (Node ((terms, (Con p q : fs)), BetaCon) (Abs_fset (Set branches))) n =
  let branch1 = (Node (p : fs, RExt) (Abs_fset (Set [expandBetaCon (Node ((terms, (fs ++ [p])), BetaCon) (Abs_fset (Set (first branches)))) (n - 1)]))) in
  let branch2 = (Node (q : fs, RExt) (Abs_fset (Set [expandBetaCon (Node ((terms, (fs ++ [q])), BetaCon) (Abs_fset (Set (second branches)))) (n - 1)]))) in
  Node (Con p q : fs, RBetaCon) (Abs_fset (Set [branch1, branch2]))
expandBetaCon (Node ((terms, (f : fs)), BetaCon) (Abs_fset (Set [current]))) 1 =
  let extRule = (Node (f : fs, RExt) (Abs_fset (Set ([expandMultiRules current])))) in
  Node (f : fs, RBetaCon) (Abs_fset (Set [extRule]))
expandBetaCon (Node ((terms, (f : fs)), BetaCon) (Abs_fset (Set rest))) n =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set [expandBetaCon (Node ((terms, (fs ++ [f])), BetaCon) (Abs_fset (Set rest))) (n - 1)])) in
  Node (f : fs, RBetaCon) (Abs_fset (Set [extRule]))

-- Expansion of BetaImp rule
-- The prover creates the product of all beta rules as branches, so we need to reassemble the branches into a binary tree
expandBetaImp :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandBetaImp (Node ((terms, (Neg (Imp p q) : fs)), BetaImp) (Abs_fset (Set [b1, b2]))) 1 =
  let branch1 = (Node (p : fs, RExt) (Abs_fset (Set [expandMultiRules b1]))) in
  let branch2 = (Node (Neg q : fs, RExt) (Abs_fset (Set [expandMultiRules b2]))) in
  Node (Neg (Imp p q) : fs, RBetaImp) (Abs_fset (Set [branch1, branch2]))
expandBetaImp (Node ((terms, (Neg (Imp p q) : fs)), BetaImp) (Abs_fset (Set branches))) n =
  let branch1 = (Node (p : fs, RExt) (Abs_fset (Set [expandBetaImp (Node ((terms, (fs ++ [p])), BetaImp) (Abs_fset (Set (first branches)))) (n - 1)]))) in
  let branch2 = (Node (Neg q : fs, RExt) (Abs_fset (Set [expandBetaImp (Node ((terms, (fs ++ [Neg q])), BetaImp) (Abs_fset (Set (second branches)))) (n - 1)]))) in
  Node (Neg (Imp p q) : fs, RBetaImp) (Abs_fset (Set [branch1, branch2]))
expandBetaImp (Node ((terms, (f : fs)), BetaImp) (Abs_fset (Set [current]))) 1 =
  let extRule = (Node (f : fs, RExt) (Abs_fset (Set ([expandMultiRules current])))) in
  Node (f : fs, RBetaImp) (Abs_fset (Set [extRule]))
expandBetaImp (Node ((terms, (f : fs)), BetaImp) (Abs_fset (Set rest))) n =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set [expandBetaImp (Node ((terms, (fs ++ [f])), BetaImp) (Abs_fset (Set rest))) (n - 1)])) in
  Node (f : fs, RBetaImp) (Abs_fset (Set [extRule]))

-- Expansion of BetaDis rule
-- The prover creates the product of all beta rules as branches, so we need to reassemble the branches into a binary tree
expandBetaDis :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandBetaDis (Node ((terms, (Neg (Dis p q) : fs)), BetaDis) (Abs_fset (Set [b1, b2]))) 1 =
  let branch1 = (Node (Neg p : fs, RExt) (Abs_fset (Set [expandMultiRules b1]))) in
  let branch2 = (Node (Neg q : fs, RExt) (Abs_fset (Set [expandMultiRules b2]))) in
  Node (Neg (Dis p q) : fs, RBetaDis) (Abs_fset (Set [branch1, branch2]))
expandBetaDis (Node ((terms, (Neg (Dis p q) : fs)), BetaDis) (Abs_fset (Set branches))) n =
  let branch1 = (Node (Neg p : fs, RExt) (Abs_fset (Set [expandBetaDis (Node ((terms, (fs ++ [Neg p])), BetaDis) (Abs_fset (Set (first branches)))) (n - 1)]))) in
  let branch2 = (Node (Neg q : fs, RExt) (Abs_fset (Set [expandBetaDis (Node ((terms, (fs ++ [Neg q])), BetaDis) (Abs_fset (Set (second branches)))) (n - 1)]))) in
  Node (Neg (Dis p q) : fs, RBetaDis) (Abs_fset (Set [branch1, branch2]))
expandBetaDis (Node ((terms, (f : fs)), BetaDis) (Abs_fset (Set [current]))) 1 =
  let extRule = (Node (f : fs, RExt) (Abs_fset (Set ([expandMultiRules current])))) in
  Node (f : fs, RBetaDis) (Abs_fset (Set [extRule]))
expandBetaDis (Node ((terms, (f : fs)), BetaDis) (Abs_fset (Set rest))) n =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set [expandBetaDis (Node ((terms, (fs ++ [f])), BetaDis) (Abs_fset (Set rest))) (n - 1)])) in
  Node (f : fs, RBetaDis) (Abs_fset (Set [extRule]))

-- Expansion of DeltaUni rule
expandDeltaUni :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandDeltaUni (Node ((terms, (f : fs)), DeltaUni) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Uni p -> [SeCaV.sub Arith.zero_nat (SeCaV.Fun (generateNew terms) []) p]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandDeltaUni (Node ((terms, (fs ++ applied)), DeltaUni) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RDeltaUni) (Abs_fset (Set [extRule]))

-- Expansion of DeltaExi rule
expandDeltaExi :: Tree (([Tm], [Fm]), Rule) -> Int -> Tree ([Fm], SeCaVRule)
expandDeltaExi (Node ((terms, (f : fs)), DeltaExi) (Abs_fset (Set [current]))) n =
  let applied = case f of
                  Neg (Exi p) -> [Neg (SeCaV.sub Arith.zero_nat (SeCaV.Fun (generateNew terms) []) p)]
                  x -> [x] in
  let extRule = if n == 1
        then (Node (applied ++ fs, RExt) (Abs_fset (Set ([expandMultiRules current]))))
        else (Node (applied ++ fs, RExt) (Abs_fset (Set [expandDeltaExi (Node ((terms, (fs ++ applied)), DeltaExi) (Abs_fset (Set [current]))) (n - 1)]))) in
  Node (f : fs, RDeltaExi) (Abs_fset (Set [extRule]))

-- Expansion of GammaExi rule
-- Here we have a counter for the sequent formulas (ns) and a counter for the terms (nt) since we need to instantiate each formula with each term
expandGammaExi :: Tree (([Tm], [Fm]), Rule) -> Int -> Int -> Tree ([Fm], SeCaVRule)
expandGammaExi (Node ((t : ts, Exi p : fs), GammaExi) (Abs_fset (Set [current]))) 1 1 =
  let applied = SeCaV.sub Arith.zero_nat t p in
  let extRule = Node (applied : Exi p : fs, RExt) (Abs_fset (Set ([expandMultiRules current]))) in
  let gammaRule = Node (Exi p : Exi p : fs, RGammaExi t) (Abs_fset (Set [extRule])) in
  Node (Exi p : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaExi node@(Node ((t : ts, Exi p : fs), GammaExi) (Abs_fset (Set [current]))) ns 1 =
  let applied = SeCaV.sub Arith.zero_nat t p in
  let extRule = Node (applied : Exi p : fs, RExt) (Abs_fset (Set [expandGammaExi (Node ((ts ++ [t], (fs ++ [applied, Exi p])), GammaExi) (Abs_fset (Set [current]))) (ns - 1) (length (t : ts))])) in
  let gammaRule = Node (Exi p : Exi p : fs, RGammaExi t) (Abs_fset (Set [extRule])) in
  Node (Exi p : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaExi (Node ((t : ts, Exi p : fs), GammaExi) (Abs_fset (Set [current]))) ns nt =
  let applied = SeCaV.sub Arith.zero_nat t p in
  let extRule = Node (applied : Exi p : fs, RExt) (Abs_fset (Set [expandGammaExi (Node ((ts ++ [t], Exi p : fs ++ [applied]), GammaExi) (Abs_fset (Set [current]))) ns (nt - 1)])) in
  let gammaRule = Node (Exi p : Exi p : fs, RGammaExi t) (Abs_fset (Set [extRule])) in
  Node (Exi p : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaExi (Node ((t : ts, f : fs), GammaExi) (Abs_fset (Set [current]))) 1 nt =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set ([expandMultiRules current]))) in
  Node (f : fs, RGammaExi t) (Abs_fset (Set [extRule]))
expandGammaExi (Node ((t : ts, f : fs), GammaExi) (Abs_fset (Set [current]))) ns nt =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set [expandGammaExi (Node ((t : ts, fs ++ [f]), GammaExi) (Abs_fset (Set [current]))) (ns - 1) nt])) in
  Node (f : fs, RGammaExi t) (Abs_fset (Set [extRule]))

-- Expansion of GammaUni rule
-- Here we have a counter for the sequent formulas (ns) and a counter for the terms (nt) since we need to instantiate each formula with each term
expandGammaUni :: Tree (([Tm], [Fm]), Rule) -> Int -> Int -> Tree ([Fm], SeCaVRule)
expandGammaUni (Node ((t : _, Neg (Uni p) : fs), GammaUni) (Abs_fset (Set [current]))) 1 1 =
  let applied = Neg (SeCaV.sub Arith.zero_nat t p) in
  let extRule = Node (applied : Neg (Uni p) : fs, RExt) (Abs_fset (Set ([expandMultiRules current]))) in
  let gammaRule = Node (Neg (Uni p) : Neg (Uni p) : fs, RGammaUni t) (Abs_fset (Set [extRule])) in
  Node (Neg (Uni p) : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaUni node@(Node ((t : ts, Neg (Uni p) : fs), GammaUni) (Abs_fset (Set [current]))) ns 1 =
  let applied = Neg (SeCaV.sub Arith.zero_nat t p) in
  let extRule = Node (applied : Neg (Uni p) : fs, RExt) (Abs_fset (Set [expandGammaUni (Node ((ts ++ [t], (fs ++ [applied, Neg (Uni p)])), GammaUni) (Abs_fset (Set [current]))) (ns - 1) (length (t : ts))])) in
  let gammaRule = Node (Neg (Uni p) : Neg (Uni p) : fs, RGammaUni t) (Abs_fset (Set [extRule])) in
  Node (Neg (Uni p) : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaUni (Node ((t : ts, Neg (Uni p) : fs), GammaUni) (Abs_fset (Set [current]))) ns nt =
  let applied = Neg (SeCaV.sub Arith.zero_nat t p) in
  let extRule = Node (applied : Neg (Uni p) : fs, RExt) (Abs_fset (Set [expandGammaUni (Node ((ts ++ [t], Neg (Uni p) : fs ++ [applied]), GammaUni) (Abs_fset (Set [current]))) ns (nt - 1)])) in
  let gammaRule = Node (Neg (Uni p) : Neg (Uni p) : fs, RGammaUni t) (Abs_fset (Set [extRule])) in
  Node (Neg (Uni p) : fs, RExt) (Abs_fset (Set [gammaRule]))
expandGammaUni (Node ((t : ts, f : fs), GammaUni) (Abs_fset (Set [current]))) 1 nt =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set ([expandMultiRules current]))) in
  Node (f : fs, RGammaUni t) (Abs_fset (Set [extRule]))
expandGammaUni (Node ((t : ts, f : fs), GammaUni) (Abs_fset (Set [current]))) ns nt =
  let extRule = Node (f : fs, RExt) (Abs_fset (Set [expandGammaUni (Node ((t : ts, fs ++ [f]), GammaUni) (Abs_fset (Set [current]))) (ns - 1) nt])) in
  Node (f : fs, RGammaUni t) (Abs_fset (Set [extRule]))

-- This function moves the positive part of a Basic pair in the front of the sequent to allow the Basic rule to be applied
-- WARNING: This will loop forever if there is no Basic pair (P and Neg P) in the sequent
sortSequent :: [Fm] -> [Fm]
sortSequent [] = []
sortSequent (x : xs) = if Neg x `elem` xs then x : xs else sortSequent (xs ++ [x])

-- This adds an Ext rule to move the Basic pair in position, then a Basic rule to end a branch
addBasicRule :: Tree (([Tm], [Fm]), Rule) -> Tree ([Fm], SeCaVRule)
addBasicRule (Node ((_, sequent), rule) (Abs_fset (Set []))) =
  let basicRule = Node (sortSequent sequent, RBasic) (Abs_fset (Set [])) in
    Node (sequent, RExt) (Abs_fset (Set [basicRule]))

-- This function takes the rules from the prover and expands them into separate SeCaV applications for each formula in the sequent with Ext's in between
-- Gamma rules are expanded for each formula and for each term
-- Note that after this function, rules are still applied to all formulas, even those that do not fit the rule
expandMultiRules :: Tree (([Tm], [Fm]), Rule) -> Tree ([Fm], SeCaVRule)
expandMultiRules node@(Node ((_, sequent), rule) (Abs_fset (Set []))) = addBasicRule node
expandMultiRules node@(Node ((_, sequent), AlphaDis) _) = expandAlphaDis node (length sequent)
expandMultiRules node@(Node ((_, sequent), AlphaCon) _) = expandAlphaCon node (length sequent)
expandMultiRules node@(Node ((_, sequent), AlphaImp) _) = expandAlphaImp node (length sequent)
expandMultiRules node@(Node ((_, sequent), NegNeg) _) = expandNegNeg node (length sequent)
expandMultiRules node@(Node ((_, sequent), BetaCon) _) = expandBetaCon node (length sequent)
expandMultiRules node@(Node ((_, sequent), BetaImp) _) = expandBetaImp node (length sequent)
expandMultiRules node@(Node ((_, sequent), BetaDis) _) = expandBetaDis node (length sequent)
expandMultiRules node@(Node ((_, sequent), DeltaUni) _) = expandDeltaUni node (length sequent)
expandMultiRules node@(Node ((_, sequent), DeltaExi) _) = expandDeltaExi node (length sequent)
expandMultiRules node@(Node ((terms, sequent), GammaExi) _) = expandGammaExi node (length sequent) (length terms)
expandMultiRules node@(Node ((terms, sequent), GammaUni) _) = expandGammaUni node (length sequent) (length terms)

-- This function removes all rule applications that do nothing (which includes all wrong rule applications)
-- It should be called both before and after the extSurgery function to be sure to remove all extraneous Ext rules
removeNoopRules :: Tree ([Fm], SeCaVRule) -> Tree ([Fm], SeCaVRule)
removeNoopRules node@(Node (_, _) (Abs_fset (Set []))) = node
removeNoopRules (Node (s1, r1) (Abs_fset (Set [Node (s2, r2) (Abs_fset (Set rest))]))) =
                                if s1 == s2
                                then removeNoopRules (Node (s2, r2) (Abs_fset (Set rest)))
                                else Node (s1, r1) (Abs_fset (Set [removeNoopRules (Node (s2, r2) (Abs_fset (Set rest)))]))
removeNoopRules (Node (s, r) (Abs_fset (Set rest))) = Node (s, r) (Abs_fset (Set (map removeNoopRules rest)))

-- This function collapses successive applications of the Ext rule to a single application
-- A lot of these will appear after eliminating rules that are applied to wrong formulas, so this shortens the proof quite a bit
extSurgery :: Tree ([Fm], SeCaVRule) -> Tree ([Fm], SeCaVRule)
extSurgery node@(Node (_, RExt) (Abs_fset (Set []))) = node
extSurgery (Node (sequent, RExt) (Abs_fset (Set [Node (_, RExt) next@(Abs_fset (Set []))]))) =
  Node (sequent, RExt) next
extSurgery (Node (sequent, RExt) (Abs_fset (Set [Node (_, RExt) (Abs_fset (Set [current]))]))) =
  extSurgery $ Node (sequent, RExt) (Abs_fset (Set [current]))
extSurgery (Node (sequent, RExt) (Abs_fset (Set [Node (_, RExt) (Abs_fset (Set [current, next]))]))) =
  extSurgery $ Node (sequent, RExt) (Abs_fset (Set [current, next]))
extSurgery node@(Node (_, _) (Abs_fset (Set []))) = node
extSurgery (Node (s, r) (Abs_fset (Set [current]))) = Node (s, r) (Abs_fset (Set [extSurgery current]))
extSurgery (Node (s, r) (Abs_fset (Set [current, next]))) = Node (s, r) (Abs_fset (Set [extSurgery current, extSurgery next]))
extSurgery (Node _ (Abs_fset (Set (_ : _ : _ : _)))) = error "No proof rule should generate more than two branches."
extSurgery (Node _ (Abs_fset (Coset _))) = error "No proof rule should generate a coset of branches."

initExtract :: NameState -> Tree ([Fm], SeCaVRule) -> String
initExtract names tree = evalState (extract tree) names

extract :: Tree ([Fm], SeCaVRule) -> NameGen String
extract (Node (sequent, rule) (Abs_fset (Set []))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  pure $ s <> "\n\n" <> r <> "\n"
extract (Node (sequent, rule) (Abs_fset (Set [current]))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  c <- extract' [] current
  pure $ s <> "\n\n" <> r <> "\n" <> c
extract (Node (sequent, rule) (Abs_fset (Set [current, next]))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  c <- extract' [extractNextSequent next] current
  n <- extract' [] next
  pure $ s <> "\n\n" <> r <> "\n" <> c <> n
extract _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extract' :: [[Fm]] -> Tree ([Fm], SeCaVRule) -> NameGen String
extract' other (Node (sequent, rule) (Abs_fset (Set []))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n"
extract' other (Node (sequent, rule) (Abs_fset (Set [current]))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  c <- extract' other current
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n" <> c
extract' other (Node (sequent, rule) (Abs_fset (Set [current, next]))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  n <- extract' (extractNextSequent next : other) current
  c <- extract' other next
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n" <> n <> c
extract' _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extractNextSequent :: Tree ([Fm], SeCaVRule) -> [Fm]
extractNextSequent (Node (sequent, _) _) = sequent

extractOtherSequents :: [[Fm]] -> NameGen String
extractOtherSequents [] = pure ""
extractOtherSequents [x] = extractSequent' x
extractOtherSequents (x:xs) = do
  s <- extractSequent' x
  ss <- extractOtherSequents xs
  pure $ s <> "\n+\n" <> ss

extractSequent :: [Fm] -> NameGen String
extractSequent [] = pure ""
extractSequent [x] = extractFormula x
extractSequent (x:xs) = do
  f <- extractFormula x
  s <- extractSequent xs
  pure $ f <> "\n" <> s

extractSequent' :: [Fm] -> NameGen String
extractSequent' [] = pure ""
extractSequent' [x] = do
  f <- extractFormula x
  pure $ "  " <> f
extractSequent' (x:xs) = do
  f <- extractFormula x
  s <- extractSequent' xs
  pure $ "  " <> f <> "\n" <> s

genName :: Integer -> String
genName x | x < 0 = "?"
genName 0 = "a"
genName 1 = "b"
genName 2 = "c"
genName 3 = "d"
genName 4 = "e"
genName 5 = "f"
genName x = "g" <> genericReplicate (x - 5) '\''

genFunName :: Integer -> NameGen String
genFunName n = do
  s <- get
  case Map.lookupR n (existingFuns s) of
    Just name -> pure name
    Nothing -> do
      let nameNum = until (\x -> Map.notMemberR x (existingFuns s)) (+ 1) 0
      let name = genName nameNum
      _ <- modify (\st -> st { funCount = funCount s + 1
                             , existingFuns = Map.insert name n (existingFuns s)
                             })
      pure $ genName nameNum

extractTerm :: Tm -> NameGen String
extractTerm (SeCaV.Fun (Nat n) []) = genFunName n
extractTerm (SeCaV.Fun (Nat n) ts) = do
  fName <- genFunName n
  termNames <- traverse extractTerm ts
  pure $ fName <> "[" <> intercalate ", " termNames <> "]"
extractTerm (SeCaV.Var n) = pure $ show n

dropEnd :: Int -> String -> String
dropEnd n = reverse . drop n . reverse

extractFormula :: Fm -> NameGen String
extractFormula (SeCaV.Pre (Nat n) []) = do
  s <- get
  pure $ existingPres s Map.!> n
extractFormula (SeCaV.Pre (Nat n) ts) = do
  s <- get
  termNames <- traverse extractTerm ts
  pure $ existingPres s Map.!> n <> " [" <> intercalate ", " termNames <> "]"
extractFormula f = do
  form <- extractFormula' f
  pure $ drop 1 $ dropEnd 1 form

extractFormula' :: Fm -> NameGen String
extractFormula' (SeCaV.Pre (Nat n) []) = do
  s <- get
  pure $ existingPres s Map.!> n
extractFormula' (SeCaV.Pre (Nat n) ts) = do
  s <- get
  termNames <- traverse extractTerm ts
  pure $ "(" <> existingPres s Map.!> n <> " [" <> intercalate ", " termNames  <> "])"
extractFormula' (SeCaV.Imp a b) = do
  formA <- extractFormula' a
  formB <- extractFormula' b
  pure $ "(Imp " <> formA <> " " <> formB <> ")"
extractFormula' (SeCaV.Dis a b) = do
  formA <- extractFormula' a
  formB <- extractFormula' b
  pure $ "(Dis " <> formA <> " " <> formB <> ")"
extractFormula' (SeCaV.Con a b) = do
  formA <- extractFormula' a
  formB <- extractFormula' b
  pure $ "(Con " <> formA <> " " <> formB <> ")"
extractFormula' (SeCaV.Exi f) = do
  form <- extractFormula' f
  pure $ "(Exi " <> form <> ")"
extractFormula' (SeCaV.Uni f) = do
  form <- extractFormula' f
  pure $ "(Uni " <> form <> ")"
extractFormula' (SeCaV.Neg f) = do
  form <- extractFormula' f
  pure $ "(Neg " <> form <> ")"

extractRule :: SeCaVRule -> NameGen String
extractRule RBasic = pure "Basic"
extractRule RAlphaDis = pure "AlphaDis"
extractRule RAlphaImp = pure "AlphaImp"
extractRule RAlphaCon = pure "AlphaCon"
extractRule RBetaCon = pure"BetaCon"
extractRule RBetaImp = pure "BetaImp"
extractRule RBetaDis = pure "BetaDis"
extractRule (RGammaUni t) = do
  termName <- extractTerm t
  pure $ "GammaUni[" <> termName <> "]"
extractRule (RGammaExi t) = do
  termName <- extractTerm t
  pure $ "GammaExi[" <> termName <> "]"
extractRule RDeltaUni = pure "DeltaUni"
extractRule RDeltaExi = pure "DeltaExi"
extractRule RNeg = pure "NegNeg"
extractRule RExt = pure "Ext"
