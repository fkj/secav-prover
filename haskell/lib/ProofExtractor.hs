module ProofExtractor where

import SeCaV
import Prover
import FSet
import Set
import Abstract_Completeness
import AST
import Arith
import Instances()
import qualified Data.Bimap as Map
import Data.List
import Data.Maybe (fromMaybe)

data Rule
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

convertRule :: Prule -> Rule
convertRule Basic = RBasic
convertRule AlphaDis = RAlphaDis
convertRule AlphaImp = RAlphaImp
convertRule AlphaCon = RAlphaCon
convertRule BetaCon = RBetaCon
convertRule BetaImp = RBetaImp
convertRule BetaDis = RBetaDis
convertRule DeltaUni = RDeltaUni
convertRule DeltaExi = RDeltaExi
convertRule NegNeg = RNeg
convertRule GammaUni = error "This should never happen (GammaUni converted)"
convertRule GammaExi = error "This should never happen (GammaExi converted)"
convertRule Rotate = RExt
convertRule Duplicate = RExt
convertRule Next = RExt

nextSurgery :: Tree (([Fm], Phase), Prule) -> Tree (([Fm], Phase), Prule)
nextSurgery node@(Node _ (Abs_fset (Set []))) = node
nextSurgery (Node ((_, _), Next) (Abs_fset (Set [node@(Node ((_, _), _) (Abs_fset (Set [])))]))) = node
nextSurgery (Node ((_, _), Next) (Abs_fset (Set [Node ((ns, np), nr) (Abs_fset (Set [current]))]))) =
  Node ((ns, np), nr) (Abs_fset (Set [nextSurgery current]))
nextSurgery (Node ((_, _), Next) (Abs_fset (Set [Node ((ns, np), nr) (Abs_fset (Set [current, next]))]))) =
  Node ((ns, np), nr) (Abs_fset (Set [nextSurgery current, nextSurgery next]))
nextSurgery (Node s (Abs_fset (Set [current]))) = Node s (Abs_fset (Set [nextSurgery current]))
nextSurgery (Node s (Abs_fset (Set [current, next]))) = Node s (Abs_fset (Set [nextSurgery current, nextSurgery next]))
nextSurgery (Node _ (Abs_fset (Set (_ : _ : _ : _)))) = error "No proof rule should generate more than two branches."
nextSurgery (Node _ (Abs_fset (Coset _))) = error "No proof rule should generate a coset of branches."

gammaSurgery :: Tree (([Fm], Phase), Prule) -> Tree (([Fm], Phase), Rule)
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaExi) (Abs_fset (Set []))) =
  Node ((sequent, phase), RGammaExi t) (Abs_fset (Set []))
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaExi) (Abs_fset (Set [current]))) =
  Node ((sequent, phase), RGammaExi t) (Abs_fset (Set [gammaSurgery current]))
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaExi) (Abs_fset (Set [current,next]))) =
  Node ((sequent, phase), RGammaExi t) (Abs_fset (Set [gammaSurgery current, gammaSurgery next]))
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaUni) (Abs_fset (Set []))) =
  Node ((sequent, phase), RGammaUni t) (Abs_fset (Set []))
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaUni) (Abs_fset (Set [current]))) =
  Node ((sequent, phase), RGammaUni t) (Abs_fset (Set [gammaSurgery current]))
gammaSurgery (Node ((sequent, phase@(PInstGamma _ _ (t : _) _)), GammaUni) (Abs_fset (Set [current,next]))) =
  Node ((sequent, phase), RGammaUni t) (Abs_fset (Set [gammaSurgery current, gammaSurgery next]))
gammaSurgery (Node (state, rule) (Abs_fset (Set []))) = Node (state, convertRule rule) (Abs_fset (Set []))
gammaSurgery (Node (state, rule) (Abs_fset (Set [current]))) = Node (state, convertRule rule) (Abs_fset (Set [gammaSurgery current]))
gammaSurgery (Node (state, rule) (Abs_fset (Set [current, next]))) = Node (state, convertRule rule) (Abs_fset (Set [gammaSurgery current, gammaSurgery next]))
gammaSurgery (Node _ (Abs_fset (Set (_ : _ : _ : _)))) = error "No proof rule should generate more than two branches."
gammaSurgery (Node _ (Abs_fset (Coset _))) = error "No proof rule should generate a coset of branches."

extSurgery :: Tree (([Fm], Phase), Rule) -> Tree (([Fm], Phase), Rule)
extSurgery node@(Node ((_, _), RExt) (Abs_fset (Set []))) = node
extSurgery (Node ((sequent, phase), RExt) (Abs_fset (Set [Node ((_, _), RExt) next@(Abs_fset (Set []))]))) =
  Node ((sequent, phase), RExt) next
extSurgery (Node ((sequent, phase), RExt) (Abs_fset (Set [Node ((_, _), RExt) (Abs_fset (Set [current]))]))) =
  extSurgery $ Node ((sequent, phase), RExt) (Abs_fset (Set [current]))
extSurgery (Node ((sequent, phase), RExt) (Abs_fset (Set [Node ((_, _), RExt) (Abs_fset (Set [current, next]))]))) =
  extSurgery $ Node ((sequent, phase), RExt) (Abs_fset (Set [current, next]))
extSurgery node@(Node (_, _) (Abs_fset (Set []))) = node
extSurgery (Node (s, r) (Abs_fset (Set [current]))) = Node (s, r) (Abs_fset (Set [extSurgery current]))
extSurgery (Node (s, r) (Abs_fset (Set [current, next]))) = Node (s, r) (Abs_fset (Set [extSurgery current, extSurgery next]))
extSurgery (Node _ (Abs_fset (Set (_ : _ : _ : _)))) = error "No proof rule should generate more than two branches."
extSurgery (Node _ (Abs_fset (Coset _))) = error "No proof rule should generate a coset of branches."

extract :: NameState -> Tree (([Fm], Phase), Rule) -> String
extract names (Node ((sequent, _), rule) (Abs_fset (Set []))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n"
extract names (Node ((sequent, _), rule) (Abs_fset (Set [current]))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names [] current
extract names (Node ((sequent, _), rule) (Abs_fset (Set [current, next]))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names [extractNextSequent next] current <>
  extract' names [] next
extract _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extract' :: NameState -> [[Fm]] -> Tree (([Fm], Phase), Rule) -> String
extract' names other (Node ((sequent, _), rule) (Abs_fset (Set []))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n"
extract' names other (Node ((sequent, _), rule) (Abs_fset (Set [current]))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names other current
extract' names other (Node ((sequent, _), rule) (Abs_fset (Set [current, next]))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names (extractNextSequent next : other) current <>
  extract' names other next
extract' _ _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extractNextSequent :: Tree (([Fm], Phase), Rule) -> [Fm]
extractNextSequent (Node ((sequent, _), _) _) = sequent

extractOtherSequents :: NameState -> [[Fm]] -> String
extractOtherSequents _ [] = ""
extractOtherSequents names [x] = extractSequent' names x
extractOtherSequents names (x:xs) = extractSequent' names x <> "\n+\n" <> extractOtherSequents names xs

extractSequent :: NameState -> [Fm] -> String
extractSequent _ [] = ""
extractSequent names [x] = extractFormula names x
extractSequent names (x:xs) = extractFormula names x <> "\n" <> extractSequent names xs

extractSequent' :: NameState -> [Fm] -> String
extractSequent' _ [] = ""
extractSequent' names [x] = "  " <> extractFormula names x
extractSequent' names (x:xs) = "  " <> extractFormula names x <> "\n" <> extractSequent' names xs

genName :: Integer -> String
genName x | x < 0 = "?"
genName 0 = "a"
genName 1 = "b"
genName 2 = "c"
genName 3 = "d"
genName 4 = "e"
genName 5 = "f"
genName x = "g" <> genericReplicate (x - 5) '\''

genNewFun :: Integer -> NameState -> String
genNewFun n _ = "F" <> genName n

extractTerm :: NameState -> Tm -> String
extractTerm names (SeCaV.Fun (Nat n) []) = fromMaybe (genNewFun n names) (Map.lookupR n $ existingFuns names)
extractTerm names (SeCaV.Fun (Nat n) ts) = fromMaybe (genNewFun n names) (Map.lookupR n $ existingFuns names) <> "[" <> intercalate ", " (map (extractTerm names) ts) <> "]"
extractTerm _ (SeCaV.Var n) = show n

dropEnd :: Int -> String -> String
dropEnd n = reverse . drop n . reverse

extractFormula :: NameState -> Fm -> String
extractFormula names (SeCaV.Pre (Nat n) []) = existingPres names Map.!> n
extractFormula names (SeCaV.Pre (Nat n) ts) = existingPres names Map.!> n <> " [" <> intercalate ", " (map (extractTerm names) ts) <> "]"
extractFormula names f = drop 1 $ dropEnd 1 $ extractFormula' names f

extractFormula' :: NameState -> Fm -> String
extractFormula' names (SeCaV.Pre (Nat n) []) = existingPres names Map.!> n
extractFormula' names (SeCaV.Pre (Nat n) ts) = "(" <> existingPres names Map.!> n <> " [" <> intercalate ", " (map (extractTerm names) ts) <> "])"
extractFormula' names (SeCaV.Imp a b) = "(Imp " <> extractFormula' names a <> " " <> extractFormula' names b <> ")"
extractFormula' names (SeCaV.Dis a b) = "(Dis " <> extractFormula' names a <> " " <> extractFormula' names b <> ")"
extractFormula' names (SeCaV.Con a b) = "(Con " <> extractFormula' names a <> " " <> extractFormula' names b <> ")"
extractFormula' names (SeCaV.Exi f) = "(Exi " <> extractFormula' names f <> ")"
extractFormula' names (SeCaV.Uni f) = "(Uni " <> extractFormula' names f <> ")"
extractFormula' names (SeCaV.Neg f) = "(Neg " <> extractFormula' names f <> ")"

extractRule :: NameState -> Rule -> String
extractRule _ RBasic = "Basic:"
extractRule _ RAlphaDis = "AlphaDis:"
extractRule _ RAlphaImp = "AlphaImp:"
extractRule _ RAlphaCon = "AlphaCon:"
extractRule _ RBetaCon = "BetaCon:"
extractRule _ RBetaImp = "BetaImp:"
extractRule _ RBetaDis = "BetaDis:"
extractRule names (RGammaUni t) = "GammaUni[" <> extractTerm names t <> "]:"
extractRule names (RGammaExi t) = "GammaExi[" <> extractTerm names t <> "]:"
extractRule _ RDeltaUni = "DeltaUni:"
extractRule _ RDeltaExi = "DeltaExi:"
extractRule _ RNeg = "NegNeg:"
extractRule _ RExt = "Ext:"
