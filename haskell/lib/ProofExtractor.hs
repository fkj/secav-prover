module ProofExtractor where

import SeCaV
import SeCaV_Enum
import FSet
import Set
import Abstract_Completeness
import AST
import Arith
import Instances
import qualified Data.Bimap as Map
import Data.List

extract :: NameState -> Tree ([Fm], Rule) -> String
extract names (Node (sequent, rule) (Abs_fset (Set []))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n"
extract names (Node (sequent, rule) (Abs_fset (Set [current]))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names [] current
extract names (Node (sequent, rule) (Abs_fset (Set [current, next]))) =
  extractSequent names sequent <>
  "\n\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names [extractNextSequent next] current <>
  extract' names [] next
extract _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extract' :: NameState -> [[Fm]] -> Tree ([Fm], Rule) -> String
extract' names other (Node (sequent, rule) (Abs_fset (Set []))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n"
extract' names other (Node (sequent, rule) (Abs_fset (Set [current]))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names other current
extract' names other (Node (sequent, rule) (Abs_fset (Set [current, next]))) =
  extractSequent' names sequent <>
  (if null other then "" else "\n+\n" <> extractOtherSequents names other) <>
  "\n" <>
  extractRule names rule <>
  "\n" <>
  extract' names (extractNextSequent next : other) current <>
  extract' names other next
extract' _ _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extractNextSequent :: Tree ([Fm], Rule) -> [Fm]
extractNextSequent (Node (sequent, _) _) = sequent

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

extractTerm :: NameState -> Tm -> String
extractTerm names (SeCaV.Fun (Nat n) []) = existingFuns names Map.!> n
extractTerm names (SeCaV.Fun (Nat n) ts) = existingFuns names Map.!> n <> "[" <> intercalate ", " (map (extractTerm names) ts) <> "]"
extractTerm _ (SeCaV.Var n) = "Var " <> show n

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
extractRule _ Basic = "Basic:"
extractRule _ AlphaDis = "AlphaDis:"
extractRule _ AlphaImp = "AlphaImp:"
extractRule _ AlphaCon = "AlphaCon:"
extractRule _ BetaCon = "BetaCon:"
extractRule _ BetaImp = "BetaImp:"
extractRule _ BetaDis = "BetaDis:"
extractRule names (GammaExi t) = "GammaExi[" <> extractTerm names t <> "]:"
extractRule names (GammaUni t) = "GammaUni[" <> extractTerm names t <> "]:"
extractRule _ DeltaUni = "DeltaUni:"
extractRule _ DeltaExi = "DeltaExi:"
extractRule _ NegNeg = "NegNeg:"
extractRule _ ExtRotate = "Ext:"
