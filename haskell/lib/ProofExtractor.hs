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

dropEnd :: Int -> String -> String
dropEnd n = reverse . drop n . reverse

extract :: NameState -> Abstract_Completeness.Tree ([Fm], Rule) -> String
extract names (Node (sequent, rule) (Abs_fset (Set rest))) =
  extractSequent names sequent <> "\n" <> extractRule names rule <> "\n" <> intercalate "+\n" (map (extract' names) rest)

extract' :: NameState -> Abstract_Completeness.Tree ([Fm], Rule) -> String
extract' names (Node (sequent, rule) (Abs_fset (Set rest))) =
  extractSequent' names sequent <> extractRule names rule <> "\n" <> intercalate "+\n" (map (extract' names) rest)

extractSequent :: NameState -> [Fm] -> String
extractSequent _ [] = ""
extractSequent names (x:xs) = extractFormula names x <> "\n" <> extractSequent names xs

extractSequent' :: NameState -> [Fm] -> String
extractSequent' _ [] = ""
extractSequent' names (x:xs) = "  " <> extractFormula names x <> "\n" <> extractSequent' names xs

extractTerm :: NameState -> Tm -> String
extractTerm names (SeCaV.Fun (Nat n) []) = existingFuns names Map.!> n
extractTerm names (SeCaV.Fun (Nat n) ts) = existingFuns names Map.!> n <> "[" <> intercalate ", " (map (extractTerm names) ts) <> "]"
extractTerm _ (SeCaV.Var n) = "Var " <> show n

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
extractRule _ Basic = "Basic"
extractRule _ AlphaDis = "AlphaDis"
extractRule _ AlphaImp = "AlphaImp"
extractRule _ AlphaCon = "AlphaCon"
extractRule _ BetaCon = "BetaCon"
extractRule _ BetaImp = "BetaImp"
extractRule _ BetaDis = "BetaDis"
extractRule names (GammaExi t) = "GammaExi[" <> extractTerm names t <> "]"
extractRule names (GammaUni t) = "GammaUni[" <> extractTerm names t <> "]"
extractRule _ DeltaUni = "DeltaUni"
extractRule _ DeltaExi = "DeltaExi"
extractRule _ NegNeg = "Neg"
extractRule _ ExtRotate = "Ext"
