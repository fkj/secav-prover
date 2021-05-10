module ProofExtractor where

import Abstract_Completeness ( Tree(..) )
import Arith ( Nat(Nat) )
import qualified Data.Bimap as Map
import Control.Monad.State (evalState, get, modify)
import Data.List ( genericReplicate, intercalate )
import FSet ( Fset(Abs_fset) )
import Prover ( Phase(PInstGamma), Prule(..) )
import ProverInstances()
import SeCaV ( Fm(..), Tm(..) )
import Set ( Set(Set, Coset) )
import ShortAST (funCount, NameGen,  NameState(existingFuns, existingPres) )

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

initExtract :: NameState -> Tree (([Fm], Phase), Rule) -> String
initExtract names tree = evalState (extract tree) names

extract :: Tree (([Fm], Phase), Rule) -> NameGen String
extract (Node ((sequent, _), rule) (Abs_fset (Set []))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  pure $ s <> "\n\n" <> r <> "\n"
extract (Node ((sequent, _), rule) (Abs_fset (Set [current]))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  c <- extract' [] current
  pure $ s <> "\n\n" <> r <> "\n" <> c
extract (Node ((sequent, _), rule) (Abs_fset (Set [current, next]))) = do
  s <- extractSequent sequent
  r <- extractRule rule
  c <- extract' [extractNextSequent next] current
  n <- extract' [] next
  pure $ s <> "\n\n" <> r <> "\n" <> c <> n
extract _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extract' :: [[Fm]] -> Tree (([Fm], Phase), Rule) -> NameGen String
extract' other (Node ((sequent, _), rule) (Abs_fset (Set []))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n"
extract' other (Node ((sequent, _), rule) (Abs_fset (Set [current]))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  c <- extract' other current
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n" <> c
extract' other (Node ((sequent, _), rule) (Abs_fset (Set [current, next]))) = do
  s <- extractSequent' sequent
  ss <- extractOtherSequents other
  r <- extractRule rule
  n <- extract' (extractNextSequent next : other) current
  c <- extract' other next
  pure $ s <> (if null other then "" else "\n+\n" <> ss) <> "\n" <> r <> "\n" <> n <> c
extract' _ _ =
  error "By the pricking of my thumbs, something wicked this way comes..."

extractNextSequent :: Tree (([Fm], Phase), Rule) -> [Fm]
extractNextSequent (Node ((sequent, _), _) _) = sequent

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

extractRule :: Rule -> NameGen String
extractRule RBasic = pure "Basic:"
extractRule RAlphaDis = pure "AlphaDis:"
extractRule RAlphaImp = pure "AlphaImp:"
extractRule RAlphaCon = pure "AlphaCon:"
extractRule RBetaCon = pure"BetaCon:"
extractRule RBetaImp = pure "BetaImp:"
extractRule RBetaDis = pure "BetaDis:"
extractRule (RGammaUni t) = do
  termName <- extractTerm t
  pure $ "GammaUni[" <> termName <> "]:"
extractRule (RGammaExi t) = do
  termName <- extractTerm t
  pure $ "GammaExi[" <> termName <> "]:"
extractRule RDeltaUni = pure "DeltaUni:"
extractRule RDeltaExi = pure "DeltaExi:"
extractRule RNeg = pure "NegNeg:"
extractRule RExt = pure "Ext:"
