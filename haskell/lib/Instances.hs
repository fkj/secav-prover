{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Instances where

import Arith(Nat(..))
import SeCaV(Tm(..), Fm(..))
import Prover(Prule(..))
import Abstract_Completeness(Tree(..))
import Set(Set(..))
import FSet(Fset(..))

instance Show Nat where
  show (Nat x) = show x

instance Show Tm where
  show (Fun n ts) = "F" <> show n <> " " <> show ts
  show (Var n) = "V" <> show n

instance Show Fm where
  show (Pre n ts) = "P" <> show n <> " " <> show ts
  show (Imp f1 f2) = "(" <> show f1 <> ") → (" <> show f2 <> ")"
  show (Dis f1 f2) = "(" <> show f1 <> ") ∨ (" <> show f2 <> ")"
  show (Con f1 f2) = "(" <> show f1 <> ") ∧ (" <> show f2 <> ")"
  show (Exi f) = "∃(" <> show f <> ")"
  show (Uni f) = "∀(" <> show f <> ")"
  show (Neg f) = "¬(" <> show f <> ")"

deriving instance Show Prule

instance Show (Set [Fm]) where
  show (Set s) = show s
  show (Coset s) = show s

instance Show (Set (Tree ([Fm], Prule))) where
  show (Set s) = show s
  show (Coset s) = show s

instance Show (Fset [Fm]) where
  show (Abs_fset s) = show s

instance Show (Fset (Tree ([Fm], Prule))) where
  show (Abs_fset s) = show s

instance Show (Tree ([Fm], Prule)) where
  show (Node (fs, r) t) = show fs <> " " <> show r <> "\n" <> show t
