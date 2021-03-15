module AST where

import Data.Bimap
import Control.Monad.State

type Name = String
type Index = Integer

data Term
  = Fun Name [Term]
  | Var Index
  deriving (Show)

data Formula
  = Pre Name [Term]
  | Imp Formula Formula
  | Dis Formula Formula
  | Con Formula Formula
  | Exi Formula
  | Uni Formula
  | Neg Formula
  deriving (Show)

data NameState = NameState
  { preCount :: Integer
  , funCount :: Integer
  , existingPres :: Bimap Name Integer
  , existingFuns :: Bimap Name Integer
  }

type NameGen a = State NameState a

data BoundNameState = BoundNameState { depth :: Integer }

type BoundNameGen a = State BoundNameState a
