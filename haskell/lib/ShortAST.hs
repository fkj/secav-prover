module ShortAST where

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

data PRule
  = PBasic
  | PAlphaDis
  | PAlphaImp
  | PAlphaCon
  | PBetaCon
  | PBetaImp
  | PBetaDis
  | PGammaExi (Maybe Term)
  | PGammaUni (Maybe Term)
  | PDeltaUni
  | PDeltaExi
  | PNeg
  | PExt
  deriving (Show)

data Application
  = Application PRule [[Formula]]
  deriving (Show)

data Intertext
  = Section (Maybe String)
  | Text (Maybe String)
  deriving (Show)

data Proof
  = Proof [Intertext] Formula [Application]
  deriving (Show)

data Program = Program [Proof] [Intertext]
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
