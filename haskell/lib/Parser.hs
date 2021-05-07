module Parser where

import AST
import Lexer
import Text.Parsec
import Data.Function (fix)

type SParser a = Parsec String () a

name :: SParser Name
name = m_identifier

index :: SParser Index
index = m_integer

-- Parsing of terms
fun :: SParser Term
fun = do
  f <- name
  args <- option [] termList
  pure $ Fun f args

var :: SParser Term
var = Var <$> index

term :: SParser Term
term = fix allTerms
  where
    allTerms _ = choice
      [ fun
      , var
      ] <?> "a function name or a variable"

termList :: SParser [Term]
termList = fix $ const (m_brackets $ m_commaSep term)

-- Parsing of formulas
predicate :: SParser Formula
predicate = Pre <$> name <*> option [] termList

implication :: SParser Formula
implication = fix $ const $ m_reserved "Imp" *> (Imp <$> formula <*> formula)

disjunction :: SParser Formula
disjunction = fix $ const $ m_reserved "Dis" *> (Dis <$> formula <*> formula)

conjunction :: SParser Formula
conjunction = fix $ const $ m_reserved "Con" *> (Con <$> formula <*> formula)

existential :: SParser Formula
existential = fix $ const $ m_reserved "Exi" *> (Exi <$> formula)

universal :: SParser Formula
universal = fix $ const $ m_reserved "Uni" *> (Uni <$> formula)

negation :: SParser Formula
negation = fix $ const $ m_reserved "Neg" *> (Neg <$> formula)

formula :: SParser Formula
formula = fix allFormulas
  where
    allFormulas _ = choice
      [ predicate
      , implication
      , disjunction
      , conjunction
      , existential
      , universal
      , negation
      , m_parens formula
      ] <?> "a formula"

sequent :: SParser [Formula]
sequent = m_commaSep1 formula

parser :: String -> Either ParseError [Formula]
parser = parse (m_whiteSpace *> sequent <* eof) ""
