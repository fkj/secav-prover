module ProofParser where

import AST
import ProofLexer
import Text.Parsec

type SParser a = Parsec String () a

fix f = f (fix f)

name :: SParser Name
name = m_identifier

index :: SParser Index
index = m_integer

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

-- Parsing of proof rules
basic :: SParser PRule
basic = do
  m_reserved "Basic"
  pure PBasic

alphaDis :: SParser PRule
alphaDis = do
  m_reserved "AlphaDis"
  pure PAlphaDis

alphaImp :: SParser PRule
alphaImp = do
  m_reserved "AlphaImp"
  pure PAlphaImp

alphaCon :: SParser PRule
alphaCon = do
  m_reserved "AlphaCon"
  pure PAlphaCon

betaDis :: SParser PRule
betaDis = do
  m_reserved "BetaDis"
  pure PBetaDis

betaImp :: SParser PRule
betaImp = do
  m_reserved "BetaImp"
  pure PBetaImp

betaCon :: SParser PRule
betaCon = do
  m_reserved "BetaCon"
  pure PBetaCon

gammaExi :: SParser PRule
gammaExi = do
  m_reserved "GammaExi"
  t <- optionMaybe (m_brackets term)
  pure $ PGammaExi t

gammaUni :: SParser PRule
gammaUni = do
  m_reserved "GammaUni"
  t <- optionMaybe (m_brackets term)
  pure $ PGammaUni t

deltaUni :: SParser PRule
deltaUni = do
  m_reserved "DeltaUni"
  pure PDeltaUni

deltaExi :: SParser PRule
deltaExi = do
  m_reserved "DeltaExi"
  pure PDeltaExi

ext :: SParser PRule
ext = do
  m_reserved "Ext"
  pure PExt

neg :: SParser PRule
neg = do
  m_reserved "NegNeg"
  pure PNeg

rule :: SParser PRule
rule = fix allRules
  where
    allRules _ = choice
      [ basic
      , alphaDis
      , alphaImp
      , alphaCon
      , betaDis
      , betaImp
      , betaCon
      , gammaExi
      , gammaUni
      , deltaUni
      , deltaExi
      , neg
      , ext
      ] <?> "a proof rule"

-- Parsing of rule applications
application :: SParser Application
application = do
  r <- rule
  m_reservedOp ":"
  l <- many formula `sepBy` m_reservedOp "+"
  pure $ Application r l

section :: SParser Intertext
section = do
  m_reservedOp "#"
  t <- optionMaybe m_stringLiteral
  pure $ Section t

text :: SParser Intertext
text = do
  m_reservedOp "-"
  t <- optionMaybe m_stringLiteral
  pure $ Text t

intertext :: SParser Intertext
intertext = do
  choice [section, text]

-- Parsing of proofs
proof :: SParser Proof
proof = do
  t <- many1 intertext
  f <- formula
  l <- many1 application
  pure $ Proof t f l

firstProof :: SParser Proof
firstProof = do
  t <- many intertext
  f <- formula
  l <- many1 application
  pure $ Proof t f l

-- Parsing of whole files
program :: SParser Program
program = do
  first <- firstProof
  l <- many $ try proof
  t <- many intertext
  pure $ Program (first:l) t

parser :: String -> Either ParseError Program
parser = parse (m_whiteSpace *> program <* eof) ""
