module ProofLexer where

import Text.Parsec.Token
import Text.Parsec.Char
import Text.Parsec.Language
import Control.Applicative

languageDef :: LanguageDef st
languageDef = emptyDef
  { commentStart = "(*"
  , commentEnd = "*)"
  , commentLine = ""
  , nestedComments = False
  , identStart = letter
  , identLetter = alphaNum <|> oneOf ['_', '\'']
  , opStart = oneOf ['+', '-', '#']
  , opLetter = oneOf ['+', '-', '#']
  , reservedNames = [ "Var"
                    , "Imp"
                    , "Dis"
                    , "Con"
                    , "Exi"
                    , "Uni"
                    , "Neg"
                    , "Basic"
                    , "AlphaDis"
                    , "AlphaImp"
                    , "AlphaCon"
                    , "BetaCon"
                    , "BetaImp"
                    , "BetaDis"
                    , "GammaExi"
                    , "GammaUni"
                    , "DeltaUni"
                    , "DeltaExi"
                    , "Ext"
                    ]
  , reservedOpNames = ["+", "-", "#"]
  , caseSensitive = True
  }

TokenParser
  { parens = m_parens
  , identifier = m_identifier
  , integer = m_integer
  , brackets = m_brackets
  , commaSep = m_commaSep
  , stringLiteral = m_stringLiteral
  , commaSep1 = m_commaSep1
  , reserved = m_reserved
  , reservedOp = m_reservedOp
  , whiteSpace = m_whiteSpace
  } = makeTokenParser languageDef
