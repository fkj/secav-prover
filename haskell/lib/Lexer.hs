module Lexer where

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
  , commaSep1 = m_commaSep1
  , reserved = m_reserved
  , whiteSpace = m_whiteSpace
  } = makeTokenParser languageDef
