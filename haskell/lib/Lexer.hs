module Lexer where

import Text.Parsec.Token
import Text.Parsec.Char
import Text.Parsec.Language
import Control.Applicative
import Text.Parsec (ParsecT)
import Control.Monad.Identity (Identity)

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

m_parens :: ParsecT String u Identity a -> ParsecT String u Identity a
m_identifier :: ParsecT String u Identity String
m_integer :: ParsecT String u Identity Integer
m_brackets :: ParsecT String u Identity a -> ParsecT String u Identity a
m_commaSep :: ParsecT String u Identity a -> ParsecT String u Identity [a]
m_commaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
m_reserved :: String -> ParsecT String u Identity ()
m_whiteSpace :: ParsecT String u Identity ()

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
