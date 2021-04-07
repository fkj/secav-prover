module Main where

import Parser
import SeCaVGenerator
import ProofExtractor
import SeCaV_Enum

import Options.Applicative
import qualified ProofParser
import IsabelleGenerator (genFile)
import System.FilePath (takeBaseName)

data Arguments = Arguments
  { formula :: String
  , isabelle :: Maybe String
  }

arguments :: Parser Arguments
arguments = Arguments
            <$> argument str (metavar "FORMULA" <> help "Formula to attempt to prove")
            <*> (optional $ strOption
                  $ long "isabelle"
                    <> short 'i'
                    <> metavar "FILENAME"
                    <> help "Output an Isabelle proof in FILENAME")

main :: IO ()
main = run =<< execParser opts
  where
    opts = info (arguments <**> helper)
      ( fullDesc
      <> progDesc "Attempt to prove the first-order formula FORMULA"
      <> header "secav-prover - a prover for SeCaV" )

run :: Arguments -> IO ()
run (Arguments formula isabelle) =
  case parser formula of
    Left error -> print error
    Right sequent ->
      let (formulas, names) = genInit sequent in
        let proof = secavTree formulas in
          let short = extract names proof in
            case isabelle of
              Just file ->
                let parse = ProofParser.parser short in
                  case parse of
                    Left e -> print e
                    Right ast ->
                      let isabelleProof = genFile (takeBaseName file) ast in
                        writeFile file isabelleProof
              Nothing ->
                putStrLn short
