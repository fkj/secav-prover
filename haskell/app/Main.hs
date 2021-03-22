module Main where

import Parser
import SeCaVGenerator
import ProofExtractor
import SeCaV_Enum

import Options.Applicative
import qualified ProofParser
import IsabelleGenerator (genProgram)

data Arguments = Arguments
  { formula :: String
  , isabelle :: Bool
  }

arguments :: Parser Arguments
arguments = Arguments
            <$> argument str
            (  metavar "FORMULA"
            <> help "Formula to attempt to prove" )
            <*> switch
            ( long "isabelle"
            <> short 'i'
            <> help "Whether to output an Isabelle proof" )

main :: IO ()
main = run =<< execParser opts
  where
    opts = info (arguments <**> helper)
      ( fullDesc
      <> progDesc "Attempt to prove a first-order formula"
      <> header "secav-prover - a prover for SeCaV" )

run :: Arguments -> IO ()
run (Arguments formula isabelle) =
  case parser formula of
    Left error -> print error
    Right sequent ->
      let (formulas, names) = genInit sequent in
        let proof = secavTree formulas in
          let short = extract names proof in
            if isabelle
            then
              let parse = ProofParser.parser short in
                case parse of
                  Left e -> print $ show e
                  Right ast ->
                    let isabelleProof = genProgram ast in
                      putStrLn isabelleProof
            else
              putStrLn short
