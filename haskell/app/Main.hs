module Main where

import SeCaVTranslator
import ProofExtractor
import Prover

import Options.Applicative
import ShortParser
import Unshortener (genFile)
import System.FilePath (takeBaseName)

data Arguments = Arguments
  { formula :: String
  , isabelle :: Maybe String
  }

arguments :: Parser Arguments
arguments = Arguments
            <$> argument str (metavar "FORMULA" <> help "Formula to attempt to prove")
            <*> optional (strOption
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
run (Arguments f i) =
  case sequentParser f of
    Left e -> print e
    Right s ->
      let (formulas, names) = genInit s in
        let proofTree = secavProver formulas in
          let shortProof = extract names $ extSurgery $ gammaSurgery $ nextSurgery proofTree in
            case i of
              Just file ->
                let parse = programParser shortProof in
                  case parse of
                    Left e -> print e
                    Right ast ->
                      let isabelleProof = genFile (takeBaseName file) ast in
                        writeFile file isabelleProof
              Nothing ->
                putStrLn shortProof
