module Runner (tests) where

import AST (Program)
import Distribution.TestSuite
  ( Progress (Finished),
    Result (Fail, Pass),
    Test (Test),
    TestInstance (TestInstance, name, options, run, setOption, tags),
  )
import IsabelleGenerator (genProgram)
import Parser (parser)
import ProofExtractor (extract)
import ProofParser (parser)
import SeCaVGenerator (genInit)
import SeCaV_Enum (secavTree)
import System.Directory
  ( copyFile,
    createDirectoryIfMissing,
    removeDirectoryRecursive,
  )
import System.Exit (ExitCode (ExitFailure, ExitSuccess))
import System.Process (readProcessWithExitCode)

testcases :: [(String, String)]
testcases = [("imp", "Imp a a")]

tests :: IO [Test]
tests = do
  let testDir = "test-tmp"
  setup testDir
  let testResults = map (createTest testDir) testcases
  pure testResults

setup :: String -> IO ()
setup testDir = do
  createDirectoryIfMissing False testDir

tearDown :: String -> IO ()
tearDown testDir = do
  removeDirectoryRecursive testDir

createTest :: String -> (String, String) -> Test
createTest topdir (testDir, f) =
  let test testDir f =
        TestInstance
          { run = Finished <$> performTest (topdir <> "/" <> testDir) f,
            name = f,
            tags = [],
            options = [],
            setOption = \_ _ -> Right $ test testDir f
          }
   in Test $ test testDir f

performTest :: String -> String -> IO Result
performTest testDir f = do
  createDirectoryIfMissing False testDir
  copyFile "isabelle/SeCaV.thy" $ testDir <> "/SeCaV.thy"
  copyFile "test/ROOT" $ testDir <> "/ROOT"

  let parse = Parser.parser f
  case parse of
    Left e -> pure $ Fail $ show e
    Right fm -> do
      let (formula, names) = genInit fm
      let proofTree = secavTree formula
      let shortProof = extract names proofTree
      let proofParse = ProofParser.parser shortProof
      case proofParse of
        Left e -> pure $ Fail $ show e
        Right proofAst -> do
          let isabelleProof = genTestFile proofAst
          writeFile (testDir <> "/Test.thy") isabelleProof
          (exit, _, error) <- readProcessWithExitCode "isabelle" ["build", "-D", testDir] []
          case exit of
            ExitFailure _ -> pure $ Fail error
            ExitSuccess -> pure Pass

genTestFile :: Program -> String
genTestFile p =
  "theory Test imports SeCaV begin\n\n"
    <> genProgram p
    <> "\n\nend"