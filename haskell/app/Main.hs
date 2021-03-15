module Main where

import Parser
import SeCaVGenerator
import ProofExtractor
import SeCaV_Enum

import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> print "Too few arguments"
    [x] -> case parser x of
             Left error -> print error
             Right sequent ->
               let result = genInit sequent in
               let formulas = fst result in
               let names = snd result in
               let proof = secavTree formulas in
               putStrLn $ extract names proof
    _ -> print "Too many arguments"
