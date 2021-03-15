module Main where

import SeCaV_Enum
import Instances

main :: IO ()
main = do
  print (secavTree thm1)
