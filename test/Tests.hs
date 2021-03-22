module Tests where

testcases :: [(String, String)]
testcases =
  [ ("true", "Imp a a")
  , ("false", "Neg (Neg (Imp a a))")
  , ("negations", "Imp (Neg p) (Neg (Neg (Neg p)))")
  , ("excludedMiddle", "Dis a (Neg a)")
  , ("excludedMiddle2", "Dis (Neg a) a")
  , ("impNeg", "Dis p (Imp p q)")
  , ("extraCon", "Imp (Con p q) (Imp r (Con p r))")
  , ("bigCon", "Con (Con (Imp a a) (Imp b b)) (Con (Imp c c) (Imp d d))")
  ]
