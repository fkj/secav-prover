module Tests where

testcases :: [(String, String)]
testcases =
  [ ("imp", "Imp a b"),
    ("con", "Con a a"),
    ("p", "p"),
    ("ex7.2b", "Imp (Imp (Uni p[0]) (Uni q[0])) (Uni (Imp p[0] q[0]))"),
    ("ex7.4b", "Imp (Uni (Imp A[0] B[0])) (Imp (Exi A[0]) (Uni B[0]))"),
    ("ex7.4c", "Imp (Dis (Uni A[0]) (Exi B[0])) (Uni (Dis A[0] B[0]))"),
    ("ex7.4d", "Imp (Imp (Exi A[0]) (Exi B[0])) (Uni (Imp A[0] B[0]))"),
    ("ex7.9", "Imp (Imp (Uni p[0]) (Uni q[0])) (Uni (Imp p[0] q[0]))"),
    ("ex9.4", "Imp (Uni (Exi A[1,0])) (Uni A[0, f[0]])")
  ]
