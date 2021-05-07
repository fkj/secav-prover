{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SeCaV_Enum(Phase(..), equal_phase, Prule(..), rules, rho, maxFunTm, maxFun,
              generate_new, branchDone, flatten, subterm_tm, subterm_fm,
              subterms, abdDone, peff, secavTree, secavProver)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lazy;
import qualified MaybeExt;
import qualified Orderings;
import qualified List;
import qualified FSet;
import qualified Abstract_Completeness;
import qualified Stream;
import qualified SeCaV;
import qualified Arith;

data Phase = PBasic | PABD | PPreGamma Arith.Nat [SeCaV.Tm]
  | PInstGamma Arith.Nat [SeCaV.Tm] [SeCaV.Tm] Bool;

equal_phase :: Phase -> Phase -> Bool;
equal_phase (PPreGamma x31 x32) (PInstGamma x41 x42 x43 x44) = False;
equal_phase (PInstGamma x41 x42 x43 x44) (PPreGamma x31 x32) = False;
equal_phase PABD (PInstGamma x41 x42 x43 x44) = False;
equal_phase (PInstGamma x41 x42 x43 x44) PABD = False;
equal_phase PABD (PPreGamma x31 x32) = False;
equal_phase (PPreGamma x31 x32) PABD = False;
equal_phase PBasic (PInstGamma x41 x42 x43 x44) = False;
equal_phase (PInstGamma x41 x42 x43 x44) PBasic = False;
equal_phase PBasic (PPreGamma x31 x32) = False;
equal_phase (PPreGamma x31 x32) PBasic = False;
equal_phase PBasic PABD = False;
equal_phase PABD PBasic = False;
equal_phase (PInstGamma x41 x42 x43 x44) (PInstGamma y41 y42 y43 y44) =
  Arith.equal_nat x41 y41 && x42 == y42 && x43 == y43 && x44 == y44;
equal_phase (PPreGamma x31 x32) (PPreGamma y31 y32) =
  Arith.equal_nat x31 y31 && x32 == y32;
equal_phase PABD PABD = True;
equal_phase PBasic PBasic = True;

instance Eq Phase where {
  a == b = equal_phase a b;
};

data Prule = Basic | AlphaDis | AlphaImp | AlphaCon | BetaCon | BetaImp
  | BetaDis | DeltaUni | DeltaExi | NegNeg | GammaExi | GammaUni | Rotate
  | Duplicate | Next;

rules :: Stream.Stream Prule;
rules =
  Stream.cycle
    [Basic, AlphaDis, AlphaImp, AlphaCon, BetaCon, BetaImp, BetaDis, DeltaUni,
      DeltaExi, NegNeg, GammaExi, GammaUni, Rotate, Duplicate, Next];

rho :: Stream.Stream Prule;
rho = Abstract_Completeness.fenum_uu rules;

maxFunTm :: SeCaV.Tm -> Arith.Nat;
maxFunTm (SeCaV.Fun n ts) =
  Orderings.max n
    (List.foldl (\ a x -> Orderings.max a (maxFunTm x)) Arith.zero_nat ts);
maxFunTm (SeCaV.Var n) = Arith.zero_nat;

maxFun :: SeCaV.Fm -> Arith.Nat;
maxFun (SeCaV.Pre n ts) =
  List.foldl (\ a x -> Orderings.max a (maxFunTm x)) Arith.zero_nat ts;
maxFun (SeCaV.Imp f1 f2) = Orderings.max (maxFun f1) (maxFun f2);
maxFun (SeCaV.Dis f1 f2) = Orderings.max (maxFun f1) (maxFun f2);
maxFun (SeCaV.Con f1 f2) = Orderings.max (maxFun f1) (maxFun f2);
maxFun (SeCaV.Exi f) = maxFun f;
maxFun (SeCaV.Uni f) = maxFun f;
maxFun (SeCaV.Neg f) = maxFun f;

generate_new :: SeCaV.Fm -> [SeCaV.Fm] -> Arith.Nat;
generate_new p z =
  Arith.plus_nat Arith.one_nat
    (Orderings.max (maxFun p)
      (List.foldl (\ a x -> Orderings.max a (maxFun x)) Arith.zero_nat z));

branchDone :: [SeCaV.Fm] -> Bool;
branchDone [] = False;
branchDone (SeCaV.Neg p : z) = List.member z p || branchDone z;
branchDone (SeCaV.Pre v va : z) =
  List.member z (SeCaV.Neg (SeCaV.Pre v va)) || branchDone z;
branchDone (SeCaV.Imp v va : z) =
  List.member z (SeCaV.Neg (SeCaV.Imp v va)) || branchDone z;
branchDone (SeCaV.Dis v va : z) =
  List.member z (SeCaV.Neg (SeCaV.Dis v va)) || branchDone z;
branchDone (SeCaV.Con v va : z) =
  List.member z (SeCaV.Neg (SeCaV.Con v va)) || branchDone z;
branchDone (SeCaV.Exi v : z) =
  List.member z (SeCaV.Neg (SeCaV.Exi v)) || branchDone z;
branchDone (SeCaV.Uni v : z) =
  List.member z (SeCaV.Neg (SeCaV.Uni v)) || branchDone z;

flatten :: forall a. [[a]] -> [a];
flatten [] = [];
flatten (l : ls) = l ++ flatten ls;

subterm_tm :: SeCaV.Tm -> [SeCaV.Tm];
subterm_tm (SeCaV.Fun n ts) =
  SeCaV.Fun n ts : List.remdups (flatten (map subterm_tm ts));
subterm_tm (SeCaV.Var n) = [SeCaV.Var n];

subterm_fm :: SeCaV.Fm -> [SeCaV.Tm];
subterm_fm (SeCaV.Pre uu ts) = List.remdups (flatten (map subterm_tm ts));
subterm_fm (SeCaV.Imp f1 f2) = List.remdups (subterm_fm f1 ++ subterm_fm f2);
subterm_fm (SeCaV.Dis f1 f2) = List.remdups (subterm_fm f1 ++ subterm_fm f2);
subterm_fm (SeCaV.Con f1 f2) = List.remdups (subterm_fm f1 ++ subterm_fm f2);
subterm_fm (SeCaV.Exi f) = subterm_fm f;
subterm_fm (SeCaV.Uni f) = subterm_fm f;
subterm_fm (SeCaV.Neg f) = subterm_fm f;

subterms :: [SeCaV.Fm] -> [SeCaV.Tm];
subterms s = List.remdups (flatten (map subterm_fm s));

abdDone :: [SeCaV.Fm] -> Bool;
abdDone (SeCaV.Dis uu uv : uw) = False;
abdDone (SeCaV.Imp ux uy : uz) = False;
abdDone (SeCaV.Neg (SeCaV.Con va vb) : vc) = False;
abdDone (SeCaV.Con vd ve : vf) = False;
abdDone (SeCaV.Neg (SeCaV.Imp vg vh) : vi) = False;
abdDone (SeCaV.Neg (SeCaV.Dis vj vk) : vl) = False;
abdDone (SeCaV.Neg (SeCaV.Neg vm) : vn) = False;
abdDone (SeCaV.Uni vo : vp) = False;
abdDone (SeCaV.Neg (SeCaV.Exi vq) : vr) = False;
abdDone (SeCaV.Pre v va : z) = abdDone z;
abdDone (SeCaV.Exi v : z) = abdDone z;
abdDone (SeCaV.Neg (SeCaV.Pre va vb) : z) = abdDone z;
abdDone (SeCaV.Neg (SeCaV.Uni va) : z) = abdDone z;
abdDone [] = True;

peff :: Prule -> ([SeCaV.Fm], Phase) -> Maybe (FSet.Fset ([SeCaV.Fm], Phase));
peff Basic (p : z, PBasic) =
  (if List.member z (SeCaV.Neg p) then Just FSet.bot_fset else Nothing);
peff Basic ([], PBasic) = Nothing;
peff Basic ([], PABD) = Nothing;
peff Basic ([], PPreGamma v va) = Nothing;
peff Basic ([], PInstGamma v va vb vc) = Nothing;
peff Basic (uu, PABD) = Nothing;
peff Basic (uu, PPreGamma v va) = Nothing;
peff Basic (uu, PInstGamma v va vb vc) = Nothing;
peff Rotate (p : z, PBasic) =
  (if branchDone (p : z) && not (List.member z (SeCaV.Neg p))
    then Just (FSet.finsert (z ++ [p], PBasic) FSet.bot_fset) else Nothing);
peff Rotate ([], uw) = Nothing;
peff Next (s, PBasic) =
  (if branchDone s then Nothing
    else Just (FSet.finsert (s, PABD) FSet.bot_fset));
peff AlphaDis (SeCaV.Dis p q : z, PABD) =
  Just (FSet.finsert (p : q : z, PBasic) FSet.bot_fset);
peff AlphaDis ([], uy) = Nothing;
peff AlphaDis (SeCaV.Pre vb vc : va, uy) = Nothing;
peff AlphaDis (SeCaV.Imp vb vc : va, uy) = Nothing;
peff AlphaDis (SeCaV.Con vb vc : va, uy) = Nothing;
peff AlphaDis (SeCaV.Exi vb : va, uy) = Nothing;
peff AlphaDis (SeCaV.Uni vb : va, uy) = Nothing;
peff AlphaDis (SeCaV.Neg vb : va, uy) = Nothing;
peff AlphaDis (ux, PBasic) = Nothing;
peff AlphaDis (ux, PPreGamma v va) = Nothing;
peff AlphaDis (ux, PInstGamma v va vb vc) = Nothing;
peff AlphaImp (SeCaV.Imp p q : z, PABD) =
  Just (FSet.finsert (SeCaV.Neg p : q : z, PBasic) FSet.bot_fset);
peff AlphaImp ([], va) = Nothing;
peff AlphaImp (SeCaV.Pre vc vd : vb, va) = Nothing;
peff AlphaImp (SeCaV.Dis vc vd : vb, va) = Nothing;
peff AlphaImp (SeCaV.Con vc vd : vb, va) = Nothing;
peff AlphaImp (SeCaV.Exi vc : vb, va) = Nothing;
peff AlphaImp (SeCaV.Uni vc : vb, va) = Nothing;
peff AlphaImp (SeCaV.Neg vc : vb, va) = Nothing;
peff AlphaImp (uz, PBasic) = Nothing;
peff AlphaImp (uz, PPreGamma v vb) = Nothing;
peff AlphaImp (uz, PInstGamma v vb vc vd) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Con p q) : z, PABD) =
  Just (FSet.finsert (SeCaV.Neg p : SeCaV.Neg q : z, PBasic) FSet.bot_fset);
peff AlphaCon ([], vc) = Nothing;
peff AlphaCon (SeCaV.Pre vd ve : va, vc) = Nothing;
peff AlphaCon (SeCaV.Imp vd ve : va, vc) = Nothing;
peff AlphaCon (SeCaV.Dis vd ve : va, vc) = Nothing;
peff AlphaCon (SeCaV.Con vd ve : va, vc) = Nothing;
peff AlphaCon (SeCaV.Exi vd : va, vc) = Nothing;
peff AlphaCon (SeCaV.Uni vd : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Pre ve vf) : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Imp ve vf) : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Dis ve vf) : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Exi ve) : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Uni ve) : va, vc) = Nothing;
peff AlphaCon (SeCaV.Neg (SeCaV.Neg ve) : va, vc) = Nothing;
peff AlphaCon (vb, PBasic) = Nothing;
peff AlphaCon (vb, PPreGamma v va) = Nothing;
peff AlphaCon (vb, PInstGamma v va vd ve) = Nothing;
peff BetaCon (SeCaV.Con p q : z, PABD) =
  Just (FSet.finsert (p : z, PBasic)
         (FSet.finsert (q : z, PBasic) FSet.bot_fset));
peff BetaCon ([], ve) = Nothing;
peff BetaCon (SeCaV.Pre vb vc : va, ve) = Nothing;
peff BetaCon (SeCaV.Imp vb vc : va, ve) = Nothing;
peff BetaCon (SeCaV.Dis vb vc : va, ve) = Nothing;
peff BetaCon (SeCaV.Exi vb : va, ve) = Nothing;
peff BetaCon (SeCaV.Uni vb : va, ve) = Nothing;
peff BetaCon (SeCaV.Neg vb : va, ve) = Nothing;
peff BetaCon (vd, PBasic) = Nothing;
peff BetaCon (vd, PPreGamma v va) = Nothing;
peff BetaCon (vd, PInstGamma v va vb vc) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Imp p q) : z, PABD) =
  Just (FSet.finsert (p : z, PBasic)
         (FSet.finsert (SeCaV.Neg q : z, PBasic) FSet.bot_fset));
peff BetaImp ([], vg) = Nothing;
peff BetaImp (SeCaV.Pre vb vc : va, vg) = Nothing;
peff BetaImp (SeCaV.Imp vb vc : va, vg) = Nothing;
peff BetaImp (SeCaV.Dis vb vc : va, vg) = Nothing;
peff BetaImp (SeCaV.Con vb vc : va, vg) = Nothing;
peff BetaImp (SeCaV.Exi vb : va, vg) = Nothing;
peff BetaImp (SeCaV.Uni vb : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Pre vc vd) : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Dis vc vd) : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Con vc vd) : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Exi vc) : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Uni vc) : va, vg) = Nothing;
peff BetaImp (SeCaV.Neg (SeCaV.Neg vc) : va, vg) = Nothing;
peff BetaImp (vf, PBasic) = Nothing;
peff BetaImp (vf, PPreGamma v va) = Nothing;
peff BetaImp (vf, PInstGamma v va vb vc) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Dis p q) : z, PABD) =
  Just (FSet.finsert (SeCaV.Neg p : z, PBasic)
         (FSet.finsert (SeCaV.Neg q : z, PBasic) FSet.bot_fset));
peff BetaDis ([], vi) = Nothing;
peff BetaDis (SeCaV.Pre vb vc : va, vi) = Nothing;
peff BetaDis (SeCaV.Imp vb vc : va, vi) = Nothing;
peff BetaDis (SeCaV.Dis vb vc : va, vi) = Nothing;
peff BetaDis (SeCaV.Con vb vc : va, vi) = Nothing;
peff BetaDis (SeCaV.Exi vb : va, vi) = Nothing;
peff BetaDis (SeCaV.Uni vb : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Pre vc vd) : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Imp vc vd) : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Con vc vd) : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Exi vc) : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Uni vc) : va, vi) = Nothing;
peff BetaDis (SeCaV.Neg (SeCaV.Neg vc) : va, vi) = Nothing;
peff BetaDis (vh, PBasic) = Nothing;
peff BetaDis (vh, PPreGamma v va) = Nothing;
peff BetaDis (vh, PInstGamma v va vb vc) = Nothing;
peff DeltaUni (SeCaV.Uni p : z, PABD) =
  Just (FSet.finsert
         (SeCaV.sub Arith.zero_nat (SeCaV.Fun (generate_new p z) []) p : z,
           PBasic)
         FSet.bot_fset);
peff DeltaUni ([], vk) = Nothing;
peff DeltaUni (SeCaV.Pre vb vc : va, vk) = Nothing;
peff DeltaUni (SeCaV.Imp vb vc : va, vk) = Nothing;
peff DeltaUni (SeCaV.Dis vb vc : va, vk) = Nothing;
peff DeltaUni (SeCaV.Con vb vc : va, vk) = Nothing;
peff DeltaUni (SeCaV.Exi vb : va, vk) = Nothing;
peff DeltaUni (SeCaV.Neg vb : va, vk) = Nothing;
peff DeltaUni (vj, PBasic) = Nothing;
peff DeltaUni (vj, PPreGamma v va) = Nothing;
peff DeltaUni (vj, PInstGamma v va vb vc) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Exi p) : z, PABD) =
  Just (FSet.finsert
         (SeCaV.Neg
            (SeCaV.sub Arith.zero_nat (SeCaV.Fun (generate_new p z) []) p) :
            z,
           PBasic)
         FSet.bot_fset);
peff DeltaExi ([], vm) = Nothing;
peff DeltaExi (SeCaV.Pre vb vc : va, vm) = Nothing;
peff DeltaExi (SeCaV.Imp vb vc : va, vm) = Nothing;
peff DeltaExi (SeCaV.Dis vb vc : va, vm) = Nothing;
peff DeltaExi (SeCaV.Con vb vc : va, vm) = Nothing;
peff DeltaExi (SeCaV.Exi vb : va, vm) = Nothing;
peff DeltaExi (SeCaV.Uni vb : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Pre vc vd) : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Imp vc vd) : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Dis vc vd) : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Con vc vd) : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Uni vc) : va, vm) = Nothing;
peff DeltaExi (SeCaV.Neg (SeCaV.Neg vc) : va, vm) = Nothing;
peff DeltaExi (vl, PBasic) = Nothing;
peff DeltaExi (vl, PPreGamma v va) = Nothing;
peff DeltaExi (vl, PInstGamma v va vb vc) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Neg p) : z, PABD) =
  Just (FSet.finsert (p : z, PBasic) FSet.bot_fset);
peff NegNeg ([], vo) = Nothing;
peff NegNeg (SeCaV.Pre vb vc : va, vo) = Nothing;
peff NegNeg (SeCaV.Imp vb vc : va, vo) = Nothing;
peff NegNeg (SeCaV.Dis vb vc : va, vo) = Nothing;
peff NegNeg (SeCaV.Con vb vc : va, vo) = Nothing;
peff NegNeg (SeCaV.Exi vb : va, vo) = Nothing;
peff NegNeg (SeCaV.Uni vb : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Pre vc vd) : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Imp vc vd) : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Dis vc vd) : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Con vc vd) : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Exi vc) : va, vo) = Nothing;
peff NegNeg (SeCaV.Neg (SeCaV.Uni vc) : va, vo) = Nothing;
peff NegNeg (vn, PBasic) = Nothing;
peff NegNeg (vn, PPreGamma v va) = Nothing;
peff NegNeg (vn, PInstGamma v va vb vc) = Nothing;
peff Rotate (p : z, PABD) =
  (if abdDone (p : z) then Nothing
    else (if abdDone [p] then Just (FSet.finsert (z ++ [p], PABD) FSet.bot_fset)
           else Nothing));
peff Next (s, PABD) =
  (if abdDone s
    then Just (FSet.finsert (s, PPreGamma (List.size_list s) (subterms s))
                FSet.bot_fset)
    else Nothing);
peff Rotate (SeCaV.Exi p : vp, PPreGamma vq vr) = Nothing;
peff Rotate (SeCaV.Neg (SeCaV.Uni p) : vs, PPreGamma vt vu) = Nothing;
peff Rotate (SeCaV.Pre v va : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Pre v va],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Imp v va : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Imp v va],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Dis v va : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Dis v va],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Con v va : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Con v va],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Uni v : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Uni v],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Pre va vb) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Pre va vb)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Imp va vb) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Imp va vb)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Dis va vb) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Dis va vb)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Con va vb) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Con va vb)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Exi va) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Exi va)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Rotate (SeCaV.Neg (SeCaV.Neg va) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (z ++ [SeCaV.Neg (SeCaV.Neg va)],
                  PPreGamma (Arith.minus_nat n Arith.one_nat) ts)
                FSet.bot_fset));
peff Duplicate (SeCaV.Exi p : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (List.replicate (List.size_list ts) (SeCaV.Exi p) ++
                   z ++ [SeCaV.Exi p],
                  PInstGamma n ts ts False)
                FSet.bot_fset));
peff Duplicate (SeCaV.Neg (SeCaV.Uni p) : z, PPreGamma n ts) =
  (if Arith.equal_nat n Arith.zero_nat then Nothing
    else Just (FSet.finsert
                (List.replicate (List.size_list ts) (SeCaV.Neg (SeCaV.Uni p)) ++
                   z ++ [SeCaV.Neg (SeCaV.Uni p)],
                  PInstGamma n ts ts False)
                FSet.bot_fset));
peff Duplicate ([], va) = Nothing;
peff Duplicate (SeCaV.Pre vd ve : vc, va) = Nothing;
peff Duplicate (SeCaV.Imp vd ve : vc, va) = Nothing;
peff Duplicate (SeCaV.Dis vd ve : vc, va) = Nothing;
peff Duplicate (SeCaV.Con vd ve : vc, va) = Nothing;
peff Duplicate (SeCaV.Uni vd : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Pre v vb) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Imp v vb) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Dis v vb) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Con v vb) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Exi v) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg (SeCaV.Neg v) : vc, va) = Nothing;
peff Duplicate (SeCaV.Neg vd : vc, PBasic) = Nothing;
peff Duplicate (SeCaV.Neg vd : vc, PABD) = Nothing;
peff Duplicate (SeCaV.Neg vd : vc, PInstGamma v vb ve vf) = Nothing;
peff Duplicate (v, PBasic) = Nothing;
peff Duplicate (v, PABD) = Nothing;
peff Duplicate (v, PInstGamma vb vc vd ve) = Nothing;
peff Next (s, PPreGamma n vw) =
  (if Arith.equal_nat n Arith.zero_nat
    then Just (FSet.finsert (s, PBasic) FSet.bot_fset) else Nothing);
peff Rotate (p : z, PInstGamma n ots ts True) =
  Just (FSet.finsert (z ++ [p], PInstGamma n ots ts False) FSet.bot_fset);
peff Rotate (v : va, PInstGamma vy vz wa False) = Nothing;
peff GammaExi (SeCaV.Exi p : z, PInstGamma n ots (t : ts) False) =
  Just (FSet.finsert
         (SeCaV.sub Arith.zero_nat t p : z, PInstGamma n ots ts True)
         FSet.bot_fset);
peff GammaExi ([], wc) = Nothing;
peff GammaExi (SeCaV.Pre vb vc : va, wc) = Nothing;
peff GammaExi (SeCaV.Imp vb vc : va, wc) = Nothing;
peff GammaExi (SeCaV.Dis vb vc : va, wc) = Nothing;
peff GammaExi (SeCaV.Con vb vc : va, wc) = Nothing;
peff GammaExi (SeCaV.Uni vb : va, wc) = Nothing;
peff GammaExi (SeCaV.Neg vb : va, wc) = Nothing;
peff GammaExi (wb, PBasic) = Nothing;
peff GammaExi (wb, PABD) = Nothing;
peff GammaExi (wb, PPreGamma v va) = Nothing;
peff GammaExi (wb, PInstGamma v va [] vc) = Nothing;
peff GammaExi (wb, PInstGamma v va vb True) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Uni p) : z, PInstGamma n ots (t : ts) False) =
  Just (FSet.finsert
         (SeCaV.Neg (SeCaV.sub Arith.zero_nat t p) : z,
           PInstGamma n ots ts True)
         FSet.bot_fset);
peff GammaUni ([], we) = Nothing;
peff GammaUni (SeCaV.Pre vb vc : va, we) = Nothing;
peff GammaUni (SeCaV.Imp vb vc : va, we) = Nothing;
peff GammaUni (SeCaV.Dis vb vc : va, we) = Nothing;
peff GammaUni (SeCaV.Con vb vc : va, we) = Nothing;
peff GammaUni (SeCaV.Exi vb : va, we) = Nothing;
peff GammaUni (SeCaV.Uni vb : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Pre vc vd) : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Imp vc vd) : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Dis vc vd) : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Con vc vd) : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Exi vc) : va, we) = Nothing;
peff GammaUni (SeCaV.Neg (SeCaV.Neg vc) : va, we) = Nothing;
peff GammaUni (wd, PBasic) = Nothing;
peff GammaUni (wd, PABD) = Nothing;
peff GammaUni (wd, PPreGamma v va) = Nothing;
peff GammaUni (wd, PInstGamma v va [] vc) = Nothing;
peff GammaUni (wd, PInstGamma v va vb True) = Nothing;
peff Next (s, PInstGamma n ots [] False) =
  Just (FSet.finsert (s, PPreGamma (Arith.minus_nat n Arith.one_nat) ots)
         FSet.bot_fset);
peff Next (wf, PInstGamma wg wh (v : va) wj) = Nothing;
peff Next (wf, PInstGamma wg wh wi True) = Nothing;

secavTree ::
  ([SeCaV.Fm], Phase) ->
    Abstract_Completeness.Tree (([SeCaV.Fm], Phase), Prule);
secavTree = Abstract_Completeness.mkTree_effG_uu peff rho;

secavProver ::
  [SeCaV.Fm] -> Abstract_Completeness.Tree (([SeCaV.Fm], Phase), Prule);
secavProver = (\ x -> secavTree (x, PBasic));

}
