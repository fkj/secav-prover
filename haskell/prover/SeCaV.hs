{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SeCaV(Tm(..), Fm(..), equal_tm, equal_fm, sub_list, sub_term, inc_term,
         inc_list, sub)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lazy;
import qualified MaybeExt;
import qualified Arith;

data Tm = Fun Arith.Nat [Tm] | Var Arith.Nat;

data Fm = Pre Arith.Nat [Tm] | Imp Fm Fm | Dis Fm Fm | Con Fm Fm | Exi Fm
  | Uni Fm | Neg Fm;

instance Eq Tm where {
  a == b = equal_tm a b;
};

equal_tm :: Tm -> Tm -> Bool;
equal_tm (Fun x11 x12) (Var x2) = False;
equal_tm (Var x2) (Fun x11 x12) = False;
equal_tm (Var x2) (Var y2) = Arith.equal_nat x2 y2;
equal_tm (Fun x11 x12) (Fun y11 y12) = Arith.equal_nat x11 y11 && x12 == y12;

equal_fm :: Fm -> Fm -> Bool;
equal_fm (Uni x6) (Neg x7) = False;
equal_fm (Neg x7) (Uni x6) = False;
equal_fm (Exi x5) (Neg x7) = False;
equal_fm (Neg x7) (Exi x5) = False;
equal_fm (Exi x5) (Uni x6) = False;
equal_fm (Uni x6) (Exi x5) = False;
equal_fm (Con x41 x42) (Neg x7) = False;
equal_fm (Neg x7) (Con x41 x42) = False;
equal_fm (Con x41 x42) (Uni x6) = False;
equal_fm (Uni x6) (Con x41 x42) = False;
equal_fm (Con x41 x42) (Exi x5) = False;
equal_fm (Exi x5) (Con x41 x42) = False;
equal_fm (Dis x31 x32) (Neg x7) = False;
equal_fm (Neg x7) (Dis x31 x32) = False;
equal_fm (Dis x31 x32) (Uni x6) = False;
equal_fm (Uni x6) (Dis x31 x32) = False;
equal_fm (Dis x31 x32) (Exi x5) = False;
equal_fm (Exi x5) (Dis x31 x32) = False;
equal_fm (Dis x31 x32) (Con x41 x42) = False;
equal_fm (Con x41 x42) (Dis x31 x32) = False;
equal_fm (Imp x21 x22) (Neg x7) = False;
equal_fm (Neg x7) (Imp x21 x22) = False;
equal_fm (Imp x21 x22) (Uni x6) = False;
equal_fm (Uni x6) (Imp x21 x22) = False;
equal_fm (Imp x21 x22) (Exi x5) = False;
equal_fm (Exi x5) (Imp x21 x22) = False;
equal_fm (Imp x21 x22) (Con x41 x42) = False;
equal_fm (Con x41 x42) (Imp x21 x22) = False;
equal_fm (Imp x21 x22) (Dis x31 x32) = False;
equal_fm (Dis x31 x32) (Imp x21 x22) = False;
equal_fm (Pre x11 x12) (Neg x7) = False;
equal_fm (Neg x7) (Pre x11 x12) = False;
equal_fm (Pre x11 x12) (Uni x6) = False;
equal_fm (Uni x6) (Pre x11 x12) = False;
equal_fm (Pre x11 x12) (Exi x5) = False;
equal_fm (Exi x5) (Pre x11 x12) = False;
equal_fm (Pre x11 x12) (Con x41 x42) = False;
equal_fm (Con x41 x42) (Pre x11 x12) = False;
equal_fm (Pre x11 x12) (Dis x31 x32) = False;
equal_fm (Dis x31 x32) (Pre x11 x12) = False;
equal_fm (Pre x11 x12) (Imp x21 x22) = False;
equal_fm (Imp x21 x22) (Pre x11 x12) = False;
equal_fm (Neg x7) (Neg y7) = equal_fm x7 y7;
equal_fm (Uni x6) (Uni y6) = equal_fm x6 y6;
equal_fm (Exi x5) (Exi y5) = equal_fm x5 y5;
equal_fm (Con x41 x42) (Con y41 y42) = equal_fm x41 y41 && equal_fm x42 y42;
equal_fm (Dis x31 x32) (Dis y31 y32) = equal_fm x31 y31 && equal_fm x32 y32;
equal_fm (Imp x21 x22) (Imp y21 y22) = equal_fm x21 y21 && equal_fm x22 y22;
equal_fm (Pre x11 x12) (Pre y11 y12) = Arith.equal_nat x11 y11 && x12 == y12;

instance Eq Fm where {
  a == b = equal_fm a b;
};

sub_list :: Arith.Nat -> Tm -> [Tm] -> [Tm];
sub_list v s [] = [];
sub_list v s (t : l) = sub_term v s t : sub_list v s l;

sub_term :: Arith.Nat -> Tm -> Tm -> Tm;
sub_term v s (Var n) =
  (if Arith.less_nat n v then Var n
    else (if Arith.equal_nat n v then s
           else Var (Arith.minus_nat n Arith.one_nat)));
sub_term v s (Fun i l) = Fun i (sub_list v s l);

inc_term :: Tm -> Tm;
inc_term (Var n) = Var (Arith.plus_nat n Arith.one_nat);
inc_term (Fun i l) = Fun i (inc_list l);

inc_list :: [Tm] -> [Tm];
inc_list [] = [];
inc_list (t : l) = inc_term t : inc_list l;

sub :: Arith.Nat -> Tm -> Fm -> Fm;
sub v s (Pre i l) = Pre i (sub_list v s l);
sub v s (Imp p q) = Imp (sub v s p) (sub v s q);
sub v s (Dis p q) = Dis (sub v s p) (sub v s q);
sub v s (Con p q) = Con (sub v s p) (sub v s q);
sub v s (Exi p) = Exi (sub (Arith.plus_nat v Arith.one_nat) (inc_term s) p);
sub v s (Uni p) = Uni (sub (Arith.plus_nat v Arith.one_nat) (inc_term s) p);
sub v s (Neg p) = Neg (sub v s p);

}
