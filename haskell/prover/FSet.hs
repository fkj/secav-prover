{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module FSet(Fset(..), fset, fimage, finsert, bot_fset) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lazy;
import qualified MaybeExt;
import qualified Set;

newtype Fset a = Abs_fset (Set.Set a);

fset :: forall a. Fset a -> Set.Set a;
fset (Abs_fset x) = x;

fimage :: forall b a. (b -> a) -> Fset b -> Fset a;
fimage xb xc = Abs_fset (Set.image xb (fset xc));

finsert :: forall a. (Eq a) => a -> Fset a -> Fset a;
finsert xb xc = Abs_fset (Set.insert xb (fset xc));

bot_fset :: forall a. Fset a;
bot_fset = Abs_fset Set.bot_set;

}
