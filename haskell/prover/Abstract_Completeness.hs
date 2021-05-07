{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Abstract_Completeness(Tree(..), fenum_uu, mkTree_effG_uu) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Lazy;
import qualified MaybeExt;
import qualified Stream;
import qualified Arith;
import qualified FSet;

data Tree a = Node a (FSet.Fset (Tree a));

fenum_uu :: forall a. Stream.Stream a -> Stream.Stream a;
fenum_uu rules =
  Stream.flat
    (Stream.smap (\ n -> Stream.stake n rules)
      (Stream.siterate Arith.suc Arith.one_nat));

mkTree_effG_uu ::
  forall a b.
    (a -> b -> Maybe (FSet.Fset b)) -> Stream.Stream a -> b -> Tree (b, a);
mkTree_effG_uu eff rs s =
  (case Lazy.force
          (Stream.unlazy_stream
            (Stream.sdrop_while
              (\ r -> not (not (MaybeExt.isNothing (eff r s)))) rs))
    of {
    Stream.SCons_Lazy r sa ->
      Node (s, r)
        (FSet.fimage (mkTree_effG_uu eff sa) (MaybeExt.fromJust (eff r s)));
  });

}
