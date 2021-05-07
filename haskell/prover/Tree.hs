{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree(Fset, Stream, Tree, mkTree_effG_uu) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Set a = Set [a] | Coset [a];

newtype Fset a = Abs_fset (Set a);

data Stream a = SCons a (Stream a);

data Tree a = Node a (Fset (Tree a));

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

fset :: forall a. Fset a -> Set a;
fset (Abs_fset x) = x;

fimage :: forall b a. (b -> a) -> Fset b -> Fset a;
fimage xb xc = Abs_fset (image xb (fset xc));

sdrop_while :: forall a. (a -> Bool) -> Stream a -> Stream a;
sdrop_while p (SCons a s) = (if p a then sdrop_while p s else SCons a s);

mkTree_effG_uu ::
  forall a b. (a -> b -> Maybe (Fset b)) -> Stream a -> b -> Tree (b, a);
mkTree_effG_uu eff rs s =
  (case sdrop_while (\ r -> not (not (isNothing (eff r s)))) rs of {
    SCons r sa ->
      Node (s, r) (fimage (mkTree_effG_uu eff sa) (fromJust (eff r s)));
  });

}
