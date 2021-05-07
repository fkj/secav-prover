{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Stream(Stream(..), Stream_lazy(..), unlazy_stream, flat, cycle, stl, shd,
          stake, siterate, sdrop_while, smap)
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
import qualified List;

newtype Stream a = Lazy_stream (Lazy.Lazy (Stream_lazy a));

data Stream_lazy a = SCons_Lazy a (Stream a);

unlazy_stream :: forall a. Stream a -> Lazy.Lazy (Stream_lazy a);
unlazy_stream (Lazy_stream uu) = uu;

flat :: forall a. Stream [a] -> Stream a;
flat xaa =
  (case Lazy.force (unlazy_stream xaa) of {
    SCons_Lazy [] x1a ->
      (error :: forall a. String -> (() -> a) -> a)
        "Missing pattern in Stream.flat."
        (\ _ -> flat (Lazy_stream (Lazy.delay (\ _ -> SCons_Lazy [] x1a))));
    SCons_Lazy (x3a : x2a) x1a ->
      Lazy_stream
        (Lazy.delay
          (\ _ ->
            SCons_Lazy x3a
              (flat (if null x2a then x1a
                      else Lazy_stream
                             (Lazy.delay (\ _ -> SCons_Lazy x2a x1a))))));
  });

cycle :: forall a. [a] -> Stream a;
cycle (x : xs) =
  Lazy_stream (Lazy.delay (\ _ -> SCons_Lazy x (cycle (xs ++ [x]))));

stl :: forall a. Stream a -> Stream a;
stl xa = (case Lazy.force (unlazy_stream xa) of {
           SCons_Lazy _ x1aa -> x1aa;
         });

shd :: forall a. Stream a -> a;
shd xa = (case Lazy.force (unlazy_stream xa) of {
           SCons_Lazy x2aa _ -> x2aa;
         });

stake :: forall a. Arith.Nat -> Stream a -> [a];
stake n s =
  (if Arith.equal_nat n Arith.zero_nat then []
    else shd s : stake (Arith.minus_nat n Arith.one_nat) (stl s));

siterate :: forall a. (a -> a) -> a -> Stream a;
siterate f x =
  Lazy_stream (Lazy.delay (\ _ -> SCons_Lazy x (siterate f (f x))));

sdrop_while :: forall a. (a -> Bool) -> Stream a -> Stream a;
sdrop_while x1ba xa =
  (case Lazy.force (unlazy_stream xa) of {
    SCons_Lazy x3a x2ba ->
      (if x1ba x3a then sdrop_while x1ba x2ba
        else Lazy_stream (Lazy.delay (\ _ -> SCons_Lazy x3a x2ba)));
  });

smap :: forall a b. (a -> b) -> Stream a -> Stream b;
smap x1ba xa =
  (case Lazy.force (unlazy_stream xa) of {
    SCons_Lazy x3a x2ba ->
      Lazy_stream (Lazy.delay (\ _ -> SCons_Lazy (x1ba x3a) (smap x1ba x2ba)));
  });

}
