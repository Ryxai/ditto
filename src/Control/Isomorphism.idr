module Control.Isomorphism

import Data.Fin
import Data.Fin.Extra
import Control.Category

%default total
||| An isomorphism between two types
record Iso a b where
  constructor MkIso
  to : a -> b
  from : b -> a
  toFrom : (y : b) -> to (from y) = y
  fromTo : (x : a) -> from (to x) = x

||| Isomorphism is reflexive
isoRefl : Iso a a
isoRefl = MkIso id id (\_ => Refl) (\_ => Refl)

||| Isomorphism is transitive
isoTrans : Iso a b -> Iso b c -> Iso a c
isoTrans (MkIso to from toFrom fromTo) (MkIso to' from' toFrom' fromTo') =
  MkIso xto xfrom xtoFrom xfromTo
  where
    xto : a -> c
    xto = to' . to
    xfrom : c -> a
    xfrom = from . from'
    xtoFrom : (z : c) -> xto (xfrom z) = z
    xtoFrom z = rewrite toFrom $ from' z in toFrom' z
    xfromTo : (z : a) -> xfrom (xto z) = z
    xfromTo z = rewrite fromTo' $ to z in fromTo z 

Category Iso where
  id = isoRefl
  (.) = flip isoTrans

Semigroup (Iso a a) where
  (<+>) = isoTrans

Monoid (Iso a a) where
  neutral = isoRefl

||| Isomorphism is symmetric
isoSym : Iso a b -> Iso b a
isoSym (MkIso to from toFrom fromTo) = MkIso from to fromTo toFrom

|||Isomorhpisms over sums
eitherComm : Iso (Either a b) (Either b a)
eitherComm = MkIso mirror mirror mirrorMirror mirrorMirror where
  mirror : Either a' b' -> Either b' a'
  mirror (Left x) = Right x
  mirror (Right x) = Left x
  mirrorMirror : (x : Either a' b') -> mirror (mirror x) = x
  mirrorMirror (Left x) = Refl
  mirrorMirror (Right x) = Refl


|||Disjunction is associative
eitherAssoc : Iso (Either (Either a b) c) (Either a (Either b c))
eitherAssoc = MkIso eitherAssoc1 eitherAssoc2 ok1 ok2 where
  eitherAssoc1 : Either (Either a b) c -> Either a (Either b c)
  eitherAssoc1 (Left (Left x)) = Left x
  eitherAssoc1 (Left (Right x)) = Right (Left x)
  eitherAssoc1 (Right x) = Right (Right x)
  
  eitherAssoc2 : Either a (Either b c) -> Either (Either a b) c
  eitherAssoc2 (Left x) = Left (Left x)
  eitherAssoc2 (Right (Left x)) = Left (Right x)
  eitherAssoc2 (Right (Right x)) = Right x
  
  ok1 : (y : Either a (Either b c)) -> eitherAssoc1 (eitherAssoc2 y) = y
  ok1 (Left x) = Refl
  ok1 (Right (Left x)) = Refl
  ok1 (Right (Right x)) = Refl

  ok2 : (y : Either (Either a b) c) -> eitherAssoc2 (eitherAssoc1 y) = y
  ok2 (Left (Left x)) = Refl
  ok2 (Left (Right x)) = Refl
  ok2 (Right x) = Refl

||| Disjunction with false is a no-op
eitherBotLeft : Iso (Either Void a) a
eitherBotLeft = MkIso to from ok1 ok2 where
  to : Either Void a -> a
  to (Left x) = void x 
  to (Right x) = x
  from : a -> Either Void a
  from = Right
  ok1 : (y : a) -> to (from y) = y
  ok1 y = Refl
  ok2 : (y : Either Void a) -> from (to y) = y
  ok2 (Left x) = void x
  ok2 (Right x) = Refl

||| Disjunction with false is a no-op
eitherBotRight : Iso (Either a Void) a
eitherBotRight = isoTrans eitherComm eitherBotLeft

||| Isomorphism is a congruence with regards to disjunction
eitherCong : Iso a a' -> Iso b b' -> Iso (Either a b) (Either a' b')
eitherCong (MkIso to from toFrom fromTo) 
  (MkIso to' from' toFrom' fromTo') = MkIso (eitherMap to to') (eitherMap from from') ok1 ok2 where
    eitherMap : (c -> c') -> (d -> d') -> Either c d -> Either c' d'
    eitherMap f g (Left x) = Left (f x)
    eitherMap f g (Right x) = Right (g x)
    ok1 : (y : Either a' b') -> eitherMap to to' (eitherMap from from' y) = y
    ok1 (Left x) = rewrite toFrom x in Refl
    ok1 (Right x) = rewrite toFrom' x in Refl
    ok2 : (y : Either a b) -> eitherMap from from' (eitherMap to to' y) = y
    ok2 (Left x) = rewrite fromTo x in Refl
    ok2 (Right x) = rewrite fromTo' x in Refl


||| Isomorphism is a congruence with regards to disjunction on the left
eitherCongLeft : Iso a a' -> Iso (Either a b) (Either a' b)
eitherCongLeft x = eitherCong x isoRefl

||| Isomorphism is a congruence with regards to disjunction on the right
eitherCongRight : Iso b b' -> Iso (Either a b) (Either a b')
eitherCongRight x = eitherCong isoRefl x

---Isomorphisms over products
|||Conjunction is commutative
pairComm : Iso (a, b) (b, a)
pairComm = MkIso swap swap swapSwap swapSwap where
  swapSwap : (y : (a', b')) -> swap (swap y) = y
  swapSwap (x, y) = Refl


|||Conjunction is associative
pairAssoc : Iso (a, (b, c)) ((a, b), c)
pairAssoc = MkIso to from ok1 ok2 where
  to : (a, (b, c)) -> ((a, b), c)
  to (x, (y, z)) = ((x, y), z)
  from : ((a, b), c) -> (a, (b, c))
  from ((x, z), y) = (x, (z, y))
  ok1 : (y : ((a, b), c)) -> to (from y) = y
  ok1 ((x, z), y) = Refl
  ok2 : (y : (a, (b, c))) -> from (to y) = y
  ok2 (x, (y, z)) = Refl

||| Conjunction with true is a no-op
pairUnitRight : Iso (a, ()) a
pairUnitRight = MkIso fst (\x => (x, ())) (\x => Refl) (\(_, ()) => Refl)

||| Conjunction with true is a no-op
pairUnitLeft : Iso (() , a) a
pairUnitLeft = isoTrans pairComm pairUnitRight

||| Isomorphism is a congruence with regards to conjunction
pairCong : Iso a a' -> Iso b b' -> Iso (a, b) (a', b')
pairCong (MkIso to from toFrom fromTo) 
  (MkIso to' from' toFrom' fromTo') = 
    MkIso to'' from'' iso1 iso2 where
      to'' : (a, b) -> (a', b')
      to'' (x, y) = (to x, to' y)
      from'' : (a', b') -> (a, b)
      from'' (x, y) = (from x, from' y)
      iso1 : (z : (a', b')) -> to'' (from'' z) = z
      iso1 (x, y) = rewrite toFrom x in
                      rewrite toFrom' y in
                        Refl
      iso2 : (z : (a, b)) -> from'' (to'' z) = z
      iso2 (x, y) = rewrite fromTo x in
                      rewrite fromTo' y in
                        Refl

||| Isomorphism is a congruence with regards to conjunction on the left
pairCongLeft : Iso a a' -> Iso (a, b) (a', b)
pairCongLeft x = pairCong x isoRefl

pairCongRight : Iso b b' -> Iso (a, b) (a, b')
pairCongRight x = pairCong isoRefl x

--Distributibity of products over sums
||| Products distribute over sums
distribLeft : Iso (Either a b, c) (Either (a, c) (b, c))
distribLeft = MkIso to from toFrom fromTo where
  to : (Either a b, c) -> Either (a, c) (b, c)
  to ((Left x), y) = Left (x, y)
  to ((Right x), y) = Right (x, y)
  from : Either (a, c) (b, c) -> (Either a b, c)
  from (Left (x, y)) = (Left x, y)
  from (Right (x, y)) = (Right x, y)
  toFrom : (y : Either (a, c) (b, c)) -> to (from y) = y
  toFrom (Left (x, y)) = Refl
  toFrom (Right (x, y)) = Refl
  fromTo : (y : (Either a b, c)) -> from (to y) = y
  fromTo ((Left x), y) = Refl
  fromTo ((Right x), y) = Refl


distribRight : Iso (a, Either b c) (Either (a, b) (a, c))
distribRight = isoTrans (isoTrans pairComm distribLeft) (eitherCong pairComm pairComm)

{--Enableing preorder reasoning syntax over isomorphisms
||| Used for preorder reasoning syntax. Not intended for direct use.
qed : (a : Type) -> Iso a a
qed a = isoRefl

||| Used for preorder reasoning syntax. Not intended for direct use.
step : (a : Type) -> Iso a b -> Iso b c -> Iso a c
step a iso1 iso2 = isoTrans iso1 iso2-}

---Isomorphims over Maybe
||| Isomorphims is a congruence with regards to Maybe
maybeCong : Iso a b -> Iso (Maybe a) (Maybe b)
maybeCong (MkIso to from toFrom fromTo) 
  = MkIso (map to) (map from) ?ok1 ?ok2 where
    ok1 : (y : Maybe b) -> map to (map from y) = y
    ok1 Nothing = Refl
    ok1 (Just x) = rewrite toFrom x in Refl
    ok2 : (y : Maybe a) -> map from (map to y) = y
    ok2 Nothing = Refl
    ok2 (Just x) = rewrite fromTo x in Refl

|||`Maybe a` is the same as `Either () a`
maybeEither : Iso (Maybe a) (Either () a)
maybeEither = MkIso to from toFrom fromTo where
  to : Maybe a -> Either () a
  to Nothing = Left ()
  to (Just x) = Right x
  from : Either () a -> Maybe a
  from (Left ()) = Nothing
  from (Right x) = Just x
  toFrom : (y : Either () a) -> to (from y) = y
  toFrom (Left ()) = Refl
  toFrom (Right x) = Refl
  fromTo : (y : Maybe a) -> from (to y) = y
  fromTo Nothing = Refl
  fromTo (Just x) = Refl

|||Maybe of void is just unit
maybeVoidUnit : Iso (Maybe Void) ()
maybeVoidUnit = MkIso to from toFrom fromTo where
  to : Maybe Void -> ()
  to Nothing = ()
  to (Just x) = absurd x
  from : () -> Maybe Void
  from () = Nothing
  toFrom : (y : ()) -> to (from y) = y
  toFrom () = Refl
  fromTo : (y : Maybe Void) -> from (to y) = y
  fromTo Nothing = Refl
  fromTo (Just x) = absurd x

eitherMaybeLeftMaybe : Iso (Either (Maybe a) b) (Maybe (Either a b))
eitherMaybeLeftMaybe = MkIso to from toFrom fromTo where
  to : Either (Maybe a) b -> Maybe (Either a b)
  to (Left Nothing) = Nothing
  to (Left (Just x)) = Just (Left x)
  to (Right x) = Just (Right x)
  from : Maybe (Either a b) -> Either (Maybe a) b
  from Nothing = Left Nothing
  from (Just (Left x)) = Left (Just x)
  from (Just (Right x)) = Right x
  toFrom : (y : Maybe (Either a b)) -> to (from y) = y
  toFrom Nothing = Refl
  toFrom (Just (Left x)) = Refl
  toFrom (Just (Right x)) = Refl
  fromTo : (y : Either (Maybe a) b) -> from (to y) = y
  fromTo (Left Nothing) = Refl
  fromTo (Left (Just x)) = Refl
  fromTo (Right x) = Refl


eitherMaybeRight : Iso (Either a (Maybe b)) (Maybe (Either a b))
eitherMaybeRight = isoTrans 
  (isoTrans isoRefl eitherComm) 
  (isoTrans eitherMaybeLeftMaybe (maybeCong eitherComm))

--Isomorphisms over Fin
maybeIsoS: Iso (Maybe (Fin n)) (Fin (S n))
maybeIsoS = MkIso to from toFrom fromTo where
  to : Maybe (Fin n) -> Fin (S n)
  to Nothing = FZ
  to (Just x) = FS x 
  from : Fin (S n) -> Maybe (Fin n)
  from FZ = Nothing
  from (FS x) = Just x 
  toFrom : (y : Fin (S n)) -> to (from y) = y
  toFrom FZ = Refl
  toFrom (FS x) = Refl
  fromTo : (y : Maybe (Fin n)) -> from (to y) = y
  fromTo Nothing = Refl
  fromTo (Just x) = Refl

finZeroBot : Iso (Fin 0) Void
finZeroBot = MkIso to from toFrom fromTo where
  to : Fin 0 -> Void
  to FZ impossible
  to (FS x) impossible
  from : Void -> Fin 0
  from = absurd
  toFrom : (y : Void) -> to (from y) = y
  toFrom y = absurd y
  fromTo : (y : Fin 0) -> from (to y) = y
  fromTo FZ impossible
  fromTo (FS x) impossible

eitherFinPlus : {m,n : _} -> Iso (Either (Fin n) (Fin m)) (Fin (n + m))
eitherFinPlus = MkIso 
  indexSum 
  splitSum 
  indexOfSplitSumInverse 
  splitOfIndexSumInverse 

finPairTimes : {m,n : _} -> Iso (Fin m, Fin n) (Fin (m * n))
finPairTimes = MkIso 
  (uncurry indexProd)
  splitProd 
  indexOfSplitProdInverse 
  (\x => case x of
              (y, z) => splitOfIndexProdInverse y z)
