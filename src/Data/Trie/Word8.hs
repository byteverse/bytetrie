{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language ScopedTypeVariables #-}
{-# language TupleSections #-}
module Data.Trie.Word8
  ( Trie
  , empty
  , singleton
  , insert
  , append
  , unionWith
  , prepend
  , lookup
  , stripPrefix
  , stripPrefixWithKey
  , fromList
  , toList
  ) where

import Prelude hiding (lookup)

import Control.Applicative ((<|>))
import Data.Bifunctor (first)
import Data.Bytes (Bytes)
import Data.Foldable (foldl')
import Data.Map.Word8 (Map)
import Data.Word (Word8)

import qualified Data.Bytes as Bytes
import qualified Data.Map.Word8 as Map
import qualified Data.Maybe.Unpacked as UMaybe

-- the `Maybe a` is a possible endpoint; it comes before the children
-- INVARIANT: Run ctor never has Bytes length < 2
data Trie a
  -- TODO could save four machine words with a separate Nil case
  = Branch {-# unpack #-} !(UMaybe.Maybe a) !(Map (Trie a))
  -- TODO use Bytes? or ByteArray directly?
  -- ByteArray uses more copying on insert, but lookup may be faster
  -- TODO it seems like I should be able to inline the Trie, but would that help?
  | Run {-# unpack #-} !(UMaybe.Maybe a) {-# unpack #-} !Bytes !(Trie a)
  deriving (Eq{- TODO needs instance for Map, Functor-})

instance Semigroup a => Semigroup (Trie a) where (<>) = append
instance Semigroup a => Monoid (Trie a) where mempty = empty
instance Show a => Show (Trie a) where show = show . toList


------------ Construction ------------

empty :: Trie a
empty = Branch UMaybe.Nothing Map.empty

singleton :: Bytes -> a -> Trie a
singleton k v = prepend k $ Branch (UMaybe.Just v) Map.empty

-- Use this internally instead of the Run ctor.
-- This ensures the run length >= 2 invariant is maintained.
prepend :: Bytes -> Trie a -> Trie a
prepend bytes next = case Bytes.length bytes of
  0 -> next
  1 -> Branch UMaybe.Nothing (Map.singleton (Bytes.unsafeIndex bytes 0) next)
  _ -> Run UMaybe.Nothing bytes next

insert :: Bytes -> a -> Trie a -> Trie a
insert k v' = unionWith const (singleton k v')

append :: Semigroup a => Trie a -> Trie a -> Trie a
append = unionWith (<>)

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f trieA trieB = case (trieA, trieB) of
  (Branch a children, Branch b children') ->
    Branch (a `mergeValue` b) (mergeChildren children children')
  (Branch a children, r@(Run _ _ _)) ->
    Branch (a `mergeValue` b) (mergeChildren children (Map.singleton c child'))
    where
    (b, c, child') = unsafeUnconsRun r
  (r@(Run _ _ _), Branch b children') ->
    Branch (a `mergeValue` b) (mergeChildren (Map.singleton c child') children')
    where
    (a, c, child') = unsafeUnconsRun r
  (Run a run next, Run b run' next') ->
    if Bytes.null common
      then
        let mkChild bytes trie = case Bytes.uncons bytes of
              Prelude.Just (c, k) -> Map.singleton c (prepend k trie)
              Prelude.Nothing -> error "invariant violation: empty run bytes"
            child = mkChild run next
            child' = mkChild run' next'
        in Branch (a `mergeValue` b) $ child `Map.union` child'
      else
        let child = prepend (uncommon run) next
            child' = prepend (uncommon run') next'
        in Run (a `mergeValue` b) common $ unionWith f child child'
    where
    common = Bytes.longestCommonPrefix run run'
    uncommon bytes = Bytes.unsafeDrop (Bytes.length common) bytes
  where
    mergeChildren left right = Map.unionWith (unionWith f) left right
    mergeValue UMaybe.Nothing UMaybe.Nothing = UMaybe.Nothing
    mergeValue (UMaybe.Just x) (UMaybe.Just y) = UMaybe.Just (f x y)
    mergeValue x y = x <|> y


------------ Conversion ------------

fromList :: [(Bytes, a)] -> Trie a
fromList kvs = foldl' (flip $ unionWith const . uncurry singleton) empty kvs

toList :: Trie a -> [(Bytes, a)]
toList = \case
  Branch valO children -> fromValue valO ++ Map.foldrWithKeys f [] children
    where
    f k v acc = prependList (Bytes.singleton k) (toList v) ++ acc
  Run valO run next -> fromValue valO ++ prependList run (toList next)
  where
  fromValue valO = (mempty,) <$> UMaybe.maybeToList valO
  prependList run list = first (run <>) <$> list


------------ Query ------------

lookup :: Bytes -> Trie a -> Maybe a
lookup k (Branch valO children) = case Bytes.uncons k of
  Prelude.Nothing -> UMaybe.toBaseMaybe valO
  Prelude.Just (c, k') -> lookup k' =<< Map.lookup c children
lookup k (Run v run next)
  | Bytes.null k = UMaybe.toBaseMaybe v
  | run `Bytes.isPrefixOf` k =
    let k' = Bytes.unsafeDrop (Bytes.length run) k
    in lookup k' next
  | otherwise = Prelude.Nothing

stripPrefix :: Trie a -> Bytes -> Maybe (a, Bytes)
stripPrefix trie inp = first snd <$> stripPrefixWithKey trie inp

stripPrefixWithKey :: forall a. Trie a -> Bytes -> Maybe ((Bytes, a), Bytes)
stripPrefixWithKey trie0 rawInp = go 0 Nothing trie0
  where
  go :: Int -> Maybe (Bytes, a) -> Trie a -> Maybe ((Bytes, a), Bytes)
  go into prior trie =
    let inp = Bytes.unsafeDrop into rawInp
        candidate = (Bytes.unsafeTake into rawInp,) <$> extractValue trie
        found = candidate <|> prior
    in if | Bytes.null inp -> mkReturn <$> found
          | Run _ run next <- trie
          , run `Bytes.isPrefixOf` inp
            -> go (into + Bytes.length run) found next
          | Branch _ children <- trie
          , Just (c, _) <- Bytes.uncons inp
          , Just next <- Map.lookup c children
            -> go (into + 1) found next
          | otherwise -> mkReturn <$> found
  mkReturn (prefix, v) =
    let post = Bytes.unsafeDrop (Bytes.length prefix) rawInp
    in ((prefix, v), post)
  extractValue :: Trie a -> Maybe a
  extractValue = \case
    Run v _ _ -> UMaybe.toBaseMaybe v
    Branch v _ -> UMaybe.toBaseMaybe v


------ Helpers ------

unsafeUnconsRun :: Trie a -> (UMaybe.Maybe a, Word8, Trie a)
unsafeUnconsRun (Run v0 bs next) = (v0, c, run')
  where
  c = Bytes.unsafeIndex bs 0
  bs' = Bytes.unsafeDrop 1 bs
  run' = prepend bs' next
unsafeUnconsRun (Branch _ _) = error "unsafeUnconsRun on Branch trie"
