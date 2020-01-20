{-# language BangPatterns #-}
module Data.Trie.Word8
  ( Trie
  , empty
  , singleton
  , insert
  , append
  , prepend
  , lookup
  ) where

import Prelude hiding (Maybe(..), lookup)
import qualified Prelude

import Data.Bytes (Bytes)
import Data.Map.Word8 (Map)
import Data.Maybe.Unpacked (Maybe(..))
import Data.Word (Word8)

import qualified Data.Bytes as Bytes
import qualified Data.Map.Word8 as Map
import qualified Data.Maybe.Unpacked as Maybe

-- the `Maybe a` is a possible endpoint; it comes before the children
-- INVARIANT: Run ctor never has empty Bytes
data Trie a
  = Nil {-# unpack #-} !(Maybe a)
  | Branch {-# unpack #-} !(Maybe a) !(Map (Trie a))
  -- TODO use Bytes? or ByteArray directly?
  -- ByteArray uses more copying on insert, but lookup may be faster
  -- TODO it seems like I should be able to inline the Trie, but would that help?
  | Run {-# unpack #-} !(Maybe a) {-# unpack #-} !Bytes !(Trie a)
  deriving (Eq{- TODO needs instance for Map, Functor-})


------------ Construction ------------

empty :: Trie a
empty = Nil Nothing

singleton :: Bytes -> a -> Trie a
singleton k v
  | Bytes.null k = Nil (Just v)
  | otherwise = Run Nothing k $ Nil (Just v)

prepend :: Bytes -> Trie a -> Trie a
prepend bytes next
  | Bytes.null bytes = next
  | otherwise = Run Nothing bytes next

insert :: Semigroup a => Bytes -> a -> Trie a -> Trie a
insert k v' = (`append` singleton k v')

append :: Semigroup a => Trie a -> Trie a -> Trie a
append (Nil a) (Nil b) =
  Nil (a <> b)
append (Nil a) (Branch b children') =
  Branch (a <> b) children'
append (Nil a) (Run b run' next') =
  Run (a <> b) run' next'
append (Branch a children) (Nil b) =
  Branch (a <> b) children
append (Branch a children) (Branch b children') =
  Branch (a <> b) (Map.union children children')
append (Branch a children) r@(Run _ _ _) =
  Branch (a <> b) (Map.union children (Map.singleton c child'))
  where
  (b, c, child') = unsafeUnconsRun r
append (Run a run next) (Nil b) =
  (Run (a <> b) run next)
append r@(Run _ _ _) (Branch b children') =
  Branch (a <> b) (Map.union (Map.singleton c child') children')
  where
  (a, c, child') = unsafeUnconsRun r
append (Run a run next) (Run b run' next') =
  if Bytes.null common
    then
      let mkChild bytes trie = case uncons bytes of
            Just (c, k) -> Map.singleton c (prepend k trie)
            Nothing -> error "invariant violation: empty run bytes"
          child = mkChild run next
          child' = mkChild run' next'
      in Branch (a <> b) $ child `Map.union` child'
    else
      let child = prepend (uncommon run) next
          child' = prepend (uncommon run') next'
      in Run (a <> b) common $ append child child'
  where
  common = sharedPrefix run run'
  uncommon bytes = Bytes.unsafeDrop (Bytes.length common) bytes


------------ Query ------------

lookup :: Bytes -> Trie a -> Prelude.Maybe a
lookup k (Nil valO)
  | Bytes.null k = Maybe.toBaseMaybe valO
  | otherwise = Prelude.Nothing
lookup k (Branch valO children) = case uncons k of
  Nothing -> Maybe.toBaseMaybe valO
  Just (c, k') -> lookup k' =<< Map.lookup c children
lookup k (Run v run next)
  | Bytes.null k = Maybe.toBaseMaybe v
  | run `Bytes.isPrefixOf` k =
    let k' = Bytes.unsafeDrop (Bytes.length run) k
    in lookup k' next
  | otherwise = Prelude.Nothing


------ Helpers ------

unsafeUnconsRun :: Trie a -> (Maybe a, Word8, Trie a)
unsafeUnconsRun (Run v0 bs next) = (v0, c, run')
  where
  c = Bytes.unsafeIndex bs 0
  run' = Run Nothing bs' next
  bs' = Bytes.unsafeDrop 1 bs
unsafeUnconsRun (Nil _) = error "unsafeUnconsRun on Nil trie"
unsafeUnconsRun (Branch _ _) = error "unsafeUnconsRun on Branch trie"


------ Workarounds ------

-- FIXME move this upstream
uncons :: Bytes -> Maybe (Word8, Bytes)
uncons bytes
  | Bytes.null bytes = Nothing
  | otherwise = Just (Bytes.unsafeIndex bytes 0, Bytes.unsafeDrop 1 bytes)

-- FIXME move this upstream
sharedPrefix :: Bytes -> Bytes -> Bytes
sharedPrefix a b = loop 0
  where
  loop :: Int -> Bytes
  loop !into
    | into < maxLen
      && Bytes.unsafeIndex a into == Bytes.unsafeIndex b into
      = loop (into + 1)
    | otherwise = Bytes.unsafeTake into a
  maxLen = min (Bytes.length a) (Bytes.length b)
