{-# language BangPatterns #-}
{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TupleSections #-}
{-# language ViewPatterns #-}
module Data.Trie.Word8
  (
  -- * Trie Type
    Trie
  -- * Construction
  , empty
  , singleton
  -- ** Conversion
  , fromList
  , toList
  -- ** Insertion
  , insert
  , insertWith
  -- ** Deletion
  , delete
  -- ** Combine
  , union
  , unionWith
  , append
  , prepend
  -- * Query
  -- ** Lookup
  , lookup
  -- ** Size
  , null
  , size
  -- ** Detect Prefixes
  , stripPrefix
  , stripPrefixWithKey
  ) where

import Prelude hiding (null, lookup)
import qualified Prelude

import Control.Applicative ((<|>))
import Data.Bifunctor (first)
import Data.Bytes (Bytes)
import Data.Foldable (foldl')
import Data.Map.Word8 (Map)
import Data.Word (Word8)

import qualified Data.Bytes as Bytes
import qualified Data.Map.Word8 as Map
import qualified Data.Maybe.Unpacked as UMaybe

-- | Tries implemented using a 256-entry bitmap as given in
-- "Data.Map.Word8".
-- This means that each branch point can be navigated with only
-- some bit manipulations and adding an offset.
-- On sparse data, this should save a lot of space relative to holding
-- a 256-entry pointer array.
--
-- This data type has 'Branch' and 'Run' nodes.
-- Branches never have only a single child,
-- and Runs always have at least one byte.
-- Leaves are branches without children.
-- Once the invariants are met (see below),
-- there is exactly one 'Trie' representation for each trie.
--
-- In each constructor, the @UMaybe.Maybe a@ is a possible entry;
-- it comes before any child bytes.
--
-- INVARIANT: The Run constructor never has a linear child.
--            Linear nodes are those with no value and exactly one child,
--            which in this case is only valueless runs.
-- INVARIANT: The Run constructor never has zero bytes.
-- INVARIANT: The Branch constructor never has exactly one child.
-- INVARIANT: No child of a node has size zero. That includes:
--              No child of a branch is ever null.
--              The next node after a run is never null.
data Trie a
  -- TODO could save four machine words with a separate Tip case
  -- also, with a Tip, branches would always have children >= 2
  = UnsafeBranch {-# unpack #-} !(UMaybe.Maybe a) !(Map (Trie a))
  -- TODO use ByteArray directly
  -- ByteArray uses more copying on modification, but lookup may be faster
  | UnsafeRun {-# unpack #-} !(UMaybe.Maybe a) {-# unpack #-} !Bytes !(Trie a)
  deriving (Eq{- TODO needs instance for Map, Functor-})

instance Semigroup a => Semigroup (Trie a) where (<>) = append
instance Semigroup a => Monoid (Trie a) where mempty = empty
instance Show a => Show (Trie a) where show = show . toList


{-# complete Run, Branch #-}

pattern Run :: UMaybe.Maybe a -> Bytes -> Trie a -> Trie a
pattern Run v run next <- UnsafeRun v run next
  where
  Run v run next
    | null next = UnsafeBranch v Map.empty
    | Bytes.null run = next -- WARNING: throws away `v`, value/non-value from `next`
    | Just (run', next') <- fromLinear next
      = Run v (run <> run') next'
    | otherwise = UnsafeRun v run next

pattern Branch :: UMaybe.Maybe a -> Map (Trie a) -> Trie a
pattern Branch v children <- UnsafeBranch v children
  where
  Branch v (removeEmptyChildren -> children)
    | Just (c, child) <- fromSingletonMap children
      = Run v (Bytes.singleton c) child
    | otherwise = UnsafeBranch v children
removeEmptyChildren :: Map (Trie a) -> Map (Trie a)
removeEmptyChildren = Map.foldrWithKeys f Map.empty
  where
  f k v xs = if null v then xs else insertMap k v xs

-- Get nodes with no value, and exactly one possible next byte.
-- I.e. it never returns an empty bytes in the tuple.
fromLinear :: Trie a -> Maybe (Bytes, Trie a)
fromLinear (Run UMaybe.Nothing run next) = Just (run, next)
fromLinear _ = Nothing


------------ Construction ------------

-- | The empty trie.
empty :: Trie a
empty = UnsafeBranch UMaybe.Nothing Map.empty

-- | A trie with a single element.
singleton :: Bytes -> a -> Trie a
singleton k v = prepend k $ UnsafeBranch (UMaybe.Just v) Map.empty

-- | Prepend every key in the 'Trie' with the given 'Bytes'.
--
-- This should be used internally instead of the Run ctor,
-- thereby ensuring the run length >= 2 invariant is maintained.
-- It is exported anyway because someone may find it useful.
prepend :: Bytes -> Trie a -> Trie a
prepend bytes next = Run UMaybe.Nothing bytes next

-- | Insert a new key/value into the trie.
-- If the key is already present in the trie, the associated value is
-- replaced with the new one.
-- 'insert' is equivalent to 'insertWith' 'const'.
insert :: Bytes -> a -> Trie a -> Trie a
insert = insertWith const

-- | Insert with a function, combining new value and old value.
-- @'insertWith' f key value trie@ will insert the pair @(key, value)@
-- into @trie@ if @key@ does not exist in the trie.
-- If the key does exist, the function will insert the pair
-- @(key, f new_value old_value)@.
insertWith :: (a -> a -> a) -> Bytes -> a -> Trie a -> Trie a
insertWith f k v = unionWith f (singleton k v)

delete :: Bytes -> Trie a -> Trie a
delete k0 trie = go k0 trie
  where
  -- `go` is not always tail-recursive.
  -- Instead, each node with exactly one child must be checked after the
  --  deletion to ensure that child is non-empty.
  -- TODO
  -- However, as soon as it is known that the size must be greater than one,
  --  we can throw away all queued normalizations so far.
  -- Therefore, we maintain a delimited continuation as an accumulator,
  --  but I'm not yet sure how to manually store it.
  -- go :: Bytes -> Trie a
  go key node@(Run v run next)
    -- found key, therefore delete
    | Bytes.null key
    , UMaybe.Just _ <- v -- NOTE this is redundant now, but when I use cps, it won't be
      = prepend run next
    -- carry on searching for the key
    | Just key' <- Bytes.stripPrefix run key
      = Run v run (go key' next)
    -- key not present
    | otherwise = node
  go key node@(Branch v children)
    -- found key, therefore delete
    | Bytes.null key
    , UMaybe.Just _ <- v
      = UnsafeBranch UMaybe.Nothing children
    -- carry on searching for the key
    | Just (c, key') <- Bytes.uncons key
    , Just child <- Map.lookup c children
      = Branch v (insertMap c (go key' child) children)
    -- key not present
    | otherwise = node


-- | Union of the two tries, but where a key appears in both,
-- the associated values are combined with '(<>)' to produce the new value,
-- i.e. @append == unionWith (<>)@.
append :: Semigroup a => Trie a -> Trie a -> Trie a
append = unionWith (<>)

-- | The left-biased union of the two tries.
-- It prefers the first when duplicate keys are encountered,
-- i.e. @union == unionWith const@.
union :: Trie a -> Trie a -> Trie a
union = unionWith const

-- | Union with a combining function.
unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f trieA trieB = case (trieA, trieB) of
  (Branch a children, Branch b children') ->
    UnsafeBranch (a `mergeValue` b) (mergeChildren children children')
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
        in UnsafeBranch (a `mergeValue` b) $ child `Map.union` child'
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

-- | Build a trie from a list of key/value pairs.
-- If more than one value for the same key appears, the last value for that
-- key is retained.
fromList :: [(Bytes, a)] -> Trie a
fromList kvs = foldl' (\xs (k, v) -> insert k v xs) empty kvs

-- | Convert the trie to a list of key/value pairs.
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

-- | Lookup the value at the 'Bytes' key in the trie.
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


-- | Find the longest prefix of the input 'Bytes' which has a value in the trie.
-- Returns the associated value and the remainder of the input after the prefix.
stripPrefix :: Trie a -> Bytes -> Maybe (a, Bytes)
stripPrefix trie inp = first snd <$> stripPrefixWithKey trie inp

-- | Find the longest prefix of the input 'Bytes' which has a value in the trie.
-- Returns the prefix and associated value found as a key/value tuple,
-- and also the remainder of the input after the prefix.
stripPrefixWithKey :: forall a. Trie a -> Bytes -> Maybe ((Bytes, a), Bytes)
stripPrefixWithKey trie0 rawInp = go 0 Nothing trie0
  where
  go :: Int -> Maybe (Bytes, a) -> Trie a -> Maybe ((Bytes, a), Bytes)
  go !into !prior node =
    let inp = Bytes.unsafeDrop into rawInp
        candidate = (Bytes.unsafeTake into rawInp,) <$> topValue node
        found = candidate <|> prior
    in if | Run _ run next <- node
          , run `Bytes.isPrefixOf` inp
            -> go (into + Bytes.length run) found next
          | Branch _ children <- node
          , Just (c, _) <- Bytes.uncons inp
          , Just next <- Map.lookup c children
            -> go (into + 1) found next
          | otherwise -> mkReturn <$> found
  mkReturn (prefix, v) =
    let post = Bytes.unsafeDrop (Bytes.length prefix) rawInp
    in ((prefix, v), post)


null :: Trie a -> Bool
null (Branch UMaybe.Nothing children) = nullMap children
null _ = False

size :: Trie a -> Int
size node = here + under
  where
  here = maybe 0 (const 1) (topValue node)
  under = case node of
    Run _ _ next -> size next
    Branch _ children -> Map.foldrWithKeys (\_ child !acc -> acc + size child) 0 children

------ Helpers ------

topValue :: Trie a -> Maybe a
topValue = \case
  Run v _ _ -> UMaybe.toBaseMaybe v
  Branch v _ -> UMaybe.toBaseMaybe v

unsafeUnconsRun :: Trie a -> (UMaybe.Maybe a, Word8, Trie a)
unsafeUnconsRun (Run v0 bs next) = (v0, c, run')
  where
  c = Bytes.unsafeIndex bs 0
  bs' = Bytes.unsafeDrop 1 bs
  run' = prepend bs' next
unsafeUnconsRun (Branch _ _) = error "unsafeUnconsRun on Branch trie"

-- FIXME move this upstream
insertMap :: Word8 -> a -> Map a -> Map a
insertMap k v xs = Map.singleton k v `Map.union` xs

-- FIXME move this upstream
nullMap :: Map a -> Bool
nullMap = Prelude.null . Map.toList

-- TODO is this really a decent way to do this?
fromSingletonMap :: Map a -> Maybe (Word8, a)
fromSingletonMap mp = case Map.toList mp of
  [(c, v)] -> Just (c, v)
  _ -> Nothing
