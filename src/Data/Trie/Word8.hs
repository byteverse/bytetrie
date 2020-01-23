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
-- Branches continue on a single byte.
-- Runs continue on a prefix of two or more bytes.
-- Leaves are branches without children,
-- and a single-character run is a 'Branch' with one child.
-- This means that there is exactly one 'Trie' representation
-- (where each run is length ≥ 2) for each trie.
--
-- In each constructor, the @UMaybe.Maybe a@ is a possible entry;
-- it comes before any child bytes.
--
-- INVARIANT: The Run constructor never has @Bytes.length < 2@.
-- INVARIANT: No child of a node has size zero.
-- INVARIANT: The next node after a Run is neither linear nor empty.
-- INVARIANT: If a Branch has no value and only a single child,
--            that child must not be linear.
data Trie a
  -- TODO could save four machine words with a separate Nil case
  = UnsafeBranch {-# unpack #-} !(UMaybe.Maybe a) !(Map (Trie a))
  -- TODO use Bytes? or ByteArray directly?
  -- ByteArray uses more copying on insert, but lookup may be faster
  -- TODO it seems like I should be able to inline the Trie, but would that help?
  | UnsafeRun {-# unpack #-} !(UMaybe.Maybe a) {-# unpack #-} !Bytes !(Trie a)
  deriving (Eq{- TODO needs instance for Map, Functor-})

instance Semigroup a => Semigroup (Trie a) where (<>) = append
instance Semigroup a => Monoid (Trie a) where mempty = empty
-- instance Show a => Show (Trie a) where show = show . toList
deriving stock instance Show a => Show (Trie a)


{-# complete Run, Branch #-}

pattern Run :: UMaybe.Maybe a -> Bytes -> Trie a -> Trie a
pattern Run v run next <- UnsafeRun v run next
  where
  Run v run next
    | null next = Branch v Map.empty
    | Just (bytes', next') <- fromLinear next
      = Run v (run <> bytes') next'
    | Bytes.null run = next -- WARNING: throws away `v`, value/non-value from `next`
    | Just (c, rest) <- Bytes.uncons run
    , Bytes.null rest
      = Branch v (Map.singleton c next)
    | otherwise = UnsafeRun v run next

pattern Branch :: UMaybe.Maybe a -> Map (Trie a) -> Trie a
pattern Branch v children <- UnsafeBranch v children
  where
  Branch v (removeEmptyChildren -> children)
    -- NOTE empty value and children is already empty, so I don't "rewrite" to empty
    | Just (c, child) <- fromSingletonMap children
    , Just (bytesB, grandchild) <- fromLinear child
      = Run v (Bytes.singleton c <> bytesB) grandchild
    | otherwise = UnsafeBranch v children
removeEmptyChildren :: Map (Trie a) -> Map (Trie a)
removeEmptyChildren = Map.foldrWithKeys f Map.empty
  where
  f k v xs = if null v then xs else insertMap k v xs

-- Get nodes with no value, and exactly one possible next byte.
-- I.e. it never returns an empty bytes in the tuple.
fromLinear :: Trie a -> Maybe (Bytes, Trie a)
fromLinear (Run UMaybe.Nothing run next) = Just (run, next)
fromLinear (Branch UMaybe.Nothing children)
  | Just (c, child) <- fromSingletonMap children
  = Just (Bytes.singleton c, child)
fromLinear _ = Nothing

------------ Construction ------------

-- | The empty trie.
empty :: Trie a
empty = Branch UMaybe.Nothing Map.empty

-- | A trie with a single element.
singleton :: Bytes -> a -> Trie a
singleton k v = prepend k $ Branch (UMaybe.Just v) Map.empty

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
delete k0 trie
  | Bytes.null k0 = deleteTop trie
  | otherwise = go k0 trie
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
      = Run UMaybe.Nothing run next
    -- carry on searching for the key
    | Just key' <- Bytes.stripPrefix run key
      = Run v run (go key' next)
    -- key not present
    | otherwise = node
  go key node@(Branch v children)
    -- found key, therefore delete
    | Bytes.null key
    , UMaybe.Just _ <- v
      = Branch UMaybe.Nothing children
    -- carry on searching for the key
    | Just (c, key') <- Bytes.uncons key
    , Just child <- Map.lookup c children
      = Branch v (insertMap c (go key' child) children)
    -- key not present
    | otherwise = node

deleteTop :: Trie a -> Trie a
deleteTop (Run _ run next)
  | null next = empty
  | otherwise = Run UMaybe.Nothing run next
deleteTop (Branch _ children)
  | Just (_, child) <- fromSingletonMap children
  , null child = empty
  | otherwise = Branch UMaybe.Nothing children


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
  topValue :: Trie a -> Maybe a
  topValue = \case
    Run v _ _ -> UMaybe.toBaseMaybe v
    Branch v _ -> UMaybe.toBaseMaybe v

null :: Trie a -> Bool
null (Branch UMaybe.Nothing children) = nullMap children
null _ = False


------ Helpers ------

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
