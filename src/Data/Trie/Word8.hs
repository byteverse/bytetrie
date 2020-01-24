{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TupleSections #-}
{-# language ViewPatterns #-}

-- | Tries with 'Bytes' (equiv. 'ByteArray') as keys.
-- This implementation is optimized for performing queries rather
-- than updating the structure repeatedly.
module Data.Trie.Word8
  (
  -- * Trie Type
    Trie
  , valid
  -- * Query
  -- ** Lookup
  , lookup
  -- ** Search
  , multiFindReplace
  , stripPrefix
  , stripPrefixWithKey
  -- ** Size
  , null
  , size
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
  ) where

import Prelude hiding (null, lookup)

import Control.Applicative ((<|>))
import Data.Bifunctor (first)
import Data.Bytes (Bytes, toByteArray, fromByteArray)
import Data.Foldable (foldl')
import Data.Map.Word8 (Map)
import Data.Maybe (isNothing)
import Data.Primitive.ByteArray (ByteArray, indexByteArray)
import Data.Word (Word8)

import qualified Data.Bytes as Bytes
import qualified Data.Map.Word8 as Map
import qualified Data.Maybe.Unpacked as U

-- | Tries implemented using a 256-entry bitmap as given in
-- "Data.Map.Word8".
-- This means that each branch point can be navigated with only
-- some bit manipulations and adding an offset.
-- On sparse data, this should save a lot of space relative to holding
-- a 256-entry pointer array.
--
-- This data type has 'Tip', 'Run', and 'Branch' nodes.
-- Branches always have at least two children,
-- and Runs always have at least one byte.
-- Leaves are 'Tip's.
-- Once the invariants are met (see below),
-- there is exactly one 'Trie' representation for each trie.
--
-- In each constructor, the @U.Maybe a@ is a possible entry;
-- it comes before any child bytes.
--
-- INVARIANT: The Run constructor never has a linear child.
--            Linear nodes are those with no value and exactly one child,
--            which in this implementation is only valueless runs.
-- INVARIANT: The Run constructor never has zero bytes.
-- INVARIANT: The Branch constructor has at least two children.
-- INVARIANT: No child of a node has size zero. That includes:
--              The next node after a run is never null.
--              No child of a branch is ever null.
data Trie a
  = Tip {-# unpack #-} !(U.Maybe a)
  -- ByteArray uses more copying on modification,
  -- but the data structures are smaller than with Bytes, making lookup faster
  | UnsafeRun {-# unpack #-} !(U.Maybe a) {-# unpack #-} !ByteArray !(Trie a)
  | UnsafeBranch {-# unpack #-} !(U.Maybe a) !(Map (Trie a))
  deriving (Eq, Functor)

instance Semigroup a => Semigroup (Trie a) where (<>) = append
instance Semigroup a => Monoid (Trie a) where mempty = empty
instance Show a => Show (Trie a) where show = show . toList


{-# complete Tip, Run, Branch #-}

pattern Run :: U.Maybe a -> ByteArray -> Trie a -> Trie a
pattern Run v run next <- UnsafeRun v run next
  where
  Run v run next
    | null next = Tip v
    | Bytes.null (fromByteArray run) = next -- WARNING: throws away `v`, value/non-value from `next`
    | Just (run', next') <- fromLinear next
      = UnsafeRun v (run <> run') next'
    | otherwise = UnsafeRun v run next

pattern Branch :: U.Maybe a -> Map (Trie a) -> Trie a
pattern Branch v children <- UnsafeBranch v children
  where
  Branch v (removeEmptyChildren -> children)
    | Map.null children = Tip v
    | Just (c, child) <- fromSingletonMap children
      = Run v (toByteArray $ Bytes.singleton c) child
    | otherwise = UnsafeBranch v children
removeEmptyChildren :: Map (Trie a) -> Map (Trie a)
removeEmptyChildren = Map.foldrWithKeys f Map.empty
  where
  f k v xs = if null v then xs else Map.insert k v xs

-- Get nodes with no value, and exactly one possible next byte.
-- I.e. it never returns an empty bytes in the tuple.
fromLinear :: Trie a -> Maybe (ByteArray, Trie a)
fromLinear (Run U.Nothing run next) = Just (run, next)
fromLinear _ = Nothing

valid :: Trie a -> Bool
valid (Tip _) = True
valid (Run _ run next)
  = not (Bytes.null (fromByteArray run))
    && isNothing (fromLinear next)
    && not (null next)
    && valid next
valid (Branch _ children)
  = Map.size children > 1
    && Map.foldrWithKeys nonNullChild True children
  where
  nonNullChild _ child !acc = acc && not (null child)

------------ Find/Replace ------------

-- | The raison-d'etre of this library: repeatedly search in a byte string
-- for the longest of multiple patterns and make replacements.
multiFindReplace :: Semigroup b
  => (Bytes -> b) -- ^ construct a portion of the result from unmatched bytes
  -> (a -> b) -- ^ construct a replacement from the found value
  -> Trie a -- ^ the dictionary of all replacements
  -> Bytes -- ^ input to be edited
  -> b -- ^ result of replacement
multiFindReplace fromNoMatch fromMatch t inp0 = go 0 inp0
  where
  needles = delete mempty t
  -- `into` counts up until the first index where a replacement is found
  go !into rawInp =
    let inp = Bytes.unsafeDrop into rawInp
        unMatched = Bytes.unsafeTake into rawInp
    in if | Bytes.null inp -> fromNoMatch unMatched
          | Just (val, rest) <- stripPrefix needles inp ->
              fromNoMatch unMatched <> fromMatch val <> go 0 rest
          | otherwise -> go (into + 1) rawInp


------------ Construction ------------

-- | The empty trie.
empty :: Trie a
empty = Tip U.Nothing

-- | A trie with a single element.
singleton :: Bytes -> a -> Trie a
singleton k v = prepend k $ Tip (U.Just v)

-- | Prepend every key in the 'Trie' with the given 'Bytes'.
--
-- This should be used internally instead of the Run ctor,
-- thereby ensuring the run length >= 2 invariant is maintained.
-- It is exported anyway because someone may find it useful.
prepend :: Bytes -> Trie a -> Trie a
prepend bytes next = Run U.Nothing (toByteArray bytes) next

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
  go key node@(Tip v)
    | Bytes.null key
    , U.Just _ <- v -- NOTE this is redundant now, but when I use cps, it won't be
      = empty
    | otherwise = node
  go key node@(Run v (fromByteArray -> run) next)
    -- found key, therefore delete
    | Bytes.null key
    , U.Just _ <- v -- NOTE this is redundant now, but when I use cps, it won't be
      = prepend run next
    -- carry on searching for the key
    | Just key' <- Bytes.stripPrefix run key
      = Run v (toByteArray run) (go key' next)
    -- key not present
    | otherwise = node
  go key node@(Branch v children)
    -- found key, therefore delete
    | Bytes.null key
    , U.Just _ <- v
      = UnsafeBranch U.Nothing children
    -- carry on searching for the key
    | Just (c, key') <- Bytes.uncons key
    , Just child <- Map.lookup c children
      = Branch v (Map.insert c (go key' child) children)
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
  (Tip a, Tip b) -> Tip (a `mergeValue` b)
  (Tip a, Run b run next) -> UnsafeRun (a `mergeValue` b) run next
  (Run a run next, Tip b) -> UnsafeRun (a `mergeValue` b) run next
  (Tip a, Branch b children) -> UnsafeBranch (a `mergeValue` b) children
  (Branch a children, Tip b) -> UnsafeBranch (a `mergeValue` b) children
  -- all non-Tip cases
  (Branch a children, Branch b children') ->
    UnsafeBranch (a `mergeValue` b) (mergeChildren children children')
  (Branch a children, r@(Run _ _ _)) ->
    UnsafeBranch (a `mergeValue` b) (mergeChildren children children')
    where
    (b, c, child') = unsafeUnconsRun r
    children' = Map.singleton c child'
  (r@(Run _ _ _), Branch b children') ->
    UnsafeBranch (a `mergeValue` b) (mergeChildren children children')
    where
    (a, c, child') = unsafeUnconsRun r
    children = Map.singleton c child'
  (Run a (fromByteArray -> run) next, Run b (fromByteArray -> run') next') ->
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
        in Run (a `mergeValue` b) (toByteArray common) $ unionWith f child child'
    where
    common = Bytes.longestCommonPrefix run run'
    uncommon bytes = Bytes.unsafeDrop (Bytes.length common) bytes
  where
    mergeChildren left right = Map.unionWith (unionWith f) left right
    mergeValue U.Nothing U.Nothing = U.Nothing
    mergeValue (U.Just x) (U.Just y) = U.Just (f x y)
    mergeValue x y = x <|> y


------------ Conversion ------------

-- | Build a trie from a list of key/value pairs.
-- If more than one value for the same key appears, the last value for that
-- key is retained.
fromList :: [(Bytes, a)] -> Trie a
fromList kvs = foldl' (\xs (k, v) -> insert k v xs) empty kvs

-- | Convert the trie to a list of key/value pairs.
-- The resulting list has its keys sorted in ascending order.
toList :: Trie a -> [(Bytes, a)]
toList = \case
  Tip valO -> fromValue valO
  Run valO run next -> fromValue valO ++ prependList (fromByteArray run) (toList next)
  Branch valO children -> fromValue valO ++ Map.foldrWithKeys f [] children
    where
    f k v acc = prependList (Bytes.singleton k) (toList v) ++ acc
  where
  fromValue valO = (mempty,) <$> U.maybeToList valO
  prependList run list = first (run <>) <$> list


------------ Query ------------

-- | Lookup the value at the 'Bytes' key in the trie.
lookup :: Bytes -> Trie a -> Maybe a
lookup k (Tip v)
  | Bytes.null k = U.toBaseMaybe v
  | otherwise = Nothing
lookup k (Run v (fromByteArray -> run) next)
  | Bytes.null k = U.toBaseMaybe v
  | run `Bytes.isPrefixOf` k =
    let k' = Bytes.unsafeDrop (Bytes.length run) k
    in lookup k' next
  | otherwise = Prelude.Nothing
lookup k (Branch valO children) = case Bytes.uncons k of
  Prelude.Nothing -> U.toBaseMaybe valO
  Prelude.Just (c, k') -> lookup k' =<< Map.lookup c children


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
    in if | Run _ (fromByteArray -> run) next <- node
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
null (Tip U.Nothing) = True
null _ = False

size :: Trie a -> Int
size node = here + under
  where
  here = maybe 0 (const 1) (topValue node)
  under = case node of
    Tip _ -> 0
    Run _ _ next -> size next
    Branch _ children -> Map.foldrWithKeys (\_ child !acc -> acc + size child) 0 children

------ Helpers ------

topValue :: Trie a -> Maybe a
topValue = \case
  Tip v -> U.toBaseMaybe v
  Run v _ _ -> U.toBaseMaybe v
  Branch v _ -> U.toBaseMaybe v

unsafeUnconsRun :: Trie a -> (U.Maybe a, Word8, Trie a)
unsafeUnconsRun (Run v0 bs next) = (v0, c, run')
  where
  c = indexByteArray bs 0
  bs' = Bytes.unsafeDrop 1 (fromByteArray bs)
  run' = prepend bs' next
unsafeUnconsRun (Tip _) = error "unsafeUnconsRun on Tip trie"
unsafeUnconsRun (Branch _ _) = error "unsafeUnconsRun on Branch trie"

-- TODO is this really a decent way to do this?
fromSingletonMap :: Map a -> Maybe (Word8, a)
fromSingletonMap mp = case Map.toList mp of
  [(c, v)] -> Just (c, v)
  _ -> Nothing
