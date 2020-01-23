{-# language MultiWayIf #-}
{-# language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Bytes.Types (Bytes(Bytes))
import Data.Monoid (Sum)
import Data.Proxy (Proxy(..))
import Data.Trie.Word8 (Trie)
import Data.Word (Word8)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.QuickCheck ((===),testProperty,property)
import Test.Tasty.QuickCheck (Arbitrary)
import Test.Tasty.QuickCheck (Discard(Discard))

import qualified Data.Trie.Word8 as Trie
import qualified Data.Bytes as Bytes
import qualified GHC.Exts as Exts
import qualified Test.QuickCheck.Classes as QCC
import qualified Test.Tasty.QuickCheck as TQC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "bytetrie"
  [ testGroup "validity"
    [ testProperty "fromList validity" $ \alist ->
      let a = Trie.fromList alist :: Trie Int
      in Trie.valid a
    , testProperty "unionWith maintains invariants" $ \xsList ysList ->
      let xs = Trie.fromList xsList :: Trie Int
          ys = Trie.fromList ysList
      in Trie.valid (Trie.unionWith (+) xs ys)
    , testProperty "delete maintains invariants" $ \alist k v ->
      let a = Trie.fromList alist :: Trie Int
          a' = Trie.insert k v a
      in Trie.valid (Trie.delete k a) && Trie.valid (Trie.delete k a')
    ]
  , testGroup "lookup"
    [ testProperty "lookup existing key" $
      \(xs :: [(Bytes, Int)]) (k, v) ys ->
      let alist = xs ++ [(k, v)] ++ ys
      in if | Nothing <- lookup k ys ->
              Trie.lookup k (Trie.fromList alist) === lookup k (reverse alist)
            | otherwise -> property Discard
    , testProperty "lookup missing key" $
      \(alist :: [(Bytes, Int)]) (k :: Bytes) ->
        if | Just _ <- lookup k alist -> property Discard
           | otherwise -> Trie.lookup k (Trie.fromList alist) === Nothing
    ]
  , testGroup "unionWith"
    [ lawsToTest (QCC.semigroupLaws (Proxy :: Proxy (Trie [Integer])))
    , lawsToTest (QCC.monoidLaws (Proxy :: Proxy (Trie [Integer])))
    , lawsToTest (QCC.commutativeMonoidLaws (Proxy :: Proxy (Trie (Sum Integer))))
    ]
  , testGroup "stripPrefix"
    [ testProperty "finds longest prefix" $
      \(a :: Bytes) (b :: Bytes) (c :: Bytes) (d :: Bytes) ->
        if | Just (wc,_) <- Bytes.uncons c
           , Just (wd,_) <- Bytes.uncons d
           , wc /= wd ->
              let t :: Trie Int = Trie.fromList [(a, 1), (a <> b, 2), (a <> b <> d, 3)]
                  expected = Just ((a <> b, 2), c)
                  found = Trie.stripPrefixWithKey t (a <> b <> c)
              in found === expected
           | otherwise -> property Discard
    , testProperty "finds nothing" $
      \(a :: Bytes) (b :: Bytes) ->
        if | Just (wa,_) <- Bytes.uncons a
           , Just (wb,_) <- Bytes.uncons b
           , wa /= wb ->
              let t :: Trie Int = Trie.fromList [(a, 1)]
              in Trie.stripPrefixWithKey t b === Nothing
           | otherwise -> property Discard
    ]
  , testGroup "delete"
    [ testProperty "maintains invariant" $
      \(xs :: [(Bytes, Int)]) (k, v) ys ->
        if | Nothing <- lookup k xs
           , Nothing <- lookup k ys ->
              let t = Trie.fromList $ xs ++ [(k, v)] ++ ys
                  t' = Trie.fromList $ xs ++ ys
              in Trie.delete k t === t'
           | otherwise -> property Discard
    ]
  ]

instance (Arbitrary a) => Arbitrary (Trie a) where
  arbitrary = Trie.fromList <$> TQC.arbitrary
instance Arbitrary Bytes where
  arbitrary = do
    xs :: [Word8] <- TQC.arbitrary
    front <- TQC.choose (0,2)
    back <- TQC.choose (0,2)
    let frontPad = replicate front (254 :: Word8)
    let backPad = replicate back (254 :: Word8)
    let raw = Exts.fromList (frontPad ++ xs ++ backPad)
    pure (Bytes raw front (length xs))

lawsToTest :: QCC.Laws -> TestTree
lawsToTest (QCC.Laws name pairs) = testGroup name (map (uncurry TQC.testProperty) pairs)
