{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Monad (forM_)
import Data.Bifunctor (first)
import Data.Bytes.Types (Bytes (Bytes))
import Data.List (isInfixOf, sort)
import Data.Monoid (Sum)
import Data.Proxy (Proxy (..))
import Data.Trie.Word8 (Trie)
import Data.Word (Word8)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)
import Test.Tasty.QuickCheck (Arbitrary, Discard (Discard), property, testProperty, (===))

import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Text.Latin1 as Latin1
import qualified Data.Trie.Word8 as Trie
import qualified GHC.Exts as Exts
import qualified Test.QuickCheck.Classes as QCC
import qualified Test.Tasty.QuickCheck as TQC
import qualified TestData

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "bytetrie"
    [ testGroup
        "validity"
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
    , testGroup
        "lookup"
        [ testProperty "lookup existing key" $
            \(xs :: [(Bytes, Int)]) (k, v) ys ->
              let alist = xs ++ [(k, v)] ++ ys
               in if
                    | Nothing <- lookup k ys ->
                        Trie.lookup k (Trie.fromList alist) === lookup k (reverse alist)
                    | otherwise -> property Discard
        , testProperty "lookup missing key" $
            \(alist :: [(Bytes, Int)]) (k :: Bytes) ->
              if
                | Just _ <- lookup k alist -> property Discard
                | otherwise -> Trie.lookup k (Trie.fromList alist) === Nothing
        ]
    , testGroup
        "unionWith"
        [ lawsToTest (QCC.semigroupLaws (Proxy :: Proxy (Trie [Integer])))
        , lawsToTest (QCC.monoidLaws (Proxy :: Proxy (Trie [Integer])))
        , lawsToTest (QCC.commutativeMonoidLaws (Proxy :: Proxy (Trie (Sum Integer))))
        ]
    , lawsToTest (QCC.functorLaws (Proxy :: Proxy Trie))
    , testGroup
        "lookupTrie"
        [ testProperty "alpha" $
            \(x :: Bytes) (y :: Bytes) (val :: Int) (xs :: [(Bytes, Int)]) ->
              let base = Trie.insert (x <> y) val (Trie.fromList xs)
               in Trie.lookup (x <> y) base === Trie.lookup y (Trie.lookupTrie x base)
        , testProperty "beta" $
            \(x :: Bool) (y :: Bool) (val :: Int) (xs :: [([Bool], Int)]) ->
              let xs' = map (first (foldMap boolToBytes)) xs
                  base = Trie.insert (boolToBytes x <> boolToBytes y) val (Trie.fromList xs')
               in Trie.lookup (boolToBytes x <> boolToBytes y) base === Trie.lookup (boolToBytes y) (Trie.lookupTrie (boolToBytes x) base)
        ]
    , testGroup
        "stripPrefix"
        [ testProperty "finds longest prefix" $
            \(a :: Bytes) (b :: Bytes) (c :: Bytes) (d :: Bytes) ->
              if
                | Just (wc, _) <- Bytes.uncons c
                , Just (wd, _) <- Bytes.uncons d
                , wc /= wd ->
                    let t :: Trie Int = Trie.fromList [(a, 1), (a <> b, 2), (a <> b <> d, 3)]
                        expected = Just ((a <> b, 2), c)
                        found = Trie.stripPrefixWithKey t (a <> b <> c)
                     in found === expected
                | otherwise -> property Discard
        , testProperty "finds nothing" $
            \(a :: Bytes) (b :: Bytes) ->
              if
                | Just (wa, _) <- Bytes.uncons a
                , Just (wb, _) <- Bytes.uncons b
                , wa /= wb ->
                    let t :: Trie Int = Trie.fromList [(a, 1)]
                     in Trie.stripPrefixWithKey t b === Nothing
                | otherwise -> property Discard
        ]
    , testGroup
        "delete"
        [ testProperty "maintains invariant" $
            \(xs :: [(Bytes, Int)]) (k, v) ys ->
              if
                | Nothing <- lookup k xs
                , Nothing <- lookup k ys ->
                    let t = Trie.fromList $ xs ++ [(k, v)] ++ ys
                        t' = Trie.fromList $ xs ++ ys
                     in Trie.delete k t === t'
                | otherwise -> property Discard
        ]
    , testProperty "toList is sorted" $ \alist ->
        let a = Trie.fromList alist :: Trie ()
            out = Trie.toList a
         in out == sort out
    , testCase "sed works" $ do
        let sedList = Trie.multiFindReplace Latin1.toString Latin1.toString
            outp = sedList TestData.replacements TestData.bigstring
            replaced = ["Francisco", "Bernardo", "Marcellus", "Horatio", "Ghost", "What", "Why"]
        forM_ replaced $ \word -> do
          let assertName = "replaced " ++ word
          assertBool assertName $ not (word `isInfixOf` outp)
    ]

instance (Arbitrary a) => Arbitrary (Trie a) where
  arbitrary = Trie.fromList <$> TQC.arbitrary
instance Arbitrary Bytes where
  arbitrary = do
    xs :: [Word8] <- TQC.arbitrary
    front <- TQC.choose (0, 2)
    back <- TQC.choose (0, 2)
    let frontPad = replicate front (254 :: Word8)
    let backPad = replicate back (254 :: Word8)
    let raw = Exts.fromList (frontPad ++ xs ++ backPad)
    pure (Bytes raw front (length xs))

lawsToTest :: QCC.Laws -> TestTree
lawsToTest (QCC.Laws name pairs) = testGroup name (map (uncurry TQC.testProperty) pairs)

boolToBytes :: Bool -> Bytes
boolToBytes True = Bytes.singleton 1
boolToBytes False = Bytes.singleton 0
