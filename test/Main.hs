{-# language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Bytes.Types (Bytes(Bytes))
import Data.Monoid (Sum, First)
import Data.Proxy (Proxy(..))
import Data.Trie.Word8 (Trie)
import Data.Word (Word8)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.QuickCheck ((===),testProperty,property,Gen)
import Test.Tasty.QuickCheck (Arbitrary,choose,vectorOf,forAll)

import qualified Data.Trie.Word8 as Trie
import qualified GHC.Exts as Exts
import qualified Test.QuickCheck.Classes as QCC
import qualified Test.Tasty.QuickCheck as TQC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "bytetrie"
  [ testGroup "append"
    [ lawsToTest (QCC.semigroupLaws (Proxy :: Proxy (Trie [Integer])))
    , lawsToTest (QCC.monoidLaws (Proxy :: Proxy (Trie [Integer])))
    , lawsToTest (QCC.commutativeMonoidLaws (Proxy :: Proxy (Trie (Sum Integer))))
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
