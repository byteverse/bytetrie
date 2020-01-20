import Data.Trie.Word8 (Trie)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.QuickCheck ((===),testProperty,property,Gen)
import Test.Tasty.QuickCheck (Arbitrary,choose,vectorOf,forAll)

import qualified Data.Trie.Word8 as Trie
import qualified Data.Map.Word8 as Map
import qualified Data.Bytes as Bytes
import qualified Data.List as List
import qualified Test.QuickCheck.Classes as QCC
import qualified Test.Tasty.QuickCheck as TQC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "bytetrie"
  [ testGroup "append" []
  ]