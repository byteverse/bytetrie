import Gauge(defaultMain,bgroup,bench,whnf)

import Data.Bifunctor (bimap)
import Data.Text (Text)

import qualified Data.Bytes as Bytes
import qualified Data.Text as T
import qualified Data.Trie.Word8 as Trie
import qualified TestData as TestData

main :: IO ()
main = defaultMain
  [ bgroup "replace"
    [ bench "trie" $
        whnf (Trie.replace TestData.replacements) bytesString
    , bench "text" $
        whnf (textReplace textRepls) textString
    ]
  ]

bytesString = Bytes.fromLatinString TestData.bigstring
textString = T.pack TestData.bigstring
textRepls = map (bimap T.pack T.pack) TestData.replacementAlist

textReplace :: [(Text, Text)] -> Text -> Text
textReplace xs inp = foldl (\acc (k, v) -> T.replace k v acc) inp xs