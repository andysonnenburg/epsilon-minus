module Main (main) where

import Test.DocTest (doctest)

main :: IO ()
main =
  doctest
  [ "-isrc"
  , "src/Node.hs"
  , "src/Path.hs"
  , "src/UnionFind.hs"
  ]
