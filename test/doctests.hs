module Main (main) where

import Test.DocTest (doctest)

main :: IO ()
main =
  doctest
  [ "-isrc"
  , "src/Path.hs"
  , "src/UnionFind.hs"
  , "src/Vertex.hs"
  ]
