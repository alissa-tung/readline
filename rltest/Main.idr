module Main

import Test.Golden

%default total

main : IO ()
main = runner
  []
  where
    withPath : String -> TestPool -> TestPool
    withPath path = record {testCases $= map (path ++ "/" ++)}
