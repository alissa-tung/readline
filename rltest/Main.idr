module Main

import Test.Golden

%default covering

main : IO ()
main = runner
  []
  where
    withPath : String -> TestPool -> TestPool
    withPath path = record {testCases $= map (path ++ "/" ++)}
