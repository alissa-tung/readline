module System.Console.ReadLine

import System.Console.ReadLine.Internal

%default total

export
readline : String -> IO String
readline = primIO . prim__ic_readline
