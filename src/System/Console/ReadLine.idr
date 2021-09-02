module System.Console.ReadLine

import Data.Maybe
import System.Console.ReadLine.Internal

%default total

--------------------------------------------------------------------------------

export
readline : String -> IO String
readline = primIO . prim__ic_readline

--------------------------------------------------------------------------------

export
setHistory : String -> Maybe Int -> IO ()
setHistory filePath maxEntries = do
  primIO $ prim__ic_set_history filePath $
    cast $ fromMaybe (-1) maxEntries

export
historyClear : IO ()
historyClear = primIO prim__ic_history_clear

export
historyRemoveLast : IO ()
historyRemoveLast = primIO prim__ic_history_remove_last

export
historyAdd : String -> IO ()
historyAdd = primIO . prim__ic_history_add
