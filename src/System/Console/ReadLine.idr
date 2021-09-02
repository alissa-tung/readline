module System.Console.ReadLine

import Data.List
import Data.Maybe
import System.Console.ReadLine.Internal

%default total

--------------------------------------------------------------------------------

public export
FmtString : Type
FmtString = String

export
record CompletionEnv where
  constructor MkCompletionEnv
  unCompletionEnv : Prim__ic_completion_envPtr

public export
CompleterFun : Type
CompleterFun = CompletionEnv -> String -> IO ()

--------------------------------------------------------------------------------

export
readline : String -> IO String
readline = primIO . prim__ic_readline

export
readlineEx : String
          -> Maybe (CompletionEnv -> String -> IO ())
          -> Maybe (String -> FmtString)
          -> IO String
readlineEx prompt completer highlighter = do
  primIO $ prim__ic_readline_ex prompt
    (case completer of
      Just completer => ?todo0
      Nothing        => believe_me prim__null_ptr)
    (believe_me prim__null_ptr)
    ?arg2
    (believe_me prim__null_ptr)

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

--------------------------------------------------------------------------------

export
completeFileName : CompletionEnv -> String
                -> Maybe Char -> List String -> List String
                -> IO ()
completeFileName (MkCompletionEnv cEnv) input dirSep filePaths exts = primIO $
  prim__ic_complete_filename cEnv input
    (fromMaybe '\NUL' dirSep)
    (concat (intersperse ";" filePaths))
    (concat (intersperse ";" exts))
