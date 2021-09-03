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

mkCompleter : CompleterFun -> Prim__ic_completer_fun
mkCompleter f = \x, str => toPrim $
  f (MkCompletionEnv x) str

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
  primIO $ case (completer, highlighter) of
    (Nothing       , Nothing)          => prim__idr_ic_readline_ex_00 prompt                         coeNullPtr                      coeNullPtr
    (Nothing       , Just highlighter) => prim__idr_ic_readline_ex_01 prompt                         coeNullPtr (?todo0 highlighter) coeNullPtr
    (Just completer, Nothing)          => prim__idr_ic_readline_ex_10 prompt (mkCompleter completer) coeNullPtr                      coeNullPtr
    (Just completer, Just highlighter) => prim__idr_ic_readline_ex_11 prompt (mkCompleter completer) coeNullPtr (?todo1 highlighter) coeNullPtr

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

public export
record Completion where
  constructor MkCompletion
  replacement : String
  display     : String
  help        : String

export
completeFileName : CompletionEnv -> String
                -> Maybe Char -> List String -> List String
                -> IO ()
completeFileName (MkCompletionEnv cEnv) input dirSep filePaths exts = primIO $
  prim__ic_complete_filename cEnv input
    (fromMaybe '\NUL' dirSep)
    (concat (intersperse ";" filePaths))
    (concat (intersperse ";" exts))

export
addCompletion : CompletionEnv -> Completion -> IO Bool
addCompletion (MkCompletionEnv env) (MkCompletion replacement display help) =
  (primIO $ prim__ic_add_completion_ex env replacement display help)
    <&> cast

export
addCompletions : CompletionEnv -> List Completion -> IO Bool
addCompletions _ [] = pure True
addCompletions env (x :: xs) =
  if !(addCompletion env x)
    then addCompletions env xs
    else pure False

export
completeWordPrim : CompletionEnv -> String
                -> Maybe (Char -> Bool) -> (CompletionEnv -> String -> IO ())
                -> IO ()

export
completeWord : CompletionEnv -> String
            -> Maybe (Char -> Bool) -> (String -> List Completion)
            -> IO ()
