module System.Console.ReadLine.Internal

import public System.FFI

%default total

--------------------------------------------------------------------------------

rlLib : String -> String
rlLib f = "C:" ++ f ++ ", /usr/local/lib/libisoclineidr.so"

--------------------------------------------------------------------------------

VoidPtr : Type
VoidPtr = AnyPtr

CBool : Type
CBool = Bits32

export
%foreign rlLib "null_ptr"
prim__null_ptr : AnyPtr

||| bool is_null_ptr(void *p)
%foreign rlLib "is_null_ptr"
prim__is_null_ptr : AnyPtr -> CBool

||| char *ptr_string_to_string(void *str)
%foreign rlLib "ptr_string_to_string"
prim__ptr_string_to_string : Ptr String -> String

||| void *string_to_ptr_string(const char *str)
%foreign rlLib "string_to_ptr_string"
prim__string_to_ptr_string : String -> PrimIO (Ptr String)

--------------------------------------------------------------------------------

Prim__ic_envPtr : Type
Prim__ic_envPtr = AnyPtr

Prim__attrbufPtr : Type
Prim__attrbufPtr = AnyPtr

Prim__bbcodePtr : Type
Prim__bbcodePtr = AnyPtr

Prim__allocPtr : Type
Prim__allocPtr = AnyPtr

||| typedef bool (ic_completion_fun_t)
|||   (ic_env_t* env, void* funenv, const char* replacement, const char* display, const char* help, long delete_before, long delete_after)
Prim__ic_completion_fun : Type
Prim__ic_completion_fun = Prim__ic_envPtr -> VoidPtr
                       -> String -> String -> String
                       -> Bits32 -> Bits32
                       -> IO CBool

||| struct ic_completion_env_s
|||   ic_env_t*            env
|||   const char*          input
|||   long                 cursor
|||   void*                arg
|||   void*                closure
|||   ic_completion_fun_t* complete
||| typedef struct ic_completion_env_s ic_completion_env_t
public export
Prim__ic_completion_envPtr : Type
Prim__ic_completion_envPtr = Struct "ic_completion_env_t"
  [ ("env"     , Prim__ic_envPtr)
  , ("input"   , Ptr String)
  , ("cursor"  , Bits32)
  , ("arg"     , VoidPtr)
  , ("closure" , VoidPtr)
  , ("complete", Ptr Prim__ic_completion_fun) ]

||| ic_completion_env_t *mk_ic_completion_env()
%foreign rlLib "mk_ic_completion_env"
prim__mk_ic_completion_env : PrimIO Prim__ic_completion_envPtr

||| void rm_ic_completion_env(ic_completion_env_t *ic_completion_env)
%foreign rlLib "rm_ic_completion_env"
prim__rm_ic_completion_env : Prim__ic_completion_envPtr -> PrimIO ()

||| struct ic_highlight_env_s
|||   attrbuf_t*    attrs
|||   const char*   input
|||   ssize_t       input_len
|||   bbcode_t*     bbcode
|||   alloc_t*      mem
|||   ssize_t       cached_upos
|||   ssize_t       cached_cpos
||| typedef struct ic_highlight_env_s ic_highlight_env_t
Prim__ic_highlight_envPtr : Type
Prim__ic_highlight_envPtr = Struct "ic_highlight_env_t"
  [ ("attrs"      , Prim__attrbufPtr)
  , ("input"      , Ptr String)
  , ("input_len"  , Bits32)
  , ("bbcode"     , Prim__bbcodePtr)
  , ("mem"        , Prim__allocPtr)
  , ("cached_upos", Bits32)
  , ("cached_cpos", Bits32) ]

||| typedef void (ic_completer_fun_t)
|||   (ic_completion_env_t* cenv, const char* prefix)
Prim__ic_completer_fun : Type
Prim__ic_completer_fun = Prim__ic_completion_envPtr -> String -> PrimIO ()

||| typedef void (ic_highlight_fun_t)
|||   (ic_highlight_env_t* henv, const char* input, void* arg)
Prim__ic_highlight_fun : Type
Prim__ic_highlight_fun = Prim__ic_highlight_envPtr -> String -> VoidPtr -> PrimIO ()

--------------------------------------------------------------------------------

||| char* ic_readline(const char* prompt_text)
export
%foreign rlLib "ic_readline"
prim__ic_readline : String -> PrimIO String

||| char* ic_readline_ex(const char* prompt_text,
|||   ic_completer_fun_t* completer, void* completer_arg,
|||   ic_highlight_fun_t* highlighter, void* highlighter_arg)
export
%foreign rlLib "ic_readline_ex"
prim__ic_readline_ex : String
                    -> Ptr Prim__ic_completer_fun -> VoidPtr
                    -> Ptr Prim__ic_highlight_fun -> VoidPtr
                    -> PrimIO String

--------------------------------------------------------------------------------

||| void ic_set_history(const char* fname, long max_entries)
export
%foreign rlLib "ic_set_history"
prim__ic_set_history : String -> Bits32 -> PrimIO ()

||| void ic_history_remove_last()
export
%foreign rlLib "ic_history_remove_last"
prim__ic_history_remove_last : PrimIO ()

||| void ic_history_clear()
export
%foreign rlLib "ic_history_clear"
prim__ic_history_clear : PrimIO ()

||| void ic_history_add(const char* entry)
export
%foreign rlLib "ic_history_add"
prim__ic_history_add : String -> PrimIO ()

--------------------------------------------------------------------------------

||| void ic_complete_filename(ic_completion_env_t* cenv, const char* prefix,
|||   char dir_separator, const char* roots, const char* extensions)
export
%foreign rlLib "ic_complete_filename"
prim__ic_complete_filename : Prim__ic_completion_envPtr -> String
                          -> Char -> String -> String
                          -> PrimIO ()
