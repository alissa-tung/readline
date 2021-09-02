module System.Console.ReadLine.Internal

import System.FFI

%default total

--------------------------------------------------------------------------------

rlLib : String -> String
rlLib f = "C:" ++ f ++ ", /usr/local/lib/libisocline.so"

--------------------------------------------------------------------------------

VoidPtr : Type
VoidPtr = AnyPtr

CBool : Type
CBool = Bits32

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

--------------------------------------------------------------------------------

||| char* ic_readline(const char* prompt_text)
export
%foreign rlLib "ic_readline"
prim__ic_readline : String -> PrimIO String
