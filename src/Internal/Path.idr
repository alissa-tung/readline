module Internal.Path

%default total

public export
rlLib : String -> String
rlLib f = "C:" ++ f ++ ", __LIB_PREFIX__/libisoclineidr.so"
