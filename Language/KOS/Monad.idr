module Language.KOS.Monad

import Language.KOS.Core
import Language.KOS.Types

%default total

record KOSState (scope : ScopeStack) where
       constructor MkKOSState
       fresh : Int

||| Drops a scope level from the state. Right now, this doesn't do anything.
dropScope : KOSState (s :: scope) -> KOSState scope
dropScope = believe_me

||| Pushes a new scope level to the state. Right now, this doesn't do anything.
enterScope : KOSState scope -> KOSState (s :: scope)
enterScope = believe_me

||| The kOS monad used for building the AST.
export
record KOS (scope : ScopeStack) (a : Type) where
       constructor MkKOS
       runKOS : KOSState scope -> (a, KOSState scope, List (Stmt scope))

export
Functor (KOS scope) where
        map f (MkKOS r) = MkKOS $ \s => let (x, s', w) = r s in (f x, s', w)

export
Applicative (KOS scope) where
            pure x = MkKOS $ \s => (x, s, [])
            (<*>) (MkKOS r1) (MkKOS r2) = MkKOS $ \s =>
                  let (f, s1, w1) = r1 s in
                  let (x, s2, w2) = r2 s1 in (f x, s2, w1 ++ w2)

export
Monad (KOS scope) where
      (>>=) m f = MkKOS $ \s => 
            let (x, s1, w1) = runKOS m s in
            let (y, s2, w2) = runKOS (f x) s1
            in (y, s2, w1 ++ w2)

public export
ScopedKOS : ScopeStack -> Type -> Type
ScopedKOS outer a = (s : Scope) -> KOS (s :: outer) a

||| Returns the current KOS state.
get : KOS scope (KOSState scope)
get = MkKOS $ \s => (s,s, [])

||| Overwrites the current KOS state.
set : KOSState scope -> KOS scope ()
set new = MkKOS $ \_ => ((), new, [])

||| Modifies the KOS state and returns the old state.
modify : (KOSState scope -> KOSState scope) -> KOS scope (KOSState scope)
modify updt = MkKOS $ \s => (s, updt s, [])

||| Generates a fresh name with the given prefix.
freshName : String -> KOS scope String
freshName baseName = do
  num <- fresh <$> modify (record { fresh $= (+ 1) })
  pure $ baseName ++ "_" ++ show num

||| Emits a single statement.
export
emit : Stmt scope -> KOS scope ()
emit st = MkKOS $ \s => ((), s, [st])

||| Allows to use a kOS value a an action in the monad, implicitly generating the correcponding statement.
export
implicit valKOS : Val vs ty -> {auto p : IsSuffix vs scope} -> KOS scope ()
valKOS v = emit (SVal v)

collect : KOS (s :: scope) a -> KOS scope (a, List (Stmt (s :: scope)))
collect action = MkKOS $ \s => let (x, s', w) = runKOS action (enterScope s)
in ((x, w), dropScope s', [])

||| Root function used for constructing kOS scripts.
export
kosScript : ScopedKOS [] a -> Script
kosScript gen = let (x,s,w) = runKOS (gen someScope) (MkKOSState 0) in SBlock w

||| Declares a local variable with a fixed name.
export
local' : String -> Val vs a -> {auto p : IsSuffix vs scope} -> KOS scope (Ref Any scope a)
local' name val = do
       emit (SLocal name val)
       pure (RVar name)

||| Declares a local variable with a fresh name.
export
local : Val vs a -> {auto p : IsSuffix vs scope} -> KOS scope (Ref Any scope a)
local val = do
      name <- freshName "l"
      local' name val

||| Creates a nested scope.
export
block : ScopedKOS s a -> KOS s a
block gen = do
  (x, st) <- collect $ gen someScope
  emit (SBlock st)
  pure x

||| Assigns a variable.
export
assign : RefAccessor a rs ty -> {auto ap : can Set a} -> {auto p : IsSuffix rs scope}
       -> Val sv ty -> {auto p2 : IsSuffix sv scope} -> KOS scope ()
assign ref val = emit (SAssign ref val)

||| Builds an if-statement
export
kIf : Val vs Boolean -> {auto p : IsSuffix vs scope}
    -> ScopedKOS scope a -> ScopedKOS scope b -> KOS scope (a,b)
kIf cond kthen kelse = do
    (retThen, stmtThen) <- collect $ kthen someScope
    (retElse, stmtElse) <- collect $ kelse someScope
    emit $ SIf cond (SBlock stmtThen) (SBlock stmtElse)
    pure (retThen, retElse)

||| Builds a UNTIL-loop
export
kUntil : Val vs Boolean -> {auto p : IsSuffix vs scope} -> ScopedKOS scope a -> KOS scope a
kUntil cond body = do
       (ret, stmtBody) <- collect $ body someScope
       emit $ SUntil cond (SBlock stmtBody)
       pure ret
