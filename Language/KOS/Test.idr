module Language.KOS.Test

import Language.KOS.Syntax

kMin : Ref Get [] (Fun [Scalar, Scalar] [] Scalar)
kMin = RVar "min"

kToString : Accessor Get [] (Fun [] [] KString) ty
kToString = ASuffix "tostring"

kFoo : Accessor Get [] Scalar ty
kFoo = ASuffix "foo"

-- syntax LOCAL {x} IS [val] [rest] = (local "foo" val >>= \x -> rest)
--syntax LOCAL IS [val] = local val
syntax BLOCK [stmts] = block $ \_ => stmts
syntax [ref] ":=" [val] = assign ref val
syntax IF [cond] THEN [kthen] ELSE [kelse] ENDIF = kIf cond (\_ => kthen) (\_ => kelse)

true : Val [] Boolean
true = unsafeVar "true" Get

false : Val [] Boolean
false = unsafeVar "false" Get

foo : Script
foo = kosScript $ \s1 => do
    x <- local 1
    y <- local 2
    x := 3 + 3
    y := y + x
    IF y > 3 THEN do
      x := 1
    ELSE do
      x := 2
    ENDIF
    z <- local $ call kMin [x, y]
    call (z # kToString) []
    pure ()
