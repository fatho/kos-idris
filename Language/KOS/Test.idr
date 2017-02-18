module Language.KOS.Test

import Language.KOS.CodeGen
import Language.KOS.Syntax

kMin : Ref Get [] (Fun [Scalar, Scalar] [] Scalar)
kMin = RVar "min"

kToString : Accessor Get [] (Fun [] [] String) ty
kToString = ASuffix "tostring"

kFoo : Accessor Get [] Scalar ty
kFoo = ASuffix "foo"

true : Ref Get [] Boolean
true = unsafeVar "true" Get

false : Ref Get [] Boolean
false = unsafeVar "false" Get

AG1 : Ref Any [] Boolean
AG1 = unsafeVar "AG1" Any

someList : Ref Get [] (Enumerable String)
someList = unsafeVar "lst" Get

foo : Script Language.KOS.Core.someScope
foo = kosScript someScope $ \s1 => do
    x <- local 1
    y <- local 2
    x := 3 + 3
    y := y + x
    if (y > 3):
      x := 1
    else:
      x := 2
    z <- local $ call kMin [x, y]
    s <- local $ call (z # kToString) []
    for e in someList:
        print e
    until (x <= 0):
          x := x - 1
    b <- local true
    toggle b
    b on
    b off
    on AG1: do
       print "AG1"
    toggle AG1
    print "end"
