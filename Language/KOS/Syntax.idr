||| Provides the basic syntax of the kOS embedding, consisting of the operators and custom Idris syntax.
module Language.KOS.Syntax

import Control.Algebra.Lattice

import public Language.KOS.Core
import public Language.KOS.Monad
import public Language.KOS.Types

%access export

syntax [ref] ":=" [val] = assign ref val
syntax "if" [cond] ":" [kthen] "else" ":" [kelse] = kIf cond (\_ => kthen) (\_ => kelse)
syntax "if" [cond] "then" [kthen] "endif" = kIf cond (\_ => kthen) (\_ => pure ())
syntax "block" [body] = block (\_ => body)
syntax "until" [cond] ":" [body] = kUntil cond (\_ => body)
syntax "for" {v} "in" [enum] ":" [body] = kFor enum (\_, v => body)
syntax "lock" [ref] "to" [val] = lock ref val
syntax "local" "lock" [val] = localLock val
syntax "wait" "until" [cond] = waitUntil cond
syntax [ref] "off" = turnOff ref
syntax [ref] "on" = turnOn ref
syntax "when" [cond] ":" [body] = when cond body
syntax "on" [cond] ":" [body] = on cond body

-- Implement standard interfaces for values.
-- The problem: all values must be in the same scope for this to work.
-- That's why further below, more general variants have been declared as well.
-- Let's hope that this doesn't confuse Idris' overload resolution.

export
Num (Val s Scalar) where
    (+) x y = VBinOp OpAdd x y
    (*) x y = VBinOp OpMul x y
    fromInteger = VScalar . fromInteger

export
Neg (Val s Scalar) where
    (-) x y = VBinOp OpSub x y
    negate x = VUnOp OpNeg x
    abs x = call (unsafeFun "abs" Get [Scalar] [] Scalar) [x]

export
Fractional (Val s Scalar) where
           (/) x y = VBinOp OpDiv x y
           recip x = VBinOp OpDiv 1 x

export
(+) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Scalar
(+) = VBinOp OpAdd

export
(-) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Scalar
(-) = VBinOp OpSub

export
(*) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Scalar
(*) = VBinOp OpMul

export
(/) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Scalar
(/) = VBinOp OpDiv

infixl 10 ^
export
(^) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Scalar
(^) = VBinOp OpPow

export
(==) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
     -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(==) = VBinOp OpEQ

export
(/=) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
     -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(/=) = VBinOp OpNEQ

export
(<) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(<) = VBinOp OpLT

export
(>) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
    -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(>) = VBinOp OpGT

export
(<=) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
     -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(<=) = VBinOp OpLEQ

export
(>=) : Val s1 Scalar -> {auto p1 : IsSuffix s1 vs}
     -> Val s2 Scalar -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(>=) = VBinOp OpGEQ


export
(&&) : Val s1 Boolean -> {auto p1 : IsSuffix s1 vs}
-> Val s2 Boolean -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(&&) = VBinOp OpAnd

export
(||) : Val s1 Boolean -> {auto p1 : IsSuffix s1 vs}
-> Val s2 Boolean -> {auto p2 : IsSuffix s2 vs} -> Val vs Boolean
(||) = VBinOp OpAnd

export
not : Val s1 Boolean -> {auto p1 : IsSuffix s1 vs} -> Val vs Boolean
not = VUnOp OpNot
