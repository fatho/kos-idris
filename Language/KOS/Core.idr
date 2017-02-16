module Language.KOS.Core

import public Control.Algebra.Lattice
import public Control.Category
import Data.Vect

import Language.KOS.Types

%default total

||| Allows the construction of a proof that one scope is a suffix of another.
public export
data IsSuffix : List a -> List a -> Type where
     SuffixRefl : IsSuffix xs xs
     SuffixSkip : IsSuffix xs ys -> IsSuffix xs (y :: ys)

||| Marker type for scopes, not really important (yet?).
export
data Scope : Type where
     MkScope : Scope

||| Allows outside modules to get a concrete scope value, without knowing what it will be.
export
someScope : Scope
someScope = MkScope

||| The stack of scopes used for making sure that references cannot escape.
public export
ScopeStack : Type
ScopeStack = List Scope

------------------------------------------------------------
-- Access control for references
------------------------------------------------------------

public export
data Access : Type where
     None : Access
     Get : Access
     Set : Access
     Any : Access

public export
JoinSemilattice Access where
  join None x = x
  join Get Get = Get
  join Set Set = Set
  join x y = Any

public export
BoundedJoinSemilattice Access where
  bottom = None

public export
MeetSemilattice Access where
  meet Any x = x
  meet Get Get = Get
  meet Get Any = Get
  meet Set Set = Set
  meet Set Any = Set
  meet x y = None

public export
BoundedMeetSemilattice Access where
  top = Any

||| `can a a'` is a statement asserting that we can perform access `a` when given access `a'`
public export
can : Access -> Access -> Type
can mustHave a = meet mustHave a = mustHave

||| `BinOp a b c` denotes a binary operator that takes arguments
||| of types `a` and `b`, and returns a value of type `c`.
public export
data BinOp : Type -> Type -> Type -> Type where
     OpAdd : BinOp Scalar Scalar Scalar
     OpMul : BinOp Scalar Scalar Scalar
     OpSub : BinOp Scalar Scalar Scalar
     OpDiv : BinOp Scalar Scalar Scalar
     OpPow : BinOp Scalar Scalar Scalar

     OpAnd : BinOp Boolean Boolean Boolean
     OpOr  : BinOp Boolean Boolean Boolean

     OpEQ  : BinOp Scalar Scalar Boolean
     OpNEQ : BinOp Scalar Scalar Boolean
     OpLT  : BinOp Scalar Scalar Boolean
     OpGT  : BinOp Scalar Scalar Boolean
     OpLEQ : BinOp Scalar Scalar Boolean
     OpGEQ : BinOp Scalar Scalar Boolean

public export
data UnOp : Type -> Type -> Type where
     OpNot : UnOp Boolean Boolean
     OpNeg : UnOp Scalar Scalar

mutual
  ||| `Ref s ty` denotes a reference declared in scope `s` of type `ty`.
  public export
  data Ref : Access -> ScopeStack -> Type -> Type where
       RVar : String -> Ref a s ty

  ||| Type of accessors, used for traversing nested data structures.
  public export
  data Accessor : Access -> ScopeStack -> Type -> Type -> Type where
       ||| This constructor essentially allows to cast a value into an arbitrary type,
       ||| so care must be taken when defining such suffixes.
       ASuffix : String -> Accessor a s tgt src
       AIndex : Val vs ti -> {auto ps : IsSuffix vs s } -> Accessor a s tgt src
       ACompose : Accessor a1 sc1 s r -> {auto ap : can Get a1} -> {auto p1 : IsSuffix sc1 sc}
                -> Accessor a2 sc2 t s -> {auto p2 : IsSuffix sc2 sc} -> Accessor a2 sc t r

  namespace args
    ||| Type safe list of scoped arguments.
    public export
    data ArgList : ScopeStack -> List Type -> Type where
         Nil  : ArgList scope []
         (::) : Val sc1 a -> {auto p : IsSuffix sc1 sc} -> ArgList sc args -> ArgList sc (a :: args)

  namespace optargs
    ||| Type safe list of scoped arguments.
    public export
    data OptArgList : ScopeStack -> List Type -> Type where
         Nil  : OptArgList scope xs
         (::) : Val sc1 a -> {auto p : IsSuffix sc1 sc} -> OptArgList sc args -> OptArgList sc (a :: args)

  ||| Data type representing a kOS value.
  public export
  data Val : ScopeStack -> Type -> Type where
     VCall : Val s1 (Fun args opt ret) -> {auto p1 : IsSuffix s1 vs}
           -> ArgList vs args -> OptArgList vs opt -> Val vs ret
     VBinOp : BinOp a b c -> Val s1 a -> {auto p1 : IsSuffix s1 vs}
            -> Val s2 b -> {auto p2 : IsSuffix s2 vs} -> Val vs c
     VUnOp : UnOp a c -> Val s1 a -> {auto p1 : IsSuffix s1 vs} -> Val vs c
     VScalar : Double -> Val scope Scalar

     VRef  : Ref a rs ty -> {auto ap : can Get a} -> {auto p : IsSuffix rs vs} -> Val vs ty
     VGet  : Val s1 ty -> {auto sp1 : IsSuffix s1 vs} -> Accessor a s2 ty' ty
           -> {auto sp1 : IsSuffix s2 vs} -> {auto ap : can Get a} -> Val vs ty'

export
(.) : Accessor a1 sc1 s r -> {auto ap : can Get a1} -> {auto p1 : IsSuffix sc1 sc}
    -> Accessor a2 sc2 t s -> {auto p2 : IsSuffix sc2 sc} -> Accessor a2 sc t r
(.) = ACompose

export
unsafeVar : String -> (a : Access) -> Ref a sc ty
unsafeVar name _ = RVar name

export
unsafeFun : String -> (a : Access) -> (arg : List Type) -> (opt : List Type) -> (ret : Type) -> Ref a sc (Fun arg opt ret)
unsafeFun name _ _ _ _ = RVar name

export
unsafeSuffix : String -> Accessor a scope s r
unsafeSuffix = ASuffix

export
unsafeIndex : Val vs ti -> {auto ps : IsSuffix vs scope} -> Accessor a scope s r
unsafeIndex = AIndex

infixl 8 #

namespace accessval
  export
  (#) : Val s1 ty -> {auto sp1 : IsSuffix s1 s} -> Accessor a' s2 ty' ty
      -> {auto sp1 : IsSuffix s2 s} -> {auto ap : can Get a'} -> Val s ty'
  (#) = VGet

||| Represents an accessor that has been applied to a reference.
public export
data RefAccessor : Access -> ScopeStack -> Type -> Type where
     RARef    : Ref a s ty -> RefAccessor a s ty
     RAAccess : RefAccessor a s ty -> {auto ap1 : can Get a} -> Accessor a' s ty' ty -> RefAccessor a' s ty'

namespace accessref
  export
  (#) : RefAccessor a s ty -> {auto ap : can Get a} -> Accessor a' s ty' ty -> RefAccessor a' s ty'
  (#) = RAAccess

||| Allows the implicit conversion of a reference to an access chain.
export
implicit refAccess : Ref a rs ty -> RefAccessor a rs ty
refAccess = RARef

||| Allows to implicitly use references as values.
export
implicit refVal : Ref a rs ty -> {auto ap : can Get a } -> {auto p : IsSuffix rs vs} -> Val vs ty
refVal r = VRef r

||| Allows to use a value where a super type is needed.
export
superCast : Val vs ty -> {auto p : ty :<= ty'} -> Val vs ty'
superCast v = believe_me v

namespace noopts
  ||| Builds a value from a function call.
  export
  call : Val sc1 (Fun args opt ret) -> {auto p : IsSuffix sc1 sc} -> ArgList sc args -> Val sc ret
  call v args = VCall v args []

namespace opts
  ||| Builds a value from a function call.
  export
  call : Val sc1 (Fun args opt ret) -> {auto p : IsSuffix sc1 sc} -> ArgList sc args 
       -> OptArgList sc opt -> Val sc ret
  call = VCall

||| Type of kOS statements. The data constructors are not meant to be used directly, 
||| but should be created using the `KOS` monad instead.
public export
data Stmt : ScopeStack -> Type where
     ||| Treats an expression as a value. Useful for expressions with side-effects, such as function calls.
     SVal    : Val vs ty -> {auto p : IsSuffix vs scope} -> Stmt scope
     ||| Introduces a nested scope.
     SBlock  : List (Stmt (s :: scope)) -> Stmt scope
     ||| Declares a local variable in the current scope.
     SLocal  : String -> Val vs ty -> {auto p : IsSuffix vs scope} -> Stmt scope
     ||| Declares a global variable.
     SGlobal : String -> Val vs ty -> {auto p : IsSuffix vs scope} -> Stmt scope
     ||| Assigns a value to something assignable.
     SAssign : RefAccessor a rs ty -> {auto ap : can Set a} -> {auto p : IsSuffix rs scope}
             -> Val sv ty -> {auto p2 : IsSuffix sv scope} -> Stmt scope
     ||| An if statement. Note that in order to seperate the scope of the then/else branches,
     ||| an explicit block needs to be introduced.
     SIf     : Val sc Boolean -> {auto p : IsSuffix sc scope}
             -> Stmt scope -> Stmt scope -> Stmt scope
     ||| UNTIL loop.
     SUntil  : Val sc Boolean -> {auto p : IsSuffix sc scope}
             -> Stmt scope -> Stmt scope
     ||| FOR loop.
     SFor    : String -> Val se enumty -> {auto p2 : IsSuffix se scope}
             -> {auto p3 : enumty :<= Enumerable ty} -> Stmt scope -> Stmt scope

||| Allows to use a kOS value as a statement. Useful for function calls.
export
implicit valStmt : Val vs ty -> {auto p : IsSuffix vs scope} -> Stmt scope
valStmt = SVal

||| Represents a kOS script file. For now, a script is a statement in the global scope.
public export
Script : Type
Script = Stmt []
