module Language.KOS.Types

import public Data.Vect

%access export

||| scalar type
data Scalar
||| Boolean type
data Boolean
||| String type
data KString
||| structure type
data Structure
||| function type
data Fun : List Type -> List Type -> Type -> Type
||| Anything that can be enumerated.
data Enumerable : Type -> Type

public export
interface Super t where
          super : (t' : Type) -> {auto p : t' = t} -> Type

public export
Super Scalar where
      super _ = Structure

public export
Super Boolean where
      super _ = Structure

public export
Super String where
      super _ = Structure

public export
Super (Fun args opt ret) where
      super _ = Structure

public export
Super (Enumerable a) where
      super _ = Structure

infix 5 :<=
public export
data (:<=) : Type -> Type -> Type where
     SuperRefl  : t :<= t
     SuperTrans : Super sub => (super sub) :<= sup -> sub :<= sup
