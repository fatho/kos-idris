module Language.KOS.CodeGen

import Data.Vect

import public Language.KOS.Core
import public Language.KOS.Types

%default total

genBinOp : BinOp a b c -> String
genBinOp OpAdd = "+"
genBinOp OpMul = "*"
genBinOp OpSub = "-"
genBinOp OpDiv = "/"
genBinOp OpPow = "^"
genBinOp OpAnd = "and"
genBinOp OpOr = "or"
genBinOp OpEQ = "="
genBinOp OpNEQ = "<>"
genBinOp OpLT = "<"
genBinOp OpGT = ">"
genBinOp OpLEQ = "<="
genBinOp OpGEQ = ">="

genUnOp : UnOp a b -> String
genUnOp OpNot = "not"
genUnOp OpNeg = "-"

mutual
  genArgs : ArgList scope args -> OptArgList scope opt -> String
  genArgs [] [] = ""
  genArgs [] (x :: []) = genVal x
  genArgs [] (x :: xs) = genVal x ++ ", " ++ genArgs [] xs
  genArgs (x :: []) [] = genVal x
  genArgs (x :: []) xs = genVal x ++ ", " ++ genArgs [] xs
  genArgs (x :: xs) ys = genVal x ++ ", " ++ genArgs xs ys

  genAccessor : Accessor a s ty' ty -> String
  genAccessor (ASuffix x) = ":" ++ x
  genAccessor (AIndex ix) = "[" ++ genVal ix ++ "]"
  genAccessor (ACompose ac1 ac2) = genAccessor ac1 ++ genAccessor ac2

  genRef : Ref a scope ty -> String
  genRef (RVar x) = x

  genVal : Val scope ty -> String
  genVal (VCall f args optargs) = "(" ++ genVal f ++ ")(" ++ genArgs args optargs ++ ")"
  genVal (VBinOp op x y) = "(" ++ genVal x ++ genBinOp op ++ genVal y ++ ")"
  genVal (VUnOp op x) = "(" ++ genUnOp op ++ " " ++ genVal x ++ ")"
  genVal (VScalar x) = show x
  genVal (VRef x) = genRef x
  genVal (VGet x ac) = genVal x ++ genAccessor ac

genRefAccessor : RefAccessor a s ty -> String
genRefAccessor (RARef x) = genRef x
genRefAccessor (RAAccess x y) = genRefAccessor x ++ genAccessor y

genStmt : Stmt scope -> String
genStmt (SVal x) = genVal x ++ "."
genStmt (SBlock xs) = "{\n" ++ unlines (assert_total (map genStmt xs))  ++ "}"
genStmt (SLocal name val) = "local " ++ name ++ " is " ++ genVal val ++ "."
genStmt (SGlobal name val) = "global  " ++ name ++ " is " ++ genVal val ++ "."
genStmt (SAssign r val) = "set " ++ genRefAccessor r ++ " to " ++ genVal val ++ "."
genStmt (SIf c t e) = "if " ++ genVal c ++ " " ++ genStmt t ++ " else " ++ genStmt e
genStmt (SUntil c b) = "until " ++ genVal c ++ " " ++ genStmt b
genStmt (SFor v e b) = "for " ++ v ++ " in " ++ genVal e ++ " " ++ genStmt b

generateCode : Script -> String
generateCode = genStmt
