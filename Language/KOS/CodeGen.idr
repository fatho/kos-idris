module Language.KOS.CodeGen

import Data.List
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

reqPrec : Int -> String -> Int -> String
reqPrec mustHave str actual = if actual > mustHave then "(" ++ str ++ ")" else str

escapeString : String -> String
escapeString = pack . foldr escape Prelude.List.Nil . unpack where
  escape c str = if c == '"' then '\\' :: c :: str else c :: str

mutual
  genArgs : ArgList scope args -> OptArgList scope opt -> String
  genArgs [] [] = ""
  genArgs [] (x :: []) = genVal x 10
  genArgs [] (x :: xs) = genVal x 10 ++ ", " ++ genArgs [] xs
  genArgs (x :: []) [] = genVal x 10
  genArgs (x :: []) xs = genVal x 10 ++ ", " ++ genArgs [] xs
  genArgs (x :: xs) ys = genVal x 10 ++ ", " ++ genArgs xs ys

  genAccessor : Accessor a s ty' ty -> String
  genAccessor (ASuffix x) = ":" ++ x
  genAccessor (AIndex ix) = "[" ++ genVal ix 10 ++ "]"
  genAccessor (ACompose ac1 ac2) = genAccessor ac1 ++ genAccessor ac2

  genRef : Ref a scope ty -> String
  genRef (RVar x) = x

  genVal : Val scope ty -> Int -> String
  genVal (VCall f args optargs) = reqPrec 10 (genVal f 10 ++ "(" ++ genArgs args optargs ++ ")")
  genVal (VBinOp op x y) = reqPrec 5 (genVal x 6 ++ genBinOp op ++ genVal y 6)
  genVal (VUnOp op x) = reqPrec 5 (genUnOp op ++ " " ++ genVal x 6)
  genVal (VScalar x) = \_ => show x
  genVal (VString x) = \_ => "\"" ++ escapeString x ++ "\""
  genVal (VRef x) = \_ => genRef x
  genVal (VGet x ac) = reqPrec 10 (genVal x 10 ++ genAccessor ac)

genRefAccessor : RefAccessor a s ty -> String
genRefAccessor (RARef x) = genRef x
genRefAccessor (RAAccess x y) = genRefAccessor x ++ genAccessor y

mutual
  genStmtList : StmtList scope -> String
  genStmtList xs = "{\n" ++ unlines (assert_total (map genStmt xs))  ++ "}"

  genStmt : Stmt scope -> String
  genStmt (SVal x) = genVal x 10 ++ "."
  genStmt (SBlock xs) = genStmtList xs
  genStmt (SLocal name val) = "local " ++ name ++ " is " ++ genVal val 10 ++ "."
  genStmt (SGlobal name val) = "global  " ++ name ++ " is " ++ genVal val 10 ++ "."
  genStmt (SAssign r val) = "set " ++ genRefAccessor r ++ " to " ++ genVal val 10 ++ "."
  genStmt (SToggle r) = "toggle " ++ genRefAccessor r ++ "."
  genStmt (STurnOn r) = genRefAccessor r ++ " on."
  genStmt (STurnOff r) = genRefAccessor r ++ " off."
  genStmt (SIf c t e) = "if " ++ genVal c 10 ++ " " ++ genStmtList t ++ " else " ++ genStmtList e
  genStmt (SUntil c b) = "until " ++ genVal c 10 ++ " " ++ genStmtList b
  genStmt (SFor v e b) = "for " ++ v ++ " in " ++ genVal e 10 ++ " " ++ genStmtList b
  genStmt (SBreak) = "break."
  genStmt (SWait x) = "wait " ++ genVal x 10 ++ "."
  genStmt (SWaitUntil x) = "wait until " ++ genVal x 10 ++ "."
  genStmt (SPrint x) = "print " ++ genVal x 10 ++ "."
  genStmt (SLocalLock name val) = "local lock " ++ name ++ " to " ++ genVal val 10 ++ "."
  genStmt (SLock ref val) = "lock " ++ genRefAccessor ref ++ " to " ++ genVal val 10 ++ "."
  genStmt (SWhen cond body) = "when " ++ genVal cond 10 ++ " then " ++ genStmtList body
  genStmt (SOn trig body) = "on " ++ genVal trig 10 ++ " " ++ genStmtList body

generateCode : Script s -> String
generateCode script = unlines $ map genStmt script
