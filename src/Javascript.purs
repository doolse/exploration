module Javascript where 

import Prelude

import Control.Monad.State (State)
import Data.String (joinWith)

data JSExpr =
     Local String
   | JSInt Int
   | JSString String
   | InfixFuncApp String JSExpr JSExpr 
   | AnonymousFunc {params::Array String, stmts :: Array JSStatement}

data JSStatement = 
  Return JSExpr | AssignVar String JSExpr

type JSFunction = { name :: String, params:: Array String, stmts :: Array JSStatement }

type JSContext m = { newArg :: m JSExpr, newLocal :: JSExpr -> m JSExpr }

exprToString (Local l) = l 
exprToString (JSString s) = "\"" <> s <> "\""
exprToString (JSInt i) = show i
exprToString (InfixFuncApp n a b) = exprToString a <> n <> exprToString b
exprToString (AnonymousFunc {params, stmts}) =  "function(" <> (joinWith "," params) <> ") {" <> 
        joinWith "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"
