module Javascript where 

import Prelude

import Control.Monad.State (State, get, modify)
import Data.Array (length, snoc)
import Data.String (joinWith)
import Data.Symbol (SProxy(..))

data JSExpr =
     Local String
   | JSInt Int
   | JSString String
   | InfixFuncApp String JSExpr JSExpr 
   | JSAnonFunc JSFunctionBody

data JSStatement = 
  Return JSExpr | AssignVar String JSExpr

type JSFunctionBody = { params:: Array String, stmts :: Array JSStatement }

return :: JSExpr -> JSFunctionBody -> JSFunctionBody
return e fb = fb {stmts = snoc fb.stmts $ Return e }
 
emptyFunction = {params:[], stmts:[]}

type JSContext m = { newArg :: m JSExpr, newLocal :: JSExpr -> m JSExpr }

exprToString (Local l) = l 
exprToString (JSString s) = "\"" <> s <> "\""
exprToString (JSInt i) = show i
exprToString (InfixFuncApp n a b) = exprToString a <> n <> exprToString b
exprToString (JSAnonFunc {params, stmts}) =  "function(" <> (joinWith "," params) <> ") {" <> 
        joinWith "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"

functionContext :: JSContext (State JSFunctionBody)
functionContext = {newArg, newLocal} 
  where 
    newArg = do 
      {params} <- get
      let newName = "p" <> (show $ length params)
      modify _ {params = snoc params newName}
      pure $ Local newName
    newLocal expr = do 
      {stmts} <- get
      let newName = "v" <> (show $ length stmts)
      modify _ {stmts = snoc stmts $ AssignVar newName expr}
      pure $ Local newName
  
