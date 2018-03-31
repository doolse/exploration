module Main where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, infoShow, log)
import Data.Array (zip)
import Data.Either (Either(..), either)
import Data.Foldable (length)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Unsafe.Coerce (unsafeCoerce)

data ArgType = Positional Type | Field String Type
type JSArg = Tuple String JSExpr
type FuncArgs = {args::Array ArgType, return::Type}
data Type = 
    IntT (Maybe Int)  
  | StringT (Maybe String)
  | UnknownT 
  | CTLambda (FuncArgs -> Either String (Tuple FuncArgs Type))
  | RTLambda Type (Array JSExpr -> Maybe JSExpr)
  | TypeError String

data JSExpr =
     JSError String
   | Local String
   | JSInt Int
   | InfixFuncApp String JSExpr JSExpr 

data JSStatement = 
  Return JSExpr | AssignVar String JSExpr

newtype JSFunction = JSFunction { name :: String, params:: Array String, stmts :: Array JSStatement }

intOrError :: Type -> Either String Type 
intOrError i@(IntT _) = Right i 
intOrError UnknownT = Right (IntT Nothing)
intOrError t = Left "Not compatible with Int"

lt = Tuple 
unkInt = IntT Nothing

known i = IntT $ Just i

applyCT :: Type -> FuncArgs -> Tuple FuncArgs Type
applyCT = case _ of 
  (CTLambda f) -> \args -> either (TypeError >>> Tuple args) id (f args)
  (RTLambda t _) -> applyCT t
  err@(TypeError _) -> flip Tuple err
  _ -> flip Tuple (TypeError "Wrong type")

ifPos :: ArgType -> String -> (Type -> Either String Type) -> Either String (Tuple ArgType Type)
ifPos (Positional p) n f = (\t -> Tuple (Field n t) t) <$> f p 
ifPos fld@(Field fn t) n f | n == fn =  (\nt -> Tuple (Field n nt) nt) <$> f t
ifPos _ _ _ = Left "Wrong arg type"

-- addInt :: Int -> Int -> Int
addInt :: Type
addInt = CTLambda addApplyCT
  where 
  -- addRT already (Positional (IntT _)) _  = JSInt (v + 2)
  -- addRT i@(IntT Nothing) f = InfixFuncApp "+" f (JSInt 2)
  -- addRT _ _ = JSError "You cant apply that at runtime"

  addApplyCT {args:[arg1,arg2], return} = do 
    Tuple a1 t1 <- ifPos arg1 "a" intOrError
    Tuple a2 t2 <- ifPos arg2 "b" intOrError
    t3 <- intOrError return
    pure $ Tuple {args: [a1, a2], return: f t1 t2 t3} (RTLambda addInt frt)
    where 
      f (IntT (Just a)) (IntT (Just b)) _ = IntT (Just $ a + b)
      f _ _ c = c
      frt [a, b] = Just $ InfixFuncApp "+" a b
      frt _ = Nothing
  addApplyCT _ = Left "Wrong number of args"

-- add2 b = addInt 2 b

add2 :: Type 
add2 = CTLambda add2CT 
  where 
  add2CT {args:[arg1], return} = Right $ applyCT addInt {args: [arg1, Positional $ known 2], return}
  add2CT _ = Left "Wrong number of args"

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log $ unsafeCoerce $ applyCT add2 {args: [Positional $ known 7], return: UnknownT}
  -- applyRT callAddTwo (known 23) (Local "a")
