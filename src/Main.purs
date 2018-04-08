module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExceptT)
import Control.Monad.Reader (lift, runReaderT)
import Control.Monad.State (State, evalState, get, gets, runState)
import Data.Array (index)
import Data.Either (Either, either)
import Data.Lens (_1)
import Data.Lens.Zoom (zoom)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..), uncurry)
import Javascript (JSExpr(..), JSFunctionBody, JSRuntimeGen, anonFunc, constOrArg, emptyFunction, exprToString, functionContext, genFunc, nativeJS, newArg, return, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors(..), NativeExpr, Type(..), TypeT(..), applyLambda, applyResult, applyUnsafe, arr, ctArr, ctInt, ctString, intValue, lambda, result, resultType, typeT, undefInt)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" [undefInt, undefInt] undefInt doMult 
  where 
  doMult args = do 
    a <- arr 0 args
    b <- arr 1 args 
    pure $ case {a,b} of 
      {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> 
          let result = ctInt (ia * ib) 
          in {args, result}
      {a, b} -> let 
        resfunc = do 
          ar <- typeToJS a  
          br <- typeToJS b
          pure $ do 
            ae <- ar 
            be <- br
            pure $ InfixFuncApp " * " ae be
            in {args, result: Type (IntT Nothing) (nativeJS <$> resfunc)}

addInt :: Type
addInt = lambda "*" [undefInt, undefInt] undefInt doMult 
  where 
  doMult args = do 
    a <- arr 0 args
    b <- arr 1 args 
    pure $ case {a,b} of 
      {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> 
          let result = ctInt (ia * ib) 
          in {args, result}
      {a, b} -> let 
        resfunc = do 
          ar <- typeToJS a  
          br <- typeToJS b
          pure $ do 
            ae <- ar 
            be <- br
            pure $ InfixFuncApp " + " ae be
            in {args, result: Type (IntT Nothing) (nativeJS <$> resfunc)}

type FuncState = { o :: Type }

errorOrFunction :: Type -> Array Type -> String 
errorOrFunction l args = 
  let (Tuple t fb) = runState (traverse constOrArg args) emptyFunction
      actualFunc g = exprToString (genFunc fb g)
      mkFunc e = maybe "ERROR" actualFunc $ typeToJS e
  in either show mkFunc $ (applyLambda l t >>= resultType)

al = applyLambda
lr = resultType

larg :: Int -> Type -> Either Errors Type
larg i t = case typeT t of 
  (Lambda {args}) -> arr i args
  _ -> throwError $ Expected "Lambda"

complex :: Type 
complex = lambda "complex" [undefInt, undefInt] undefInt doComp 
  where 
  doComp args = do
    a <- arr 0 args
    b <- arr 1 args
    o <- applyLambda mulInt [b, ctInt 3]
    a5 <- applyLambda mulInt [a, ctInt 5]
    aba0 <- larg 0 a5
    aba1 <- lr a5
    ab <- applyLambda addInt [aba0, aba1]
    res0 <- lr ab
    res1 <- lr o
    res <- applyLambda addInt [res0, res1]
    result [larg 0 ab, larg 0 o] (lr res) 



  -- result <- except $ do 
  --   o <- applyResult mulInt [a, ctInt 3]
  --   a5 <- applyResult mulInt [b, ctInt 5]
  --   ab <- applyResult addInt [a, a5]
  --   applyLambda addInt [ab, o]
  -- pure (Tuple result $ Just $ nativeJS $ typeToJS result)

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- let stateFul :: Type 
  --     stateFul = lambda "State" UnknownT  consts body 

  log $ unsafePartial $ unsafeCoerce $ errorOrFunction complex [undefInt, ctInt 15]
    
-- program(a, b)
-- {
--   let o = b * 3
--   a + a * 5 + o
--   
-- }