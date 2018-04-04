module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExceptT)
import Control.Monad.Reader (lift, runReaderT)
import Control.Monad.State (evalState, get, gets, runState)
import Data.Either (Either, either)
import Data.Lens (_1)
import Data.Lens.Zoom (zoom)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)
import Javascript (JSExpr(..), anonFunc, emptyFunction, exprToString, functionContext, nativeJS, return, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors, NativeExpr, Type(..), applyLambda, applyResult, applyUnsafe, arg, ctArr, ctInt, ctString, intValue, lambda, resultType, undefInt)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" {args:ctArr [undefInt, undefInt]} undefInt  $ do 
  a <- arg 0
  b <- arg 1
  let calc (Just a) (Just b) = let v = IntT (Just $ a * b) in Tuple v (Just $ nativeJS $ typeToJS v) 
      calc _ _ = Tuple undefInt $ Just $ nativeJS do 
        ajs <- typeToJS a 
        bjs <- typeToJS b 
        pure $ InfixFuncApp " * " ajs bjs
  pure $ calc (intValue a) (intValue b)

addInt :: Type
addInt = lambda "+" {args:ctArr [undefInt, undefInt]} undefInt $ do 
  a <- arg 0
  b <- arg 1
  let calc (Just a) (Just b) = let v = IntT (Just $ a + b) in Tuple v (Just $ nativeJS $ typeToJS v)
      calc _ _ = Tuple undefInt $ Just $ nativeJS  do 
        ajs <- typeToJS a 
        bjs <- typeToJS b 
        pure $ InfixFuncApp " + " ajs bjs
  pure $ calc (intValue a) (intValue b)

type FuncState = { o :: Type }

errorOrFunction :: Either Errors Type -> String 
errorOrFunction ee = ee # either show mkFunc 
  where 
    mkFunc e = 
      let (Tuple ret body) = runState (runReaderT (typeToJS e) functionContext) emptyFunction
      in exprToString (anonFunc ret body)

complex :: Type 
complex = lambda "complex" {args:ctArr [undefInt, undefInt]} undefInt $ do
  a <- arg 0
  b <- arg 1
  result <- except $ do 
    o <- applyResult mulInt [a, ctInt 3]
    a5 <- applyResult mulInt [b, ctInt 5]
    ab <- applyResult addInt [a, a5]
    applyLambda addInt [ab, o]
  pure (Tuple result $ Just $ nativeJS $ typeToJS result)

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- let stateFul :: Type 
  --     stateFul = lambda "State" UnknownT  consts body 

  log $ unsafePartial $ unsafeCoerce $ errorOrFunction $ (applyLambda complex [undefInt, undefInt])
    
-- program(a, b)
-- {
--   let o = b * 3
--   a + a * 5 + o
--   
-- }