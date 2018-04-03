module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (lift, runReaderT)
import Control.Monad.State (evalState, get, gets, runState)
import Data.Either (Either, either)
import Data.Lens (_1)
import Data.Lens.Zoom (zoom)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)
import Javascript (JSExpr(..), anonFunc, emptyFunction, exprToString, functionContext, nativeJS, return, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors, NativeExpr, Type(..), applyUnsafe, arg, ctArr, ctInt, ctString, intValue, undefInt, unifiedLambda)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = unifiedLambda "*" undefInt {args:ctArr [undefInt, undefInt]} $ do 
  a <- arg 0
  b <- arg 1
  let calc (Just a) (Just b) = IntT (Just $ a * b)
      calc _ _ = nativeJS undefInt do 
        ajs <- typeToJS a 
        bjs <- typeToJS b 
        pure $ InfixFuncApp " * " ajs bjs
  pure $ calc (intValue a) (intValue b)

addInt :: Type
addInt = unifiedLambda "*" undefInt {args:ctArr [undefInt, undefInt]} $ do 
  a <- arg 0
  b <- arg 1
  let calc (Just a) (Just b) = IntT (Just $ a + b)
      calc _ _ = nativeJS undefInt do 
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

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  let stateFul :: Type 
      stateFul = unifiedLambda "State" UnknownT  consts body 

  log $ unsafePartial $ unsafeCoerce $ errorOrFunction $ pure (applyUnsafe stateFul [ctInt (-341)])
    
  where 
    consts = {args: ctArr [undefInt], o: applyUnsafe mulInt [ctInt 23, ctInt 232]}
    body = do 
      {o} <- get
      a0 <- arg 0 
      pure $ applyUnsafe addInt [a0, o]
