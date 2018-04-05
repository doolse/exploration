module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExceptT)
import Control.Monad.Reader (lift, runReaderT)
import Control.Monad.State (evalState, get, gets, runState)
import Data.Array (index)
import Data.Either (Either, either)
import Data.Lens (_1)
import Data.Lens.Zoom (zoom)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..), uncurry)
import Javascript (JSExpr(..), anonFunc, emptyFunction, exprToString, functionContext, nativeJS, return, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (AP, Errors(..), NativeExpr, Type(..), applyLambda, applyResult, applyUnsafe, arg, ctArr, ctInt, ctString, intValue, lambda, resultType, undefInt)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" {args:ctArr [undefInt, undefInt]} undefInt (nativeApp undefInt undefInt) $ do 
  a <- arg 0
  b <- arg 1
  pure $ case {a,b} of 
    {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> 
        let v = IntT (Just $ ia * ib) 
        in Tuple v (nativeJS $ typeToJS v)
    {a, b} -> Tuple undefInt $ nativeApp a b 
  where 
  nativeApp a1 b1 = nativeJS do 
    ag <- typeToJS a1
    bg <- typeToJS b1
    pure $ do 
      ae <- ag 
      be <- bg
      pure $ InfixFuncApp " * " ae be

addInt :: Type
addInt = lambda "+" {args:ctArr [undefInt, undefInt]} undefInt (nativeApp undefInt undefInt) $ do 
  a <- arg 0
  b <- arg 1
  pure $ case {a,b} of 
    {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> 
        let v = IntT (Just $ ia + ib) 
        in Tuple v (nativeJS $ typeToJS v)
    {a, b} -> Tuple undefInt $ nativeApp a b 
  where 
  nativeApp a1 b1 = nativeJS do 
    ag <- typeToJS a1
    bg <- typeToJS b1
    pure $ do 
      ae <- ag 
      be <- bg
      pure $ InfixFuncApp " + " ae be

type FuncState = { o :: Type }

errorOrFunction :: Either Errors Type -> String 
errorOrFunction ee = bind ee typeToJS # either show mkFunc 
  where 
    mkFunc e = 
      let (Tuple ret body) = runState (runReaderT e functionContext) emptyFunction
      in exprToString (anonFunc ret body)

al l a = except $ applyLambda l a 

la :: Int -> Type -> forall r. AP r Type 
la i l = case l of 
  Lambda {args : ArrayT (Just arr) _} -> maybe (throwError $ Expected "Arg out of bounds") pure $ index arr i
  _ -> throwError (Expected "Lambda")

lr :: Type -> forall r. AP r Type 
lr l = case l of 
  Lambda {result} -> pure $ result
  _ -> throwError (Expected "Lambda")

ar :: Type -> forall r. AP r (Tuple Type (Either Errors NativeExpr))
ar l = case l of 
  Lambda {result, native} -> pure $ (Tuple result native)
  _ -> throwError (Expected "Lambda")

complex :: Type 
complex = lambda "complex" {args:ctArr [undefInt, undefInt]} undefInt (throwError $ Expected "To be applied") $ do
  a <- arg 0
  b <- arg 1
  o <- al mulInt [b, ctInt 3]
  a5 <- al mulInt [a, ctInt 5]
  aba0 <- la 0 a5
  aba1 <- lr a5
  ab <- al addInt [aba0, aba1]
  res0 <- lr ab
  res1 <- lr o
  result <- al addInt [res0, res1]
  ar result



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

  log $ unsafePartial $ unsafeCoerce $ errorOrFunction $ (applyLambda complex [undefInt, undefInt])
    
-- program(a, b)
-- {
--   let o = b * 3
--   a + a * 5 + o
--   
-- }