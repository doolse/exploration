{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts #-}
{-# LANGUAGE LambdaCase,TupleSections,TemplateHaskell #-}

module NativeJavascript where 

import Types 
import Javascript 
import Data.Semigroup
import Control.Monad.State
import Control.Monad.Trans.Except

mulInt :: Type
mulInt = lambda "*" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT = NativeGenerator (\args _ _ -> do 
    let a = jsArg args 0
        b = jsArg args 1 
    pure $ nativeJS $ InfixFuncApp " * " a b)

  doMult args = do
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case (a,b) of 
          (a, b) | (Just ia, Just ib) <- (intValue a, intValue b) -> ctInt (ia * ib)
          _ -> undefInt
    pure $ ArgsResult {args = [a,b], result}

addString :: Type 
addString = lambda "+" [undefString, undefString] undefString doAddStr doAddStrRT 
  where 
  doAddStr args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case (a,b) of 
          (a, b) | (Just ia, Just ib) <- (strValue a, strValue b) -> ctString (ia <> ib)
          _ -> undefString
    pure $ ArgsResult {args = [a,b], result}

  doAddStrRT = NativeGenerator (\args toNE out -> do
    let a = jsArg args 0
        b = jsArg args 1 
    pure $ nativeJS $ InfixFuncApp " + " a b)
  
add :: Type 
add = polyLambda "+" [unknownT, unknownT] unknownT [addInt, addString]

addInt :: Type
addInt = lambda "+" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT = NativeGenerator (\args _ _ -> pure $ nativeJS $ case (jsArg args 0, jsArg args 1) of 
    -- {a:JSInt 0,b} -> b
    -- {a,b:JSInt 0} -> a 
    -- {a:JSInt a,b:JSInt b} -> JSInt $ a + b
    (a,b) -> InfixFuncApp " + " a b)

  doMult args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case (a,b) of 
          (a, b) | (Just ia, Just ib) <- (intValue a, intValue b) -> ctInt (ia + ib)
          (a, Type {t}) | Just 0 <- intValue a -> Type {t, refs=0}
          (Type {t}, b) | Just 0 <- intValue b -> Type {t, refs=0}
          _ -> undefInt
    pure $ ArgsResult {args=[a,b], result}

errorOrFunction :: Type -> [Type] -> String 
errorOrFunction l args = either show id $ do
  LambdaR {frt= NativeGenerator f, args= aargs} <- applyLambda l args >>= lambdaR
  let mkConst = fmap nativeJS <$> typeToJS
      local e = nativeJS <$> newLocal (fromNative e)
      natArg t = (t,) . nativeJS <$> constOrArg t
      funcBody = do 
        nargs <- traverse natArg aargs
        f nargs unknownT NativeContext {mkConst,local}
  let (errorOrlast, fb) = runState (runExceptT funcBody) emptyFunction
  last <- errorOrlast
  pure $ exprToString $ anonFunc fb (fromNative last)
