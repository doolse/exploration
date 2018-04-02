module Main where 

import Prelude

import Control.Monad.Except (ExceptT(..), runExceptT, throwError)
import Control.Monad.Reader (ReaderT(..), ask, runReaderT)
import Control.Monad.State (State, execState, gets, runState, runStateT)
import Data.Array (index)
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either)
import Data.Lens (ALens', Lens', assign, cloneLens, modifying, use, withLens)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Javascript (JSContext, JSExpr(..))
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String

type CompileAp = (forall s. Array (ALens' s Type) -> s -> Either Errors s)

type RuntimeAp = (forall m. Monad m => JSContext m -> m JSExpr)

type CT s = ReaderT (Array (ALens' s Type)) (ExceptT Errors (State s))

data Type = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | NamedType String Type
  | Lambda String CompileAp (Maybe RuntimeAp)

lambda :: String -> (forall s.  CT s Unit) -> Type
lambda name f = Lambda name (\l s -> 
    let (Tuple e ns) = (runState (runExceptT (runReaderT f l)) s) in rmap (const ns) e
  ) Nothing

self :: forall s. CT s Type
self = useArg 0 

runtime :: forall s. RuntimeAp -> CT s Unit
runtime r = do 
  t <- self >>= case _ of 
    Lambda name ca _ -> pure (Lambda name ca $ Just (unsafeCoerce r))
    _ -> throwError (Expected "Lambda")
  argLens 0 >>= modified (const t)

modified :: forall s a. (a -> a) -> ALens' s a -> CT s Unit
modified f l = modifying (cloneLens l) f

updateResult :: forall s. (Type -> Type) -> CT s Unit
updateResult f = argLens 1 >>= modified f

setResult :: forall s. Type -> CT s Unit 
setResult t = updateResult (const t)

useArg :: forall s. Int -> CT s Type
useArg i = argLens i >>= \l -> use (cloneLens l)

argLens :: forall s. Int -> CT s (ALens' s Type)
argLens i = ReaderT (\args -> index args i # maybe (throwError $ MissingArg (show i)) pure)

unify :: Type -> Type -> Either Errors Type 
unify (IntT _) UnknownT = Right $ IntT Nothing
unify (IntT _) b@(IntT _) = Right b
unify (StringT _) UnknownT = Right $ StringT Nothing
unify (StringT _) b@(StringT _) = Right $ b
unify (IntT _) o = Left $ Expected "Int"
unify (StringT _) o = Left $ Expected "String"
unify _ _ = Left $ Expected "Types that could unify"

unified :: forall s. Type -> ALens' s Type -> CT s Type
unified t1 t2l = do 
  let l = cloneLens t2l
  t2 <- use l
  unify t1 t2 # either throwError (\n2t -> assign l n2t $> n2t)

jsConstant :: Type -> Maybe JSExpr
jsConstant (IntT (Just a)) = JSInt a
jsConstant ()

exprForType :: Type -> Maybe RuntimeAp
exprForType = case _ of 
  UnknownT -> Nothing
  IntT

mulInt :: Type 
mulInt = lambda "*" do
  let calc (IntT (Just a)) (IntT (Just b)) = IntT (Just $ a * b)
      calc _ _ = IntT Nothing
  (calc <$> useArg 2 <*> useArg 3) >>= setResult
  runtime \ctx -> do 
    ctx.newArg 
    pure $ InfixFuncApp " * "
  -- pure UnknownT

--     use 
--   let _a = _arg "a"
--   let _b = _arg "b"
--   at <- unified unkInt _a
--   bt <- unified at _b  
--   let result = case {at,bt} of 
--         {at: (IntT (Just a)), bt:(IntT (Just b))} -> IntT (Just $ a * b)
--         _ -> IntT Nothing
--   assign (cloneLens return) result
--   pure $ RTLambda mulInt result $ ApplyRT case _ of 
--         [a,b] -> do 
--           ae <- lift $ a.expr
--           be <- lift $ b.expr
--           pure $ InfixFuncApp " * " ae be
--         _ -> throwError $ Expected "2 args" 
