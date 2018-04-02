module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Except (ExceptT(..), lift, runExceptT, throwError)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (ReaderT(..), ask, runReaderT)
import Control.Monad.State (State, evalState, execState, gets, runState, runStateT)
import Data.Array (index, length, range, unsafeIndex, updateAt)
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either)
import Data.Lens (ALens', Lens', assign, cloneLens, lens, modifying, use, withLens)
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Tuple (Tuple(..))
import Javascript (JSContext, JSExpr(..), emptyFunction, exprToString, functionContext, return)
import Partial.Unsafe (unsafePartial)
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String

type CompileAp = (forall s. Array (ALens' s Type) -> s -> Either Errors s)

newtype RuntimeAp = RuntimeAp (forall m. Monad m => ReaderT (JSContext m) m JSExpr)

type CT s = ReaderT (Array (ALens' s Type)) (ExceptT Errors (State s))

data Type = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | NamedType String Type
  | Lambda String CompileAp (Maybe RuntimeAp)

hasRT :: Type -> Boolean 
hasRT = case _ of 
  (IntT _) -> true 
  (StringT _) -> true 
  _ -> false

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
jsConstant = case _ of 
  (IntT (Just a)) -> Just $ JSInt a
  (StringT (Just s)) -> Just $ JSString s
  _ -> Nothing

-- exprToRT :: JSExpr -> (forall m. Monad m => JSContext m -> m JSExpr)
-- exprToRT e = \_ -> pure e 

exprForArg :: forall m. Monad m => Type -> ReaderT (JSContext m) m JSExpr
exprForArg t = ReaderT \ctx -> case t of 
  t | Just e <- jsConstant t -> pure e
  t -> ctx.newArg

mulInt :: Type 
mulInt = lambda "*" do
  let calc (IntT (Just a)) (IntT (Just b)) = IntT (Just $ a * b)
      calc _ _ = IntT Nothing
  result <- calc <$> useArg 2 <*> useArg 3
  setResult result
  at <- useArg 2
  bt <- useArg 3
  runtime $ RuntimeAp (
    jsConstant result # flip maybe pure do 
    a <- exprForArg at
    b <- exprForArg bt
    pure $ InfixFuncApp " * " a b)
    
unsafeIx :: Int -> ALens' (Array Type) Type
unsafeIx i = unsafePartial $ 
  lens (flip unsafeIndex i) (\s u -> fromJust $ updateAt i u s)

runFunc :: Array Type -> Either Errors (Array Type)
runFunc args = unsafePartial $ case unsafeIndex args 0 of 
  (Lambda name f _) -> f (unsafeIx <$> (range 0 $ (length args) - 1)) args
  _ -> throwError $ Expected ""

expressionFunc :: Type -> Either Errors JSExpr
expressionFunc = case _ of 
  (Lambda name _ (Just (RuntimeAp f))) -> do 
    let (Tuple e fb) = runState (runReaderT f functionContext) emptyFunction
    pure $ JSAnonFunc (return e fb)
  _ -> throwError $ Expected "Lambda with RT"

-- (Tuple _ {return}) | Just e <- ctConstant return = Right e
-- expressionOrFunc (Tuple r _) | Just e <- ctConstant r = Right e
-- expressionOrFunc (Tuple (RTLambda _ _ f) {args}) = 
--   let appliedRT = runExceptT $ do 
--         expr <- runApplyRT f $ (\arg -> {arg, expr:constantOrParam arg}) <$> args
--         gets (_ {stmts = [Return expr]})
--   in AnonymousFunc <$> evalState appliedRT {params:[],stmts:[]}
-- expressionOrFunc (Tuple t _) = Left $ (Expected $ "Lambda but was: " <> show t)

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log $ unsafePartial $ unsafeCoerce $ do 
    a <- runFunc [mulInt, UnknownT, IntT $ Just 12, IntT $ Nothing]
    exprToString <$> (expressionFunc $ unsafeIndex a 0)

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
