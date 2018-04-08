module Main where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExceptT)
import Control.Monad.Reader (lift, runReaderT)
import Control.Monad.State (State, StateT(..), evalState, get, gets, runState, runStateT)
import Data.Array (foldl, foldr, fromFoldable, index, mapWithIndex, unsafeIndex, updateAt, zip)
import Data.Either (Either(..), either)
import Data.Lens (ALens', Lens', _1, _2, assign, cloneLens, lens', modifying, set, use, view, viewOn)
import Data.Lens.Record (prop)
import Data.Lens.Zoom (zoom)
import Data.List.Lazy (range)
import Data.Maybe (Maybe(..), fromJust, maybe, maybe')
import Data.Symbol (SProxy(..))
import Data.Traversable (sequence, traverse, traverse_)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Debug.Trace (spy)
import Javascript (JSExpr(..), JSFunctionBody, JSRuntimeGen, anonFunc, constJS, constOrArg, emptyFunction, exprToString, fromNative, functionContext, genFunc, jsArg, nativeJS, newArg, return, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors(..), LambdaR, NativeContext, NativeExpr, Type(..), TypeT(..), applyLambda, applyResult, applyUnsafe, arr, ctArr, ctInt, ctString, incRef, intValue, lambda, lambdaR, result, resultType, typeT, undefInt, unknownT)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT args toNE = pure $ nativeJS do 
    a <- jsArg args 0
    b <- jsArg args 1 
    pure $ InfixFuncApp " * " a b

  doMult args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case {a,b} of 
          {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> ctInt (ia * ib)
          _ -> undefInt
    pure $ {args:[a,b], result}

addInt :: Type
addInt = lambda "+" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT args toNE = pure $ nativeJS do
    a <- jsArg args 0
    b <- jsArg args 1 
    pure $ InfixFuncApp " + " a b

  doMult args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case {a,b} of 
          {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> ctInt (ia + ib)
          _ -> undefInt
    pure $ {args:[a,b], result}

type FuncState = { o :: Type }

errorOrFunction :: Type -> Array Type -> String 
errorOrFunction l args = 
  let mkFunc (Tuple fb r) = exprToString (genFunc fb $ fromNative r)
  in either show mkFunc $ do 
        {frt,args:pargs} <- applyLambda l args >>= lambdaR
        let (Tuple t fb) = runState (traverse constOrArg pargs) emptyFunction
        Tuple fb <$> frt (zip pargs $ constJS <$> t) {const: typeToJS >>> map constJS}

al = applyLambda
lr = resultType

larg :: Int -> Type -> Either Errors Type
larg i t = case typeT t of 
  (Lambda {args}) -> arr i args
  _ -> throwError $ Expected "Lambda"

newtype LTypeArray = LTypeArray (Array (LType LTypeArray))

type LType s = Tuple Type (s -> NativeContext -> Either Errors NativeExpr)

type App s = {name :: String, f :: ALens' s (LType s), args :: Array (ALens' s (LType s)), result :: ALens' s (LType s) }

type StateLambda s = {args :: ALens' s (Array (LType s)), apps :: Array (App s)}

typeOnly :: forall s. String -> Type -> LType s
typeOnly n t = Tuple t \_ _ -> throwError $ Expected $ "A native representation for " <> n 

constExpr :: forall s. Type -> NativeExpr -> LType s 
constExpr t ne = Tuple t (\_ _ -> pure ne)

ltIx :: forall a. Int -> ALens' LTypeArray (LType LTypeArray)
ltIx i = unsafePartial $ lens' \(LTypeArray arr) -> Tuple (unsafeIndex arr i) 
        (\lt -> LTypeArray $ fromJust $ updateAt i lt arr) 

argl :: forall s. Array (ALens' s (LType s)) -> Lens' s (Array (LType s))
argl la = lens' \s -> Tuple ((\l -> view (cloneLens l) s) <$> la) 
            (\ta -> foldr doset s (zip la ta))
  where 
  doset (Tuple l v) = set (cloneLens l) v

c :: forall s a. Type -> Lens' s (LType s) 
c a = lens' \s -> Tuple (Tuple a \_ ctx -> maybe (throwError $ Expected $ "A constant for" <> show a) pure $ ctx.const a) (const s)

capp :: forall s. String -> Type -> Array (ALens' s (LType s)) -> ALens' s (LType s) -> App s
capp name cf args result = {name, f: c cf, args, result}

applyIt :: forall s. (LambdaR -> LType s) -> App s -> StateT s (Either Errors) (LType s)
applyIt f ap = do 
  (Tuple lam _) <- use (cloneLens ap.f)
  args <- traverse (\al -> use (cloneLens al)) ap.args
  r <- lift $ applyLambda lam (fst <$> args) >>= lambdaR 
  let lt = f r
  traverse_ (\(Tuple al v) -> assign ((cloneLens al) <<< _1) v) $ zip ap.args r.args
  assign (cloneLens ap.result) $ lt
  news <- get
  let _ = spy (news)
  pure $ lt

ct :: forall s. StateLambda s -> s -> Array Type -> Either Errors {args:: Array Type, result :: Type}
ct sl s args = 
  let applyCT fa app = fa *> (Just <<< fst <$> applyIt (_.result >>> typeOnly app.name) app) 
      run = foldl applyCT (pure Nothing) sl.apps
      convertResult (Tuple (Just result) s) = pure {args: fst <$> view (cloneLens sl.args) s, result}
      convertResult _ = throwError $ Expected "No result from body"
  in convertResult =<< runStateT (assign (cloneLens sl.args) (mapWithIndex (\i t -> typeOnly (show i) t) args) *> run) s 

rt  :: forall s. StateLambda s -> s -> Array (Tuple Type NativeExpr) -> NativeContext -> Either Errors NativeExpr
rt sl s args ctx = 
  let applyRT fa app = 
          let nativeExpr {result,frt} = 
               let mkExpr s ctx = do
                    let mkArg l = let (Tuple t nee) = view (cloneLens l) s in Tuple t <$> nee s ctx 
                    argLTypes <- traverse mkArg app.args 
                    frt argLTypes ctx
               in maybe' (\_ -> Tuple result mkExpr) (constExpr result) (ctx.const result) 
        in fa *> (Just <$> applyIt nativeExpr app) 
      run = foldl applyRT (pure Nothing) sl.apps
      convertResult (Tuple (Just (Tuple _ result)) s) = result s ctx 
      convertResult _ = throwError $ Expected "No result from body"
      initialState = set (cloneLens sl.args) (uncurry constExpr <$> args) s
  in convertResult =<< runStateT run (spy initialState) 

complex :: Type 
complex = lambda "complex" [undefInt, undefInt] undefInt (ct body initial) (rt body initial) 
  where 
  _a = ltIx 0
  _b = ltIx 1
  _o = ltIx 2
  _a5 = ltIx 3
  _apa5 = ltIx 4
  _result = ltIx 5

  initial :: LTypeArray 
  initial = LTypeArray $ fromFoldable $ (\i -> typeOnly (show i) unknownT) <$> range 0 5

  body :: StateLambda LTypeArray 
  body = {args : argl [_a, _b], apps: [
    capp "o" mulInt [_b, c $ ctInt 3] _o,
    capp "a5" mulInt [_a, c $ ctInt 5] _a5,
    capp "apa5" addInt [_a, _a5] _apa5,
    capp "result" addInt [_apa5, _o] _result 
  ]}
  
-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- let stateFul :: Type 
  --     stateFul = lambda "State" UnknownT  consts body 

  log $ unsafePartial $ unsafeCoerce $ errorOrFunction complex [unknownT, ctInt 3]
    
-- program(a, b)
-- {
--   let o = b * 3
--   let a5 = a * 5
--   let apa5 = a + a5
--   apa5 + o
--   
-- }