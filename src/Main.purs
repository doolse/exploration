module Main where 

import Prelude hiding (add)

import Control.Alt ((<|>))
import Control.Apply (applySecond)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (lift)
import Control.Monad.State (State, StateT, evalStateT, execStateT, get, modify, runState, runStateT, state)
import Data.Array (foldl, foldr, fromFoldable, mapWithIndex, unsafeIndex, updateAt, zip)
import Data.Bifunctor (bimap, rmap)
import Data.Either (Either, either)
import Data.Lens (ALens', Lens', _1, assign, cloneLens, lens', set, use, view)
import Data.List.Lazy (range)
import Data.Maybe (Maybe(..), fromJust, maybe, maybe')
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple(Tuple), fst, snd, uncurry)
import Debug.Trace (spy, traceAnyA)
import Javascript (JSExpr(InfixFuncApp), constJS, constOrArg, emptyFunction, exprToString, fromNative, genFunc, jsArg, nativeJS, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors(Expected), LambdaR, NativeContext, NativeExpr, PrimType(..), Type, TypeT(Lambda), applyLambda, arr, ctInt, ctString, incRef, intValue, lambda, lambdaR, polyLambda, resultType, strValue, typeT, undefInt, undefPrim, undefString, unknownT)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT args toNE out = pure $ nativeJS do 
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

addString :: Type 
addString = lambda "+" [undefString, undefString] undefString doAddStr doAddStrRT 
  where 
  doAddStr args  = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case {a,b} of 
          {a, b} | {a: Just ia, b:Just ib} <- {a: strValue a, b:strValue b} -> ctString (ia <> ib)
          _ -> undefString
    pure $ {args:[a,b], result}

  doAddStrRT args toNE out = pure $ nativeJS do
    a <- jsArg args 0
    b <- jsArg args 1 
    pure $ InfixFuncApp " + " a b
  
add :: Type 
add = polyLambda "+" [unknownT, unknownT] unknownT [addInt, addString]

addInt :: Type
addInt = lambda "+" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT args toNE out = pure $ nativeJS do
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
        Tuple fb <$> frt (zip pargs $ constJS <$> t) unknownT {const: typeToJS >>> map constJS}

al = applyLambda
lr = resultType

larg :: Int -> Type -> Either Errors Type
larg i t = case typeT t of 
  (Lambda {args}) -> arr i args
  _ -> throwError $ Expected "Lambda"

newtype LTypeArray = LTypeArray (Array (LType LTypeArray))

type LTypeLens s = ALens' s (LType s)
type LensArray s = Array (LTypeLens s)
type ArgLens s = ALens' s (Array (LType s))

type LType s = Tuple Type (s -> Type -> NativeContext -> Either Errors NativeExpr)

type App s = {name :: String, f :: ArgLens s -> StateT s (Either Errors) LambdaR, args :: ArgLens s, result :: LType s -> s -> s }

type StateLambda s = {args :: ArgLens s, apps :: Array (App s)}

typeOnly :: forall s. String -> Type -> LType s
typeOnly n t = Tuple t \_ _ _ -> throwError $ Expected $ "A native representation for " <> n 

constExpr :: forall s. Type -> NativeExpr -> LType s 
constExpr t ne = Tuple t (\_ _ _ -> pure ne)

ixUn :: forall s. Int -> ArgLens s -> Lens' s (LType s)
ixUn i o = cloneLens o <<< (unsafePartial $ lens' \arr -> Tuple (unsafeIndex arr i) 
        (\lt -> fromJust $ updateAt i lt arr))

ltIx :: forall a. Int -> Lens' LTypeArray (LType LTypeArray)
ltIx i = unsafePartial $ lens' \(LTypeArray arr) -> Tuple (unsafeIndex arr i) 
        (\lt -> LTypeArray $ fromJust $ updateAt i lt arr) 

argl :: forall s. Array (ALens' s (LType s)) -> ArgLens s
argl la = lens' \s -> Tuple ((\l -> view (cloneLens l) s) <$> la) 
            (\ta -> foldr doset s (zip la ta))
  where 
  doset (Tuple l v) = set (cloneLens l) v

cl :: forall s a. Type -> Lens' s (LType s)
cl t = lens' \s -> Tuple (c t) (const s)

c :: forall s a. Type -> LType s
c a = Tuple a (\_ t ctx -> maybe (throwError $ Expected $ "A constant for" <> show t) pure $ ctx.const t)

capp :: forall s. String -> Type -> Array (ALens' s (LType s)) -> (LType s -> s -> s) -> App s
capp name lam args result = {name, f: runStateless, args: argl args, result}
  where 
  runStateless al = do 
    let argsLens = cloneLens al
    args <- use argsLens 
    r <- lift $ applyLambda lam (fst <$> args) >>= lambdaR 
    assign argsLens (zip r.args (snd <$> args))
    pure $ r


appLocal :: forall s. String -> (ArgLens s -> StateT s (Either Errors) LambdaR) -> Array (ALens' s (LType s)) -> (LType s -> s -> s) -> App s
appLocal name f args result = {name, f , args: argl args, result}


applyIt :: forall s. String -> (LambdaR -> LType s) -> App s -> StateT s (Either Errors) (LType s)
applyIt phase f ap = do 
  r <- ap.f ap.args
  -- let (Tuple lam _) = ap.f s ap.args
  -- args <- use argsLens
  -- r <- lift $ applyLambda lam (fst <$> args) >>= lambdaR 
  -- 
  -- assign argsLens (zip r.args (snd <$> args))
  let lt = f r
  modify $ ap.result lt
  news <- get 
  let _ = spy {phase, name: ap.name, news} 
  pure $ lt

ct :: forall s. StateLambda s -> Array Type -> StateT s (Either Errors) {args:: Array Type, result :: Type}
ct sl args = do 
  let applyCT app = Just <<< fst <$> applyIt "ct" (_.result >>> typeOnly app.name) app
      run = foldl (\a b -> a *> applyCT b) (pure Nothing) sl.apps
      -- convertResult (Tuple (Just result) s) = 
      -- convertResult a = throwError $ Expected "No result from body"
  assign (cloneLens sl.args) (mapWithIndex (\i t -> typeOnly (show i) t) args)
  result <- run >>= maybe (throwError $ Expected "") pure
  s <- get
  pure {args: fst <$> view (cloneLens sl.args) s, result}

 

rt  :: forall s. StateLambda s -> s -> Array (Tuple Type NativeExpr) -> Type -> NativeContext -> Either Errors NativeExpr
rt sl is args resultType ctx = 
  let applyRT app = 
        let nativeExpr {result,frt} = 
              let mkExpr s resultType ctx = do 
                    let mkArg (Tuple t mkNative) = Tuple t <$> mkNative s t ctx
                    stateArgs <- traverse mkArg $ view (cloneLens app.args) s
                    frt stateArgs resultType ctx
              in Tuple result mkExpr
        in Just <$> applyIt "rt" nativeExpr app
      run = foldl (\a b -> a *> applyRT b) (pure Nothing) sl.apps
      convertResult (Tuple (Just (Tuple _ result)) s) = result s resultType ctx
      convertResult _ = throwError $ Expected "No result from body"
      initialState = set (cloneLens sl.args) (uncurry constExpr <$> args) is
  in convertResult =<< runStateT run initialState

aba :: Type 
aba = lambda "aba" [unknownT, unknownT] unknownT (ct body initial) (rt body initial)
  where 
  _a = ltIx 0
  _b = ltIx 1
  _ab = ltIx 2
  _result = ltIx 3
  body :: StateLambda LTypeArray 
  body = {args : argl [_a, _b], apps: [
    capp "ab" add [_a, _b] $ set _ab,
    capp "aba" add [_ab, _a] $ const id
  ]}
  initial = typeArr 4

typeArr len = LTypeArray $ fromFoldable $ (\i -> typeOnly (show i) unknownT) <$> range 0 (len - 1)

-- complex(a, b)
-- {
--   let o = b * 3
--   let a5 = a * 5
--   let apa5 = a + a5
--   apa5 + o
--   
-- }

ctt :: forall s. s -> StateLambda s -> Array Type -> Either Errors {args:: Array Type, result :: Type}
ctt initial lam args = evalStateT (ct lam args) initial

complex :: Type 
complex = lambda "complex" [undefInt, undefInt] undefInt (ctt initial body) (rt body initial) 
  where 
  _a = ltIx 0
  _b = ltIx 1
  _o = ltIx 2
  _a5 = ltIx 3
  _apa5 = ltIx 4
  _result = ltIx 5

  initial = typeArr 6

  body :: StateLambda LTypeArray 
  body = {args : argl [_a, _b], apps: [
    capp "o" mulInt [_b, cl $ ctInt 3] $ set _o,
    capp "a5" mulInt [_a, cl $ ctInt 5] $ set _a5,
    capp "apa5" add [_a, _a5] $ set _apa5,
    capp "result" add [_apa5, _o] $ const id
  ]}

-- innerLambda(a, b)
-- {
--   let o = b * 3
--   let c d = d * 5 + o
--   let ca = c a
--   let cb = c b
--   let cacb = ca + cb
--   cacb + o   
-- }  
innerLambda :: Type 
innerLambda = lambda "innerLambda" [undefInt, undefInt] undefInt (ct body initial) (rt body initial) 
  where 
  _a = ltIx 0
  _b = ltIx 1
  _o = ltIx 2
  _ca = ltIx 3
  _cb = ltIx 4
  _cacb = ltIx 5
  _car = ltIx 6
  _cbr = ltIx 7

  initial = typeArr 8

  lamC :: Lens' LTypeArray (LType LTypeArray) -> StateT LTypeArray   -> ArgLens LTypeArray -> LType LTypeArray
  lamC l s args = c $ lambda "innerLambda" [undefInt] undefInt (ct {args, apps} s) (rt {args, apps} s)
    where apps = [
      capp "c1" mulInt [ixUn 0 args, cl $ ctInt 5] $ set l, 
      capp "cresult" add [l, _o] $ const id
    ]

  body :: StateLambda LTypeArray 
  body = {args : argl [_a, _b], apps: [
    capp "o" mulInt [_b, cl $ ctInt 3] $ set _o,    
    appLocal "a5" (lamC _car) [_a] $ set _ca,
    appLocal "cb" (lamC _cbr) [_b] $ set _cb,
    capp "cacb" add [_ca, _cb] $ set _cacb,
    capp "result" add [_cacb, _o] $ const id
  ]}

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- let stateFul :: Type 
  --     stateFul = lambda "State" UnknownT  consts body 

  log $ errorOrFunction innerLambda [undefInt, undefInt]
  -- log $ show $ al aba [unknownT, ctString "sda"]
  -- log $ errorOrFunction complex [unknownT, ctString "120"]
    

