module Main where 

import Prelude hiding (add)

import Control.Alt ((<|>))
import Control.Apply (applySecond)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (ask, lift)
import Control.Monad.State (class MonadState, State, StateT, evalState, evalStateT, execState, execStateT, get, modify, runState, runStateT, state)
import Control.MonadZero (guard)
import Data.Array (catMaybes, foldl, foldr, fromFoldable, mapWithIndex, replicate, unsafeIndex, updateAt, updateAtIndices, zip)
import Data.Bifunctor (bimap, rmap)
import Data.Either (Either(..), either, fromRight)
import Data.FoldableWithIndex (foldlWithIndex, traverseWithIndex_)
import Data.Lens (ALens', Lens', _1, assign, cloneLens, lens', modifying, over, preview, set, use, view)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..))
import Data.List.Lazy (range)
import Data.Maybe (Maybe(..), fromJust, maybe, maybe')
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse, traverse_)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(Tuple), fst, snd, uncurry)
import Debug.Trace (spy, traceAnyA)
import Javascript (JSContext(..), JSExpr(InfixFuncApp), constJS, constOrArg, emptyFunction, exprToString, fromNative, genFunc, jsArg, nativeJS, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors(..), LambdaR, NativeContext, NativeExpr, PrimType(..), Type, TypeT(Lambda), applyLambda, arr, checkArgs, ctInt, ctString, incRef, intValue, lambda, lambdaR, polyLambda, refCount, resultType, strValue, typeT, undefInt, undefPrim, undefString, unknownT)
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
      const = typeToJS >>> map constJS
      local e = nativeJS do 
        expr <- fromNative e
        (JSContext ctx) <- ask
        ctx.newLocal expr 
  in either show mkFunc $ do 
        {frt,args:pargs} <- applyLambda l args >>= lambdaR
        let (Tuple t fb) = runState (traverse constOrArg pargs) emptyFunction
        Tuple fb <$> frt (zip pargs $ constJS <$> t) unknownT {const, local}

al = applyLambda
lr = resultType

larg :: Int -> Type -> Either Errors Type
larg i t = case typeT t of 
  (Lambda {args}) -> arr i args
  _ -> throwError $ Expected "Lambda"

type TypeRef = Int 
type LamState = StateT LambdaState (Either Errors)
type NativeCreate = Type -> NativeContext -> LamState NativeExpr

newtype LambdaState = LambdaState (Array LType)

derive instance lsNT :: Newtype LambdaState _ 

type ArgLens = Array TypeRef

type LType = Tuple Type (Either NativeExpr NativeCreate)

type App = {name :: String, f :: ArgLens -> LamState LType, args :: ArgLens, result :: Maybe TypeRef }

type StateLambda = {args :: ArgLens, apps :: Array App}

-- typeOnly :: forall s. String -> Type -> LType s
-- typeOnly n t = Tuple t \_ _ -> throwError $ Expected $ "A native representation for " <> n 

constExpr :: forall s. Type -> NativeExpr -> LType
constExpr t ne = Tuple t $ Left ne

-- ixUn :: forall s. Int -> ArgLens s -> Lens' s (LType s)
-- ixUn i o = cloneLens o <<< (unsafePartial $ lens' \arr -> Tuple (unsafeIndex arr i) 
--         (\lt -> fromJust $ updateAt i lt arr))

-- ltIx :: forall a. Int -> Lens' LTypeArray (LType LTypeArray)
-- ltIx i = unsafePartial $ lens' \(LTypeArray arr) -> Tuple (unsafeIndex arr i) 
--         (\lt -> LTypeArray $ fromJust $ updateAt i lt arr) 

-- argl :: forall s. Array (ALens' s (LType s)) -> ArgLens s
-- argl la = lens' \s -> Tuple ((\l -> view (cloneLens l) s) <$> la) 
--             (\ta -> foldr doset s (zip la ta))
--   where 
--   doset (Tuple l v) = set (cloneLens l) v

-- cl :: forall s a. Type -> Lens' s (LType s)
-- cl t = lens' \s -> Tuple (c t) (const s)

-- c :: forall s a. Type -> LType s
-- c a = Tuple a (\t ctx -> maybe (throwError $ Expected $ "A constant for" <> show t) pure $ ctx.const t)

capp :: forall s. String -> Type -> ArgLens -> Maybe TypeRef -> App
capp name lam args result = {name, f: runStateless, args, result}
  where 
  runStateless al = do 
    args <- getTypes al
    r <- lift $ applyLambda lam args >>= lambdaR 
    typesOnly al r.args
    pure $ Tuple r.result $ Right \t ctx -> case ctx.const $ spy t of 
      Just c -> pure c
      Nothing -> do 
        argsLTypes <- getLTypes al
        let mkArg (Tuple t mkNative) = Tuple t <$> (mkNative # either pure (\f -> f t ctx))
        stateArgs <- traverse mkArg argsLTypes
        ne <- lift $ r.frt stateArgs t ctx
        traceAnyA {result, rc: refCount t}
        (guard (refCount t > 1) *> result) # maybe (pure ne) \resRef -> 
          let loc = ctx.local ne in setOne (constExpr t loc) resRef *> pure loc

appLocal :: forall s. String -> (ArgLens -> LamState LType) -> ArgLens -> Maybe TypeRef -> App
appLocal name f args result = {name, f , args, result}


applyIt :: forall s. String -> App -> LamState LType
applyIt phase ap = do 
  lt <- ap.f ap.args
  maybe (pure unit) (modifyOne $ const lt) ap.result 
  news <- get 
  let _ = spy {phase, name: ap.name, news} 
  pure $ lt

runCT :: Array App -> LamState LType
runCT apps = do 
  let applyCT app = Just <$> applyIt "ct" app
      run = foldl (\a b -> a *> applyCT b) (pure Nothing) apps
  run >>= maybe (throwError $ Expected "") pure

typeArr :: Int -> LambdaState
typeArr len = LambdaState $ replicate len (Tuple unknownT $ Right \_ _ -> throwError $ NoNative)

constants :: ArgLens -> Array Type -> LambdaState -> LambdaState 
constants al t = execState $ traverse_ mkConstant $ zip al t
  where mkConstant (Tuple i t) = modifyOne (\_ -> Tuple t $ Right mkNativeConst) i 
        mkNativeConst t ctx = maybe (throwError NoNative) pure $ ctx.const t

aix :: Int -> ArgLens -> TypeRef
aix i arr = unsafePartial $ unsafeIndex arr i 

setOne :: LType -> TypeRef -> LamState Unit 
setOne = const >>> modifyOne 

modifyOne :: forall m. MonadState LambdaState m => (LType -> LType) -> TypeRef -> m Unit 
modifyOne f i = modifying (_Newtype <<< ix i) f

typesOnly :: ArgLens -> Array Type -> LamState Unit
typesOnly al types = traverse_ (\(Tuple i t) -> modifyOne (bimap (const t) id) i) $ zip al types 

getLType :: TypeRef -> LamState LType 
getLType i = get <#> \(LambdaState t) -> unsafePartial $ unsafeIndex t i

getLTypes :: ArgLens -> LamState (Array LType)
getLTypes = traverse getLType

getTypes :: ArgLens -> LamState (Array Type)
getTypes a = map fst <$> getLTypes a

ct :: StateLambda -> Array Type -> LamState {args:: Array Type, result :: Type}
ct sl args = do 
  typesOnly sl.args args
  result <- fst <$> runCT sl.apps 
  newargs <- getTypes sl.args
  pure {args: newargs , result}

ctt :: LambdaState -> StateLambda -> Array Type -> Either Errors {args:: Array Type, result :: Type}
ctt initial lam args = evalStateT (ct lam args) initial

rt :: LambdaState -> StateLambda -> Array (Tuple Type NativeExpr) -> Type -> NativeContext -> Either Errors NativeExpr
rt initial lam nargs t ctx = initial # evalStateT do 
  traverseWithIndex_ (\i t -> setOne (bimap id Left t) i) nargs
  (Tuple _ ne) <- runCT lam.apps
  s <- get
  either pure (\nc -> lift $ evalStateT (nc t ctx) s) ne 
  
aba :: Type 
aba = lambda "aba" [unknownT, unknownT] unknownT (ctt initial body) (rt initial body)
  where 
  _a = 0
  _b = 1
  _ab = 2
  _result = 3
  body :: StateLambda 
  body = {args : [_a, _b], apps: [
    capp "ab" add [_a, _b] $ pure _ab,
    capp "aba" add [_ab, _a] $ Nothing
  ]}
  initial = typeArr 4

-- complex(a, b)
-- {
--   let o = b * 3
--   let a5 = a * 5
--   let apa5 = a + a5
--   apa5 + o
--   
-- }

complex :: Type 
complex = lambda "complex" [undefInt, undefInt] undefInt (ctt initial body) (rt initial body) 
  where 
  _a = 0
  _b = 1
  _o = 2
  _a5 = 3
  _apa5 = 4
  _result = 5
  _o_2 = 6
  _a5_2 = 7

  initial = constants [_o_2, _a5_2] [ctInt 3, ctInt 5] $ typeArr 8

  body :: StateLambda 
  body = {args : [_a, _b], apps: [
    capp "o" mulInt [_b, _o_2] $ pure _o,
    capp "a5" mulInt [_a, _a5_2] $ pure _a5,
    capp "apa5" add [_a, _a5] $ pure _apa5,
    capp "result" add [_apa5, _o] Nothing
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
innerLambda = lambda "innerLambda" [undefInt, undefInt] undefInt (ctt initial body) (rt initial body) 
  where 
  _a = 0
  _b = 1
  _o = 2
  _ca = 3
  _cb = 4
  _cacb = 5
  _car = 6
  _cbr = 7
  _c1_c = 8 
  _o_a2 = 9

  initial = constants [_c1_c, _o_a2] [ctInt 5, ctInt 3] $ typeArr 10

  lamC :: TypeRef -> ArgLens -> LamState LType
  lamC l args = do 
    result <- runCT apps
    pure result
    where apps = [
      capp "c1" mulInt [aix 0 args, _c1_c] $ pure l, 
      capp "cresult" add [l, _o] Nothing
    ]

  body :: StateLambda
  body = {args : [_a, _b], apps: [
    capp "o" mulInt [_b, _o_a2] $ pure _o,    
    appLocal "a5" (lamC _car) [_a] $ pure _ca,
    appLocal "cb" (lamC _cbr) [_b] $ pure _cb,
    capp "cacb" add [_ca, _cb] $ pure _cacb,
    capp "result" add [_cacb, _o] $ Nothing
  ]}

-- Have to make it combine the 
main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  -- let stateFul :: Type 
  --     stateFul = lambda "State" UnknownT  consts body 

  log $ errorOrFunction innerLambda [undefInt, unknownT]
  -- log $ show $ al aba [unknownT, ctString "sda"]
  -- log $ errorOrFunction complex [unknownT, ctString "120"]
    

