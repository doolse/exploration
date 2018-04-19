module Main where 

import Prelude hiding (add)

import Control.Alt ((<|>))
import Control.Apply (applySecond)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (ask, lift)
import Control.Monad.State (class MonadState, State, StateT, evalState, evalStateT, execState, execStateT, get, modify, runState, runStateT, state)
import Control.Monad.Writer (runWriterT)
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
import Data.Monoid (mempty)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Traversable (sequence, traverse, traverse_)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(Tuple), fst, snd, uncurry)
import Debug.Trace (spy, traceAnyA)
import Javascript (JS, JSExpr(..), anonFunc, constOrArg, emptyFunction, exprToString, fromNative, genFunc, jsArg, nativeJS, newLocal, typeToJS)
import Partial.Unsafe (unsafePartial)
import Types (Errors(..), LambdaR, NativeContext, NativeExpr, NativeGenerator(..), PrimType(..), Type, TypeT(Lambda), applyLambda, arr, checkArgs, ctInt, ctString, incRef, intValue, lambda, lambdaR, polyLambda, refCount, resultType, strValue, typeT, undefInt, undefPrim, undefString, unknownT)
import Unsafe.Coerce (unsafeCoerce)


mulInt :: Type
mulInt = lambda "*" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT = NativeGenerator \args toNE out -> do 
    let a = jsArg args 0
        b = jsArg args 1 
    pure $ nativeJS $ InfixFuncApp " * " a b

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
  doAddStr args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case {a,b} of 
          {a, b} | {a: Just ia, b:Just ib} <- {a: strValue a, b:strValue b} -> ctString (ia <> ib)
          _ -> undefString
    pure $ {args:[a,b], result}

  doAddStrRT = NativeGenerator \args toNE out -> do
    let a = jsArg args 0
        b = jsArg args 1 
    pure $ nativeJS $ InfixFuncApp " + " a b
  
add :: Type 
add = polyLambda "+" [unknownT, unknownT] unknownT [addInt, addString]

addInt :: Type
addInt = lambda "+" [undefInt, undefInt] undefInt doMult doRT
  where 
  doRT = NativeGenerator \args toNE out -> do
    let a = jsArg args 0
        b = jsArg args 1 
    pure $ nativeJS $ InfixFuncApp " + " a b

  doMult args = do 
    a <- incRef <$> arr 0 args
    b <- incRef <$> arr 1 args 
    let result = case {a,b} of 
          {a, b} | {a: Just ia, b:Just ib} <- {a: intValue a, b:intValue b} -> ctInt (ia + ib)
          _ -> undefInt
    pure $ {args:[a,b], result}

type FuncState = { o :: Type }

errorOrFunction :: Type -> Array Type -> String 
errorOrFunction l args = either show id do
  {frt: NativeGenerator f, args:aargs} <- applyLambda l args >>= lambdaR
  let const = map nativeJS <$> typeToJS
      local e = map nativeJS <$> (newLocal (fromNative <$> e))
      natArg t = nativeJS >>> Tuple t <$> constOrArg t
      funcBody = do 
        nargs <- traverse natArg aargs
        f nargs unknownT {const,local}
  let (Tuple errorOrlast fb) = emptyFunction # runState (runExceptT funcBody)
  last <- errorOrlast
  pure $ exprToString $ anonFunc fb (fromNative last)

al = applyLambda
lr = resultType

larg :: Int -> Type -> Either Errors Type
larg i t = case typeT t of 
  (Lambda {args}) -> arr i args
  _ -> throwError $ Expected "Lambda"

type TypeRef = Int 
type LamState = StateT LambdaState (Either Errors)
newtype NativeCreate = NativeCreate (forall m. MonadThrow Errors m => Type -> NativeContext m -> NativeCreate -> 
  LamState (m (Tuple NativeCreate NativeExpr)))

newtype LambdaState = LambdaState (Array LType)

derive instance lsNT :: Newtype LambdaState _ 

type ArgLens = Array TypeRef

type LType = Tuple Type NativeCreate

noNative :: Type -> LType 
noNative t = Tuple t (NativeCreate \_ _ c -> throwError $ NoNative)

constNative :: NativeExpr -> NativeCreate 
constNative ne = NativeCreate \_ _ c -> pure $ pure (Tuple c ne)

withNative :: Type -> NativeExpr -> LType 
withNative t ne = Tuple t $ constNative ne

constOrError :: Type -> LType 
constOrError t = Tuple t (NativeCreate \t ctx c -> pure $ maybe (throwError NoNative) (Tuple c >>> pure) $ ctx.const t)

type App = {name :: String, f :: ArgLens -> LamState LType, args :: ArgLens, result :: Maybe TypeRef }

type StateLambda = {args :: ArgLens, apps :: Array App}

-- convertToM :: forall m. MonadThrow Errors m => NativeContext m -> Array LType -> m (LamState (Array (Tuple Type NativeExpr)))
-- convertToM ctx args = sequence <$> traverse mkNative args
--   where 
--   mkNative :: LType -> m (LamState (Tuple Type NativeExpr))
--   mkNative (Tuple t (NativeCreate nc)) = map (Tuple t) <$> nc t ctx



capp :: forall s. String -> Type -> ArgLens -> Maybe TypeRef -> App
capp name lam args result = {name, f: runStateless, args, result}
  where 
  runStateless al = do 
    args <- getTypes al
    r <- lift $ applyLambda lam args >>= lambdaR 
    typesOnly al r.args
    pure $ Tuple r.result $ NativeCreate \t ctx c -> 
      let inlineCall = do
            let (NativeGenerator genRuntime) = r.frt
                creators (Tuple t nc@(NativeCreate f)) = Tuple t <$> f t ctx nc
            args <- traverse (getLType >=> creators) al
            {expr, changes} <- pure $ do 
              let toNative (Tuple t mne) = Tuple t <$> mne
              actualArgs <- traverse toNative args
              expr <- genRuntime (rmap snd <$> actualArgs) t ctx
              pure $ {expr, changes: snd >>> fst <$> actualArgs}
            pure expr
    
      in case t of 
        t | Just ref <- guard (refCount t > 1) *> result -> do 
            expr <- inlineCall
            -- setOne (Tuple t $ NativeCreate \t ctx -> pure $ pure $ unsafeCoerce $ expr) ref
            -- pure $ expr
            pure $ do 
              joined <- ctx.local expr
              now <- joined
              pure $ Tuple (constNative now) now
        t -> map (Tuple c) <$> inlineCall

      -- NativeCreate \t ctx -> case ctx.const $ spy t of 
      -- Just c -> pure $ pure c
      -- Nothing -> do 
      --   traceAnyA {result, rc: refCount t, name}
      --   -- argLTypes <- pure $ traverse getLType al
      --   -- stateArgs <- convertToM ctx argLTypes
      --   let (NativeGenerator genRuntime) = r.frt
      --   let stateSide = do 
      --         argLTypes <- traverse getLType al
      --   map pure $ do  
      --     genRuntime ?o t ctx
      --   -- argLTypes <- lift $ traverse getLType al
      --   -- stateArgs <- convertToM ctx argLTypes
      --   -- let (NativeGenerator genRuntime) = r.frt
      --   -- let exprGen = stateArgs >>= \a -> genRuntime a t ctx
      --   -- (guard (refCount t > 1) *> result) # maybe (pure $ exprGen) \resRef -> do
      --   --   -- let localVar = ctx.local exprGen
      --   --   setOne (Tuple r.result $ NativeCreate \_ _ -> pure $ unsafeCoerce $ exprGen >>= ctx.local ) resRef
      --   --   pure $ unsafeCoerce $ exprGen >>= ctx.local

appLocal :: forall s. String -> (ArgLens -> LamState LType) -> ArgLens -> Maybe TypeRef -> App
appLocal name f args result = {name, f , args, result}


applyIt :: forall s. String -> App -> LamState LType
applyIt phase ap = do 
  lt <- ap.f ap.args
  maybe (pure unit) (modifyOne $ const lt) ap.result 
  news <- get 
  -- let _ = spy {phase, name: ap.name, news} 
  pure $ lt

runCT :: Array App -> LamState LType
runCT apps = do 
  let applyCT app = Just <$> applyIt "ct" app
      run = foldl (\a b -> a *> applyCT b) (pure Nothing) apps
  run >>= maybe (throwError $ Expected "") pure

typeArr :: Int -> LambdaState
typeArr len = LambdaState $ replicate len (noNative unknownT) 

constants :: ArgLens -> Array Type -> LambdaState -> LambdaState 
constants al t = execState $ traverse_ mkConstant $ zip al t
  where mkConstant (Tuple i t) = modifyOne (\_ -> constOrError t) i 

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

rt :: LambdaState -> StateLambda -> NativeGenerator
rt initial lam = NativeGenerator \nargs t ctx -> either throwError id $ initial # evalStateT do
  traverse_ (\(Tuple i (Tuple t ne)) -> setOne (withNative t ne) i) $ zip lam.args nargs -- traverseWithIndex_ (\i (Tuple t ) -> setOne t (NativeCreate \_ _ -> pure i) nargs
  (Tuple t nc@(NativeCreate f)) <- runCT lam.apps
  map snd <$> f t ctx nc
  
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
    

