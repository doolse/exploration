module Main where

import Javascript
import Prelude

import Control.Alt ((<|>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, infoShow, log)
import Control.Monad.Except (ExceptT(..), except, lift, runExcept, runExceptT, throwError)
import Control.Monad.Reader (ask)
import Control.Monad.State (State, evalState, get, gets, modify, put, runState, runStateT, state)
import Data.Array (find, findIndex, findMap, foldr, last, length, mapWithIndex, modifyAt, range, snoc, unsafeIndex, updateAt, zip)
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either)
import Data.FoldableWithIndex (findWithIndex)
import Data.Lens (ALens', Getter', Lens', _1, _2, assign, cloneLens, lens, lens', modifying, over, set, to, traversed, use, view, viewOn, (.~), (^.))
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), fromJust, fromMaybe, isJust, isNothing, maybe)
import Data.Profunctor (dimap)
import Data.StrMap (fromFoldable, lookup)
import Data.String (joinWith)
import Data.Symbol (SProxy(..))
import Data.Traversable (mapAccumR, sequence, sequence_, traverse)
import Data.Tuple (Tuple(..), fst, snd)
import Debug.Trace (spy)
import Partial.Unsafe (unsafePartial)
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String

type ArgType = Tuple (Maybe String) Type

type RawArgs = {args::Array ArgType, return :: Type}
type FuncArgs s = { args :: Array (ALens' s ArgType), return::ALens' s Type}
type ApplyArg c = { arg :: ArgType, expr :: State c JSExpr }

type ErrState s = ExceptT Errors (State s)
newtype ApplyRT = ApplyRT (forall c. Array (ApplyArg c) -> ErrState c JSExpr)
type CTFunction a = (forall s. FuncArgs s -> ErrState s a)
data VerArgs s = VerArgs (String -> ALens' s Type) (ALens' s Type)  
type VerFunction s a = VerArgs s -> ErrState s a

data Type = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | CTLambda String (CTFunction Type)
  | RTLambda Type Type ApplyRT

instance showType :: Show Type where 
  show (UnknownT) = "Unknown Type"
  show (IntT i) = "IntT:" <> show i
  show (StringT s) = "StringT:" <> show s
  show (CTLambda n _) = "Compile time lambda for " <> n
  show (RTLambda _ _ _) = "Runtime generatable lambda"

ctConstant :: Type -> Maybe JSExpr
ctConstant (IntT (Just i)) = Just $ JSInt i
ctConstant (StringT (Just v)) = Just $ JSString v
ctConstant (RTLambda _ res _) = ctConstant res
ctConstant _ = Nothing

namedField :: String -> Type -> ArgType 
namedField n = Tuple (Just n)

typeForArg :: ArgType -> Type 
typeForArg = snd

lt = Tuple 
unkInt = IntT Nothing

unkString = StringT Nothing 

knownString s = StringT $ Just s

known i = IntT $ Just i

runApplyRT (ApplyRT f) = f

ctLambda :: forall s. String -> (FuncArgs s -> ErrState s Type) -> Type
ctLambda name f = CTLambda name (unsafeCoerce f)

_args = prop (SProxy :: SProxy "args")
_return = prop (SProxy :: SProxy "return")

nextUnsafeIx :: forall a. Array a -> Lens' (Array a) a
nextUnsafeIx arr = unsafeIx (length arr)

unsafeIx :: forall a. Int -> Lens' (Array a) a
unsafeIx i = lens (unsafePartial $ flip unsafeIndex i) (\s u -> unsafePartial $ fromJust $ updateAt i u s)

asFuncArgs :: RawArgs -> FuncArgs RawArgs
asFuncArgs {args} = let arglen = length args 
  in {args: (\i -> unsafeIx i >>> _args) <$> (range 0 $ arglen - 1), return: _return}

runFunc :: forall a. CTFunction a -> RawArgs -> Either Errors (Tuple a RawArgs)
runFunc f raw = 
  let (Tuple e fa) = runState (runExceptT $ f (asFuncArgs raw)) raw 
  in either Left (Right <<< flip Tuple fa) e

applyCT :: Type -> CTFunction Type
applyCT (CTLambda _ f) = f
applyCT (RTLambda t _ _) = applyCT t
applyCT t = \_ -> throwError (Expected $ "To apply a lambda but was actually: " <> show t)

unify :: Type -> Type -> Either Errors Type 
unify (IntT _) UnknownT = Right $ IntT Nothing
unify (IntT _) b@(IntT _) = Right b
unify (StringT _) UnknownT = Right $ StringT Nothing
unify (StringT _) b@(StringT _) = Right $ b
unify (IntT _) o = Left $ Expected "Int"
unify (StringT _) o = Left $ Expected "String"
unify _ _ = Left $ Expected "Types that could unify"

unified :: forall s. Type -> ALens' s Type -> ExceptT Errors (State s) Type
unified t1 rt = do 
  t2 <- use (cloneLens rt)
  either throwError updated $ unify t1 t2
  where 
  updated t = modify (set (cloneLens rt) t) $> t

maybeNamedArg :: String -> ArgType -> Maybe Type
maybeNamedArg n (Tuple (Just fn) t) | fn == n = Just t
maybeNamedArg _ _ = Nothing

withName :: String -> ArgType -> Boolean
withName n = maybeNamedArg n >>> isJust

nameIndex :: String -> Array ArgType -> Maybe Int 
nameIndex = findIndex <<< withName

useArg :: forall s a. ALens' s a -> ErrState s a
useArg l = use $ cloneLens l

mulInt :: Type 
mulInt = ctLambda "*" $ fromPosArgs ["a", "b"] \(VerArgs _arg return) -> do
  let _a = _arg "a"
  let _b = _arg "b"
  at <- unified unkInt _a
  bt <- unified at _b  
  let result = case {at,bt} of 
        {at: (IntT (Just a)), bt:(IntT (Just b))} -> IntT (Just $ a * b)
        _ -> IntT Nothing
  assign (cloneLens return) result
  pure $ RTLambda mulInt result $ ApplyRT case _ of 
        [a,b] -> do 
          ae <- lift $ a.expr
          be <- lift $ b.expr
          pure $ InfixFuncApp " * " ae be
        _ -> throwError $ Expected "2 args" 

getRTAdd :: forall s. Type -> VerFunction s (Maybe {result::Type, rt::ApplyRT})
getRTAdd (IntT _) = \(VerArgs _arg return) -> do
  at <- useArg $ _arg "a"
  bt <- unified at (_arg "b")
  let result = case {at,bt} of 
        {at:(IntT (Just a)), bt:(IntT (Just b))} -> IntT (Just $ a + b)
        _ -> IntT Nothing
      rt = ApplyRT case _ of 
        [a,b] -> do 
          ae <- lift $ a.expr
          be <- lift $ b.expr
          pure $ InfixFuncApp " + " ae be
        _ -> throwError $ Expected "2 args" 
  pure $ Just {result, rt}
  
getRTAdd (StringT _) = \(VerArgs _arg return) -> do 
  at <- useArg $ _arg "a"
  bt <- unified at (_arg "b")
  let result = case {at,bt} of 
        {at: (StringT (Just a)), bt:(StringT (Just b))} -> StringT (Just $ a <> b)
        _ -> StringT Nothing
      rt = ApplyRT case _ of 
        [a,b] -> do 
          ae <- lift $ a.expr
          be <- lift $ b.expr
          pure $ InfixFuncApp " + " ae be
        _ -> throwError $ Expected "2 args" 
  pure $ Just {result, rt}

getRTAdd _ = \_ -> pure $ Nothing

-- I think this should return a CTLambda which re-uses the current state if it fails to produce a RTLambda
fromPosArgs :: forall s a. Array String -> VerFunction s a -> FuncArgs s -> ErrState s a
fromPosArgs names f = \{args, return} -> do 
  s <- get
  let ifPos allowPos (Tuple ifNone l) = case view (cloneLens l) s of 
        (Tuple Nothing _) -> 
          if allowPos 
          then {accum:true, value: Right $ Tuple ifNone l}
          else {accum:false, value: Left $ PositionalFirst "Positional args only allowed at start"}
        (Tuple (Just name) _) -> {accum:false, value: Right $ Tuple name l}

  let checkedArgs = sequence (mapAccumR ifPos true (zip names args)).value
  argMap <- either throwError (pure <<< fromFoldable) checkedArgs
  let mkLens str = typeOnly $ (unsafePartial $ fromJust $ lookup str argMap)
  f (VerArgs mkLens (cloneLens return))
  
  -- -- either throwError pure $ 
  -- -- {args} <- get
  -- -- maybe (pure unit) (throwError <<< MissingArg) $ find (flip nameIndex args >>> isNothing) names

  -- where 

-- addInt :: forall a. {a: a, b:a} -> a
addAny :: Type
addAny = ctLambda "addAny" $ fromPosArgs ["a", "b"] \va@(VerArgs _arg return) -> do     
    at <- useArg $ _arg "a"
    rtApply <- getRTAdd at va
    rtApply # maybe (pure addAny) (\{result, rt} -> do
      assign (cloneLens return) $ result
      pure $ RTLambda addAny result rt)

typeOnly :: forall s. ALens' s ArgType -> Lens' s Type 
typeOnly al = let l = cloneLens al in lens' \s -> 
  let arg = s ^. l
  in Tuple (snd arg) \nt -> set l (Tuple (fst arg) nt) s

argLens :: forall s. Lens' s (Maybe String) -> Lens' s Type -> Lens' s ArgType
argLens nl tl = lens' \s -> 
  let setter (Tuple name t) = (set nl name >>> set tl t) s
  in Tuple (Tuple (s ^. nl) (s ^. tl)) setter
  
type LocalStorage = { names :: Array (Maybe String), locals :: Array Type }

type Locals s a = State (Tuple s LocalStorage) a
type LocalLens s a = ALens' (Tuple s LocalStorage) a
type LocalStorageLens s a = Locals s (LocalLens s a)

_names = prop (SProxy :: SProxy "names")
_locals = prop (SProxy :: SProxy "locals")

newLocalType :: forall s. Type -> LocalStorageLens s Type 
newLocalType t = do
  {locals} <- gets snd
  let l = _2 <<< (_locals <<< nextUnsafeIx locals)
  modify $ over (_2 <<< _locals) (flip snoc t)
  pure l

positionalLocal :: forall s. LocalLens s Type -> LocalStorageLens s ArgType
positionalLocal lt = do 
  {names} <- gets snd
  let argl = argLens (_2 <<< _names <<< nextUnsafeIx names) (cloneLens lt)
  modify $ over (_2 <<< _names) (flip snoc Nothing)
  pure argl


constPos :: forall s. Type -> LocalStorageLens s ArgType
constPos t = do 
  {names, locals} <- gets snd
  let l = _2 <<< argLens (_names <<< nextUnsafeIx names) (_locals <<< nextUnsafeIx locals)
  modify $ set _2 {names: snoc names Nothing, locals: snoc locals t}
  pure l  

refType :: forall s. ALens' s Type -> LocalStorageLens s Type
refType l = pure $ _1 <<< l

refPositional :: forall s. ALens' s Type -> LocalStorageLens s ArgType 
refPositional lt = do 
  {names} <- gets snd
  let argl = argLens (_2 <<< _names <<< nextUnsafeIx names) (_1 <<< (cloneLens lt))
  modify $ over (_2 <<< _names) (flip snoc Nothing)
  pure argl

applyLocal' :: forall s. Type -> Array (LocalStorageLens s ArgType) -> LocalStorageLens s Type -> Locals s (ErrState s Type)
applyLocal' t args return = do 
  a <- sequence args
  r <- return 
  applyLocal t a r

applyLocal :: forall s. Type -> Array (LocalLens s ArgType) -> LocalLens s Type -> Locals s (ErrState s Type)
applyLocal t args return = 
  except <$> (runExceptT $ applyCT t {args, return})

runLocals :: forall s a. Locals s (ErrState s a) -> ErrState s a 
runLocals ls = do 
  s <- get
  evalState ls (Tuple s {names:[], locals:[]})

add2 :: Type 
add2 = ctLambda "add2" $ fromPosArgs ["a"] \(VerArgs _arg return) -> do     
    let _a = _arg "a"
    a1 <- unified unkInt _a
    let body = applyLocal' addAny [refPositional _a, constPos $ known 2] (refType return)
    runLocals body

newParam :: forall r. State {params::Array String|r} JSExpr
newParam = state npf 
  where 
  npf jsf@{params} = 
    let paramName = "p" <> show (length params)         
    in Tuple (Local paramName) (jsf {params = params <> [paramName]})

constantOrParam :: forall r. ArgType -> State {params::Array String|r} JSExpr
constantOrParam a = maybe newParam pure (ctConstant $ typeForArg a)

expressionOrFunc :: Tuple Type RawArgs -> Either Errors JSExpr
expressionOrFunc (Tuple _ {return}) | Just e <- ctConstant return = Right e
expressionOrFunc (Tuple r _) | Just e <- ctConstant r = Right e
expressionOrFunc (Tuple (RTLambda _ _ f) {args}) = 
  let appliedRT = runExceptT $ do 
        expr <- runApplyRT f $ (\arg -> {arg, expr:constantOrParam arg}) <$> args
        gets (_ {stmts = [Return expr]})
  in AnonymousFunc <$> evalState appliedRT {params:[],stmts:[]}
expressionOrFunc (Tuple t _) = Left $ (Expected $ "Lambda but was: " <> show t)

-- test(a, b) = 
--  let o = mul(a, b)
--  in add(o, 5)
-- test a b = a * b  

lastOne :: forall s. Array Type -> ErrState s Type 
lastOne t = maybe (throwError $ Expected "Some result type") pure $ last t

runLast f = runLocals (map sequence f) >>= lastOne

testIt :: Type 
testIt = ctLambda "testIt" $ fromPosArgs ["a", "b"] \(VerArgs _arg return) -> do     
    let _a = _arg "a"
        _b = _arg "b"
    a1 <- unified unkInt _a
    let body = do 
          o <- newLocalType (UnknownT)
          ret <- newLocalType (UnknownT)
          sequence [ 
            applyLocal' mulInt [refPositional _a, refPositional _b] (pure o), 
            applyLocal' addAny [positionalLocal o, constPos $ known 13] (pure ret) 
          ]
    runLast body


main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log $ unsafeCoerce $ do 
    ft <- runFunc (applyCT testIt) {args: [Tuple Nothing $ known 12, Tuple Nothing $ unkInt], return: UnknownT}
    pure $ exprToString <$> expressionOrFunc ft

