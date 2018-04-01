module Main where

import Javascript
import Prelude

import Control.Alt ((<|>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, infoShow, log)
import Control.Monad.Except (ExceptT(..), except, lift, runExceptT, throwError)
import Control.Monad.Reader (ask)
import Control.Monad.State (State, evalState, get, gets, modify, put, runState, runStateT, state)
import Data.Array (find, findIndex, findMap, foldr, length, modifyAt, unsafeIndex, updateAt, zip)
import Data.Either (Either(..), either)
import Data.Lens (Getter', Lens', lens', set, to, use)
import Data.Maybe (Maybe(..), fromJust, fromMaybe, isJust, isNothing, maybe)
import Data.String (joinWith)
import Data.Traversable (mapAccumR, sequence, sequence_, traverse)
import Data.Tuple (Tuple(..))
import Debug.Trace (spy)
import Partial.Unsafe (unsafePartial)
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String
data ArgType = Positional Type | Field String Type

type FuncArgs = {args::Array ArgType, return::Type}

type ApplyArg c = { arg :: ArgType, expr :: State c JSExpr }
newtype ApplyRT = ApplyRT (forall c. Array (ApplyArg c) -> ExceptT Errors (State c) JSExpr)

type CTFunction = ExceptT Errors (State FuncArgs)

data Type = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | CTLambda (CTFunction Type)
  | RTLambda Type ApplyRT

instance showType :: Show Type where 
  show (UnknownT) = "Unknown Type"
  show (IntT i) = "IntT:" <> show i
  show (StringT s) = "StringT:" <> show s
  show (CTLambda _) = "Compile time only lambda"
  show (RTLambda _ _) = "Runtime generatable lambda"

ctConstant :: Type -> Maybe JSExpr
ctConstant (IntT (Just i)) = Just $ JSInt i
ctConstant (StringT (Just v)) = Just $ JSString v
ctConstant _ = Nothing

typeForArg :: ArgType -> Type 
typeForArg (Field _ t) = t 
typeForArg (Positional t) = t

lt = Tuple 
unkInt = IntT Nothing

unkString = StringT Nothing 

knownString s = StringT $ Just s

known i = IntT $ Just i

runApplyRT (ApplyRT f) = f

runFunc :: forall a. CTFunction a -> FuncArgs -> Either Errors (Tuple a FuncArgs)
runFunc f args = let (Tuple e fa) = runState (runExceptT f) args in either Left (Right <<< flip Tuple fa) e

applyCT :: Type -> CTFunction Type
applyCT (CTLambda f) = f
applyCT (RTLambda t _) = applyCT t
applyCT t = throwError (Expected $ "Lambda but was: " <> show t)

applyCTWith :: Type -> FuncArgs -> CTFunction Type
applyCTWith t a = put a *> applyCT t

unify :: Type -> Type -> Either Errors Type 
unify (IntT _) UnknownT = Right $ IntT Nothing
unify (IntT _) b@(IntT _) = Right b
unify (StringT _) UnknownT = Right $ StringT Nothing
unify (StringT _) b@(StringT _) = Right $ b
unify (IntT _) o = Left $ Expected "Int"
unify (StringT _) o = Left $ Expected "String"
unify _ _ = Left $ Expected "Types that could unify"

unifyConst = unified <<< (to <<< const) 

unified :: forall s. Getter' s Type -> Lens' s Type -> ExceptT Errors (State s) Type
unified lt rt = do 
  t1 <- use lt
  t2 <- use rt
  either throwError updated $ unify t1 t2
  where 
  updated t = modify (set rt t) $> t

_a = namedArg "a"
_b = namedArg "b"

nameIndex :: String -> Array ArgType -> Maybe Int 
nameIndex n = findIndex withName
  where
  withName (Field fn _) | fn == n = true
  withName _ = false

-- Unsafe unless fromPosArgs has been called
namedArg :: String -> Lens' FuncArgs Type
namedArg n = lens' lenfunc
  where 
  lenfunc s@{args} = 
    let index = unsafePartial $ fromJust $ nameIndex n s.args 
    in Tuple (unsafePartial $ typeForArg $ unsafeIndex args index) (\b -> s 
    {args = unsafePartial $ fromJust $ modifyAt index (\(Field fn _) -> Field fn b) args})


getRTAdd :: Type -> Maybe (CTFunction ApplyRT)
getRTAdd (IntT _) = Just $ do
  at <- use _a
  bt <- unified _a _b
  let 
    result (IntT (Just a)) (IntT (Just b)) = IntT (Just $ a + b)
    result _ _ = IntT Nothing
  modify _ { return = result at bt}
  let frt = ApplyRT case _ of 
        [a,b] -> do 
          ae <- lift $ a.expr
          be <- lift $ b.expr
          pure $ InfixFuncApp " + " ae be
        _ -> throwError $ Expected "2 args" 
  pure frt
getRTAdd (StringT _) = Just $ do 
  at <- use _a
  bt <- unified _a _b
  let 
    result (StringT (Just a)) (StringT (Just b)) = StringT (Just $ a <> b)
    result _ _ = StringT Nothing
  modify _ { return = result at bt}
  let frt = ApplyRT case _ of 
        [a,b] -> do 
          ae <- lift $ a.expr
          be <- lift $ b.expr
          pure $ InfixFuncApp " + " ae be
        _ -> throwError $ Expected "2 args" 
  pure frt

getRTAdd _ = Nothing

fromPosArgs :: Array String -> CTFunction Unit
fromPosArgs names = do 
  {args} <- get
  either throwError (\args -> modify _ {args=args}) $ sequence  (mapAccumR ifPos true (zip names args)).value
  {args} <- get
  maybe (pure unit) (throwError <<< MissingArg) $ find (flip nameIndex args >>> isNothing) names
  where 
  ifPos :: Boolean -> Tuple String ArgType -> {accum::Boolean, value :: Either Errors ArgType}
  ifPos pa (Tuple n (Positional p)) = if pa then 
    {accum:pa, value:Right $ Field n p } else {accum:false, value: Left $ PositionalFirst "Positional args only allowed at start"}
  ifPos _ (Tuple _ a) = {accum:false, value:Right a}

-- addInt :: forall a. {a: a, b:a} -> a
addAny :: Type
addAny = CTLambda do 
    fromPosArgs ["a", "b"]
    at <- use _a
    maybe (pure addAny) (map $ RTLambda addAny) $ getRTAdd at

add2 :: Type 
add2 = CTLambda $ do 
    fromPosArgs ["a"]
    a1 <- unifyConst unkInt _a 
    {return} <- get
    applyCTWith addAny {args:[Positional a1, Positional $ known 2], return}

newParam :: forall r. State {params::Array String|r} JSExpr
newParam = state npf 
  where 
  npf jsf@{params} = 
    let paramName = "p" <> show (length params)         
    in Tuple (Local paramName) (jsf {params = params <> [paramName]})

constantOrParam :: forall r. ArgType -> State {params::Array String|r} JSExpr
constantOrParam a = maybe newParam pure (ctConstant $ typeForArg a)

expressionOrFunc :: Tuple Type FuncArgs -> Either Errors JSExpr
expressionOrFunc (Tuple _ {return}) | Just e <- ctConstant return = Right e
expressionOrFunc (Tuple (RTLambda _ f) {args}) = 
  let appliedRT = runExceptT $ do 
        expr <- runApplyRT f $ (\arg -> {arg, expr:constantOrParam arg}) <$> args
        gets (_ {stmts = [Return expr]})
  in AnonymousFunc <$> evalState appliedRT {params:[],stmts:[]}
expressionOrFunc (Tuple t _) = Left $ (Expected $ "Lambda but was: " <> show t)

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log $ unsafeCoerce $ do 
    ft <- runFunc (applyCT addAny) {args: [Positional $ knownString "sdf", Positional $ UnknownT], return: UnknownT}
    pure $ exprToString <$> expressionOrFunc ft

-- testIt :: Type 
-- testIt = CTLambda ?o


-- test(a, b) = 
--  let o = mul(a, b)
--  in add(o, 5)
-- test a b = a * b  