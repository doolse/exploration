module Types where 

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Except (ExceptT(..), except, lift, mapExceptT, runExceptT, throwError)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (ReaderT(..), ask, runReaderT)
import Control.Monad.State (State, StateT(..), evalState, execState, get, gets, modify, put, runState, runStateT)
import Data.Array (index, length, unsafeIndex, updateAt, zip)
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either, fromRight)
import Data.Lens (ALens', Lens', _1, assign, cloneLens, lens, modifying, set, use, withLens)
import Data.Lens.Zoom (zoom)
import Data.List.Lazy (range)
import Data.Maybe (Maybe(..), fromJust, fromMaybe, maybe, maybe')
import Data.Record.Builder (build, merge)
import Data.Traversable (sequence, traverse, traverse_)
import Data.Tuple (Tuple(..), uncurry)
import Debug.Trace (spy)
import Partial.Unsafe (unsafePartial)
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String | FailedUnification

data TypeFlags = UnifyWith String 

foreign import data NativeExpr :: Type 

data PrimType = PInt | PString

derive instance pEq :: Eq PrimType

type NativeContext = {const :: Type -> Maybe NativeExpr}

data Type = Type {t :: TypeT, refs :: Int }

type LambdaR = { name :: String, args :: Array Type, result :: Type, 
      f :: Array Type -> Either Errors Type, frt :: Array (Tuple Type NativeExpr) -> NativeContext -> Either Errors NativeExpr }

data TypeT = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | ArrayT Type (Maybe (Array Type))
  | Lambda LambdaR

typeT :: Type -> TypeT 
typeT (Type {t}) = t

typeToPrim :: TypeT -> Maybe PrimType 
typeToPrim (IntT _) = Just PInt 
typeToPrim (StringT _) = Just PString 
typeToPrim _ = Nothing

emptyPrim :: PrimType -> TypeT
emptyPrim PInt = IntT Nothing
emptyPrim PString = StringT Nothing 

primToString :: PrimType -> String 
primToString PInt = "Int"
primToString PString = "String"

unify :: Type -> Type -> Either Errors Type 
unify (Type {t:t1}) (Type {t:t2, refs:r2}) = map (\nt -> Type {t:nt, refs:r2}) $ unifyT t1 t2 

unifyT :: TypeT -> TypeT -> Either Errors TypeT 
unifyT UnknownT o = pure o
unifyT l r        | {lpM: Just lp, rpM: Just rp} <- {lpM:typeToPrim l, rpM:typeToPrim r} = 
    if lp == rp then pure r else throwError $ Expected (primToString lp)
unifyT l UnknownT | Just p <- typeToPrim l = pure $ emptyPrim p
unifyT l o        | Just p <- typeToPrim l = throwError $ Expected $ (primToString p) <> " but was " <> show o
unifyT _ _ = throwError FailedUnification

incRef :: Type -> Type 
incRef (Type {t,refs}) = Type {t, refs: refs + 1}

unknownT :: Type 
unknownT = Type {t:UnknownT, refs:0}

ctArr :: Type -> Array Type -> Type 
ctArr art arr = Type {t:ArrayT art (Just arr), refs:0}

arr :: forall r. Int -> Array Type -> Either Errors Type 
arr i args | Just a <- index args i = pure a
arr i _  = throwError $ MissingArg (show i)

intValue :: Type -> Maybe Int 
intValue (Type {t}) = case t of 
  (IntT a) -> a 
  _ -> Nothing

undefPrim :: PrimType -> Type 
undefPrim p = Type {t, refs:0}
  where t = case p of 
          PInt -> IntT Nothing 
          PString -> StringT Nothing 

undefInt :: Type 
undefInt = undefPrim PInt

ctInt :: Int -> Type 
ctInt i = Type {t:IntT (Just i), refs:0}

ctString :: String -> Type 
ctString s = Type {t:(StringT (Just s)), refs:0}

lambda :: forall r. String 
  -> Array Type 
  -> Type 
  -> (Array Type -> Either Errors {args::Array Type, result::Type}) 
  -> (Array (Tuple Type NativeExpr) -> NativeContext -> Either Errors NativeExpr)
  -> Type
lambda name args result app frt = Type {t: Lambda {name, args, result, f: f 1 args, frt }, refs:0}
  where 
    f refs args nextargs = do 
      unifiedargs <- sequence $ (uncurry unify <$> zip args nextargs)
      res <- app unifiedargs
      pure $ Type { t:Lambda {name, args:res.args, result: res.result, f: f (refs + 1) res.args, frt}, refs}

lambdaR :: Type -> Either Errors LambdaR
lambdaR (Type {t: Lambda r}) = pure r
lambdaR _ = throwError (Expected "Lambda result")

resultType :: Type -> Either Errors Type 
resultType (Type {t: Lambda {result}}) = pure result
resultType _ = throwError (Expected "Lambda result")

applyResult :: Type -> Array Type -> Either Errors Type 
applyResult t arr = applyLambda t arr >>= resultType

applyLambda :: Type -> Array Type -> Either Errors Type
applyLambda t args = case typeT t of 
  Lambda {f} -> f args
  _ -> throwError (Expected "A lambda to apply")

applyUnsafe :: Type -> Array Type -> Type 
applyUnsafe t args = unsafePartial case typeT t of 
  Lambda {f} -> fromRight $ (f args >>= resultType)

result :: Array (Either Errors Type) -> Either Errors Type -> Either Errors {args::Array Type, result::Type}
result a r = do 
  args <- sequence a 
  result <- r 
  pure $ {args,result}

instance showError :: Show Errors where 
  show = case _ of 
    (Expected a) -> "Expected " <> a
    (PositionalFirst msg) -> "Positional arguments must be first " <> msg 
    (MissingArg msg) -> "Missing argument to function: " <> msg
    (FailedUnification) -> "Failed to unify types"

instance showTypeT :: Show TypeT where 
  show = case _ of 
    a | Just p <- typeToPrim a -> primToString p
    UnknownT -> "An unknown type"
    (Lambda {name, args, result }) -> "\\" <> name
    _ -> "Who knows?"

instance showType :: Show Type where 
  show (Type {t,refs}) = show t <> ":" <> show refs