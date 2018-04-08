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

data PrimType = PInt | PString | PArray

derive instance pEq :: Eq PrimType

data Type = Type TypeT (Maybe NativeExpr)
data TypeT = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | ArrayT (Maybe (Array Type)) (TypeT -> TypeT -> Either Errors TypeT)
  | Lambda { name :: String, args :: Array Type, result :: Type, f :: Array Type -> Either Errors Type }

typeT :: Type -> TypeT 
typeT (Type t _) = t

typeToPrim :: TypeT -> Maybe PrimType 
typeToPrim (IntT _) = Just PInt 
typeToPrim (StringT _) = Just PString 
typeToPrim (ArrayT _ _) = Just PArray 
typeToPrim _ = Nothing

emptyPrim :: PrimType -> TypeT
emptyPrim PInt = IntT Nothing
emptyPrim PString = StringT Nothing 
emptyPrim PArray = ArrayT Nothing unifyArray

primToString :: PrimType -> String 
primToString PInt = "Int"
primToString PString = "String"
primToString PArray = "Array"

unify :: Type -> Type -> Either Errors Type 
unify (Type t1 r1) (Type t2 r2) = map (\nt -> Type nt r2) $ unifyT t1 t2 

unifyT :: TypeT -> TypeT -> Either Errors TypeT 
unifyT UnknownT o = pure o
unifyT l@(ArrayT _ u) o = u l o
unifyT l r        | {lpM: Just lp, rpM: Just rp} <- {lpM:typeToPrim l, rpM:typeToPrim r} = 
    if lp == rp then pure r else throwError $ Expected (primToString lp)
unifyT l UnknownT | Just p <- typeToPrim l = pure $ emptyPrim p
unifyT l o        | Just p <- typeToPrim l = throwError $ Expected $ (primToString p) <> " but was " <> show o
unifyT _ _ = throwError FailedUnification

unifyArray :: TypeT -> TypeT -> Either Errors TypeT
unifyArray (ArrayT (Just a) u) (ArrayT (Just b) _) | length a == length b = (\a -> ArrayT (Just a) u) <$> (traverse (uncurry unify) (zip a b))
unifyArray l r = throwError $ Expected $ "An array to unify but got: " <> show l <> " and " <> show r

ctArr :: Array Type -> Type 
ctArr arr = Type (ArrayT (Just arr) unifyArray) Nothing

arr :: forall r. Int -> Array Type -> Either Errors Type 
arr i args | Just a <- index args i = pure a
arr i _  = throwError $ MissingArg (show i)

intValue :: Type -> Maybe Int 
intValue (Type t _ ) = case t of 
  (IntT a) -> a 
  _ -> Nothing

undefInt :: Type 
undefInt = Type (IntT Nothing) Nothing

ctInt :: Int -> Type 
ctInt i = Type (IntT (Just i)) Nothing

ctString :: String -> Type 
ctString s = Type (StringT (Just s)) Nothing

lambda :: forall r. String -> Array Type -> Type -> (Array Type -> Either Errors {args::Array Type, result::Type}) -> Type
lambda name args result app = Type (Lambda {name, args, result, f: f args }) Nothing
  where 
    f args nextargs = do 
      unifiedargs <- sequence $ (uncurry unify <$> zip args nextargs)
      res <- app unifiedargs
      pure $ Type (Lambda {name, args:res.args, result: res.result, f: f res.args}) Nothing

resultType :: Type -> Either Errors Type 
resultType (Type (Lambda {result}) _) = pure result
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

instance showType :: Show TypeT where 
  show = case _ of 
    a | Just p <- typeToPrim a -> primToString p
    UnknownT -> "An unknown type"
    (Lambda {name, args, result }) -> "\\" <> name
    _ -> "Who knows?"
