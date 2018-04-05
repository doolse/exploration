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
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple(..), uncurry)
import Debug.Trace (spy)
import Partial.Unsafe (unsafePartial)
import Unsafe.Coerce (unsafeCoerce)

data Errors = Expected String | PositionalFirst String | MissingArg String | FailedUnification

type AP r = ExceptT Errors (State {args::Type|r})

data TypeFlags = UnifyWith String 

foreign import data NativeExpr :: Type 

data PrimType = PInt | PString | PArray

derive instance pEq :: Eq PrimType

data Type = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | ArrayT (Maybe (Array Type)) (Type -> Type -> Either Errors Type)
  | Lambda { name :: String, args :: Type, result :: Type, native :: Either Errors NativeExpr, f :: Type -> Either Errors Type }

typeToPrim :: Type -> Maybe PrimType 
typeToPrim (IntT _) = Just PInt 
typeToPrim (StringT _) = Just PString 
typeToPrim (ArrayT _ _) = Just PArray 
typeToPrim _ = Nothing

emptyPrim :: PrimType -> Type 
emptyPrim PInt = IntT Nothing
emptyPrim PString = StringT Nothing 
emptyPrim PArray = ArrayT Nothing (unifyArray)

primToString :: PrimType -> String 
primToString PInt = "Int"
primToString PString = "String"
primToString PArray = "Array"

unify :: Type -> Type -> Either Errors Type 
unify UnknownT o = pure o
unify l@(ArrayT _ u) o = u l o
unify l r        | {lpM: Just lp, rpM: Just rp} <- {lpM:typeToPrim l, rpM:typeToPrim r} = 
    if lp == rp then pure r else throwError $ Expected (primToString lp)
unify l UnknownT | Just p <- typeToPrim l = pure $ emptyPrim p
unify l o        | Just p <- typeToPrim l = throwError $ Expected $ (primToString p) <> " but was " <> show o
unify _ _ = throwError FailedUnification

unifyArray :: Type -> Type -> Either Errors Type
unifyArray (ArrayT (Just a) u) (ArrayT (Just b) _) | length a == length b = (\a -> ArrayT (Just a) u) <$> (traverse (uncurry unify) (zip a b))
unifyArray l r = throwError $ Expected $ "An array to unify but got: " <> show l <> " and " <> show r

ctArr :: Array Type -> Type 
ctArr arr = ArrayT (Just arr) unifyArray

arg :: forall r. Int -> AP r Type 
arg i = do
  {args} <- get 
  case args of 
    (ArrayT (Just a) _) -> index a i # maybe' (\_ -> throwError $ MissingArg (show i)) pure
    _ -> throwError $ Expected "An array of args"

intValue :: Type -> Maybe Int 
intValue = case _ of 
  (IntT a) -> a 
  _ -> Nothing

undefInt :: Type 
undefInt = IntT Nothing 

ctInt :: Int -> Type 
ctInt i = IntT (Just i)

ctString :: String -> Type 
ctString s = StringT (Just s)

lambda :: forall r. String -> {args::Type|r} -> Type -> Either Errors NativeExpr -> AP r (Tuple Type (Either Errors NativeExpr)) -> Type
lambda name initial result native body = 
  Lambda {name,result, args: initial.args, native, f: f initial }
  where 
    f s@{args} newargs = do 
      unifiedArgs <- unify args newargs
      let unifiedState = s {args = unifiedArgs}
      let (Tuple res nextState) = runState (runExceptT body) unifiedState
      res # rmap (\(Tuple nr ne) -> Lambda {name, result:nr, native: ne, args: nextState.args, f: f nextState})

resultType :: Type -> Either Errors Type 
resultType (Lambda {result}) = pure result
resultType _ = throwError (Expected "Lambda result")

applyResult :: Type -> Array Type -> Either Errors Type 
applyResult t arr = applyLambda t arr >>= resultType

applyLambda :: Type -> Array Type -> Either Errors Type
applyLambda t args = case t of 
  Lambda {f} -> f (ctArr args)
  _ -> throwError (Expected "A lambda to apply")

applyUnsafe :: Type -> Array Type -> Type 
applyUnsafe t args = unsafePartial case t of 
  Lambda {f} -> fromRight $ (f (ctArr args) >>= resultType)

instance showError :: Show Errors where 
  show = case _ of 
    (Expected a) -> "Expected " <> a
    (PositionalFirst msg) -> "Positional arguments must be first " <> msg 
    (MissingArg msg) -> "Missing argument to function: " <> msg
    (FailedUnification) -> "Failed to unify types"

instance showType :: Show Type where 
  show = case _ of 
    a | Just p <- typeToPrim a -> primToString p
    UnknownT -> "An unknown type"
    (Lambda {name, args, result }) -> "\\" <> name
    _ -> "Who knows?"
