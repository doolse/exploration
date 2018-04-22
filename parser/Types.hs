{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts,LambdaCase #-}

module Types where 

import Prelude
import Control.Monad.Error.Class 
import Data.Semigroup
import Data.Maybe 
import Control.Monad
import Data.List 

data Errors = Expected String 
  | PositionalFirst String 
  | MissingArg String 
  | TooManyArgs Int Int
  | FailedUnification
  | NoNative deriving Eq

data TypeFlags = UnifyWith String 

data PrimType = PInt | PString deriving Eq

data NativeExpr 

data NativeContext m = NativeContext {mkConst :: Type -> Maybe NativeExpr, local :: NativeExpr -> m NativeExpr }

newtype NativeGenerator = NativeGenerator (forall m. MonadError Errors m => [(Type, NativeExpr)] -> Type -> NativeContext m -> m NativeExpr)

data Type = Type {t :: TypeT, refs :: Int }


data ArgsResult = ArgsResult {args::[Type], result :: Type }

data LambdaR = LambdaR { name :: String, args :: [Type], result :: Type, 
      f :: [Type] -> Either Errors Type, 
      frt ::  NativeGenerator}

data TypeT = 
    UnknownT 
  | IntT (Maybe Int)  
  | StringT (Maybe String)
  | ArrayT Type (Maybe [Type])
  | Lambda LambdaR

refCount :: Type -> Int 
refCount (Type {refs}) = refs 

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
unify (Type {t=t1}) (Type {t=t2, refs=r2}) = (\nt -> Type {t=nt, refs=r2}) <$> unifyT t1 t2 

unifyT :: TypeT -> TypeT -> Either Errors TypeT 
unifyT UnknownT o = pure o
unifyT l r        | (Just lp, Just rp) <- (typeToPrim l, typeToPrim r) = 
    if lp == rp then pure r else throwError $ Expected (primToString lp)
unifyT l UnknownT | Just p <- typeToPrim l = pure $ emptyPrim p
unifyT l o        | Just p <- typeToPrim l = throwError $ Expected $ (primToString p) <> " but was " <> show o
unifyT _ _ = throwError FailedUnification

incRef :: Type -> Type 
incRef (Type {t,refs}) = Type {t, refs= refs + 1}

unknownT :: Type 
unknownT = Type {t=UnknownT, refs=0}

ctArr :: Type -> [Type] -> Type 
ctArr art arr = Type {t=ArrayT art (Just arr), refs=0}

arr :: Int -> [Type] -> Either Errors Type 
arr i args = pure $ args !! i
arr i _  = throwError $ MissingArg (show i)

intValue :: Type -> Maybe Int 
intValue (Type {t}) = case t of 
  (IntT a) -> a 
  _ -> Nothing

strValue :: Type -> Maybe String 
strValue (Type {t}) = case t of 
  (StringT a) -> a 
  _ -> Nothing

undefPrim :: PrimType -> Type 
undefPrim p = Type {t, refs=0}
  where t = case p of 
          PInt -> IntT Nothing 
          PString -> StringT Nothing 

undefInt :: Type 
undefInt = undefPrim PInt

undefString :: Type 
undefString = undefPrim PString

ctInt :: Int -> Type 
ctInt i = Type {t=IntT (Just i), refs=0}

ctString :: String -> Type 
ctString s = Type {t=(StringT (Just s)), refs=0}

polyLambda :: String 
  -> [Type] 
  -> Type 
  -> [Type]
  -> Type
polyLambda name args result lams = Type {t = Lambda LambdaR {name, args, result, f, 
  frt = NativeGenerator (\_ _ _ -> throwError $ Expected "")}, refs=0}
  where 
  f newargs = 
    let ignoreError l = either (const Nothing) Just $ applyLambda l newargs
    in case mapMaybe ignoreError lams of 
      [one] -> pure one 
      [] -> throwError $ Expected "To match a lambda"
      a -> throwError $ Expected "Types to be more specific"

checkArgs :: [Type] -> [Type] -> Either Errors ([Type])
checkArgs args nextargs = do 
  let expectLen = length args
      actualLen = length nextargs
  when (expectLen > actualLen) $ throwError $ 
    MissingArg $ "Not enough args, need " <> show (expectLen - actualLen) <> " more"
  when (expectLen < actualLen) $ throwError $ TooManyArgs actualLen expectLen
  sequence $ (uncurry unify <$> zip args nextargs) 

lambda :: String 
  -> [Type] 
  -> Type 
  -> ([Type] -> Either Errors ArgsResult)
  -> NativeGenerator
  -> Type
lambda name args result app frt = Type {t = Lambda LambdaR {name, args, result, f = f 1 args, frt }, refs = 0}
  where 
    f refs args nextargs = do 
      unifiedargs <- checkArgs args nextargs
      ArgsResult {result=nr,args=nargs} <- app unifiedargs
      pure $ Type { t = Lambda LambdaR {name, args = nargs, result = nr, f = f (refs + 1) nargs, frt}, refs}

lambdaR :: Type -> Either Errors LambdaR
lambdaR (Type {t = Lambda r}) = pure r
lambdaR _ = throwError (Expected "Lambda result")

resultType :: Type -> Either Errors Type 
resultType (Type {t = Lambda LambdaR {result}}) = pure result
resultType _ = throwError (Expected "Lambda result")

applyResult :: Type -> [Type] -> Either Errors Type 
applyResult t arr = applyLambda t arr >>= resultType

applyLambda :: Type -> [Type] -> Either Errors Type
applyLambda t args = case typeT t of 
  Lambda LambdaR {f} -> f args
  _ -> throwError (Expected "A lambda to apply")

applyUnsafe :: Type -> [Type] -> Type 
applyUnsafe t args = (case typeT t of 
  Lambda LambdaR {f} -> either (error.show) id (f args >>= resultType))

-- result :: Array (Either Errors Type) -> Either Errors Type -> Either Errors ArgsResult
-- result a r = do 
--   args <- sequence a 
--   result <- r 
--   pure $ ArgsResult {args,result}

instance Show Errors where 
  show = \case 
    (Expected a) -> "Expected " <> a
    (PositionalFirst msg) -> "Positional arguments must be first " <> msg 
    (MissingArg msg) -> "Missing argument to function: " <> msg
    (TooManyArgs actual expected) -> "Too many arguments to function, expected" 
        <> show expected <> " but got " <> show actual
    FailedUnification -> "Failed to unify types"
    NoNative -> "No native representation"

instance Show TypeT where 
  show = \case 
    IntT (Just i) -> "Int(" <> show i <> ")" 
    StringT (Just s) -> "String(" <> show s <> ")" 
    a | Just p <- typeToPrim a -> primToString p
    UnknownT -> "?"
    (Lambda LambdaR {name, args, result }) -> name 
      <> "(" <> (intercalate "," $ show <$> args) <> "=" <> show result <> ")"
    _ -> "Who knows?"

instance Show Type where 
  show (Type {t,refs}) = show t <> ":" <> show refs