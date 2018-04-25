{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts,LambdaCase,TupleSections #-}

module Types where 

import Prelude
import Control.Monad.Error.Class 
import Data.Semigroup
import Data.Maybe 
import Control.Monad
import Data.List 
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Foldable
import Control.Lens

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

type TypeRef = Int 

newtype NativeCreate = NativeCreate (forall m. MonadError Errors m => Type -> NativeContext m ->
  StateT LambdaState m NativeExpr)

type LType = (Type, NativeCreate)

type LambdaState = [LType]

type LamState = StateT LambdaState (Either Errors)

-- derive instance lsNT :: Newtype LambdaState _ 

type ArgLens = [TypeRef]


data App = App {name :: String, f :: ArgLens -> LamState LType, args :: ArgLens, result :: Maybe TypeRef }

instance Show App where 
  show App {name} = name

data StateLambda = StateLambda {args :: ArgLens, apps :: [App]}
    
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

noNative :: Type -> LType 
noNative t = (t, NativeCreate (\_ _ -> throwError NoNative))

constNative :: NativeExpr -> NativeCreate 
constNative ne = NativeCreate (\_ _ -> pure ne)

withNative :: Type -> NativeExpr -> LType 
withNative t ne = (t, constNative ne)

constOrError :: Type -> LType 
constOrError t = (t, NativeCreate (\t (NativeContext {mkConst}) -> lift $ maybe (throwError NoNative) pure $ mkConst t))


toM :: forall a m. MonadError Errors m => LamState a -> StateT LambdaState m a 
toM = mapStateT (either throwError pure)

capp :: String -> Type -> ArgLens -> Maybe TypeRef -> App
capp name lam args result = App {name, f = runStateless, args, result}
  where 
  runStateless al = do 
    args <- getTypes al
    LambdaR {frt = NativeGenerator frt, result = resultType, args = rargs} <- lift $ applyLambda lam args >>= lambdaR 
    typesOnly al rargs
    pure $ (resultType, NativeCreate (\t ctx@NativeContext {mkConst,local} -> 
      let inlineCall = do
            let createArg (t, (NativeCreate f)) = (t,) <$> f t ctx
            args <- traverse (toM.getLType >=> createArg) al
            lift $ frt args t ctx
    
      in case t of 
        t | Just ne <- mkConst t -> pure ne
        t | Just ref <- guard (refCount t > 1) *> result -> do 
            expr <- inlineCall
            me <- lift $ local expr
            toM $ setOne (withNative t me) ref
            pure $ me
        t -> inlineCall))


appLocal :: String -> (ArgLens -> LamState LType) -> ArgLens -> Maybe TypeRef -> App
appLocal name f args result = App {name, f , args, result}

applyIt :: App -> LamState LType
applyIt App {f,args,result} = do 
  lt <- f args
  maybe (pure ()) (modifyOne $ const lt) result 
  pure $ lt

runCT :: [App] -> LamState LType
runCT apps = do 
  let applyCT app = Just <$> applyIt app
      run = foldl (\a b -> a *> applyCT b) (pure Nothing) apps
  run >>= maybe (throwError $ Expected "") pure

typeArr :: Int -> LambdaState
typeArr len = replicate len (noNative unknownT) 

constants :: ArgLens -> [Type] -> LambdaState -> LambdaState 
constants al t = execState $ traverse_ mkConstant $ zip al t
  where mkConstant (i, t) = modifyOne (\_ -> constOrError t) i 

aix :: Int -> ArgLens -> TypeRef
aix i arr = arr !! i 

setOne :: LType -> TypeRef -> LamState ()
setOne = modifyOne . const

modifyOne :: forall m. MonadState LambdaState m => (LType -> LType) -> TypeRef -> m () 
modifyOne f i = modifying (ix i) f

typesOnly :: ArgLens -> [Type] -> LamState ()
typesOnly al types = traverse_ (\(i, t) -> modifyOne (bimap (const t) id) i) $ zip al types 

getLType :: TypeRef -> LamState LType 
getLType i = (\t -> t !! i) <$> get

getLTypes :: ArgLens -> LamState [LType]
getLTypes = traverse getLType

getTypes :: ArgLens -> LamState [Type]
getTypes a = fmap fst <$> getLTypes a

ct :: StateLambda -> [Type] -> LamState ArgsResult
ct StateLambda {args,apps} aargs = do 
  typesOnly args aargs
  result <- fst <$> runCT apps 
  newargs <- getTypes args
  pure ArgsResult {args= newargs, result}

ctt :: LambdaState -> StateLambda -> [Type] -> Either Errors ArgsResult
ctt initial lam args = evalStateT (ct lam args) initial

rt :: LambdaState -> StateLambda -> NativeGenerator
rt initial StateLambda {apps,args} = NativeGenerator (\nargs t ctx -> 
  let 
  doRT = do
    traverse_ (\(i, (t, ne)) -> setOne (withNative t ne) i) $ zip args nargs
    (t, (NativeCreate f)) <- runCT apps
    (evalStateT $ f t ctx) <$> get
  in either throwError id $ evalStateT doRT initial)


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

