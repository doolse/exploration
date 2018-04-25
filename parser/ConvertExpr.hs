{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts #-}
{-# LANGUAGE LambdaCase,TupleSections,TemplateHaskell #-}

module ConvertExpr where 

import Prelude

import qualified Syntax as S
import qualified Data.Map as Map
import Types 
import Control.Lens
import Control.Monad.State
import Data.Semigroup
import NativeJavascript
import Debug.Trace


newtype DecodeFunc = DecodeFunc (S.Expr -> State ExprState (Either TypeRef DecodeFunc))

instance Show DecodeFunc where 
    show _ = "<Decode>"

data ExprState = ExprState { 
    _constantTypes :: [(TypeRef, Type)], 
    _names :: Map.Map String (Either TypeRef DecodeFunc), 
    _typeCount :: Int,
    _applics :: [App]
    }

instance Show ExprState where 
  show ExprState {_constantTypes=ct,_names=names} = "constants: " <> show ct <> " names:" <> show names

makeLenses ''ExprState

opToType :: S.Binop -> Type 
opToType S.Mul = mulInt
opToType S.Add = add

newType :: State ExprState TypeRef
newType = typeCount <<%= (+) 1

mkNewType = Just <$> newType

namedType :: String -> State ExprState TypeRef
namedType name = do 
    ref <- newType
    names.at name .= Just (Left ref)
    pure ref

collectArgs :: S.Expr -> State ExprState ([TypeRef], S.Expr)
collectArgs (S.Lam name next) = do 
  ref <- namedType name
  (a, e) <- collectArgs next
  pure (ref : a, e)
collectArgs o = pure ([], o)

errorState :: String -> State ExprState a
errorState msg = do 
    traceM msg 
    s <- get 
    error $ show s

collectApps :: S.Expr -> State ExprState (Either TypeRef DecodeFunc)
collectApps (S.Var name) = do 
    tr <- use $ names.at name
    case tr of 
        Just refOr -> pure refOr 
collectApps (S.Lam name b) = do 
    pure $ Right $ DecodeFunc (\e -> do 
        t <- collectApps e 
        names.at name .= Just t 
        collectApps b)
collectApps (S.App l r) = do
    ll <- collectApps l
    case ll of 
        Right (DecodeFunc f) -> f r
collectApps (S.Op op l r) = do 
    ltm <- collectApps l 
    rtm <- collectApps r
    out <- newType
    case (ltm,rtm) of
        (Left lt, Left rt) -> do
            applics %= (:) (capp (show op) (opToType op) [lt,rt] out) 
            pure $ Left out 
        o -> error $ "No argTypes:" <> show o
collectApps (S.Lit (S.LInt i)) = do 
    c <- newType
    constantTypes %= (:) (c, ctInt i)
    pure $ Left c
collectApps o = error $ "COLLECT:" <> show o

convertExpr :: S.Expr -> State ExprState Type
convertExpr e = do 
    (arefs, be) <- collectArgs e
    res <- collectApps be
    s@ExprState {_applics,_typeCount,_constantTypes} <- get
    let (cRefs, cs) = unzip _constantTypes
        initial = constants cRefs cs $ typeArr _typeCount
        body = StateLambda {args = arefs, apps = reverse _applics}
    trace (" state: " <> show s <> show res)
        pure $ lambda "top" (const unknownT <$> arefs) unknownT (ctt initial body) (rt initial body) 
