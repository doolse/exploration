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

data CurrentExpr = CurrentParams [TypeRef] | CurrentArgs S.Expr [TypeRef] | NoExpr deriving (Show)
data ExprState = ExprState {_currentExpr :: CurrentExpr, _exprArgs :: [TypeRef], 
    _constantTypes :: [(TypeRef, Type)], _inners :: Map.Map String (Maybe TypeRef -> State ExprState [App]),
    _names :: Map.Map String TypeRef, _typeCount :: Int }

instance Show ExprState where 
  show ExprState {} = ""

makeLenses ''ExprState

opToType :: S.Binop -> Type 
opToType S.Mul = mulInt
opToType S.Add = add

convertExpr :: S.Expr -> State ExprState Type
convertExpr e = do 
  cu <- use currentExpr
  case cu of 
    NoExpr -> case e of 
      S.Lam p next -> addArg p [] next
    CurrentParams params -> case e of 
      S.Lam p next -> addArg p params next 
      o -> do 
        apps <- collectApps o Nothing
        ExprState {_exprArgs,_typeCount,_constantTypes} <- get
        let lamArgs = const unknownT <$> _exprArgs
            body = StateLambda {args = _exprArgs, apps}
            (cRefs, cs) = unzip _constantTypes
            initial = constants cRefs cs $ typeArr _typeCount
        pure $ lambda "myLam" lamArgs unknownT (ctt initial body) (rt initial body) 
      -- S.App ap arg -> do 
      --   exprArgs .= params
      --   assign currentExpr $ CurrentArgs ap []
      --   convertExpr arg
      -- o -> error $ "PARAMS:" <> show o
    -- CurrentArgs lame argRefs -> case e of 
    --   S.Op op le re -> do 
    --     apps %= ((:) $ capp "" (opToType op) (traverse asRef [le, re]) Nothing)
    --   _ -> error $ "ARGS:" <> show e 
  where 
  collectApps :: S.Expr -> Maybe TypeRef -> State ExprState [App]
  collectApps (S.App (S.Lam name l) r) out = do 
    lamOut <- addNamed name 
    rapps <- collectApps r $ Just lamOut
    lapps <- collectApps l out
    pure $ lapps <> rapps
  collectApps (S.App (S.Var il) r) out = do 
    inn <- use $ inners.at il 
    pure $ case inn of 
      Just f -> [ App {name="inner"} ]
  collectApps (S.Lam name r) out = do 
    inners.at name .= (Just $ collectApps r)
    pure []

  collectApps (S.Op op l r) out = do 
    (leftType,lapps) <- asRef l 
    (rightType,rapps) <- asRef r 
    pure $ lapps <> rapps <> [capp "" (opToType op) [leftType, rightType] out]
  collectApps o _ = error $ "CAPPS:" <> show o

  asRef :: S.Expr -> State ExprState (TypeRef, [App])
  asRef op@(S.Op _ _ _) = do 
    typeRef <- newType
    a <- collectApps op (Just typeRef)
    pure (typeRef, a)
  asRef (S.Lit (S.LInt i)) = do 
    typeRef <- newType
    constantTypes %= (:) (typeRef, ctInt i)
    pure (typeRef, [])
  asRef sapp@(S.App _ _) = do
    typeRef <- newType
    a <- collectApps sapp (Just typeRef)
    pure (typeRef, a)
  asRef (S.Var n) = do 
    r <- use $ names.at n
    let actualRef = case r of 
          Just ref -> ref
    pure $ (actualRef, []) 
      
  asRef o = do
    s <- get 
    error $ "ASREF:" <> show s <> "\n" <> show o

  newType = typeCount <<%= (+) 1

  addNamed p = do 
    typeRef <- newType
    names.at p .= Just typeRef
    pure typeRef

  addArg p l next = do 
    typeRef <- addNamed p
    assign currentExpr (CurrentParams $ typeRef : l)
    convertExpr next
