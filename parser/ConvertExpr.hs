{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts #-}
{-# LANGUAGE LambdaCase,TupleSections,TemplateHaskell #-}

module ConvertExpr where 

import Prelude

import qualified Syntax as S
import qualified Data.Map as Map
import Types (TypeRef, App, Type)
import Control.Lens
import Control.Monad.State
import Data.Semigroup

data CurrentExpr = CurrentParams [TypeRef] | CurrentArgs S.Expr [TypeRef] | NoExpr deriving (Show)
data ExprState = ExprState {_currentExpr :: CurrentExpr, _args :: [TypeRef], 
    _apps :: [App], _names :: Map.Map String TypeRef, _typeCount :: Int } deriving (Show)

makeLenses ''ExprState

convertExpr :: S.Expr -> State ExprState Type
convertExpr e = do 
  cu <- use currentExpr
  case cu of 
    NoExpr -> case e of 
      S.Lam p next -> addArg p [] next
    CurrentParams params -> case e of 
      S.Lam p next -> addArg p params next 
      S.App ap arg -> do 
        args .= params
        assign currentExpr $ CurrentArgs ap []
        convertExpr arg
      o -> error $ "PARAMS:" <> show o
    CurrentArgs lame argRefs -> 
        error $ "ARGS:" <> show e 
  where 
  addArg p l next = do 
    typeRef <- typeCount <<%= (+) 1
    names.at p .= Just typeRef
    assign currentExpr (CurrentParams $ typeRef : l)
    convertExpr next
