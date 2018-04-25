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
collectApps (S.App (S.Lam name l) r) = do
    rr <- collectApps r
    names.at name .= Just rr 
    collectApps l
--     (lamArgs, next) <- collectArgs l
--     case lamArgs of 
--         [o] -> do 
--             (_, apps) <- collectApps r (pure $ Just o)
--             (o, nxapps) <- collectApps next mkType
--             pure (o,apps <> nxapps)
-- collectApps lam@(S.Lam _ _) _ = do 
--     (lamArgs, next) <- collectArgs lam
--     case lamArgs of 
--         o -> errorState $  "LAM:" <> show o
collectApps (S.Op op l r) = do 
    ltm <- collectApps l 
    rtm <- collectApps r
    out <- newType
    case (ltm,rtm) of
        (Left lt, Left rt) -> do
            applics %= (:) (capp (show op) (opToType op) [lt,rt] $ Just out) 
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

--     do 
--   cu <- use currentExpr
--   case cu of 
--     NoExpr -> case e of 
--       S.Lam p next -> addArg p [] next
--     CurrentParams params -> case e of 
--       S.Lam p next -> addArg p params next 
--       o -> do 
--         apps <- collectApps o Nothing
--         ExprState {_exprArgs,_typeCount,_constantTypes} <- get
--         let lamArgs = const unknownT <$> _exprArgs
--             body = StateLambda {args = _exprArgs, apps}
--             (cRefs, cs) = unzip _constantTypes
--             initial = constants cRefs cs $ typeArr _typeCount
--         pure $ lambda "myLam" lamArgs unknownT (ctt initial body) (rt initial body) 
--       -- S.App ap arg -> do 
--       --   exprArgs .= params
--       --   assign currentExpr $ CurrentArgs ap []
--       --   convertExpr arg
--       -- o -> error $ "PARAMS:" <> show o
--     -- CurrentArgs lame argRefs -> case e of 
--     --   S.Op op le re -> do 
--     --     apps %= ((:) $ capp "" (opToType op) (traverse asRef [le, re]) Nothing)
--     --   _ -> error $ "ARGS:" <> show e 
--   where 
--   collectApps :: S.Expr -> Maybe TypeRef -> State ExprState [App]
--   collectApps (S.App (S.Lam name l) r) out = do 
--     lamOut <- addNamed name 
--     rapps <- collectApps r $ Just lamOut
--     lapps <- collectApps l out
--     pure $ lapps <> rapps
--   collectApps (S.App (S.Var il) r) out = do 
--     inn <- use $ inners.at il 
--     pure $ case inn of 
--       Just f -> [ App {name="inner"} ]
--   collectApps (S.Lam name r) out = do 
--     inners.at name .= (Just $ collectApps r)
--     pure []

--   collectApps (S.Op op l r) out = do 
--     (leftType,lapps) <- asRef l 
--     (rightType,rapps) <- asRef r 
--     pure $ lapps <> rapps <> [capp "" (opToType op) [leftType, rightType] out]
--   collectApps o _ = error $ "CAPPS:" <> show o

--   asRef :: S.Expr -> State ExprState (TypeRef, [App])
--   asRef op@(S.Op _ _ _) = do 
--     typeRef <- newType
--     a <- collectApps op (Just typeRef)
--     pure (typeRef, a)
--   asRef (S.Lit (S.LInt i)) = do 
--     typeRef <- newType
--     constantTypes %= (:) (typeRef, ctInt i)
--     pure (typeRef, [])
--   asRef sapp@(S.App _ _) = do
--     typeRef <- newType
--     a <- collectApps sapp (Just typeRef)
--     pure (typeRef, a)
--   asRef (S.Var n) = do 
--     r <- use $ names.at n
--     let actualRef = case r of 
--           Just ref -> ref
--     pure $ (actualRef, []) 
      
--   asRef o = do
--     s <- get 
--     error $ "ASREF:" <> show s <> "\n" <> show o


--   addArg p l next = do 
--     typeRef <- addNamed p
--     assign currentExpr (CurrentParams $ typeRef : l)
--     convertExpr next
