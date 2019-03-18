{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}

import Prelude 
import Control.Monad.State
import qualified Data.Vector as V
import Debug.Trace
import Data.List
import Data.Maybe

data TypePredicate = IntRange Int Int | StringType Int Int | FuncPred TypeRef
    deriving Show

type TypeRef = Int 

data PrimitiveApp = BindByPosition Int | BindOffset Int | Positioned Int
    deriving Show
data PrimitiveFunc = Multiply | Plus
    deriving Show

data Type = ConstInt Int | ConstString String | Array [TypeRef] 
    | Unknown | Reference TypeRef
    | Application {args::TypeRef, func:: TypeRef}
    | Function {name :: String, register :: [Type]}
    | PrimFunc PrimitiveFunc
    | PrimFuncApp PrimitiveApp TypeRef
    deriving Show

data TypeFlags = Position Int 
    deriving (Show, Eq)
data EType = Evaled [TypeFlags] Type | Unevaled Type
    deriving Show

type ETypeArray = V.Vector EType

type TypeState a = State ETypeArray a 

argRef :: Type
argRef = Reference 0 

withPosition :: Int -> TypeRef -> Type
withPosition pos = PrimFuncApp (Positioned pos)

-- func(b) = 
--     let something(a) = *(a, b)
--     in +(something(23), 234)

something :: Type 
something = Function {name = "something", register = [
    PrimFuncApp (BindByPosition 0) 0, -- 1
    PrimFuncApp (BindOffset 0) 0, -- 2
    PrimFunc Multiply, -- 3
    Array [1, 2], -- 4
    Application {args = 4, func = 3}
]}

mainType :: Type 
mainType = Function {name = "func", register = [
    PrimFuncApp (BindByPosition 0) 0, -- 1
    something, -- 2
    ConstInt 23, -- 3 
    ConstInt 234, -- 4
    withPosition 0 3, -- 5
    withPosition 1 4, -- 6
    Array [1, 5], -- 7
    Application {args = 7, func = 2}, -- 8
    withPosition 0 8, -- 9
    PrimFunc Plus, -- 10
    Array [9, 6], -- 11
    Application {args = 11, func = 10}
]}

runProg :: ETypeArray 
runProg = V.fromList [ 
    Unevaled $ ConstInt 23,
    Unevaled $ withPosition 0 0, 
    Unevaled mainType, 
    Unevaled $ Array [1],
    Unevaled $ Application {args=3, func = 2}] 

main :: IO ()
main = let (_, state) = runState (evaluateType 4) runProg
    in void $ traverse (print . show) $ V.indexed state

intFunc :: (Int -> Int -> Int) -> TypeRef -> TypeState (Maybe EType)
intFunc f r = do 
    t <- evaluateType r
    case t of 
        Evaled _ (Array [arg1, arg2]) -> do 
            v1 <- evaluateType arg1
            v2 <- evaluateType arg2
            iv1m <- intValue arg1
            iv2m <- intValue arg2
            case (iv1m, iv2m) of 
                (Just iv1, Just iv2) -> return $ Just $ Evaled [] (ConstInt $ f iv1 iv2)
                _ -> return Nothing

applyPrim :: PrimitiveFunc -> TypeRef -> TypeState (Maybe EType)
applyPrim pf = case pf of 
            Plus -> intFunc (+)     
            Multiply -> intFunc (*)

addOffset :: TypeRef -> TypeRef -> Type -> Type 
addOffset ar offs t = 
  let 
    changeRef 0 = ar 
    changeRef o = offs + o
  in case t of 
    Array atr -> Array $ changeRef <$> atr  
    Reference tr -> Reference $ changeRef tr
    Application atr ftr -> Application (changeRef atr) (changeRef ftr)
    PrimFuncApp pa ft -> PrimFuncApp pa $ changeRef ft
    other -> other

intValue :: TypeRef -> TypeState (Maybe Int) 
intValue tr = do 
    s <- gets $ flip (V.!) tr
    case s of 
        Evaled _ (ConstInt i) -> return $ Just i
        Evaled _ (Reference ref) -> intValue ref 
        _ -> return $ Nothing

addFlag :: TypeFlags -> EType -> EType 
addFlag fl t = case t of 
    Evaled flags t -> Evaled (fl : flags) t  

hasFlag :: TypeFlags -> EType -> Bool 
hasFlag fl (Evaled flags t) | any ((==) fl) flags = True
hasFlag _ _ = False

evalType :: Type -> TypeState EType 
evalType t = case t of 
    Application {args,func} -> do 
        evalF <- evaluateType func
        case evalF of 
            Evaled flags (PrimFunc f) -> do 
                mt <- applyPrim f args
                return $ fromMaybe (Evaled [] t) mt
            Evaled flags (Function name types) -> do 
                offs <- gets $ V.length
                let newtypes = V.fromList $ Unevaled . addOffset args (offs - 1) <$> types
                modify (flip mappend newtypes)
                newLen <- gets V.length
                evaluateType (newLen - 1)
            o -> trace (show o) error "Can't apply"  
    PrimFuncApp primFunc fapt -> do 
        e <- evaluateType fapt
        case primFunc of 
            BindByPosition p -> case e of 
                Evaled _ (Array refs) -> do 
                    evaledRefs <- traverse (\tr -> do 
                        t <- evaluateType tr
                        return (tr, t)
                        ) refs
                    case find (hasFlag (Position p). snd) evaledRefs of 
                        Just (tr, _) -> return $ Evaled [] (Reference tr)
            BindOffset o -> case e of 
                Evaled _ (Array refs) -> return $ Evaled [] (Reference $ refs !! o)
            Positioned p -> return $ addFlag (Position p) e
    o -> return (Evaled [] o)

evaluateType :: TypeRef -> TypeState EType
evaluateType r = do 
    s <- gets $ flip (V.!) r 
    case s of 
        Evaled f t -> return $ Evaled f t 
        Unevaled t -> do 
            nt <- evalType t
            traceM (show r ++ " " ++ show s ++ "=======" ++ show nt)
            modify (flip (V.//) [(r, nt)] )
            return nt

