{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}

import Prelude 
import Control.Monad.State
import qualified Data.Vector as V
import Debug.Trace
import Data.List 
import Data.Maybe
import Control.Monad.Extra (findM)
import qualified Javascript as J

data TypePredicate = IntRange Int Int | StringType Int Int | FuncPred TypeRef
    deriving Show

type TypeRef = Int 

data PrimitiveApp = BindByPosition Int | BindOffset Int
    deriving Show
data PrimitiveFunc = Multiply | Plus
    deriving Show

data Type = ConstInt Int | ConstString String | Array [TypeRef] 
    | Unknown | Reference TypeRef
    | Application {args::TypeRef, func:: TypeRef}
    | Function {name :: String, register :: [FType]}
    | PrimFunc PrimitiveFunc
    | PrimFuncApp PrimitiveApp TypeRef
    deriving Show

data TypeFlags = Position Int 
    deriving (Show, Eq)

data Reduction = Unreduced | Reducing | ReducedFrom Type
    deriving Show

data EType = EType Reduction [TypeFlags] Type 
    deriving Show

data FType = FType [TypeFlags] Type
    deriving Show

type ETypeArray = V.Vector EType

type TypeState a = State ETypeArray a 

argRef :: Type
argRef = Reference 0 

withPosition :: Int -> Type -> FType
withPosition pos = FType [Position pos]

-- func(b) = 
--     let something(a) = *(a, b)
--     in +(something(23), 234)

primApp :: PrimitiveApp -> TypeRef -> FType 
primApp pa = FType [] . PrimFuncApp pa

primFunc :: PrimitiveFunc -> FType 
primFunc = FType [] . PrimFunc

simple :: Type -> FType 
simple = FType []

something :: Type 
something = Function {name = "something", register = [
    primApp (BindByPosition 0) 0, -- 1
    primApp (BindOffset 0) 0, -- 2
    primFunc Multiply, -- 3
    simple $ Array [1, 2], -- 4
    simple $ Application {args = 4, func = 3}
]}

mainType :: Type 
mainType = Function {name = "func", register = [
    primApp (BindByPosition 0) 0, -- 1
    FType [] something, -- 2
    withPosition 0 $ ConstInt 23, -- 3 
    withPosition 1 $ ConstInt 234, -- 4
    simple $ Array [1, 3], -- 5
    withPosition 0 $ Application {args = 5, func = 2}, -- 6
    primFunc Plus, -- 7
    simple $ Array [6, 4], -- 8
    simple $ Application {args = 8, func = 7}
]}

unreduced :: FType -> EType 
unreduced (FType flags t) = EType Unreduced flags t

runProg :: ETypeArray 
runProg = V.fromList [ 
    unreduced $ withPosition 0 $ Unknown, -- 0
    unreduced $ simple mainType, -- 1 
    unreduced $ simple $ Array [0], -- 2
    unreduced $ simple $ Application {args=2, func = 1}] 

printAll :: (Applicative m) => ETypeArray -> m ()
printAll st = void $ traverse (traceM . show) $ V.indexed st

intFunc :: (Int -> Int -> Int) -> TypeRef -> TypeState (Maybe Type)
intFunc f r = do 
    t <- reducedType r
    case t of 
        (Array [arg1, arg2]) -> do 
            v1 <- reducedType arg1
            v2 <- reducedType arg2
            iv1m <- intValue arg1
            iv2m <- intValue arg2
            case (iv1m, iv2m) of 
                (Just iv1, Just iv2) -> return $ Just $ (ConstInt $ f iv1 iv2)
                _ -> return Nothing

applyPrim :: PrimitiveFunc -> TypeRef -> TypeState (Maybe Type)
applyPrim pf = case pf of 
            Plus -> intFunc (+)     
            Multiply -> intFunc (*)

addOffsetF :: TypeRef -> TypeRef -> FType -> EType 
addOffsetF ar offs (FType flags t) = EType Unreduced flags $ addOffset ar offs t

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

followRefs :: TypeRef -> TypeState (TypeRef, EType)
followRefs tr = do 
    s <- gets $ flip (V.!) tr
    case s of 
        EType _ _ (Reference ref) -> followRefs ref 
        o -> return (tr, o)

intValue :: TypeRef -> TypeState (Maybe Int) 
intValue tr = do 
    (_,t) <- followRefs tr
    case t of 
        (EType _ _ (ConstInt i)) -> return $ Just i
        _ -> return $ Nothing

addFlag :: TypeFlags -> TypeRef -> TypeState () 
addFlag fl tr = do 
    (r, (EType red flags t)) <- followRefs tr 
    modify (flip (V.//) [(r, EType red (fl : flags) t)])

hasFlag :: TypeFlags -> TypeRef -> TypeState Bool 
hasFlag fl tr = do 
    EType _ flags _ <- gets $ flip (V.!) tr
    return $ any ((==) fl) flags

reducible :: Type -> Bool
reducible (Application _ _) = True
reducible (PrimFuncApp _ _) = True
reducible _ = False

reducedType :: TypeRef -> TypeState Type 
reducedType tr = do 
    s <- gets $ flip (V.!) tr 
    case s of 
        EType Unreduced flags t | reducible t -> do 
            modify (flip (V.//) [(tr, EType Reducing flags t)])
            reduced <- reduceType t 
            let (redType, ty) = case reduced of 
                    Just didreduce -> (ReducedFrom t, didreduce)
                    Nothing -> (Unreduced, t)
            modify (flip (V.//) [(tr, EType redType flags ty)])        
            return ty
        EType Reducing _ _ -> do 
            get >>= printAll
            error $ "Already reducing: " ++ show s
        EType _ _ t -> return t


reduceType :: Type -> TypeState (Maybe Type) 
reduceType t = case t of 
    Application {args,func} -> do 
        evalF <- reducedType func
        case evalF of 
            (PrimFunc f) -> applyPrim f args 
            (Function name types) -> do 
                offs <- gets $ V.length
                let newtypes = V.fromList $ addOffsetF args (offs - 1) <$> types
                modify (flip mappend newtypes)
                newLen <- gets V.length
                Just <$> reducedType (newLen - 1)
            o -> trace (show o) error "Can't apply"  
    PrimFuncApp primFunc fapt -> do 
        e <- reducedType fapt 
        case primFunc of 
            BindByPosition p -> case e of 
                (Array refs) -> do 
                    _ <- traverse reducedType refs
                    foundIt <- findM (hasFlag $ Position p) refs
                    case foundIt of  
                        Just tr -> return $ Just (Reference tr)
                        _ -> error $ "Could not find position " ++ show p ++ show refs
            BindOffset o -> case e of 
                (Array refs) -> return $ Just $ (Reference $ refs !! o)
    _ -> return Nothing 

getType :: TypeRef -> TypeState Type 
getType tr = do 
    EType _ _ t <- gets $ flip (V.!) tr
    return t 

createJSBody :: TypeRef -> TypeState J.JSExpr
createJSBody tr = do 
    s <- getType tr
    case s of 
       (Application {args, func}) -> do
            ft <- getType func 
            case ft of 
                PrimFunc pf -> do
                    argT <- getType args
                    let infunc = case pf of 
                            Plus -> " + "
                            Multiply -> " * "
                    case argT of 
                        Array [a1, a2] -> do 
                            l <- createJSBody a1
                            r <- createJSBody a2 
                            return $ J.JSInfix 3 infunc l r
       Reference ref -> createJSBody ref
       ConstInt c -> return $ J.JSInt c
       Unknown -> return $ J.Reference "r"
       o -> error $ "Couldn't convert " ++ (show o) ++ "into JS"
                    


main :: IO ()
main = let prog = evalState (reducedType 3 *> createJSBody 3) runProg
    in print $ snd $ J.exprToString $ prog