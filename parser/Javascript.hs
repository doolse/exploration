{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts,LambdaCase #-}

module Javascript where 

import Control.Monad.Trans.Except
import Control.Monad.State.Class
import Control.Monad.State
import Unsafe.Coerce
import Data.Semigroup
import Data.List
import Types 

data JSExpr =
    Reference String
    | JSInt Int
    | JSString String
    | InfixFuncApp String JSExpr JSExpr 
    | JSAnonFunc JSFunctionBody

type JS = ExceptT Errors (State JSFunctionBody)

nativeJS :: JSExpr -> NativeExpr 
nativeJS = unsafeCoerce

fromNative :: NativeExpr -> JSExpr
fromNative = unsafeCoerce

jsArg :: [(Type, NativeExpr)] -> Int -> JSExpr
jsArg arr i = fromNative $ snd $ (arr !! i)

typeToJS :: Type -> Maybe JSExpr
typeToJS (Type {t}) = case t of 
    (IntT (Just a)) -> pure $ JSInt a
    (StringT (Just s)) -> pure $ JSString s
    _ -> Nothing

data JSStatement = 
    Return JSExpr | AssignVar String JSExpr

data JSFunctionBody = JSFunctionBody { params:: [String], stmts :: [JSStatement] }

emptyFunction = JSFunctionBody {params=[], stmts=[]}

anonFunc :: JSFunctionBody -> JSExpr -> JSExpr 
anonFunc b = JSAnonFunc . addReturn b

addReturn :: JSFunctionBody -> JSExpr -> JSFunctionBody
addReturn fb e = fb {stmts = mappend (stmts fb) [Return e] }

exprToString :: JSExpr -> String
exprToString (Reference l) = l 
exprToString (JSString s) = "\"" <> s <> "\""
exprToString (JSInt i) = show i
exprToString (InfixFuncApp n a b) = exprToString a <> n <> exprToString b
exprToString (JSAnonFunc JSFunctionBody {params, stmts}) =  "function(" <> (intercalate "," params) <> ") {\n" <> 
    intercalate "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString :: JSStatement -> String
stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"

constOrArg :: Type -> JS JSExpr
constOrArg t = maybe createArg pure $ typeToJS t
  where 
  createArg = do 
    JSFunctionBody {params} <- get
    let newName = "p" <> (show $ length params)
    modify (\fb -> fb {params = mappend params [newName]})
    pure $ Reference newName

genFunc :: JSFunctionBody -> JS JSExpr -> Either Errors JSExpr
genFunc init rgen = mkFunc $ runState (runExceptT rgen) init
    where 
    mkFunc (e, fb) = (anonFunc fb) <$> e

newLocal :: JSExpr -> JS JSExpr
newLocal e = do 
    JSFunctionBody {stmts} <- get
    let newName = "v" <> (show $ length stmts)
    modify (\fb -> fb {stmts = mappend stmts [AssignVar newName e]})
    pure $ Reference newName
     
       