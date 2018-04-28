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
    | JSBool Bool
    | JSInfix Int String JSExpr JSExpr 
    | JSTernary JSExpr JSExpr JSExpr
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
    (BoolT (Just b)) -> pure $ JSBool b
    _ -> Nothing

data JSStatement = 
    Return JSExpr | AssignVar String JSExpr

data JSFunctionBody = JSFunctionBody { params:: [String], stmts :: [JSStatement] }

emptyFunction = JSFunctionBody {params=[], stmts=[]}

anonFunc :: JSFunctionBody -> JSExpr -> JSExpr 
anonFunc b = JSAnonFunc . addReturn b

addReturn :: JSFunctionBody -> JSExpr -> JSFunctionBody
addReturn fb e = fb {stmts = mappend (stmts fb) [Return e] }

exprToStringB :: Int -> JSExpr -> String 
exprToStringB i e = case exprToString e of 
    (p, s) | p < i && p /= 0 -> "(" <> s <> ")"
    (_, s) -> s

exprToString :: JSExpr -> (Int, String)
exprToString (Reference l) = (0, l)
exprToString (JSString s) = (0, "\"" <> s <> "\"")
exprToString (JSInt i) = (0, show i)
exprToString (JSBool True) = (0, "true")
exprToString (JSTernary a b c) = 
    (4, exprToStringB 4 a <> " ? " <> exprToStringB 4 b <> " : " <> exprToStringB 4 c)
exprToString (JSBool False) = (0, "false")
exprToString (JSInfix p op a b) = (p, exprToStringB p a <> op <> exprToStringB p b)
exprToString (JSAnonFunc JSFunctionBody {params, stmts}) =  (0, "function(" <> (intercalate "," params) <> ") {\n" <> 
    intercalate "\n" (stmtToString <$> stmts) <> "\n}\n")

stmtToString :: JSStatement -> String
stmtToString (Return expr) = "return " <> (snd $ exprToString expr) <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToStringB 3 expr <> ";"

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
     
       