module Javascript where 

import Prelude

import Control.Monad.Except (ExceptT(..), except, runExcept, runExceptT, throwError)
import Control.Monad.Reader (ReaderT(..), ask, lift, runReaderT)
import Control.Monad.State (State, get, modify, runState)
import Data.Array (length, snoc)
import Data.Either (Either, either)
import Data.Maybe (Maybe(..), maybe)
import Data.String (joinWith)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Debug.Trace (spy)
import Types (Errors(..), NativeExpr, Type(..), TypeT(..))
import Unsafe.Coerce (unsafeCoerce)

data JSExpr =
     Local String
   | JSInt Int
   | JSString String
   | InfixFuncApp String JSExpr JSExpr 
   | JSAnonFunc JSFunctionBody

type JSRuntimeGen s = ReaderT (JSContext s) (State s)

nativeJS :: forall s. (JSRuntimeGen s JSExpr) -> NativeExpr
nativeJS = unsafeCoerce

fromNative :: NativeExpr -> (forall s. JSRuntimeGen s JSExpr)
fromNative = unsafeCoerce

typeToJS :: forall s. Type -> Maybe (JSRuntimeGen s JSExpr)
typeToJS (Type _ (Just ne)) = Just (fromNative ne)
typeToJS (Type t _) = case t of 
  (IntT (Just a)) -> pure $ pure $ JSInt a
  (StringT (Just s)) -> pure $ pure $ JSString s
  _ -> Nothing

withCtx :: forall s a. (JSContextR s -> JSRuntimeGen s a) -> JSRuntimeGen s a 
withCtx f = ask >>= \(JSContext c) -> f c 

newLocal :: forall s. JSExpr -> JSRuntimeGen s JSExpr 
newLocal e = withCtx (\a -> a.newLocal e)

data JSStatement = 
  Return JSExpr | AssignVar String JSExpr

type JSFunctionBody = { params:: Array String, stmts :: Array JSStatement }

anonFunc :: JSExpr -> JSFunctionBody -> JSExpr 
anonFunc r b = JSAnonFunc $ return r b 

return :: JSExpr -> JSFunctionBody -> JSFunctionBody
return e fb = fb {stmts = snoc fb.stmts $ Return e }
 
emptyFunction = {params:[], stmts:[]}

type JSContextR s = { newLocal :: JSExpr -> JSRuntimeGen s JSExpr }
newtype JSContext s = JSContext (JSContextR s)

exprToString (Local l) = l 
exprToString (JSString s) = "\"" <> s <> "\""
exprToString (JSInt i) = show i
exprToString (InfixFuncApp n a b) = exprToString a <> n <> exprToString b
exprToString (JSAnonFunc {params, stmts}) =  "function(" <> (joinWith "," params) <> ") {" <> 
        joinWith "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"

constOrArg :: Type -> State JSFunctionBody Type 
constOrArg t@(Type o _) = maybe ((\l -> Type o (Just $ nativeJS $ pure l)) <$> newArg) alreadyConst $ typeToJS t
  where alreadyConst g = pure (Type o $ Just $ nativeJS g)

newArg :: State JSFunctionBody JSExpr 
newArg = do 
  {params} <- get
  let newName = "p" <> (show $ length params)
  modify _ {params = snoc params newName}
  pure $ Local newName

genFunc :: JSFunctionBody -> JSRuntimeGen JSFunctionBody JSExpr -> JSExpr
genFunc init rgen = let (Tuple ret body) = runState (runReaderT rgen functionContext) init
  in anonFunc ret body

functionContext :: JSContext JSFunctionBody
functionContext = JSContext {newLocal} 
  where 
    newLocal expr = do 
      {stmts} <- get
      let newName = "v" <> (show $ length stmts)
      modify _ {stmts = snoc stmts $ AssignVar newName expr}
      pure $ Local newName
  
