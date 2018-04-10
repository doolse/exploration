module Javascript where 

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State (State, get, modify, runState)
import Data.Array (length, snoc, unsafeIndex)
import Data.Maybe (Maybe(..), maybe)
import Data.String (joinWith)
import Data.Tuple (Tuple(..), snd)
import Partial.Unsafe (unsafePartial)
import Types (NativeExpr, Type(Type), TypeT(StringT, IntT))
import Unsafe.Coerce (unsafeCoerce)

data JSExpr =
     Local String
   | JSInt Int
   | JSString String
   | InfixFuncApp String JSExpr JSExpr 
   | JSAnonFunc JSFunctionBody

type JSRuntimeGen s = ReaderT (JSContext s) (State s)

constJS :: JSExpr -> NativeExpr 
constJS e = nativeJS $ pure e

nativeJS :: forall s. (JSRuntimeGen s JSExpr) -> NativeExpr
nativeJS = unsafeCoerce

fromNative :: NativeExpr -> (forall s. JSRuntimeGen s JSExpr)
fromNative = unsafeCoerce

jsArg :: forall s. Array (Tuple Type NativeExpr) -> Int -> (JSRuntimeGen s JSExpr)
jsArg arr i = fromNative $ snd $ (unsafePartial $ unsafeIndex arr i)


typeToJS :: forall s. Type -> Maybe JSExpr
typeToJS (Type {t}) = case t of 
  (IntT (Just a)) -> pure $ JSInt a
  (StringT (Just s)) -> pure $ JSString s
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
exprToString (JSAnonFunc {params, stmts}) =  "function(" <> (joinWith "," params) <> ") {\n" <> 
        joinWith "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"

constOrArg :: Type -> State JSFunctionBody JSExpr 
constOrArg t = maybe newArg pure $ typeToJS t

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
  
