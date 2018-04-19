module Javascript where 

import Prelude

import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State (State, StateT(..), get, modify, runState, runStateT)
import Control.Monad.Writer (Writer, WriterT(..), runWriterT, tell)
import Data.Array (length, snoc, unsafeIndex)
import Data.Either (Either)
import Data.Lens (modifying, over)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.List (List)
import Data.Maybe (Maybe(..), maybe, maybe')
import Data.Monoid (class Monoid)
import Data.Newtype (class Newtype)
import Data.String (joinWith)
import Data.Tuple (Tuple(..), snd)
import Partial.Unsafe (unsafePartial)
import Types (Errors, NativeExpr, Type(Type), TypeT(StringT, IntT))
import Unsafe.Coerce (unsafeCoerce)

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

jsArg :: Array (Tuple Type NativeExpr) -> Int -> JSExpr
jsArg arr i = fromNative $ snd $ (unsafePartial $ unsafeIndex arr i)

typeToJS :: Type -> Maybe JSExpr
typeToJS (Type {t}) = case t of 
  (IntT (Just a)) -> pure $ JSInt a
  (StringT (Just s)) -> pure $ JSString s
  _ -> Nothing

data JSStatement = 
  Return JSExpr | AssignVar String JSExpr

type JSFunctionBody = { params:: Array String, stmts :: Array JSStatement }

emptyFunction = {params:[], stmts:[]}

anonFunc :: JSFunctionBody -> JSExpr -> JSExpr 
anonFunc b = JSAnonFunc <<< return b

return :: JSFunctionBody -> JSExpr -> JSFunctionBody
return fb e = fb {stmts = snoc fb.stmts $ Return e }
 
exprToString :: JSExpr -> String
exprToString (Reference l) = l 
exprToString (JSString s) = "\"" <> s <> "\""
exprToString (JSInt i) = show i
exprToString (InfixFuncApp n a b) = exprToString a <> n <> exprToString b
exprToString (JSAnonFunc {params, stmts}) =  "function(" <> (joinWith "," params) <> ") {\n" <> 
        joinWith "\n" (stmtToString <$> stmts) <> "\n}\n"

stmtToString :: JSStatement -> String
stmtToString (Return expr) = "return " <> exprToString expr <> ";"
stmtToString (AssignVar v expr) = "var " <> v <> " = " <> exprToString expr <> ";"

constOrArg :: Type -> JS JSExpr
constOrArg t = maybe' (\_ -> createArg) pure $ typeToJS t
  where 
  createArg = do 
    {params} <- get
    let newName = "p" <> (show $ length params)
    modify _ {params = snoc params newName}
    pure $ Reference newName

genFunc :: JSFunctionBody -> JS JSExpr -> Either Errors JSExpr
genFunc init rgen = mkFunc $ runState (runExceptT rgen) init
  where 
  mkFunc (Tuple e fb) = map (anonFunc fb) e

newLocal :: JS JSExpr -> JS (JS JSExpr)
newLocal expr = do 
  {stmts} <- get
  e <- expr
  let newName = "v" <> (show $ length stmts)
  modify _ {stmts = snoc stmts $ AssignVar newName e}
  pure $ pure $ Reference newName
  
