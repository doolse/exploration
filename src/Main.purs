module Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Unsafe.Coerce (unsafeCoerce)

data Type = IntT (Maybe Int) | Lambda Type (Type -> Tuple Type Type) | UnknownT | TypeError String

unkInt = IntT Nothing

-- add2 :: Int -> Int
add :: Type -> Type
add UnknownT = Lambda nextArg
add l@(Lambda f) = l
add _ = TypeError "Not actually that type"
  where 
  nextArg (Tuple a ) = Tuple a (Lambda result)
  result b = 

apply :: Type -> Type -> Tuple Type Type
apply (Lambda f) a = f a
apply _ b = Tuple (TypeError "Not a lambda") b

addTwo = apply (add UnknownT) UnknownT

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log $ unsafeCoerce $ addTwo
