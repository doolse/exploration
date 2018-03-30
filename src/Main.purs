module Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Array (unsafeIndex)
import Data.Foldable (traverse_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)

data Address = DP Int | A | Imm Int

data AddrMode = DP_M | A_M | Imm_M

data Expr = Runtime Address | Const Int | AddExpr Int Int

data ExprAssign = Expr Expr Address

addModes :: Address -> Array (Tuple AddrMode AddrMode)
addModes A = [Tuple A_M DP_M, Tuple A_M Imm_M ]
addModes _ = []

addInst :: Address -> Address -> String
addInst A (Imm v) = "adc #" <> show v
addInst A (DP a) = "adc " <> show a
addInst _ _ = "ERROR"

paramInst :: Address -> Address -> String
paramInst (DP a) A = "lda " <> show a
paramInst (Imm v) A = "lda #" <> show v
paramInst _ _ = "ERROR param"

simpleExpr :: Array ExprAssign
simpleExpr = [Expr (Runtime (DP 0)) A, Expr (Const 2) (Imm 2), Expr (AddExpr 0 1) A, Expr (Const 50) (Imm 50), Expr (AddExpr 2 3) A]

writeInst :: Partial => Array ExprAssign -> ExprAssign -> Array String
writeInst ae (Expr e a) = case e of
  (AddExpr p1 p2) ->
    let exprA1@(Expr _ a1) = unsafeIndex ae p1
        exprA2@(Expr _ a2) = unsafeIndex ae p2
    in writeInst ae exprA1 <> writeInst ae exprA2 <> [addInst a1 a2]
  (Runtime m) -> [paramInst m a]
  (Const v) -> []

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
    traverse_ log $ unsafePartial $ writeInst simpleExpr (unsafeIndex simpleExpr 4)
    log "OK"
