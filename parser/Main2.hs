{-# LANGUAGE NamedFieldPuns,DuplicateRecordFields,RankNTypes,FlexibleContexts #-}
{-# LANGUAGE LambdaCase,TupleSections,TemplateHaskell #-}

import Prelude

import qualified Syntax as S
import qualified Data.Map as Map
import Eval (runEval)
import Parser (parseExpr, parseTokens)

import Control.Monad.Trans
import System.Console.Haskeline

import Types 
import ConvertExpr
import Javascript
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Semigroup 
import Control.Monad.Error.Class 
import Data.Foldable
import Control.Lens
import NativeJavascript

  
-- aba :: Type 
-- aba = lambda "aba" [unknownT, unknownT] unknownT (ctt initial body) (rt initial body)
--   where 
--   _a = 0
--   _b = 1
--   _ab = 2
--   _result = 3
--   body :: StateLambda 
--   body = {args : [_a, _b], apps: [
--     capp "ab" add [_a, _b] $ pure _ab,
--     capp "aba" add [_ab, _a] $ Nothing
--   ]}
--   initial = typeArr 4

-- -- complex(a, b)
-- -- {
-- --   let o = b * 3
-- --   let a5 = a * 5
-- --   let apa5 = a + a5
-- --   apa5 + o
-- --   
-- -- }

-- complex :: Type 
-- complex = lambda "complex" [undefInt, undefInt] undefInt (ctt initial body) (rt initial body) 
--   where 
--   _a = 0
--   _b = 1
--   _o = 2
--   _a5 = 3
--   _apa5 = 4
--   _result = 5
--   _o_2 = 6
--   _a5_2 = 7

--   initial = constants [_o_2, _a5_2] [ctInt 3, ctInt 5] $ typeArr 8

--   body :: StateLambda 
--   body = {args : [_a, _b], apps: [
--     capp "o" mulInt [_b, _o_2] $ pure _o,
--     capp "a5" mulInt [_a, _a5_2] $ pure _a5,
--     capp "apa5" add [_a, _a5] $ pure _apa5,
--     capp "result" add [_apa5, _o] Nothing
--   ]}

-- -- innerLambda(a, b)
-- -- {
-- --   let o = b * 3
-- --   let c d = d * 5 + o
-- --   let ca = c a
-- --   let cb = c b
-- --   let cacb = ca + cb
-- --   cacb + o   
-- -- }  
-- -- let i = \a -> \b -> let o = b * 3 in let c = \d -> d * 5 + o in c a + c b + o in i 34 2

-- innerLambda :: Type 
-- innerLambda = lambda "innerLambda" [undefInt, undefInt] undefInt (ctt initial body) (rt initial body) 
--   where 
--   _a = 0
--   _b = 1
--   _o = 2
--   _ca = 3
--   _cb = 4
--   _cacb = 5
--   _car = 6
--   _cbr = 7
--   _c1_c = 8 
--   _o_a2 = 9

--   initial = constants [_c1_c, _o_a2] [ctInt 5, ctInt 3] $ typeArr 10

--   lamC :: TypeRef -> ArgLens -> LamState LType
--   lamC l args = do 
--     result <- runCT apps
--     pure result
--     where 
--     apps = [
--         capp "c1" mulInt [aix 0 args, _c1_c] $ pure l, 
--         capp "cresult" add [l, _o] Nothing
--       ]

--   body :: StateLambda
--   body = StateLambda {args = [_a, _b], apps = [
--     capp "o" mulInt [_b, _o_a2] $ pure _o,    
--     appLocal "a5" (lamC _car) [_a] $ pure _ca,
--     appLocal "cb" (lamC _cbr) [_b] $ pure _cb,
--     capp "cacb" add [_ca, _cb] $ pure _cacb,
--     capp "result" add [_cacb, _o] $ Nothing
--    ] }

-- Have to make it combine the 
process :: String -> Type
process input = do
  case parseExpr input of
    Left err -> do
      error err
    Right ast -> evalState (convertExpr ast) 
      ExprState {_names=Map.empty, _applics=[], _typeCount = 0, _constantTypes = []}

main :: IO ()
main = do
  let parsed = process "\\a -> \\b -> let o = b * 3 in let c = a + b in c + o + (c * o * a)"
    -- process "\\a -> \\b -> let c = \\d -> d * 5 in c a + c b"
    -- process "\\a -> \\b -> let o = b * 3 in a + o"
    
  putStrLn $ errorOrFunction parsed [unknownT, unknownT]
  -- process "\\a -> \\b -> let o = b * 3 in let c = \\d -> d * 5 + o in c a + c b + o"
-- runInputT defaultSettings loop
--   where
  
  -- loop = do
  --   minput <- getInputLine "Happy> "
  --   case minput of
  --     Nothing -> outputStrLn "Goodbye."
  --     Just input -> (liftIO $ process input) >> loop

    

