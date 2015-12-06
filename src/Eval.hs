
-- Este archivo es parte de Qriollo.

-- Qriollo is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- Qriollo is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with Qriollo.  If not, see <http://www.gnu.org/licenses/>.

module Eval(
        ValueI(..), EffectM, eval, evalWith,
        fixnumAdd, fixnumSub, constantTag,
    ) where

import System.Exit(exitWith, ExitCode(..))
import Data.Char(ord, chr)
import qualified Data.Map as Map(Map, empty, lookup, insert, fromList)
import Control.Monad.Trans.State.Lazy(
        StateT(..), get, modify, evalStateT
    )
import Control.Monad.Trans.Class(lift)
import Data.Bits((.&.), (.|.), xor, complement)

import Primitive(primMinFixnum, primMaxFixnum)
import ExpressionE
import ExpressionL
import ExpressionK

data ValueI = RecordI [ValueI]
            | ConstantI Constant
            | FunctionI ContI
            | LocationI Integer

instance Show ValueI where
  show (RecordI xs)  = "(RecordI " ++ show xs ++ ")"
  show (ConstantI c) = "(ConstantI " ++ show c ++ ")"
  show (FunctionI _) = "<fun>"

instance Eq ValueI where
  RecordI r1   == RecordI r2    = r1 == r2
  ConstantI c1 == ConstantI c2  = c1 == c2
  FunctionI _  == FunctionI _   = False    -- not comparable
  _            == _             = False

type AnswerI = ValueI
type EnvI    = Map.Map IdK ValueI
type ContI   = [ValueI] -> EvalM AnswerI

answer :: AnswerI
answer = RecordI []

type EffectM = IO

data EvalState = EvalState {
                   evNextFreshLocation :: Integer,
                   evStore :: Map.Map Integer ValueI
                 }
type EvalM a = StateT EvalState EffectM a

bind :: IdK -> ValueI -> EnvI -> EnvI
bind = Map.insert

bindMany :: [(IdK, ValueI)] -> EnvI -> EnvI
bindMany bindings env = foldr (uncurry Map.insert) env bindings

evalFreshLocation :: EvalM ValueI
evalFreshLocation = do
  state <- get
  modify (\ state ->
    state {
      evNextFreshLocation = evNextFreshLocation state + 1
    })
  return $ LocationI (evNextFreshLocation state)

evalNewRef :: ValueI -> EvalM ValueI
evalNewRef val = do
  loc <- evalFreshLocation
  evalAssign loc val
  return loc

evalDeref :: ValueI -> EvalM ValueI
evalDeref (LocationI loc) = do
  state <- get
  case Map.lookup loc (evStore state) of
    Nothing  -> error "(evalDeref: referencia no inicializada)"
    Just val -> return val

evalAssign :: ValueI -> ValueI -> EvalM ()
evalAssign (LocationI loc) val =
  modify (\ state ->
    state {
      evStore = Map.insert loc val (evStore state)
    })

evalValue :: EnvI -> ValueK -> ValueI
evalValue env (VarK x)      = do
  case Map.lookup x env of
    Nothing -> error ("(evalValue: Variable no ligada: " ++ show x ++ ")")
    Just v  -> v
evalValue env (LabelK x)    = do
  case Map.lookup x env of
    Nothing -> error ("(evalValue: Etiqueta no ligada: " ++ show x ++ ")")
    Just v  -> v
evalValue env (ConstantK c) = ConstantI c
evalValue env (SelK i x)    = do
  case Map.lookup x env of
    Nothing -> error ("(evalValue: Variable seleccionada no ligada: " ++
                        show x ++ ")")
    Just (RecordI vs)
      | 0 <= i && i < fromIntegral (length vs)
                  -> vs !! fromIntegral i
      | otherwise -> error ("(evalValue: SelK fuera de rango)")
    Just _ -> error ("(evalValue: SelK sobre un valor que no es un registro)")

evalExpr :: EnvI -> ExprK -> EvalM AnswerI

evalExpr env (AppK func args) =
  case evalValue env func of
    FunctionI func' ->
      let vals' = map (evalValue env) args
       in func' vals'
    value -> error (
               "(evalExpr: " ++ show func ++ " no evalúa a una función " ++
               "sino a " ++ show value ++ ")")

evalExpr env (RecordK vals x cont) =
  let vals' = map (evalValue env) vals in
    evalExpr (bind x (RecordI vals') env) cont

evalExpr env (SelectK i val x cont) =
  case evalValue env val of
    RecordI rec ->
      evalExpr (bind x (rec !! fromIntegral i) env) cont
    _ -> error ("(evalExpr: El argumento de SelectK no es un registro: " ++
                show i ++ " " ++
                show (evalValue env val) ++ " " ++
                show x)

evalExpr env (LetK decls cont) =
    evalExpr extendedEnv cont
  where
    extendedEnv :: EnvI
    extendedEnv = bindMany (map binding decls) env
    binding :: DeclarationK -> (IdK, ValueI)
    binding (ValueDK f args body) =
      (f,
        FunctionI $ \ values ->
          evalExpr (bindMany (zip args values) extendedEnv) body)

evalExpr env (SwitchK val branches) =
  let ConstantI (FixnumC i) = evalValue env val in
    evalExpr env (branches !! fromIntegral i)

-- Primitives

evalExpr env (PrimitiveK PrimFixnumAdd values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumAdd env values ret cont

evalExpr env (PrimitiveK PrimFixnumSub values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumSub env values ret cont

evalExpr env (PrimitiveK PrimFixnumEq values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (==) env values conts

evalExpr env (PrimitiveK PrimFixnumLe values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (<=) env values conts

evalExpr env (PrimitiveK PrimFixnumMul values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumMul env values ret cont

evalExpr env (PrimitiveK PrimFixnumDiv values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumDiv env values ret cont

evalExpr env (PrimitiveK PrimFixnumMod values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumMod env values ret cont

evalExpr env (PrimitiveK PrimFixnumNe values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (/=) env values conts

evalExpr env (PrimitiveK PrimFixnumLt values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (<) env values conts

evalExpr env (PrimitiveK PrimFixnumGe values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (>=) env values conts

evalExpr env (PrimitiveK PrimFixnumGt values [] conts) =
  liftPrimitiveK_FixFix_Branch2 (>) env values conts

evalExpr env (PrimitiveK PrimFixnumLshift values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumLshift env values ret cont

evalExpr env (PrimitiveK PrimFixnumRshift values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumRshift env values ret cont

evalExpr env (PrimitiveK PrimFixnumOrb values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumOrb env values ret cont

evalExpr env (PrimitiveK PrimFixnumAndb values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumAndb env values ret cont

evalExpr env (PrimitiveK PrimFixnumXorb values [ret] [cont]) =
  liftPrimitiveK_FixFix_Fix fixnumXorb env values ret cont

evalExpr env (PrimitiveK PrimFixnumNotb values [ret] [cont]) =
  liftPrimitiveK_Fix_Fix fixnumNotb env values ret cont

evalExpr env (PrimitiveK PrimCharOrd values [ret] [cont]) =
  liftPrimitiveK_Char_Fix (fromIntegral . ord) env values ret cont
evalExpr env (PrimitiveK PrimCharChr values [ret] [cont]) =
  liftPrimitiveK_Fix_Char (chr . fromIntegral) env values ret cont
evalExpr env (PrimitiveK PrimSystemExit [value] [ret] [cont]) =
  let (ConstantI (FixnumC n)) = evalValue env value
   in
     if n == 0
      then lift $ exitWith ExitSuccess
      else lift $ exitWith $ ExitFailure (fromIntegral n)

evalExpr env (PrimitiveK PrimBoxed [value] [] [cont1, cont2]) =
  if valueIsBoxed (evalValue env value)
   then evalExpr env cont1
   else evalExpr env cont2

evalExpr env (PrimitiveK PrimTag [value] [ret] [cont]) =
  let value' = evalValue env value in
    evalExpr (bind ret (valueTag value') env) cont

evalExpr env (PrimitiveK PrimRef [value] [ret] [cont]) = do
  ref <- evalNewRef (evalValue env value)
  evalExpr (bind ret ref env) cont

evalExpr env (PrimitiveK PrimDeref [value] [ret] [cont]) = do
  val <- evalDeref (evalValue env value)
  evalExpr (bind ret val env) cont

-- For effect and value
evalExpr env (PrimitiveK PrimAssign [vref, vval] [ret] [cont]) = do
  evalAssign (evalValue env vref) (evalValue env vval)
  evalExpr (bind ret (ConstantI (FixnumC 0)) env) cont
-- For effect
evalExpr env (PrimitiveK PrimAssign [vref, vval] [] [cont]) = do
  evalAssign (evalValue env vref) (evalValue env vval)
  evalExpr env cont

-- For effect and value
evalExpr env (PrimitiveK PrimPutChar [val] [ret] [cont]) = do
  let ConstantI (CharC c) = evalValue env val in do
    lift (putChar c)
    evalExpr (bind ret (ConstantI (FixnumC 0)) env) cont
-- For effect
evalExpr env (PrimitiveK PrimPutChar [val] [] [cont]) = do
  let ConstantI (CharC c) = evalValue env val in do
    lift (putChar c)
    evalExpr env cont

evalExpr env (PrimitiveK PrimReferenceEq values [] conts) =
  liftPrimitiveK_RefRef_Branch2 (==) env values conts

evalExpr env (PrimitiveK p values rets conts) =
  error ("La primitiva " ++ show p ++ " no está implementada.")

evalExpr env (ForeignK p values rets conts) =
  error ("No se puede usar una función gringa en el intérprete:\n" ++
         show p)

liftPrimitiveK_FixFix_Fix ::
    (Integer -> Integer -> Integer) ->
    EnvI -> [ValueK] -> IdK -> ExprK -> EvalM AnswerI
liftPrimitiveK_FixFix_Fix f env values ret cont =
  let [ConstantI (FixnumC n1), ConstantI (FixnumC n2)] =
        map (evalValue env) values
   in evalExpr (bind ret (ConstantI (FixnumC (f n1 n2))) env) cont

liftPrimitiveK_Fix_Fix ::
    (Integer -> Integer) ->
    EnvI -> [ValueK] -> IdK -> ExprK -> EvalM AnswerI
liftPrimitiveK_Fix_Fix f env values ret cont =
  let [ConstantI (FixnumC n1)] =
        map (evalValue env) values
   in evalExpr (bind ret (ConstantI (FixnumC (f n1))) env) cont

liftPrimitiveK_Char_Fix ::
    (Char -> Integer) ->
    EnvI -> [ValueK] -> IdK -> ExprK -> EvalM AnswerI
liftPrimitiveK_Char_Fix f env values ret cont =
  let [ConstantI (CharC n1)] =
        map (evalValue env) values
   in evalExpr (bind ret (ConstantI (FixnumC (f n1))) env) cont

liftPrimitiveK_Fix_Char ::
    (Integer -> Char) ->
    EnvI -> [ValueK] -> IdK -> ExprK -> EvalM AnswerI
liftPrimitiveK_Fix_Char f env values ret cont =
  let [ConstantI (FixnumC n1)] =
        map (evalValue env) values
   in evalExpr (bind ret (ConstantI (CharC (f n1))) env) cont

liftPrimitiveK_FixFix_Branch2 ::
    (Integer -> Integer -> Bool) ->
    EnvI -> [ValueK] -> [ExprK] -> EvalM AnswerI
liftPrimitiveK_FixFix_Branch2 f env values [cont1, cont2] =
  let [ConstantI (FixnumC n1), ConstantI (FixnumC n2)] =
        map (evalValue env) values in
     if f n1 n2
      then evalExpr env cont1
      else evalExpr env cont2

liftPrimitiveK_RefRef_Branch2 ::
    (Integer -> Integer -> Bool) ->
    EnvI -> [ValueK] -> [ExprK] -> EvalM AnswerI
liftPrimitiveK_RefRef_Branch2 f env values [cont1, cont2] =
  let [LocationI n1, LocationI n2] =
        map (evalValue env) values in
     if f n1 n2
      then evalExpr env cont1
      else evalExpr env cont2

valueTag :: ValueI -> ValueI
valueTag (RecordI (ConstantI (FixnumC n) : _)) = ConstantI (FixnumC n)
valueTag (ConstantI c) = ConstantI (FixnumC $ constantTag c)

constantTag :: Constant -> Integer
constantTag (FixnumC n) = n
constantTag (CharC c)   = fromIntegral (ord c)

valueIsBoxed :: ValueI -> Bool
valueIsBoxed (RecordI _)   = True
valueIsBoxed (ConstantI _) = False
--valueIsBoxed (FunctionI _) = True
--valueIsBoxed (LocationI _) = False

----

-- Arithmetic primitives

fixnumAdd :: Integer -> Integer -> Integer
fixnumAdd x y = (x + y) `mod` (primMaxFixnum + 1)

fixnumSub :: Integer -> Integer -> Integer
fixnumSub x y = (x - y) `mod` (primMaxFixnum + 1)

fixnumMul :: Integer -> Integer -> Integer
fixnumMul x y = (x * y) `mod` (primMaxFixnum + 1)

fixnumDiv :: Integer -> Integer -> Integer
fixnumDiv x y = (x `div` y) `mod` (primMaxFixnum + 1)

fixnumMod :: Integer -> Integer -> Integer
fixnumMod x y = (x `mod` y) `mod` (primMaxFixnum + 1)

fixnumLshift :: Integer -> Integer -> Integer
fixnumLshift x y = (x * (2 ^ y)) `mod` (primMaxFixnum + 1)

fixnumRshift :: Integer -> Integer -> Integer
fixnumRshift x y = (x `div` (2 ^ y)) `mod` (primMaxFixnum + 1)

fixnumOrb :: Integer -> Integer -> Integer
fixnumOrb x y = (x .|. y) `mod` (primMaxFixnum + 1)

fixnumAndb :: Integer -> Integer -> Integer
fixnumAndb x y = (x .&. y) `mod` (primMaxFixnum + 1)

fixnumXorb :: Integer -> Integer -> Integer
fixnumXorb x y = (x `xor` y) `mod` (primMaxFixnum + 1)

fixnumNotb :: Integer -> Integer
fixnumNotb x = (complement x) `mod` (primMaxFixnum + 1)

----

evalWith :: ContI -> ExprK -> EffectM AnswerI
evalWith cont expr =
    evalStateT (evalExpr initialEnv expr) initialState
  where
    initialState :: EvalState
    initialState = EvalState {
                     evNextFreshLocation = 0,
                     evStore = Map.empty
                   }
    initialEnv :: EnvI
    initialEnv = Map.fromList [
        (-1, FunctionI cont)
      ]

toplevelContinuation :: ContI
toplevelContinuation [x] = do
  lift (putStr (show x ++ "\n"))
  return answer

returnContinuation :: ContI
returnContinuation [x] = return x

eval :: ExprK -> IO ValueI
eval = evalWith returnContinuation

