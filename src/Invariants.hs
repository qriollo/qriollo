
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

module Invariants(exprKInvariant) where

import ExpressionK

-- Check invariants for the ExprK type

import Control.Monad(mapM_)
import qualified Data.Map as Map(
        Map, empty, fromList, member, insert, delete, lookup
    )
import Control.Monad.Trans.State.Lazy(
        StateT(..), get, put, modify, evalStateT
    )


data InvState = InvState {
                  iksArity :: Map.Map IdK Integer,
                  iksBound :: Map.Map IdK ()
                }
type InvM a = StateT InvState (Either String) a

-- invFail should be defined using lift, which seems to have a bug
-- this is a workaround
invFail :: String -> InvM a
invFail msg = StateT . const . Left $ msg

exprKInvariant :: ExprK -> Either String ()
exprKInvariant expr = evalStateT (inv expr) initialState
  where
    initialState :: InvState
    initialState = InvState {
                     iksArity = Map.fromList [
                       -- Toplevel continuation
                       (-1, 1)
                     ],
                     iksBound = Map.fromList [
                       -- Toplevel continuation
                       (-1, ())
                     ]
                   }
    inv :: ExprK -> InvM ()
    inv (RecordK vals id expr) = do
      mapM_ invV vals
      bind id
      inv expr
      unbind id
    inv (SelectK _ val id expr) = do
      invV val
      bind id
      inv expr
      unbind id
    inv (AppK val vals) = do
        checkArity val (fromIntegral (length vals))
        invV val
        mapM_ invV vals
      where
        checkArity :: ValueK -> Integer -> InvM ()
        checkArity (VarK f) n = do
          state <- get
          case Map.lookup f (iksArity state) of
            Nothing -> return () -- might be a variable
                                 -- not bound by a LetK
            Just n' -> if n == n'
                        then return ()
                        else invFail (
                               "La función " ++ show f ++ " espera " ++
                               show n' ++ " parámetros, " ++
                               "pero se le pasaron " ++ show n ++
                               " argumentos."
                             )
        checkArity _ _ = return ()
    inv (LetK decls expr) = do
        mapM_ bind (map declId decls)
        mapM_ declareArity decls
        mapM_ invDecl decls
        inv expr
        mapM_ unbind (map declId decls)
      where
        invDecl :: DeclarationK -> InvM ()
        invDecl (ValueDK _ params body) = do
          mapM_ bind params
          inv body
          mapM_ unbind params
        declareArity :: DeclarationK -> InvM ()
        declareArity (ValueDK f args _) =
          modify (\ state -> state {
            iksArity = Map.insert f (fromIntegral (length args))
                                  (iksArity state)
          })
    inv (SwitchK val exprs) = do
      invV val
      mapM_ inv exprs
    inv (PrimitiveK _ vals ids exprs) = do
      mapM_ invV vals
      mapM_ bind ids
      mapM_ inv exprs
      mapM_ unbind ids
    inv (ForeignK _ vals id expr) = do
      mapM_ invV vals
      bind id
      inv expr
      unbind id

    invV :: ValueK -> InvM ()
    invV (VarK x) = checkBound x
    invV _        = return ()

    declId :: DeclarationK -> IdK
    declId (ValueDK x _ _) = x

    isBound :: IdK -> InvM Bool
    isBound x = do
      state <- get
      return $ Map.member x (iksBound state)

    checkBound :: IdK -> InvM ()
    checkBound x = do
      b <- isBound x
      if b
       then return ()
       else invFail ("La variable " ++ show x ++ " no está ligada.")

    bind :: IdK -> InvM ()
    bind x = do
      b <- isBound x
      if b
       then invFail ("La variable " ++ show x ++ " ya está ligada.")
       else return ()
      modify (\ state -> state {
        iksBound = Map.insert x () (iksBound state)
      })

    unbind :: IdK -> InvM ()
    unbind x = do
      checkBound x
      modify (\ state -> state {
        iksBound = Map.delete x (iksBound state)
      })

