
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

module Compress(compress) where

import Control.Monad.Trans.State.Lazy(State, get, modify, runState)
import qualified Data.Map as Map(Map, empty, insert, lookup)
import Control.Applicative((<$>))

import ExpressionK

data CompressState = CompressState {
                       cmpChanges :: Integer,
                       cmpCache :: Map.Map ([IdK], ExprK) IdK,
                       cmpReplacements :: Map.Map IdK IdK
                     }
type CompressM = State CompressState

compress :: ExprK -> ExprK
compress expr = compressFixpoint expr
  where
    compressFixpoint :: ExprK -> ExprK
    compressFixpoint expr = do
      let (expr', state) = runState (compressExpr expr) initialState
       in
         if cmpChanges state == 0
          then expr
          else compressFixpoint expr'

    initialState :: CompressState
    initialState = CompressState {
                     cmpChanges = 0,
                     cmpCache = Map.empty,
                     cmpReplacements = Map.empty
                   }

    compressExpr :: ExprK -> CompressM ExprK
    compressExpr (LetK decls expr) = do
      decls'  <- compressDecls decls
      decls'' <- mapM replaceLabelsD decls'
      expr'   <- replaceLabels expr
      return $ LetK decls'' expr'
    compressExpr expr = return expr

    compressDecls :: [DeclarationK] -> CompressM [DeclarationK]
    compressDecls decls = do
      declsList <- mapM compressDecl decls
      return $ concat declsList

    click :: CompressM ()
    click = modify (\ state -> state {
              cmpChanges = cmpChanges state + 1
            })

    compressDecl :: DeclarationK -> CompressM [DeclarationK]
    compressDecl decl@(ValueDK id args expr) = do
      state <- get
      case Map.lookup (args, expr) (cmpCache state) of
        Just id2 -> do
          click
          modify (\ state -> state {
            cmpReplacements = Map.insert
                                id
                                id2
                                (cmpReplacements state)
          })
          return []
        Nothing -> do
          modify (\ state -> state {
            cmpCache = Map.insert (args, expr) id (cmpCache state)
          })
          return [decl]

    replaceLabels :: ExprK -> CompressM ExprK
    replaceLabels (RecordK vals id expr) = do
      vals' <- mapM replaceLabelsV vals 
      RecordK vals' id <$> replaceLabels expr
    replaceLabels (SelectK n val id expr) = do
      val' <- replaceLabelsV val
      SelectK n val' id <$> replaceLabels expr
    replaceLabels (AppK val vals) = do
      val'  <- replaceLabelsV val
      vals' <- mapM replaceLabelsV vals
      return $ AppK val' vals'
    replaceLabels (LetK _ _) =
      error "(compress: no debería encontrar un LetK)"
    replaceLabels (SwitchK val exprs) = do
      val' <- replaceLabelsV val
      SwitchK val' <$> mapM replaceLabels exprs
    replaceLabels (PrimitiveK p vals ids exprs) = do
      vals' <- mapM replaceLabelsV vals
      PrimitiveK p vals' ids <$> mapM replaceLabels exprs
    replaceLabels (ForeignK sig vals id expr) = do
      vals' <- mapM replaceLabelsV vals
      ForeignK sig vals' id <$> replaceLabels expr

    replaceLabelsV :: ValueK -> CompressM ValueK
    replaceLabelsV (LabelK id) = do
      state <- get
      case Map.lookup id (cmpReplacements state) of
        Just id2 -> return $ LabelK id2
        Nothing  -> return $ LabelK id
    replaceLabelsV val = return val

    replaceLabelsD :: DeclarationK -> CompressM DeclarationK
    replaceLabelsD (ValueDK id args expr) =
      ValueDK id args <$> replaceLabels expr

