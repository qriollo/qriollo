
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

module CPS(cps, cpsOrFail, CpsOptions(..)) where

import qualified Data.Char as Char(ord)
import Data.Maybe(isNothing, maybeToList)
import qualified Data.Map as Map(Map, empty, insert, lookup, fromList)
import Data.List(sortBy, partition)
import Control.Applicative((<$>), (<*>))
import Control.Monad(zipWithM, zipWithM_, foldM)
import Control.Monad.Trans.State.Lazy(
        StateT(..), get, modify, runStateT,
    )

import ExpressionE
import ExpressionL
import ExpressionK
import Deps(Dependency(..), dependencySortL)

data CpsOptions = AllowRecursionOnData
                | DisallowRecursionOnData

data RenamingK = RenameTo IdK
               | RenameToRef IdK

type IdRenaming = Map.Map IdL RenamingK
data CpsState = CpsState {
    cpsOptions :: CpsOptions,
    cpsNextFreshId :: Integer,
    cpsIdRenaming :: IdRenaming
  }
type CpsM a = StateT CpsState (Either String) a

-- cpsFail should be defined using lift, which seems to have a bug
-- this is a workaround
cpsFail :: String -> CpsM a
cpsFail = StateT . const . Left

cpsSetRenaming :: IdL -> RenamingK -> CpsM ()
cpsSetRenaming idL renK = do
  state <- get
  case Map.lookup idL (cpsIdRenaming state) of
    Just _  -> cpsFail ("IdL ya ligado: " ++ show idL)
    Nothing -> return ()
  modify (\ state -> 
    state {
      cpsIdRenaming =
        Map.insert idL renK (cpsIdRenaming state)
    })

cpsGetRenaming :: IdL -> CpsM RenamingK
cpsGetRenaming idL = do
  state <- get
  case Map.lookup idL (cpsIdRenaming state) of
    Nothing   -> cpsFail ("IdL no ligado para renombrar: " ++ show idL)
    Just renK -> return renK

cpsFreshIdK :: CpsM IdK
cpsFreshIdK = do
  state <- get
  modify (\ state ->
    state {
      cpsNextFreshId = 1 + cpsNextFreshId state
    })
  return $ cpsNextFreshId state

matchLinearSearchThreshold :: Integer
matchLinearSearchThreshold = 3

matchDensityThreshold :: Integer
matchDensityThreshold = 2

cpsMatch :: ExprL -> (ValueK -> CpsM ExprK) -> CpsM ExprK
cpsMatch (MatchL span e branches o) k =
    cpsExpr e (\ v -> compileMatch span v branches o k)
  where
    compileMatch :: MatchLSpan -> ValueK -> [MatchBranchL] -> Maybe ExprL ->
                    (ValueK -> CpsM ExprK) -> CpsM ExprK
    compileMatch _ _ [] Nothing k =
      error "(cpsMatch: el match no es exhaustivo)"
    compileMatch _ _ [MatchBranchL _ e] Nothing k =
      cpsExpr e k
    compileMatch _ _ [] (Just e) k =
      cpsExpr e k
    compileMatch _ _ (MatchBranchL (DataConstructor UntaggedCR) e : _) _ k =
      cpsExpr e k
    compileMatch _ _ (MatchBranchL (DataConstructor TransparentCR) e : _) _ k =
      cpsExpr e k
    compileMatch _ _ (MatchBranchL (DataConstructor RefCR) e : _) _ k =
      cpsExpr e k

    compileMatch span scrutinee branches ow k = do
      contVar <- cpsFreshIdK
      contX   <- cpsFreshIdK
      kContX  <- k (VarK contX)

      (mOwVar, owDecl)  <-
        case ow of
          Nothing     -> return (Nothing, [])
          Just owExpr -> do
            owVar   <- cpsFreshIdK
            owK     <- cpsFreshIdK
            owExpr' <- cpsExpr owExpr
                               (\ val -> return $ AppK (VarK owK) [val])
            return (Just owVar, [ValueDK owVar [owK] owExpr'])

      (checkBoxity, branches') <-
        if involvesSafeUntaggedCR span
         then
           let (boxedBranch_0_or_1, unboxedBranches) =
                 partition isSafeUntaggedBranch branches in do
             exprKBoxed <- compileSafeUntaggedMatch
                             boxedBranch_0_or_1 mOwVar contVar
             return (
                   \ exprKUnboxed ->
                     PrimitiveK PrimBoxed [scrutinee] [] [
                       exprKBoxed,
                       exprKUnboxed
                     ],
                   unboxedBranches)
         else return (id, branches)

      tagVar  <- cpsFreshIdK
      result <- compileMatch' tagVar branches' mOwVar contVar
      return $
        LetK ([ValueDK contVar [contX] kContX] ++ owDecl) $
        checkBoxity $
        PrimitiveK PrimTag [scrutinee] [tagVar] [result]
 
    compileMatch' :: IdK -> [MatchBranchL] -> Maybe IdK -> IdK -> CpsM ExprK
    compileMatch' tagVar branches mOwVar k | shouldSwitch branches =
      switchBranches tagVar branches mOwVar k
    compileMatch' tagVar branches mOwVar k | shouldBinarySearch branches =
      binarySearch tagVar branches mOwVar k
    compileMatch' tagVar branches mOwVar contVar =
      linearSearch tagVar branches mOwVar contVar

    compileSafeUntaggedMatch :: [MatchBranchL] -> Maybe IdK -> IdK ->
                                CpsM ExprK
    compileSafeUntaggedMatch
        (MatchBranchL (DataConstructor SafeUntaggedCR) e : _) _ kvar =
      cpsExpr e (\ val -> return $ AppK (VarK kvar) [val])
    compileSafeUntaggedMatch [] (Just owVar) kvar =
      return $ AppK (VarK owVar) [VarK kvar]

    -- Switch

    shouldSwitch :: [MatchBranchL] -> Bool
    shouldSwitch branches =
        nBranches > matchLinearSearchThreshold &&
        mapsToInt (head branches) &&
        dense
      where
        minTag, maxTag :: Integer
        minTag = minimum branchTags
        maxTag = maximum branchTags
        branchTags :: [Integer]
        branchTags = map branchTag branches
        arraySize :: Integer
        arraySize = maxTag - minTag + 1
        dense :: Bool
        dense = matchDensityThreshold * nBranches >= arraySize
        nBranches :: Integer
        nBranches = fromIntegral (length branches) 

    branchTag :: MatchBranchL -> Integer
    branchTag (MatchBranchL constructor _) = constructorTag constructor

    involvesSafeUntaggedCR :: MatchLSpan -> Bool
    involvesSafeUntaggedCR MatchLSpansConstants         = False
    involvesSafeUntaggedCR (MatchLSpansConstructors cs) =
      not (null (filter isSafeUntaggedCR cs))

    isSafeUntaggedBranch :: MatchBranchL -> Bool
    isSafeUntaggedBranch (MatchBranchL (DataConstructor conrep) _) =
      isSafeUntaggedCR conrep

    isSafeUntaggedCR :: ConstructorRepresentation -> Bool
    isSafeUntaggedCR SafeUntaggedCR = True
    isSafeUntaggedCR _              = False

    switchBranches :: IdK -> [MatchBranchL] -> Maybe IdK -> IdK -> CpsM ExprK
    switchBranches tagVar branches mOwVar contVar = do
        indexVar  <- cpsFreshIdK
        branches' <- mapM cpsBranch [minTag..maxTag]
        return $ checkBoundaries mOwVar $ 
          PrimitiveK
            PrimFixnumSub [VarK tagVar, cMinTag]
            [indexVar]
            [SwitchK (VarK indexVar) branches']
      where
        taggedBranches :: Map.Map Integer MatchBranchL
        taggedBranches = Map.fromList $
          map (\ branch -> (branchTag branch, branch)) branches

        minTag, maxTag :: Integer
        minTag = minimum branchTags
        maxTag = maximum branchTags

        cMinTag, cMaxTag :: ValueK
        cMinTag = ConstantK (FixnumC minTag)
        cMaxTag = ConstantK (FixnumC maxTag)

        branchTags :: [Integer]
        branchTags = map branchTag branches

        cpsBranch :: Integer -> CpsM ExprK
        cpsBranch i = case Map.lookup i taggedBranches of
          Just (MatchBranchL _ e) ->
            cpsExpr e (\ val -> return $ AppK (VarK contVar) [val])
          Nothing -> return $ defaultCont mOwVar

        checkBoundaries :: Maybe IdK -> ExprK -> ExprK
        checkBoundaries Nothing      expr = expr
        checkBoundaries (Just owVar) expr =
            PrimitiveK PrimFixnumLe [cMinTag, VarK tagVar] [] [
              PrimitiveK PrimFixnumLe [VarK tagVar, cMaxTag] [] [
                expr,
                AppK (VarK owVar) [VarK contVar]
              ],
              AppK (VarK owVar) [VarK contVar]
            ]

        defaultCont :: Maybe IdK -> ExprK
        defaultCont Nothing      = AppK (VarK contVar) [ConstantK (FixnumC 0)]
        defaultCont (Just owVar) = AppK (VarK owVar) [VarK contVar]

    -- Binary search

    shouldBinarySearch :: [MatchBranchL] -> Bool
    shouldBinarySearch branches =
        fromIntegral (length branches) > matchLinearSearchThreshold &&
        mapsToInt (head branches)

    binarySearch :: IdK -> [MatchBranchL] -> Maybe IdK -> IdK -> CpsM ExprK
    binarySearch tagVar branches mOwVar contVar = do
        exprL <- compileMatch' tagVar branchesL mOwVar contVar
        exprU <- compileMatch' tagVar branchesU mOwVar contVar
        return $ PrimitiveK PrimFixnumLe [cMedianValue, VarK tagVar] [] [
           exprU,
           exprL
         ]
      where
        sortedBranches :: [MatchBranchL]
        sortedBranches = sortBy compareBranches branches
        compareBranches :: MatchBranchL -> MatchBranchL -> Ordering
        compareBranches b1 b2 = branchTag b1 `compare` branchTag b2
        branchesL, branchesU :: [MatchBranchL]
        (branchesL, branchesU) = splitAt (length branches `div` 2)
                                         sortedBranches 
        medianValue :: Integer
        medianValue = branchTag (head branchesU)

        cMedianValue :: ValueK
        cMedianValue = ConstantK (FixnumC medianValue)

    -- Linear search

    linearSearch :: IdK -> [MatchBranchL] -> Maybe IdK -> IdK -> CpsM ExprK
    linearSearch tagVar branches mOwVar contVar = rec branches
      where
        rec :: [MatchBranchL] -> CpsM ExprK
        rec [] = case mOwVar of
          Nothing    -> error "(cpsMatch: match sin ramas y sin else)"
          Just owVar -> return $ AppK (VarK owVar) [VarK contVar]
        rec [MatchBranchL _ e] | isNothing mOwVar =
          cpsExpr e (\ val -> return $ AppK (VarK contVar) [val])
        rec (MatchBranchL constructor e : branches) = do
            b1 <- cpsExpr e (\ val -> return $ AppK (VarK contVar) [val])
            b2 <- rec branches
            return $ PrimitiveK PrimFixnumEq [VarK tagVar, tagCon] [] [b1, b2]
          where
            tagCon = ConstantK (FixnumC (constructorTag constructor))
    --

    mapsToInt :: MatchBranchL -> Bool
    mapsToInt (MatchBranchL (DataConstructor (TaggedCR _)) _)     = True
    mapsToInt (MatchBranchL (DataConstructor (ConstantCR _)) _)   = True
    mapsToInt (MatchBranchL (ConstantConstructor (FixnumC _)) _) = True
    mapsToInt (MatchBranchL (ConstantConstructor (CharC _)) _)    = True
    mapsToInt _ = False

    constructorTag :: Constructor -> Integer
    constructorTag (DataConstructor (TaggedCR n))     = n
    constructorTag (DataConstructor (ConstantCR n))   = n
    constructorTag (ConstantConstructor (FixnumC n)) = n
    constructorTag (ConstantConstructor (CharC c))    =
      fromIntegral $ Char.ord c

cpsExpr :: ExprL -> (ValueK -> CpsM ExprK) -> CpsM ExprK
cpsExpr (VarL x) k = do
  renX <- cpsGetRenaming x
  case renX of
    RenameTo x'       -> k (VarK x')
    RenameToRef x' -> do
      y' <- cpsFreshIdK
      ky <- k (VarK y')
      return $ PrimitiveK PrimDeref [VarK x'] [y'] [ky]
cpsExpr (ConstantL c) k = k (ConstantK c)
cpsExpr (LamL x b) k = do
  f  <- cpsFreshIdK 
  ki <- cpsFreshIdK 
  x' <- cpsFreshIdK 
  cpsSetRenaming x (RenameTo x')
  b' <- cpsExpr b (\ val -> return $ AppK (VarK ki) [val])
  LetK [ValueDK f [ki, x'] b'] <$> k (VarK f)
cpsExpr (AppL e1 e2) k = do
  rk <- cpsFreshIdK
  rx <- cpsFreshIdK
  krx <- k (VarK rx)
  LetK [ValueDK rk [rx] krx] <$>
    cpsExpr e1 (\ r1 ->
      cpsExpr e2 (\ r2 -> do
        return $ AppK r1 [VarK rk, r2]))
cpsExpr (LetL decls e) k = do
    cpsDecls (dependencySortL decls) e k
  where
    cpsDecls :: [Dependency DeclarationL] -> ExprL ->
                (ValueK -> CpsM ExprK) -> CpsM ExprK
    cpsDecls [] e k = cpsExpr e k
    cpsDecls (DpAcyclic (ValueDL x e1) : moreDecls) e2 k = do
      cpsExpr e1 (\ r1 -> do
        rk <- cpsFreshIdK
        rx <- cpsFreshIdK
        f  <- cpsFreshIdK
        ki <- cpsFreshIdK
        x' <- cpsFreshIdK
        cpsSetRenaming x (RenameTo x')
        b <- cpsDecls moreDecls e2 (\ val -> return $ AppK (VarK ki) [val])
        krx <- k (VarK rx)
        return $
          LetK [ValueDK rk [rx] krx] $
            LetK [ValueDK f [ki, x'] b] $ 
              AppK (VarK f) [VarK rk, r1])

    cpsDecls (DpFunctions decls : moreDecls) e k = do
        freshNames <- mapM freshIdsForDecl decls 
        zipWithM_ declareRenamings decls freshNames
        funcDecls <- zipWithM functionDeclsList decls freshNames
        body <- cpsDecls moreDecls e k
        body' <- assignReferences decls freshNames body
        declareReferences decls freshNames $
          LetK (concat funcDecls) $
          body'
      where
        freshIdsForDecl :: DeclarationL -> CpsM [IdK]
        -- Function declaration
        freshIdsForDecl (ValueDL _ (LamL _ _)) = do
           id1 <- cpsFreshIdK
           id2 <- cpsFreshIdK
           id3 <- cpsFreshIdK
           return [id1, id2, id3]
        -- Non-function declaration
        freshIdsForDecl _ = do
           state <- get
           case cpsOptions state of
             AllowRecursionOnData -> do
               id1 <- cpsFreshIdK
               return [id1]
             DisallowRecursionOnData ->
               cpsFail (
                 "Que te ayude Montoto.\n" ++
                 "La recursión en estructuras de datos está deshabilitada."
               )

        declareRenamings :: DeclarationL -> [IdK] -> CpsM ()
        -- Function declaration
        declareRenamings (ValueDL x (LamL y _)) [x', _, y'] = do
          cpsSetRenaming x (RenameTo x')
          cpsSetRenaming y (RenameTo y')
        -- Non-function declaration
        declareRenamings (ValueDL x _) [x'] =
          cpsSetRenaming x (RenameToRef x')

        functionDeclsList :: DeclarationL -> [IdK] -> CpsM [DeclarationK]
        -- Function declaration
        functionDeclsList (ValueDL x (LamL y b)) [x', k, y'] = do
          b' <- cpsExpr b (\ val -> return $ AppK (VarK k) [val])
          return [ValueDK x' [k, y'] b']
        -- Non-function declaration
        functionDeclsList _ _ = return []

        ziprm :: (a -> b -> c -> CpsM c) -> [a] -> [b] -> c -> CpsM c
        ziprm f []     []     x = return x
        ziprm f (a:as) (b:bs) x = do
          y <- ziprm f as bs x
          f a b y

        declareReferences :: [DeclarationL] -> [[IdK]] -> ExprK -> CpsM ExprK
        declareReferences decls freshNames expr =
            ziprm declareReference decls freshNames expr
          where
            declareReference :: DeclarationL -> [IdK] -> ExprK -> CpsM ExprK
            -- Function declaration
            declareReference (ValueDL _ (LamL _ _)) _ expr = return expr
            -- Non-function declaration
            declareReference (ValueDL x _) [x'] expr =
              return $
                PrimitiveK PrimRef [ConstantK (FixnumC 0)] [x'] [expr]

        assignReferences :: [DeclarationL] -> [[IdK]] -> ExprK -> CpsM ExprK
        assignReferences decls freshNames expr = do
            ziprm assignReference decls freshNames expr
          where
            assignReference :: DeclarationL -> [IdK] -> ExprK -> CpsM ExprK
            -- Function declaration
            assignReference (ValueDL _ (LamL _ _)) _ expr = return expr
            -- Non-function declaration
            assignReference (ValueDL x exprX) [x'] expr =
              cpsExpr exprX (\ val -> do
                y <- cpsFreshIdK
                return $ PrimitiveK PrimAssign [VarK x', val] [y] [expr])

    isFunctionDeclaration :: DeclarationL -> Bool
    isFunctionDeclaration (ValueDL _ (LamL _ _)) = True
    isFunctionDeclaration _                      = False

cpsExpr match@(MatchL _ _ _ _) k = cpsMatch match k 
cpsExpr (RecordL []) k = k (ConstantK $ FixnumC 0) 
cpsExpr (RecordL es) k =
  cpsExprList es $ \ vs -> do
    r <- cpsFreshIdK
    RecordK vs r <$> k (VarK r)
cpsExpr (SelectL i e) k = do
  cpsExpr e $ \ v -> do
    r <- cpsFreshIdK
    SelectK i v r <$> k (VarK r)
cpsExpr (PrimitiveL PrimContinuationCallCC [e]) k = do
  cpsExpr e $ \ func -> do
    rk  <- cpsFreshIdK
    rx  <- cpsFreshIdK
    krx <- k (VarK rx)
    return $
      LetK [
        ValueDK rk [rx] krx
      ] $
      AppK func [VarK rk, VarK rk]
cpsExpr (PrimitiveL PrimContinuationThrow es) k = do
  cpsExprList es $ \ [cont, val] ->
    return $ AppK cont [val]
cpsExpr (PrimitiveL p es) k
  | nBranches == 1 =
      cpsExprList es $ \ vs -> do
        x  <- cpsFreshIdK
        kx <- k (VarK x)
        return $ PrimitiveK p vs [x] [kx]
  | nBranches > 1 =
      cpsExprList es $ \ vs -> do
        rk  <- cpsFreshIdK
        rx  <- cpsFreshIdK
        krx <- k (VarK rx)
        return $
          LetK [
            ValueDK rk [rx] krx
          ] $
          PrimitiveK p vs []
            (map (\ i -> AppK (VarK rk) [ConstantK $ FixnumC i])
                 [0..nBranches - 1])
  where
    nBranches = paBranches (primopArity p)
cpsExpr (ForeignL sig es) k =
  cpsExprList es $ \ vs -> do
    x  <- cpsFreshIdK
    kx <- k (VarK x)
    return $ ForeignK sig vs x kx

cpsExprList :: [ExprL] -> ([ValueK] -> CpsM ExprK) -> CpsM ExprK
cpsExprList es kk = rec es [] kk
  where
    rec :: [ExprL] -> [ValueK] -> ([ValueK] -> CpsM ExprK) -> CpsM ExprK
    rec (e : es) values kk =
      cpsExpr e (\ v -> rec es (v : values) kk)
    rec [] values kk = kk (reverse values)

cps :: CpsOptions -> ExprL -> Either String ExprK
cps cpsOpts e =
    case runStateT (cpsExpr e (\ v -> return $ retK v)) initialState of
      Left msg     -> Left msg
      Right (e, _) -> Right e
  where
    initialState = CpsState {
       cpsOptions = cpsOpts,
       cpsNextFreshId = 0,
       cpsIdRenaming = Map.empty
     }

cpsOrFail :: CpsOptions -> ExprL -> ExprK
cpsOrFail cpsOpts e = case cps cpsOpts e of
                Left msg     -> error msg
                Right result -> result

