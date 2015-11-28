
module Reader(
        ReaderOptions(..),
        readPackage, readPackageOrFail, readFromStrings, readFromStringsOrFail,
    ) where

import System.Directory(doesFileExist)
import System.IO(FilePath, openFile, IOMode(..))
import qualified Data.Map as Map(fromList, findWithDefault)

import ExpressionE(joinS, QualifId(..), PackageName)
import Position(packageToFilename)
import Lexer(Token(..), TokenType(..), tokenize, packageFor)
import Deps(Graph, graphFromList, topoSort, transpose)

data ReaderOptions = ReaderOptions {
                       rdoPath :: [String]
                     }

readPackage :: ReaderOptions -> PackageName ->
               IO (Either String [(PackageName, [Token])])
readPackage options package = do
    mPackages <- readPackage1 package []
    case mPackages of
      Left msg       -> return $ Left msg
      Right packages -> do
        let ordering =
              topoSort . transpose .  graphFromList .
              dependencyGraph $ packages
         in
          return $ Right $ sortByOrdering ordering packages
  where
    readPackage1 :: PackageName -> [(PackageName, [Token])] ->
                    IO (Either String [(PackageName, [Token])])
    readPackage1 package result =
      readPackageWithPath (rdoPath options) package result

    readPackageWithPath :: [String] -> PackageName ->
                           [(PackageName, [Token])] ->
                           IO (Either String [(PackageName, [Token])])
    readPackageWithPath [] package result =
        return $ Left ("No se puede encontrar el archivo " ++
                       packageToFilename package ++ ", salame.\n" ++
                       "Los directorios donde se buscan los módulos son:\n" ++
                       "    " ++ joinS "\n    " (rdoPath options) ++ "\n")
    readPackageWithPath (path : paths) package result =
      let filename = path ++ "/" ++ packageToFilename package in do
        ex <- doesFileExist filename
        if not ex
         then
           readPackageWithPath paths package result
         else do
           contents <- readFile filename
           case tokenize package contents of
             Left msg -> return $ Left msg
             Right tokens -> do
               readPackages (importedPackages tokens)
                            ((package, tokens) : result)

    readPackages :: [PackageName] -> [(PackageName, [Token])] ->
                    IO (Either String [(PackageName, [Token])])
    readPackages []                   result = return $ Right result
    readPackages (package : packages) result =
      if package `elem` map fst result
       then readPackages packages result
       else do
         result' <- readPackage1 package result
         case result' of
           Left msg       -> return $ Left msg
           Right result'' -> readPackages packages result''

    dependencyGraph :: [(PackageName, [Token])] ->
                       [(PackageName, [PackageName])]
    dependencyGraph packages = map dependencies packages

    dependencies :: (PackageName, [Token]) -> (PackageName, [PackageName])
    dependencies (package, toks) = (package, importedPackages toks)

    importedPackages :: [Token] -> [PackageName]
    importedPackages [] = []
    importedPackages
      (Token T_Enchufar _ : Token (T_Upperid qualif ident) _ : toks) =
      packageFor (QualifId qualif ident) : importedPackages toks
    importedPackages (_ : toks) = importedPackages toks

    sortByOrdering :: Ord a => [a] -> [(a, b)] -> [(a, b)]
    sortByOrdering ordering dict =
      let dict' = Map.fromList dict in
        map (\ key -> (key, Map.findWithDefault (error "") key dict'))
            ordering

readPackageOrFail :: ReaderOptions -> PackageName -> IO [(PackageName, [Token])]
readPackageOrFail options package = do
  p <- readPackage options package
  case p of
    Left msg -> error msg
    Right x  -> return x

readFromStrings :: [(PackageName, String)] ->
                   Either String [(PackageName, [Token])]
readFromStrings = mapM tok
  where
    tok :: (PackageName, String) -> Either String (PackageName, [Token])
    tok (package, contents) = do
      toks <- tokenize package contents
      return (package, toks)

readFromStringsOrFail :: [(PackageName, String)] -> [(PackageName, [Token])]
readFromStringsOrFail ps =
  case readFromStrings ps of
    Left msg -> error msg
    Right x  -> x

