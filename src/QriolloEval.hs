
module QriolloEval(
        evalString, evalStringAsString, evalPackages,
        inferPackages,
        compilePackages,
        stringValueToString,
        OptionsQ, OptionQ(..),
    ) where

import Data.Char(toUpper)
import qualified Data.Map as Map(
        Map, empty, member, notMember, lookup, findWithDefault
    )
import Control.Applicative((<$>))
import System.IO(openBinaryFile, IOMode(..), hPutStr, hClose)

import Position(stringToPackageName)
import Primitive(primMain)
import ExpressionE
import ExpressionK
import Invariants(exprKInvariant)
import Lexer(Token)
import Parser(ParserOptions(..),
              parsePackagesWithPragmas, parseFromStringOrFail)
import Infer(infer, inferOrFail, InferOptions(..))
import Precompiler(precompile, precompileOrFail)
import CPS(cps, cpsOrFail, CpsOptions(..))
import Eval(eval, ValueI(..))
import Optim(optimizeExpr, OptimOptions(..), contractUntilNoChanges)
import Closure(closureConvert)
import RegAlloc(allocateRegisters, assignRegisters)
import Compress(compress)
import Backend.Py(
        compileToPy,
        PyOptions(..), PyOptionsMangling(..), PyOptionsToplevel(..),
    )
import Backend.Jvm(
        compileToJvm,
        JvmOptions(..), JvmOptionsToplevel(..),
    )
import Backend.C(compileToC)

type OptionsQ = Map.Map OptionQ String 

data OptionQ =
      OptQ_CheckInternalInvariants
    | OptQ_Compile
    | OptQ_DisallowRecursionOnData
    | OptQ_EnforceValueRestriction
    | OptQ_Interactive
    | OptQ_Input
    | OptQ_FeatureList
    | OptQ_MainName
    | OptQ_NoClosureConversion
    | OptQ_NoRegAlloc
    | OptQ_NoRegAssign
    | OptQ_NoRun
    | OptQ_OnlyType
    | OptQ_OptimizationRounds
    | OptQ_OptimizeForSpace
    | OptQ_OutputFile
    | OptQ_OutputLanguage
    | OptQ_ShowAst
    | OptQ_ShowClosedExpression
    | OptQ_ShowCPSExpression
    | OptQ_ShowOptimizedExpression
    | OptQ_ShowPrecompiledExpression
    | OptQ_ShowRegAllocExpression
    | OptQ_ShowRegAssigExpression
    | OptQ_ShowTypedAst
    | OptQ_ShowValue
    | OptQ_PyOptionsToplevel
    | OptQ_JvmOptionsToplevel
    | OptQ_Path
  deriving (Show, Eq, Ord)

globalPackage :: PackageName
globalPackage = ["Input"]

parserOptionsFor :: OptionsQ -> ParserOptions
parserOptionsFor options =
    ParserOptions {
      parserOptionsFeatures =
        featureCompiled ++
        featurePython ++
        featureJvm ++
        featureC ++
        words (Map.findWithDefault "" OptQ_FeatureList options)
    }
  where
    featureCompiled :: [String]
    featureCompiled
      | Map.member OptQ_Compile options = ["Compilado"]
      | otherwise = []

    featurePython :: [String]
    featurePython 
      | Map.findWithDefault "" OptQ_OutputLanguage options == "Py" = ["Py"]
      | otherwise = []

    featureJvm :: [String]
    featureJvm 
      | Map.findWithDefault "" OptQ_OutputLanguage options == "Jvm" = ["Jvm"]
      | otherwise = []

    featureC :: [String]
    featureC 
      | Map.findWithDefault "" OptQ_OutputLanguage options == "C" = ["C"]
      | otherwise = []

evalString :: OptionsQ -> Id -> String -> IO ValueI
evalString options mainName string = do
    let exprK = cpsOrFail (recursionOnData options) .
                precompileOrFail .
                fst . inferOrFail (valueRestriction options) .
                parseFromStringOrFail (parserOptionsFor options)
                                      globalPackage mainName $
                string
      in do
        exprKOpt <- optimizeOrFail options exprK
        eval exprKOpt

-- The program must return a string, i.e. a list of characters
evalStringAsString :: OptionsQ -> Id -> String -> IO String
evalStringAsString options mainName string =
  stringValueToString <$> evalString options mainName string

stringValueToString :: ValueI -> String
stringValueToString (ConstantI (FixnumC 0)) = ""
stringValueToString (RecordI [ConstantI (CharC c), s]) =
  c : stringValueToString s

orDie :: Either String a -> (a -> IO (Either String b)) ->
         IO (Either String b)
orDie (Left msg) f = return (Left msg)
orDie (Right x)  f = f x

mainName :: OptionsQ -> Id
mainName options = case Map.lookup OptQ_MainName options of
                     Nothing -> primMain
                     Just m  -> m

optimize :: OptionsQ -> ExprK -> IO (Either String ExprK)
optimize options exprK =
    case reads nRoundsString of
      [(nRounds, _)] ->
        return $ Right $ optimizeExpr (optimizeSpace options) nRounds exprK
      _ ->
        return $ Left (
          "El número de rondas de optimización está mal:\n    " ++
          nRoundsString ++ "\nno es un número."
         )
  where
    nRoundsString :: String
    nRoundsString = Map.findWithDefault "1" OptQ_OptimizationRounds options
    optimizeSpace :: OptionsQ -> OptimOptions
    optimizeSpace options
      | Map.member OptQ_OptimizeForSpace options = OptimizeForSpace
      | otherwise = OptimizeForTime

optimizeOrFail :: OptionsQ -> ExprK -> IO ExprK
optimizeOrFail options exprK = do
  mRes <- optimize options exprK
  case mRes of
    Left msg -> error msg
    Right x  -> return x

valueRestriction :: OptionsQ -> InferOptions
valueRestriction options
  | Map.member OptQ_EnforceValueRestriction options = EnforceValueRestriction
  | otherwise = DoNotEnforceValueRestriction

recursionOnData :: OptionsQ -> CpsOptions
recursionOnData options
  | Map.member OptQ_DisallowRecursionOnData options = DisallowRecursionOnData
  | otherwise = AllowRecursionOnData

showIf :: Show a => OptionsQ -> OptionQ -> a -> IO ()
showIf options option value
  | Map.member option options = putStrLn $ show value
  | otherwise                 = return ()

compileAndOptimize :: OptionsQ -> [(PackageName, [Token])] ->
                      IO (Either String ([Pragma], ExprK))
compileAndOptimize options packages =
    parsePackagesWithPragmas (parserOptionsFor options)
                             packages
                             (mainName options)
                                         `orDie` \ (pragmas, ast) -> do
    let resultIs expr = return $ Right (pragmas, compress expr)
     in do
      showIf options OptQ_ShowAst (eraseAnnotations ast)

      infer (valueRestriction options) ast      `orDie` \ (ast', _) -> do
      showIf options OptQ_ShowTypedAst (eraseAnnotations ast')

      precompile ast'                           `orDie` \ exprL     -> do
      showIf options OptQ_ShowPrecompiledExpression exprL

      cps (recursionOnData options) exprL       `orDie` \ exprK     -> do
      showIf options OptQ_ShowCPSExpression exprK

      checkExprKInvariant "expresión CPS" exprK `orDie` \ _         -> do

      mExprKOpt <- optimize options exprK
      mExprKOpt                                 `orDie` \ exprOpt   -> do
      showIf options OptQ_ShowOptimizedExpression exprOpt

      checkExprKInvariant "expresión optimizada" exprOpt
                                                `orDie` \ _         -> do

      if Map.member OptQ_NoClosureConversion options
       then resultIs exprOpt
       else do
         Right (closureConvert exprOpt)            `orDie` \ exprClo   -> do

         showIf options OptQ_ShowClosedExpression exprClo
         checkExprKInvariant "expresión clausurada" exprClo
                                                   `orDie` \ _         -> do

         if Map.member OptQ_NoRegAlloc options
          then resultIs exprClo
          else do
           Right (allocateRegisters numRegisters exprClo)
                                                   `orDie` \ exprAlloc -> do
           showIf options OptQ_ShowRegAllocExpression exprAlloc
           checkExprKInvariant "expresión reservada" exprAlloc
                                                   `orDie` \ _         -> do

           if Map.member OptQ_NoRegAssign options
            then resultIs exprAlloc
            else do
              Right (assignRegisters numRegisters exprAlloc)
                                                   `orDie` \ exprAssign -> do
              showIf options OptQ_ShowRegAssigExpression exprAssign

              resultIs exprAssign
  where
    checkExprKInvariant :: String -> ExprK -> Either String ()
    checkExprKInvariant description expr = do
      if Map.member OptQ_CheckInternalInvariants options
       then
         case exprKInvariant expr of
           Left msg ->
             Left (
               "No se cumplen los invariantes para " ++ description ++ "\n" ++
               msg
             )
           Right _ -> Right ()
       else Right ()
    numRegisters :: Integer
    numRegisters = 8

writeBinaryFile :: String -> String -> IO()
writeBinaryFile filename contents = do
  h <- openBinaryFile filename WriteMode
  hPutStr h contents
  hClose h

generateCode :: OptionsQ -> [Pragma] -> String -> ExprK ->
                IO (Either String String)
generateCode options pragmas "Py" expr = do
    let pySource = compileToPy pyOptions pragmas expr in
      case Map.findWithDefault "-" OptQ_OutputFile options of
        "-"        -> return $ Right pySource
        pyFilename -> do
          writeFile pyFilename pySource
          return $ Right ""
  where
    pyOptions :: PyOptions
    pyOptions = PyOptions {
                  pyoMangling = PyOpt_MinimalMangling,
                  pyoToplevel =
                    read (Map.findWithDefault "PyOpt_ToplevelExit"
                                              OptQ_PyOptionsToplevel
                                              options)
                }

generateCode options pragmas "Jvm" expr = do
    writeBinaryFile jarName (compileToJvm jvmOptions pragmas className expr)
    return $ Right ""
  where
    jvmOptions :: JvmOptions
    jvmOptions = JvmOptions {
                   jvoToplevel =
                    read (Map.findWithDefault "JvmOpt_ToplevelExit"
                                              OptQ_JvmOptionsToplevel
                                              options)
                 }

    jarName :: String
    jarName = Map.findWithDefault (className ++ ".jar")
                                  OptQ_OutputFile
                                  options

    className :: String
    className = toJvmClassName
                  (Map.findWithDefault defaultClassName OptQ_Input options)

    toJvmClassName :: String -> String
    toJvmClassName inputFileName =
        let cls = dropWhile (not . isAlpha) .
                  filter isAlnum .
                  last .
                  stringToPackageName $ inputFileName
         in
           if null cls
            then defaultClassName
            else [toUpper (head cls)] ++ tail cls
      where
        isAlpha, isAlnum :: Char -> Bool
        isAlpha c = ('a' <= c && c <= 'z') ||
                    ('A' <= c && c <= 'Z')
        isAlnum c = isAlpha c || c == '_' || ('0' <= c && c <= '9')

    defaultClassName :: String
    defaultClassName = "Chorizo"

generateCode options pragmas "C" expr =
    let cSource = compileToC pragmas expr
     in
       case Map.findWithDefault "-" OptQ_OutputFile options of
         "-"        -> return $ Right cSource
         cFilename -> do
           writeFile cFilename cSource
           return $ Right ""

generateCode _ _ language _ =
  return $ Left ("Lenguaje no reconocido: " ++ language)

compilePackages :: OptionsQ -> [(PackageName, [Token])] ->
                   IO (Either String String)
compilePackages options packages = do
    mExpr <- compileAndOptimize options packages
    mExpr `orDie` \ (pragmas, expr) -> do
    let language = Map.findWithDefault "" OptQ_OutputLanguage options
     in generateCode options pragmas language expr

evalPackages :: OptionsQ -> [(PackageName, [Token])] ->
                IO (Either String ValueI)
evalPackages options packages = do
    mExpr <- compileAndOptimize options packages
    mExpr `orDie` \ (pragmas, expr) -> do
    if Map.member OptQ_Compile options
     then
       let language = Map.findWithDefault "" OptQ_OutputLanguage options
        in do
           res <- generateCode options pragmas language expr
           case res of
             Left msg   -> return $ Left msg
             Right result -> do
                 putStr result
                 return $ Right (RecordI []) 
    else 
      if Map.member OptQ_NoRun options
       then return $ Right (RecordI [])
       else do
         value <- eval expr
         showIf options OptQ_ShowValue value
         return $ Right value

inferPackages :: OptionsQ -> [(PackageName, [Token])] ->
                 Either String ConstrainedType
inferPackages options packages = do
    (_, ast) <- parsePackagesWithPragmas
                  (parserOptionsFor options)
                  packages (mainName options)
    (ast', typ) <- infer (valueRestriction options) ast
    return typ

