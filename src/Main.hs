
import System.IO(stderr, hPutStrLn)
import System.Exit(exitFailure)
import System.Environment(getArgs, lookupEnv)
import Control.Monad.Trans.Class(lift)
import qualified System.Console.Haskeline as RL(
        InputT, runInputT, getInputLine, defaultSettings,
        outputStrLn,
    )
import Data.Char(isUpper)
import Data.List((\\), span)
import qualified Data.Map as Map(
        Map, empty, insert, lookup, findWithDefault, member, notMember,
        fromList,
    )

import Lexer(Token)
import ExpressionE(Id, PackageName, showPackage, ConstrainedType)
import Position(stringToPackageName)
import Reader(ReaderOptions(..), readPackageOrFail, readFromStrings)
import QriolloEval(
        evalPackages, inferPackages, stringValueToString,
        OptionsQ, OptionQ(..),
    )
import Primitive(primMain)

version :: String
version = "0,91 \"Atorrante\""

banner :: String
banner =
  "____________________________________________________________________________\n\
  \   \\__ \\  \\   ooooooooooooooo   /  / __/\n\
  \      \\ \\  ooo               ooo  / /          ___       _       _ _\n\
  \ _____ | \\o   _____     _____   o/ | _____    / _ \\ _ __(_) ___ | | | ___\n\
  \__    \\ \\o   (     \\   /     )   o/ /    _   | | | | '__| |/ _ \\| | |/ _ \\\n\
  \  \\__  \\o     <(O)> ) ( <(O)>     o/  __/    | |_| | |  | | (_) | | | (_) |\n\
  \     \\__o           / \\           o__/        \\__\\_\\_|  |_|\\___/|_|_|\\___/\n\
  \________o         (_(_)_)         o________\n\
  \     ___o          _____          o___          Qriollo "
                                                          ++ version ++ "\n\
  \  __/  /o         /_____\\         o\\  \\__ \n\
  \_/    / /o         \\___/         o\\ \\    \\_            1810-2016\n\
  \ ____/ | /o          n          o\\ | \\____         Hermandá Qriolla\n\
  \    __/ /  ooo               ooo  \\ \\__\n\
  \ __/   /  /   ooooooooooooooo   \\  \\   \\__\n\
  \______/___|__/___\\___|___/___\\__|___\\_______________________________________\n"

usage :: Bool -> IO a
usage full = do
  defaultOptions <- getDefaultOptions
  putStr ("Qriollo versión " ++ version ++ "\n")
  putStr ("Uso: qr [opciones] [entrada[.q]]\n")
  putStr ("\nOpciones principales\n")
  putStr ("-i, --chinela : " ++
          "Modo chinela (CHupar, INterpretar, Escupir La sAlida).\n")
  putStr ("-p <nombre>   : " ++
          "Nombre del punto de entrada principal " ++
          dflt defaultOptions OptQ_MainName ++ ".\n")
  putStr ("-t, --tipo    : " ++
          "Muestra el tipo del programa, sin ejecutarlo.\n")
  putStr ("--py          : " ++
          "Compila a Python.\n")
  putStr ("--jvm         : " ++
          "Compila a la JVM.\n")
  putStr ("--c           : " ++
          "Compila a C.\n")
  putStr ("-o <archivo>  : " ++
          "Nombre del archivo de salida.\n")
  putStr ("--ruta <dirs> : " ++
          "Directorios donde se buscan los módulos (separados por \":\").\n")
  if full
   then do
    putStr ("\nDesinsectación\n")
    putStr ("--al-pedo    : Compilar el programa, sin ejecutarlo.\n")
    putStr ("--facho      : Prohíbe la recursión en estructuras de datos.\n")
    putStr ("--gorra      : " ++
            "Obliga a que se respete la restricción de valores.\n")
    putStr ("--malpensado : Chequea invariantes de las estructuras internas.\n")
    putStr ("\nOpciones válidas sólo si se interpreta (no para compilar)\n")
    putStr ("--trucho  : " ++
            "No convertir clausuras, reservar, ni asignar registros.\n")
    putStr ("--pedorro : " ++
            "No resevar ni asignar registros.\n")
    putStr ("--berreta : " ++
            "No asignar registros.\n")
    putStr ("\nFuncionalidades\n")
    putStr ("--con <Funcionalidad> : Declara presente la funcionalidad.\n")
    putStr ("--sin <Funcionalidad> : Declara ausente la funcionalidad.\n")
    putStr ("\nCharlatán\n")
    putStr ("--mast : Escupe el árbol sintáctico.\n")
    putStr ("--masT : Escupe el árbol sintáctico después del tipado.\n")
    putStr ("--mpre : Escupe la expresión después de precompilar.\n")
    putStr ("--mcps : Escupe la expresión después de convertir a CPS.\n")
    putStr ("--mopt : Escupe la expresión después de optimizada.\n")
    putStr ("--mclo : Escupe la expresión después de clausurada.\n")
    putStr ("--mall : Escupe la expresión después de reservar registros.\n")
    putStr ("--mreg : Escupe la expresión después de asignar registros.\n")
    putStr ("--mval : Escupe el resultado.\n")
    putStr ("\nMejoras\n")
    putStr ("--manija <n> : Cantidad de rondas de optimización " ++
            dflt defaultOptions OptQ_OptimizationRounds ++ ".\n")
    putStr ("--lenteja    : " ++
            "Optimiza el tamaño del programa (puede ser más lento).\n")
   else do
    putStr ("--mano        : " ++
            "Muestra todas las opciones disponibles.\n")
  putStr ("\nEjemplos\n")
  putStr ("  qr Fulano    # ejecuta\n")
  putStr ("  qr -i Fulano # modo interactivo\n")
  putStr ("  qr Fulano --py | python -  # ejecuta en Python \n")
  putStr ("  qr Fulano --c -o f.c && gcc -o f f.c -Wall && ./f  " ++
          "# ejecuta en C\n")
  exitFailure
  where
    dflt :: OptionsQ -> OptionQ -> String
    dflt defaultOptions key =
      "[=" ++ Map.findWithDefault "" key defaultOptions ++ "]"

getDefaultOptions :: IO OptionsQ
getDefaultOptions = do
    path <- getPath
    return $ Map.fromList [
      (OptQ_OptimizationRounds, show 4),
      (OptQ_MainName, primMain),
      (OptQ_Path, path)
     ]
  where
    getPath :: IO String
    getPath = do
      mPath <- lookupEnv "RUTA_QRIOLLO"
      case mPath of
        Nothing   -> return "."
        Just path -> return path

parseOptions :: IO OptionsQ
parseOptions = do
    args <- getArgs
    defaultOptions <- getDefaultOptions
    rec args defaultOptions
  where
    rec :: [String] -> OptionsQ -> IO OptionsQ

    -- No more options
    rec [] options =
      case Map.lookup OptQ_Input options of
        Nothing -> case Map.lookup OptQ_Interactive options of
                     Nothing -> usage False
                     Just _  -> return options
        Just _  -> return options

    -- Show full help
    rec ("--mano" : args) options =
      usage True

    -- Interactive
    rec ("-i" : args) options =
        rec args (Map.insert OptQ_Interactive "" options)
    rec ("--chinela" : args) options =
        rec args (Map.insert OptQ_Interactive "" options)
    rec ("-o" : outFile : args) options =
        rec args (Map.insert OptQ_OutputFile outFile options)

    -- Compiler
    rec ("--py" : args) options =
        rec args (Map.insert OptQ_OutputLanguage "Py" $
                  Map.insert OptQ_Compile "" options)
    rec ("--jvm" : args) options =
        rec args (Map.insert OptQ_OutputLanguage "Jvm" $
                  Map.insert OptQ_Compile "" options)
    rec ("--c" : args) options =
        rec args (Map.insert OptQ_OutputLanguage "C" $
                  Map.insert OptQ_Compile "" options)

    -- Name of main
    rec ("-p" : mainName : args) options =
        rec args (Map.insert OptQ_MainName mainName options)

    -- Strictness
    rec ("--facho" : args) options =
        rec args (Map.insert OptQ_DisallowRecursionOnData "" options)
    rec ("--gorra" : args) options =
        rec args (Map.insert OptQ_EnforceValueRestriction "" options)
    rec ("--malpensado" : args) options =
        rec args (Map.insert OptQ_CheckInternalInvariants "" options)

    -- Path
    rec ("--ruta" : path : args) options =
        rec args (Map.insert OptQ_Path path options)

    -- Debugging
    rec ("--al-pedo" : args) options =
        rec args (Map.insert OptQ_NoRun "" options)
    rec ("--trucho" : args) options =
        rec args (Map.insert OptQ_NoClosureConversion "" options)
    rec ("--pedorro" : args) options =
        rec args (Map.insert OptQ_NoRegAlloc "" options)
    rec ("--berreta" : args) options =
        rec args (Map.insert OptQ_NoRegAssign "" options)

    -- Debugging: verbosity level
    rec ("--mast" : args) options =
        rec args (Map.insert OptQ_ShowAst "" options)
    rec ("--masT" : args) options =
        rec args (Map.insert OptQ_ShowTypedAst "" options)
    rec ("--mpre" : args) options =
        rec args (Map.insert OptQ_ShowPrecompiledExpression "" options)
    rec ("--mcps" : args) options =
        rec args (Map.insert OptQ_ShowCPSExpression "" options)
    rec ("--mopt" : args) options =
        rec args (Map.insert OptQ_ShowOptimizedExpression "" options)
    rec ("--mclo" : args) options =
        rec args (Map.insert OptQ_ShowClosedExpression "" options)
    rec ("--mall" : args) options =
        rec args (Map.insert OptQ_ShowRegAllocExpression "" options)
    rec ("--mreg" : args) options =
        rec args (Map.insert OptQ_ShowRegAssigExpression "" options)
    rec ("--mval" : args) options =
        rec args (Map.insert OptQ_ShowValue "" options)
    rec ("-t" : args) options =
        rec args (Map.insert OptQ_OnlyType "" options)
    rec ("--tipo" : args) options =
        rec args (Map.insert OptQ_OnlyType "" options)

    -- Feature declarations
    rec ("--con" : feature : args) options =
      if null feature || not (isUpper (head feature))
       then do
         showError (
           "La funcionalidad indicada en --con " ++
           "tiene que empezar con mayúscula.")
         usage False
       else
         let features = words (Map.findWithDefault "" OptQ_FeatureList options)
          in rec args (Map.insert OptQ_FeatureList
                                  (unwords (feature : features))
                                  options)
    rec ("--sin" : feature : args) options =
      let features = words (Map.findWithDefault "" OptQ_FeatureList options)
       in rec args (Map.insert OptQ_FeatureList
                               (unwords (features \\ [feature]))
                               options)

    -- Optimizations
    rec ("--manija" : nRounds : args) options =
        rec args (Map.insert OptQ_OptimizationRounds nRounds options)
    rec ("--lenteja" : args) options =
        rec args (Map.insert OptQ_OptimizeForSpace "" options)

    -- Input file
    rec (input:args) options =
      case Map.lookup OptQ_Input options of
        Nothing -> rec args (Map.insert OptQ_Input input options)
        Just _  -> usage False

showError :: String -> IO ()
showError msg = hPutStrLn stderr (
                  "Se te escapó la tortuga.\n" ++
                  "\n" ++
                  msg
                )

showType :: ConstrainedType -> IO ()
showType typ = putStrLn ("    de " ++ show typ)

prompt :: String
prompt = "qriollo> "

readerOptions :: OptionsQ -> ReaderOptions
readerOptions options =
    ReaderOptions {
      rdoPath = splitBy ':' $
                Map.findWithDefault "." OptQ_Path options
    }
  where
    splitBy :: Char -> String -> [String]
    splitBy sep string =
      case span (/= sep) string of
        (word, [])       -> [word]
        (word, _ : rest) -> word : splitBy sep rest

runScript :: OptionsQ -> String -> IO ()
runScript options packageStr = do
   packages <- readPackageOrFail (readerOptions options)
                                 (stringToPackageName packageStr)
   if Map.member OptQ_OnlyType options
    then
      case inferPackages options packages of
        Left msg  -> showError msg
        Right typ -> showType typ
    else do
      result <- evalPackages options packages
      case result of
        Left msg -> showError msg
        Right _ -> return ()

scriptThenREPL :: OptionsQ -> String -> IO ()
scriptThenREPL options packageStr = do
    packages <- readPackageOrFail (readerOptions options)
                                  (stringToPackageName packageStr)
    readEvalPrintLoop options packages

preludePackage :: PackageName
preludePackage = ["Chamuyo"]

replHelp :: String
replHelp =
    "\
    \:chau           Se va del modo chinela.\n\
    \:mano           Para pedir una mano.\n\
    \:t <expresión>  Muestra el tipo de la expresión.\n"

toplevelPackage :: PackageName
toplevelPackage = ["<entrada>"]

toplevelMain :: Id
toplevelMain = "__"

exitMessage :: String
exitMessage = "Morir es una costumbre que sabe tener la gente.\n"

readEvalPrintLoop :: OptionsQ -> [(PackageName, [Token])] -> IO ()
readEvalPrintLoop options packages = do
    putStr banner
    putStr "\n"
    putStr "Estás en modo chinela.\n"
    putStr "Si necesitás una mano poné :mano\n"
    RL.runInputT RL.defaultSettings repl
  where
    repl :: RL.InputT IO ()
    repl = do
      cmd <- RL.getInputLine prompt
      case cmd of
        Nothing     -> do
          RL.outputStrLn exitMessage
          return ()
        Just "" -> repl
        Just ":chau" -> do
          RL.outputStrLn exitMessage
          return ()
        Just ":mano" -> do
          RL.outputStrLn replHelp
          repl
        Just (':':'t':' ':line) -> do
          infer line
          repl
        Just line   -> do
          eval line
          repl

    eval :: String -> RL.InputT IO ()
    eval line = do
      case packagesForEvaluation line of
        Left msg -> lift $ showError msg
        Right packsEval -> do
          result <- lift $ evalPackages (optionsWithMain toplevelMain)
                                        packsEval
          case result of
            Left msg  -> lift $ showError msg
            Right val -> do
                RL.outputStrLn (stringValueToString val)
                infer line

    infer :: String -> RL.InputT IO ()
    infer line = do
      case packagesForInference line of
        Left msg -> lift $ showError msg
        Right packsInfer -> do
          case inferPackages (optionsWithMain toplevelMain) packsInfer of
            Left msg  -> lift $ showError msg
            Right typ -> lift $ showType typ

    packagesForEvaluation :: String -> Either String [(PackageName, [Token])]
    packagesForEvaluation line = do
        rpackage <- readFromStrings [(
                      toplevelPackage,
                      importPackage preludePackage ++
                      importLastPackage packages ++
                      "el " ++ toplevelMain ++ " es Chamuyo.mostrar (\n\n" ++
                      line ++
                      "\n\n)"
                     )]
        return (packages ++ rpackage)

    packagesForInference :: String -> Either String [(PackageName, [Token])]
    packagesForInference line = do
        rpackage <- readFromStrings [(
                      toplevelPackage,
                      importPackage preludePackage ++
                      importLastPackage packages ++
                      "el " ++ toplevelMain ++ " es\n" ++ line
                     )]
        return (packages ++ rpackage)

    importPackage :: PackageName -> String 
    importPackage pack = "enchufar " ++ showPackage pack ++ "\n"

    optionsWithMain :: Id -> OptionsQ
    optionsWithMain mainName = Map.insert OptQ_MainName mainName options

    importLastPackage :: [(PackageName, [Token])] -> String 
    importLastPackage [] = ""
    importLastPackage packs
      | pack == preludePackage = ""
      | otherwise              = importPackage pack
      where (pack, _) = last packs

main :: IO ()
main = do
    options <- parseOptions
    go options
  where
    go :: OptionsQ -> IO ()
    go options
      | (Map.member OptQ_NoClosureConversion options ||
         Map.member OptQ_NoRegAlloc options ||
         Map.member OptQ_NoRegAssign options) &&
        Map.member OptQ_Compile options =
          -- Cannot use sloppy options when compiling
          hPutStrLn stderr (
            "Las opciones --trucho, --pedorro y --berreta\n" ++
            "son incompatibles con la compilación."
          )

    go options
      | Map.notMember OptQ_Interactive options &&
        Map.member OptQ_Input options =
          let packageStr = Map.findWithDefault "" OptQ_Input options
           in runScript options packageStr

    go options
      | Map.member OptQ_Interactive options &&
        Map.member OptQ_Input options =
          let packageStr = Map.findWithDefault "" OptQ_Input options
           in scriptThenREPL options packageStr

    go options
      | Map.member OptQ_Interactive options &&
        Map.notMember OptQ_Input options = do
           prelude <- readPackageOrFail (readerOptions options) preludePackage
           readEvalPrintLoop options prelude

