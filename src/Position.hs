module Position(
        Position(..),
        packageToFilename,
        stringToPackageName,
        describePosition,
        showNearbyCode,
        updatePosition,
    ) where

import AST(PackageName)

data Position = Position PackageName String Int Int
  deriving (Show, Eq)

joinS :: String -> [String] -> String
joinS sep []   = []
joinS sep list = foldr1 (\ x r -> x ++ sep ++ r) list

packageToFilename :: PackageName -> FilePath
packageToFilename package = joinS "/" package ++ ".q"

stringToPackageName :: String -> PackageName
stringToPackageName str =
  case span (`notElem` "./") str of
    (p, ".q")       -> [p]
    (p, '.' : str') -> p : stringToPackageName str'
    (p, '/' : str') -> p : stringToPackageName str'
    (p, "")         -> [p]

describePosition :: Position -> String
describePosition (Position package contents row col) =
  packageToFilename package ++ ":" ++ show row ++ "," ++ show col 

showNearbyCode :: Position -> String
showNearbyCode (Position package contents row col) =
    joinS "\n" (concat [
                  previousLine,
                  currentLine,
                  [cursorLine],
                  followingLine
                ])
  where
    lines :: [(Integer, String)] 
    lines = zip [1..] (split '\n' contents)

    previousLine :: [String] 
    previousLine = filterByLineNum (fromIntegral (row - 1))

    currentLine :: [String] 
    currentLine = filterByLineNum (fromIntegral row)

    followingLine :: [String] 
    followingLine = filterByLineNum (fromIntegral (row + 1))

    cursorLine :: String
    cursorLine = (take (col - 1) $ repeat ' ') ++ "^"

    filterByLineNum :: Integer -> [String] 
    filterByLineNum num = map snd $ filter (\ (no, _) -> no == num) lines

    split :: Char -> String -> [String]
    split sep s = case span (/= sep) s of
                    (line, '\n' : s') -> line : split sep s'
                    (line, "")        -> [line]

updatePosition :: String -> Position -> Position
updatePosition string = foldr (.) id (map updChar string)
  where updChar :: Char -> Position -> Position
        updChar '\n' (Position filename contents row _)   =
                     Position filename contents (row + 1) 1
        updChar _    (Position filename contents row col) =
                     Position filename contents row (col + 1)

