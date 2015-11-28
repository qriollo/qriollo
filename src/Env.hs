
module Env(
        Env,
        envEmpty, envPushFrame, envPopFrame, envIsLocallyDefined,
        envDefine, envSet, envGet, envAllValues, envFromList,
    ) where

import Data.Map as Map(Map, empty, insert, lookup, fold)

data Env a b = Env {
                 envRibs :: Map a [b],
                 envFrames :: [[a]]
               }

envEmpty :: Env a b
envEmpty = Env { envRibs = Map.empty, envFrames = [[]] }

envPushFrame :: Env a b -> Env a b
envPushFrame env = env { envFrames = [] : envFrames env }

envPopFrame :: Ord a => Env a b -> Env a b
envPopFrame env = env {
                    envRibs = updatedRibs,
                    envFrames = tail (envFrames env)
                  }
  where
    updatedRibs = foldr popKey (envRibs env) (head (envFrames env))
    popKey key dict =
      case Map.lookup key dict of
        Just (val:vals) -> insert key vals dict
        _ -> error "Env: Cannot pop frame from empty stack"

envIsLocallyDefined :: Ord a => a -> Env a b -> Bool
envIsLocallyDefined key env =
  key `elem` head (envFrames env)

envDefine :: Ord a => a -> b -> Env a b -> Env a b
envDefine key val env =
    env {
        envRibs = defKey (envRibs env),
        envFrames = updateFrames (envFrames env)
    }
  where
    defKey dict =
      case Map.lookup key dict of
        Just vals -> insert key (val:vals) dict
        Nothing   -> insert key [val] dict
    updateFrames (f : fs) = (key : f) : fs

envSet :: Ord a => a -> b -> Env a b -> Env a b
envSet key val env = env { envRibs = setKey (envRibs env) }
  where
    setKey dict =
      case Map.lookup key dict of
        Just (_:vals) -> insert key (val:vals) dict
        _             -> error "Env: Cannot set undefined key"

envGet :: Ord a => a -> Env a b -> Maybe b
envGet key env = getKey (envRibs env)
  where
    getKey dict =
      case Map.lookup key dict of
        Just (val:_) -> Just val
        _            -> Nothing

envAllValues :: Env a b -> [b]
envAllValues = Map.fold (++) [] . envRibs

envFromList :: Ord a => [(a, b)] -> Env a b
envFromList = foldr (uncurry envDefine) envEmpty

