module Main where

import Lang
import TSGInt

import qualified Data.Text as T

main :: IO ()
main = putStrLn $ T.unpack $ printExp selfInterp
