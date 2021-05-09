module Main where

import Lang
import TSGInt

main :: IO ()
main = putStrLn $ printExp selfInterp
