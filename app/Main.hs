module Main where

import Lisp
import SM

main :: IO ()
main = do
    c <- getContents
    print $ compileSM $ compileLisp c
