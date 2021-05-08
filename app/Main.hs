module Main where

import Lisp

main :: IO ()
main = do
    c <- getContents
    print $ compileLisp c
