{-# LANGUAGE OverloadedStrings #-}

module Main where

import Lang
import Ura
import TSGInt

import Control.Monad
import qualified Data.Text as T

main :: IO ()
--main = putStrLn $ T.unpack $ printExp selfInterp
main = forM_ (ura tsgInterp ([CVE 1, ATOM "Nil"], RESTR []) (ATOM "test")) $ \(m, _) -> print m
