{-# LANGUAGE PackageImports #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Core.Util
import Core.Front
import Core.World
import Core.Render
import Haste.Prim
import Haste.DOM

import Motion.Main

main :: IO ()
main = do
  start
  getCanvasById "canvas" >>= \case
    Nothing -> error "Canvas not found!"
    Just cvs -> concurrent $ runWorld $ launch cvs
