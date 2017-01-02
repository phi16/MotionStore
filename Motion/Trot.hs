module Motion.Trot where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

trotMot :: Color -> World (Render (), World ())
trotMot c = do
  s <- ease 0 40 $ easeIn . cubic
  d <- ease 0 40 $ easeInOut . smooth
  let
    render = translate (morph d,0) $ rotateAt (morph s) (100,200) $ do
      fill c $ rect (25,125) (75,75)
    handler = forever $ do
      s ==> 0
      d ==> 0
      s ~~>! pi/2
      d ~~>! -75
  return (render,handler)