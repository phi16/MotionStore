module Motion.Speed where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

speedMot :: Color -> World (Render (), World ())
speedMot c = do
  let
    render = translate (100,100) $ do
      a <- io $ randomRIO (0,1)
      b <- io $ randomRIO (0,1)
      let
        a' = sqrt (-2 * log a) * sin (2*pi*b)
        b' = sqrt (-2 * log a) * cos (2*pi*b)
        dx = a' * 2
      dy' <- io $ randomRIO (0,1)
      let dy = 4 / (1 - dy')
      rotateAt (pi/6) (0,0) $ do
        fill c $ centerRect (po dx,-30+po dy) (60,60)
    handler = return ()
  return (render,handler)