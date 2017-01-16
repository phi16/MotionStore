module Motion.Info where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

infoMot :: Color -> World (Render (), World ())
infoMot c = do
  s <- ease 1 20 $ easeOut . back
  fis <- forM [0..2] $ \i -> ease 1 20 $ sequent i 3 0.6 . easeOut . quad
  fos <- forM [0..2] $ \i -> ease 1 20 $ sequent i 3 0.6 . easeOut . cubic
  let
    fs = zip fis fos
    drawFrame i o = do
      i' <- io $ valueIO i
      o' <- io $ valueIO o
      case (i',o') of
        (Just iu,Just ou) | abs (iu-ou) > 1 -> do
          fill c $ centerRect (0,0) (o,o)
          fill white $ centerRect (0,0) (i,i)
        _ -> return ()
    render = do
      translate (100,100) $ do
        forM_ fs $ \(i,o) -> drawFrame (100 * morph i) (100 * morph o)
        scale (morph s,morph s) $ fill c $ centerRect (0,0) (80,80)
    handler = do
      forever $ do
        sleep 40
        s ==> 1.2
        iforM_ fs $ \p (i,o) -> do
          let t = 1.8 - fromIntegral p / 2 * 0.4
          i ==> 1
          o ==> 1
          i ~~> t
          o ~~> t
        s ~~>! 1
  return (render,handler)