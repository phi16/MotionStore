module Motion.Change where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

changeMot :: Color -> World (Render (), World ())
changeMot c = do
  bs <- replicateM 9 $ immediate True
  s <- ease 1 10 $ easeOut . expo
  let
    pos = zip bs [ (x*100,y*100) | x<-[-1..1], y<-[-1..1] ]
    render = do
      translate (100,100) $ scale (morph s / 3, morph s / 3) $ do
        forM_ pos $ \(e,(x,y)) -> do
          e' <- io $ valueIO $ morph e
          when (e' == Just True) $ fill c $ centerRect (po x,po y) (100,100)
    handler = forever $ do
      let
        shuffle = do
          forM_ bs $ \b -> do
            n <- io randomIO
            b ==> n
          s ==> 1.5
          s ~~> 1
      replicateM 4 $ shuffle >> sleep 15
      shuffle
      sleep 50
      shuffle
      sleep 100
  newMVar 0
  return (render,handler)