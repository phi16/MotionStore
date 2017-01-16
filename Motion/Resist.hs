module Motion.Resist where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

resistMot :: Color -> World (Render (), World ())
resistMot c = do
  a <- ease 0 100 $ easeOut . expo
  v <- immediate 0
  d <- ease 0 80 $ easeOut . expo
  let
    recur 0 act = act
    recur i act = do
      r <- io $ randomRIO (-0.02,0.02)
      rotate (po r * morph d) $ rotate (morph a) $ translate (0,-40) $ recur (i-1) act
    render = do
      let sh = (1+signum (morph a))/2 * 40
      translate (40+sh,200) $ do
      forM_ [1..5] $ \i -> recur i $ fill c $ rect (-sh,0) (40,40)
    handler = do
      forever $ do
        a ~~> 0.3
        io $ print "po1"
        sleep 20
        io $ print "po2"
        d ~~>! 1
        io $ print "po3"
        d ==> 0
        io $ print "po4"
        v ==> -0.05
        io $ print "po5"
        forM_ [0..100] $ const $ do
          a' <- valueOf $ morph a
          v' <- valueOf $ morph v
          a ==> a' + v'
          io $ print "po6"
          v ==> v' * 0.6 - a' * 0.3
          io $ print "po7"
          sleep 0
          io $ print "po8"
        io $ print "po9"
  return (render,handler)