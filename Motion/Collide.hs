module Motion.Collide where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

import System.Random

collideMot :: Color -> World (Render (), World ())
collideMot c = do
  x <- ease (-20) 40 $ easeIn . cubic
  y <- ease 20 40 $ easeIn . cubic
  r <- ease (pi*6/5) 40 $ easeIn . cubic
  let
    render = do
      translate (100+morph x,100+morph y) $ rotate (morph r) $ fill c $ centerRect (0,0) (60,60)
    handler = forever $ do
      (easing .~ easeOut . quint) r ~~> 0
      (easing .~ easeOut . quint) y ~~> 0
      (easing .~ easeOut . quint) x ~~>! 40
      x ==> 40
      (easing .~ easeOut . cubic) x ~~>! 60
      x ==> 60
      (easing .~ easeIn . quad $ duration .~ 3 $ x) ~~>! -70
      x ==> -70
      (easing .~ easeOut . expo) r ~~> pi/5
      (easing .~ easeOut . expo) y ~~> 20
      (easing .~ easeOut . expo) x ~~>! -20
      r ==> pi*6/5
      y ==> 20
      x ==> -20
  return (render,handler)
