{-# LANGUAGE OverloadedStrings #-}

module Motion.Main where

import Core.Util
import Core.World
import Core.Ease
import Core.Front
import Core.Shape
import Core.Render
import Core.UI
import Core.View

import Haste.DOM

import Motion.Bounce
import Motion.Grow
import Motion.Speed
import Motion.Change
import Motion.Trot

type Views = [View FocusEvent]

size :: R
size = 150

pad :: R
pad = 40

sz :: Value R
sz = po size

launch :: Canvas -> World ()
launch cvs = do
  v1 <- consView (0,0.3,1,1) bounceMot "Bounce" "Velocity & Acceleration"
  v2 <- consView (0.3,0.8,0,1) growMot "Grow" "Sequential easeOutBack"
  v3 <- consView (1.0,0.2,0,1) speedMot "Speed" "Uniform Distr & Exponential Distr"
  v4 <- consView (0.1,0.8,0.8,1) changeMot "Change" "easeOutExpo"
  v5 <- consView (1,0.5,0,1) trotMot "Trot" "rotateAt corner easeInCubic & smoothStep scroll"
  let views = [v1,v2,v3,v4,v5]
  let height = pad + fromIntegral (length views) * (size + pad)
  setProp (elemOf cvs) "height" $ show height
  state <- makeMVar views
  onFrame state $ \s -> render cvs $ renderContents s
  spawn $ emitting $ forever $ do
    s <- withMVar state get
    applyTransform $ renderContents s
    sleep 1
  return ()

renderContents :: Views -> Render ()
renderContents vs = do
  iforM_ vs $ \i v -> let
      y = fromIntegral i
    in translate (po $ pad,po $ pad+(size+pad)*y) $ v^.rendering

consView :: Color -> (Color -> World (Render (), World ())) -> String -> String -> World (View FocusEvent)
consView c a title desc = do
  (rend,hand) <- a c
  h <- ease 6 10 linear
  let
    shape = rect (0,0) (sz,sz)
    render = do
      shadowed (0,3) (morph h) black $ fill white $ rect (0,0) (sz,sz)
      clip shape $ scale (0.75,0.75) rend
      shadowed (0,3) 5 (0,0,0,0.2) $ do
        fill (0.2,0.2,0.2,1) $ text "mplus" (po title) LeftAlign BottomBase (sz*1.2,sz/2) (sz*0.3)
        fill (0.5,0.5,0.5,1) $ text "mplus" (po desc) LeftAlign TopBase (sz*1.2,sz*0.6) (sz*0.15)
  makeView Just shape render $ \box -> do
    fork hand
    button (h ~~> 6) (h ~~> 15) (return ()) box
