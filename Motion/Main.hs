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

type Views = [View FocusEvent]

size :: R
size = 200

pad :: R
pad = 40

sz :: Value R
sz = po size

launch :: Canvas -> World ()
launch cvs = do
  v1 <- consView (0,0.3,1,1) bounceMot "Bounce" "No description"
  v2 <- consView (0.3,0.8,0,1) growMot "Grow" "No description"
  v3 <- consView (1.0,0.2,0,1) speedMot "Speed" "No description"
  v4 <- consView (0.1,0.8,0.8,1) changeMot "Change" "No description"
  let views = [v1,v2,v3,v4]
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
      clip shape rend
      shadowed (0,3) 5 (0,0,0,0.2) $ do
        fill (0.2,0.2,0.2,1) $ text "mplus" (po title) LeftAlign BottomBase (sz*1.2,sz/2) (sz*0.2)
  makeView Just shape render $ \box -> do
    fork hand
    button (h ~~> 6) (h ~~> 15) (return ()) box
