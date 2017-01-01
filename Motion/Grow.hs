module Motion.Grow where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

growMot :: Color -> World (Render (), World ())
growMot c = do
  ss <- forM [0..4] $ \i -> ease 0 20 $ sequent i 5 0.3 . easeOut . back
  let
    render = do
      iforM_ ss $ \i s -> let
          y = 4 - fromIntegral i
        in scaleAt (morph s,morph s) (50+20,po y*40+40) $ fill c $ centerRect (50+20,po y*40+20) (40,40)
    handler = forever $ do
      forM_ ss (~~>1)
      sleep 40
      forM_ ss $ (~~>0) . reflected
      sleep 40
  return (render,handler)