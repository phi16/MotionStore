module Motion.Grow where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

growMot :: Color -> World (Render (), World ())
growMot c = do
  ss <- forM [0..7] $ \i -> ease 0 40 $ sequent i 8 0.3 . easeOut . back
  let
    render = do
      iforM_ ss $ \i s -> let
          x = fromIntegral $ min 3 $ max 1 $ i-2
          y = fromIntegral $ if i < 4 then 4 - i else if i > 4 then i - 4 else 1
          origX = if i == 4 || i == 5 then -20 else 0
          origY = if i < 4 then 20 else if i > 4 then -20 else 0
        in scaleAt (morph s,morph s) (po x*40+20+po origX,po y*40+20+po origY) $ fill c $ centerRect (po x*40+20,po y*40+20) (40,40)
    handler = forever $ do
      forM_ ss (~~>1)
      sleep 60
      forM_ ss $ (~~>0) . reflected
      sleep 60
  return (render,handler)