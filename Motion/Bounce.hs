module Motion.Bounce where

import Core.Util
import Core.World
import Core.Ease
import Core.Shape
import Core.Render

bounceMot :: Color -> World (Render (), World ())
bounceMot c = do
  y <- ease 100 20 $ easeOut . quad
  xl <- immediate 0
  xr <- immediate 0
  xu <- immediate 0
  xd <- immediate 0
  vl <- immediate 0
  vr <- immediate 0
  vu <- immediate 0
  vd <- immediate 0
  al <- immediate 0
  ar <- immediate 0
  au <- immediate 0
  ad <- immediate 0
  let
    render = fill c $ rect (75-morph xl,morph y-morph xu) (50+morph xl+morph xr,100+morph xu+morph xd)
    handler = do
      fork $ forever $ do
        xl' <- valueOf $ morph xl
        xr' <- valueOf $ morph xr
        xu' <- valueOf $ morph xu
        xd' <- valueOf $ morph xd
        vl' <- valueOf $ morph vl
        vr' <- valueOf $ morph vr
        vu' <- valueOf $ morph vu
        vd' <- valueOf $ morph vd
        al' <- valueOf $ morph al
        ar' <- valueOf $ morph ar
        au' <- valueOf $ morph au
        ad' <- valueOf $ morph ad
        al ==> al' * 0.7
        ar ==> ar' * 0.7
        au ==> au' * 0.7
        ad ==> ad' * 0.7
        vl ==> (vl' + al') * 0.7
        vr ==> (vr' + ar') * 0.7
        vu ==> (vu' + au') * 0.7
        vd ==> (vd' + ad') * 0.7
        xl ==> (xl' + vl') * 0.7
        xr ==> (xr' + vr') * 0.7
        xu ==> (xu' + vu') * 0.7
        xd ==> (xd' + vd') * 0.7
        sleep 0
      forever $ do
        ad ==> -10
        y ~~>! 30
        reflected y ~~>! 100
        vu ==> -30
        al ==> 3
        ar ==> 3
        sleep 50
  return (render,handler)