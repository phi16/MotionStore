{-# OPTIONS_HADDOCK hide #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Core.Shape.Internal (
  Path, Shape,
  execPath, E, E2,
  bezier, line, circle, rect, centerRect, roundRect, polygon, 
  Font, TextAlign(..), TextBase(..), text,
  disable,
  Affine(..),
  inside) where

import qualified Haste.Graphics.Canvas as G
import Haste.Foreign
import Haste.Prim
import Core.Util
import Core.Front
import Core.Ease
import Control.Applicative

type Domain = R2 -> IO Bool
type Path = G.Ctx -> Bool -> IO ()
-- | @Shape ()@で図形を表現します。'Monad'になっているのは複数の図形の合成をdo文で簡単に行う為です。
data Shape a = Shape Domain Path a

execPath :: Shape () -> Path
execPath (Shape _ p _) = p

next :: Path -> Path -> Path
next x y ctx b = x ctx b >> y ctx b

blank :: Domain
blank _ = return False

none :: Path
none _ _ = return ()

instance Functor Shape where
  fmap f (Shape b p x) = Shape b p (f x)
instance Applicative Shape where
  pure x = Shape blank none x
  Shape b1 p1 f <*> Shape b2 p2 x = Shape (liftA2 (liftA2 (&&)) b1 b2) (p1`next`p2) $ f x
instance Monad Shape where
  Shape b1 p1 x >>= f = let
      Shape b2 p2 y = f x
    in Shape (liftM2 (liftM2 (&&)) b1 b2) (p1`next`p2) y

magic :: R
magic = 4 * (sqrt 2 - 1) / 3

ext :: Value a -> (a -> IO Bool) -> IO Bool
ext v h = valueIO v >>= \case
  Nothing -> return False
  Just v' -> h v'

-- | 実数のEasingです。
type E = Value R
-- | R^2上のEasingです。
type E2 = (Value R, Value R)

dom :: Value a -> (a -> Path) -> Path
dom v h c b = valueIO v >>= \case
  Nothing -> return ()
  Just x -> h x c b

dom2 :: E2 -> ((R,R) -> Path) -> Path
dom2 (v1,v2) h c b = valueIO v1 >>= \case
  Nothing -> return ()
  Just x1 -> valueIO v2 >>= \case
    Nothing -> return ()
    Just x2 -> h (x1,x2) c b

jsMoveTo :: Double -> Double -> Path
jsMoveTo = ffi "(function(x,y,ctx,_){ctx.moveTo(x,y);})"

jsLineTo :: Double -> Double -> Path
jsLineTo = ffi "(function(x,y,ctx,_){ctx.lineTo(x,y);})"

jsBezierTo :: Double -> Double -> Double -> Double -> Double -> Double -> Path
jsBezierTo = ffi "(function(x1,y1,x2,y2,x,y,ctx,_){ctx.bezierCurveTo(x1,y1,x2,y2,x,y);})"

jsFillText :: JSString -> Double -> Double -> Path
jsFillText = ffi "(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})"

jsStrokeText :: JSString -> Double -> Double -> Path
jsStrokeText = ffi "(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})"

moveTo :: R2 -> Path
moveTo = uncurry jsMoveTo

lineTo :: R2 -> Path
lineTo = uncurry jsLineTo

bezierTo :: R2 -> R2 -> R2 -> Path
bezierTo (a,b) (c,d) (e,f) = jsBezierTo a b c d e f

-- | @'bezier' a b c d@で、@b@と@c@を制御点とした@a@から@d@への3次Bezier曲線を表現します。領域を持ちません。
bezier :: E2 -> E2 -> E2 -> E2 -> Shape ()
bezier a b c d = Shape blank path () where
  path = dom2 a $ \a -> dom2 b $ \b -> dom2 c $ \c -> dom2 d $ \d -> do
    moveTo a `next` bezierTo b c d
-- | @'line' a b@で、@a@から@b@への線分を表現します。領域を持ちません。
line :: E2 -> E2 -> Shape ()
line a b = Shape blank path () where
  path = dom2 a $ \a -> dom2 b $ \b -> do
    moveTo a `next` lineTo b
-- | @'circle' c r@で、中心@c@、半径@r@の円を表現します。
circle :: E2 -> E -> Shape ()
circle (p,q) r = Shape region path () where
  region (x,y) = ext p $ \p -> ext q $ \q -> ext r $ \r -> do
    return $ (p-x)^2 + (q-y)^2 <= r^2
  path = dom p $ \p -> dom q $ \q -> dom r $ \r -> let
      p1 = (p,q-r)
      p2 = (p+r,q)
      p3 = (p,q+r)
      p4 = (p-r,q)
      p12 = (p+r*magic,q-r)
      p21 = (p+r,q-r*magic)
      p23 = (p+r,q+r*magic)
      p32 = (p+r*magic,q+r)
      p34 = (p-r*magic,q+r)
      p43 = (p-r,q+r*magic)
      p41 = (p-r,q-r*magic)
      p14 = (p-r*magic,q-r)
    in moveTo p1 `next`
      bezierTo p12 p21 p2 `next`
      bezierTo p23 p32 p3 `next`
      bezierTo p34 p43 p4 `next`
      bezierTo p41 p14 p1
-- | @'rect' p s@で、左上の点を@p@、サイズを@s@とした矩形を表現します。
rect :: E2 -> E2 -> Shape ()
rect (x,y) (w,h) = Shape region path () where
  region (p,q) = ext x $ \x -> ext y $ \y -> ext w $ \w -> ext h $ \h -> do
    return $ abs (p-x-w/2) < w/2 && abs (q-y-h/2) < h/2
  path = dom x $ \x -> dom y $ \y -> dom w $ \w -> dom h $ \h -> let
      p1 = (x,y)
      p2 = (x+w,y)
      p3 = (x+w,y+h)
      p4 = (x,y+h)
    in moveTo p1 `next`
      lineTo p2 `next`
      lineTo p3 `next`
      lineTo p4 `next`
      lineTo p1
-- | @'centerRect' p s@で、中心を@p@、サイズを@s@とした矩形を表現します。
centerRect :: E2 -> E2 -> Shape ()
centerRect (x,y) (w,h) = Shape region path () where
  region (p,q) = ext x $ \x -> ext y $ \y -> ext w $ \w -> ext h $ \h -> do
    return $ abs (p-x) < w/2 && abs (q-y) < h/2
  path = dom x $ \x -> dom y $ \y -> dom w $ \w -> dom h $ \h -> let
      pw = w/2
      ph = h/2
      p1 = (x-pw,y-ph)
      p2 = (x+pw,y-ph)
      p3 = (x+pw,y+ph)
      p4 = (x-pw,y+ph)
    in moveTo p1 `next`
      lineTo p2 `next`
      lineTo p3 `next`
      lineTo p4 `next`
      lineTo p1
-- | @'roundRect' p s r@で、左上の点を@p@、サイズを@s@、角の丸み半径を@r@とした角丸矩形を表現します。
roundRect :: E2 -> E2 -> E -> Shape ()
roundRect (x,y) (w,h) r = Shape region path () where
  region (p,q) = ext x $ \x -> ext y $ \y -> ext w $ \w -> ext h $ \h -> ext r $ \r -> let
      p' = p - x - w/2
      q' = q - y - h/2
      p'' = max 0 $ abs p' - w/2 + r
      q'' = max 0 $ abs q' - h/2 + r
    in return $ p''^2 + q''^2 < r^2
  path = dom x $ \x -> dom y $ \y -> dom w $ \w -> dom h $ \h -> dom r $ \r -> let
      xa = x
      xb = x + r
      xc = x+w - r
      xd = x+w
      ya = y
      yb = y + r
      yc = y+h - r
      yd = y+h
      p1  = (xb,ya)
      p1' = (xc,ya)
      p2  = (xd,yb)
      p2' = (xd,yc)
      p3  = (xc,yd)
      p3' = (xb,yd)
      p4  = (xa,yc)
      p4' = (xa,yb)
      p12 = (xc+r*magic,ya)
      p21 = (xd,yb-r*magic)
      p23 = (xd,yc+r*magic)
      p32 = (xc+r*magic,yd)
      p34 = (xb-r*magic,yd)
      p43 = (xa,yc+r*magic)
      p41 = (xa,yb-r*magic)
      p14 = (xb-r*magic,ya)
    in moveTo p1 `next`
      lineTo p1' `next`
      bezierTo p12 p21 p2 `next`
      lineTo p2' `next`
      bezierTo p23 p32 p3 `next`
      lineTo p3' `next`
      bezierTo p34 p43 p4 `next`
      lineTo p4' `next`
      bezierTo p41 p14 p1
-- | @'polygon' xs@で、@xs@の頂点を結んでできる図形を表現します。例えば三角形の指定には3要素あれば良いです。
polygon :: [E2] -> Shape ()
polygon [] = Shape blank none ()
polygon xs = Shape blank path () where
  valueIO2 (x,y) = do
    x' <- valueIO x
    y' <- valueIO y
    return $ liftM2 (,) x' y'
  path ctx b = do
    ys <- mapM valueIO2 xs
    case sequence ys of
      Just ys@(z:zs) -> do
        moveTo z ctx b
        forM_ ys $ \y -> lineTo y ctx b
        lineTo z ctx b
      Nothing -> return ()

-- | フォント指定は普通にいつも通り文字列を書けば良いです。
type Font = JSString
data TextAlign = LeftAlign   -- ^ 左端がX軸原点
               | CenterAlign -- ^ 中心がX軸原点
               | RightAlign  -- ^ 右端がX軸原点
data TextBase = TopBase      -- ^ 上端がY軸原点
              | MiddleBase   -- ^ 中心がY軸原点
              | BottomBase   -- ^ 下端がY軸原点
              
-- | @'text' font str align base p s@は、フォント@font@の文字列@str@の、@align, base@で指定された原点を@p@、文字サイズを@s@とした図形を表現します。領域を持ちません。
text :: Font -> Value String -> TextAlign -> TextBase -> E2 -> E -> Shape ()
text font str a b (p,q) s = Shape blank path () where
  path = dom str $ \str -> dom p $ \p -> dom q $ \q -> dom s $ \s -> \ctx fill -> do
    let
      f = if fill then jsFillText else jsStrokeText
      a' = case a of
        LeftAlign   -> "left" :: JSString
        CenterAlign -> "center"
        RightAlign  -> "right"
      b' = case b of
        TopBase    -> "hanging" :: JSString
        MiddleBase -> "middle"
        BottomBase -> "alphabetic"
    jsPushState ctx fill
    ffi "(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})" font a' b' ctx :: IO ()
    jsTranslate p q ctx fill
    jsScale (s/10) (s/10) ctx fill
    f (toJSStr str) 0 0 ctx fill
    jsPopState ctx fill

-- | @'disable' b s@は、@b@が'True'のときに領域を持たない'Shape'を返します。
disable :: Value Bool -> Shape () -> Shape ()
disable b (Shape reg pat _) = Shape region path () where
  region (p,q) = ext b $ \b -> if b
    then reg (p,q)
    else return False
  path = dom b $ \b -> if b
    then pat
    else none

jsTransform :: Double -> Double -> Double -> Double -> Double -> Double -> Path
jsTransform = ffi "(function(a,b,c,d,e,f,ctx,_){ctx.transform(a,d,b,e,c,f);})"

jsTranslate :: Double -> Double -> Path
jsTranslate = ffi "(function(x,y,ctx,_){ctx.translate(x,y);})"

jsRotate :: Double -> Path
jsRotate = ffi "(function(rad,ctx,_){ctx.rotate(rad);})"

jsScale :: Double -> Double -> Path
jsScale = ffi "(function(x,y,ctx,_){ctx.scale(x,y);})"

jsPushState :: Path
jsPushState = ffi "(function(ctx,_){ctx.save();})"

jsPopState :: Path
jsPopState = ffi "(function(ctx,_){ctx.restore();})"

-- | アフィン変換を表現します。
class Affine f where
  affine :: E -> E -> E -> E -> E -> E -> f () -> f ()
  translate :: E2 -> f () -> f ()
  translate (p,q) a = affine 0 0 p 0 0 q a
  rotate :: E -> f () -> f ()
  rotate p a = let c = cos p; s = sin p in affine c (-s) 0 s c 0 a
  scale :: E2 -> f () -> f ()
  scale (p,q) a = affine p 0 0 0 q 0 a
  rotateAt :: E -> E2 -> f () -> f ()
  rotateAt a (x,y) = translate (x,y) . rotate a . translate (-x,-y)
  scaleAt :: E2 -> E2 -> f () -> f ()
  scaleAt a (x,y) = translate (x,y) . scale a . translate (-x,-y)

instance Affine Shape where
  affine a b c d e f (Shape reg pat _) = Shape region path () where
    region (p,q) = ext a $ \a -> ext b $ \b -> ext c $ \c -> ext d $ \d -> ext e $ \e -> ext f $ \f -> let
        ix = -b*f + b*q + e*c - e*p
        iy =  a*f - a*q - d*c + d*p
        z = b*d - a*e
      in reg (ix/z,iy/z)
    path = dom a $ \a -> dom b $ \b -> dom c $ \c -> dom d $ \d -> dom e $ \e -> dom f $ \f -> do
      jsPushState
      jsTransform a b c d e f
      pat
      jsPopState
  translate (a,b) (Shape reg pat _) = Shape region path () where
    region (p,q) = ext a $ \a -> ext b $ \b -> reg (p-a,q-b)
    path = dom a $ \a -> dom b $ \b -> do
      jsPushState
      jsTranslate a b
      pat
      jsPopState
  rotate a (Shape reg pat _) = Shape region path () where
    region (p,q) = ext a $ \a -> reg (p*cos a+q*sin a, -p*sin a+q*cos a)
    path = dom a $ \a -> do
      jsPushState
      jsRotate a
      pat
      jsPopState
  scale (a,b) (Shape reg pat _) = Shape region path () where
    region (p,q) = ext a $ \a -> ext b $ \b -> reg (p/a,q/b)
    path = dom a $ \a -> dom b $ \b -> do
      jsPushState
      jsScale a b
      pat
      jsPopState

inside :: R2 -> Shape () -> IO Bool
inside p (Shape b _ _) = b p
