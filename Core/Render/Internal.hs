{-# OPTIONS_HADDOCK hide #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Core.Render.Internal (
  Render, 
  Color, black, white,
  fill, stroke, clip, shadowed,
  getCanvasById, Canvas,
  render, withValue,
  Image, getImage, sizeOf, draw, drawClipped,
  cache,
  embedTransformation, applyTransform) where

import qualified Haste.Graphics.Canvas as G
import Haste.Graphics.Canvas (Canvas, getCanvasById)
import Core.Util
import Core.Ease
import Core.Front.Internal (imageCache, beginCache, endCache, getCache)
import Core.Shape.Internal
import Core.World
import Control.Monad.Skeleton
import Data.Maybe
import Haste.Foreign
import Haste.DOM.JSString
import Haste
import Data.Hashable

type Ctx = G.Ctx

jsBeginPath :: Ctx -> IO ()
jsBeginPath = ffi "(function(ctx){ctx.beginPath();})"

jsStroke :: Ctx -> IO ()
jsStroke = ffi "(function(ctx){ctx.stroke();})"

jsFill :: Ctx -> IO ()
jsFill = ffi "(function(ctx){ctx.fill();})"

jsTransform :: Ctx -> Double -> Double -> Double -> Double -> Double -> Double -> IO ()
jsTransform = ffi "(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})"

jsTranslate :: Ctx -> Double -> Double -> IO ()
jsTranslate = ffi "(function(ctx,x,y){ctx.translate(x,y);})"

jsRotate :: Ctx -> Double -> IO ()
jsRotate = ffi "(function(ctx,rad){ctx.rotate(rad);})"

jsScale :: Ctx -> Double -> Double -> IO ()
jsScale = ffi "(function(ctx,x,y){ctx.scale(x,y);})"

jsPushState :: Ctx -> IO ()
jsPushState = ffi "(function(ctx){ctx.save();})"

jsPopState :: Ctx -> IO ()
jsPopState = ffi "(function(ctx){ctx.restore();})"

jsResetCanvas :: Elem -> IO ()
jsResetCanvas = ffi "(function(e){e.width = e.width;})"

jsDrawImage :: Ctx -> Elem -> IO ()
jsDrawImage = ffi "(function(ctx,i){ctx.drawImage(i,0,0);})"

jsDrawImageClipped :: Ctx -> Elem -> Double -> Double -> Double -> Double -> IO ()
jsDrawImageClipped = ffi "(function(ctx,img,x,y,w,h){ctx.drawImage(img,x,y,w,h,0,0,w,h);})"

jsClip :: Ctx -> IO ()
jsClip = ffi "(function(ctx){ctx.clip();})"

color2JSString :: G.Color -> JSString
color2JSString (G.RGB r g b) =
  catJSStr "" ["rgb(", toJSString r, ",", toJSString g, ",", toJSString b, ")"]
color2JSString (G.RGBA r g b a) =
  catJSStr "" ["rgba(", toJSString r, ",",
                        toJSString g, ",",
                        toJSString b, ",",
                        toJSString a, ")"]

data RenderF a where
  EmbedDraw  :: (Ctx -> IO ()) -> a -> RenderF a
  EmbedIO    :: IO a -> RenderF a
  EmbedWorld :: (R -> R -> R -> R -> R -> R -> World ()) -> a -> RenderF a
  WithCtx    :: G.Ctx -> Render () -> a -> RenderF a
  Affined    :: E -> E -> E -> E -> E -> E -> Render () -> a -> RenderF a
  Translated :: E2 -> Render () -> a -> RenderF a
  Rotated    :: E  -> Render () -> a -> RenderF a
  Scaled     :: E2 -> Render () -> a -> RenderF a
  Switch     :: Render () -> Render () -> a -> RenderF a

instance Functor RenderF where
  fmap f (EmbedDraw h x) = EmbedDraw h $ f x
  fmap f (EmbedIO a) = EmbedIO $ fmap f a
  fmap f (EmbedWorld w x) = EmbedWorld w $ f x
  fmap f (WithCtx c a x) = WithCtx c a $ f x
  fmap f' (Affined a b c d e f h x) = Affined a b c d e f h $ f' x
  fmap f (Translated p a x) = Translated p a $ f x
  fmap f (Rotated    p a x) = Rotated    p a $ f x
  fmap f (Scaled     p a x) = Scaled     p a $ f x
  fmap f (Switch a b x) = Switch a b $ f x

-- | レンダリングする'Monad'です。'Affine'なのでアフィン変換もできます。
newtype Render a = Render (Skeleton RenderF a)
  deriving (Functor, Applicative, Monad)

instance MonadIO Render where
  liftIO a = Render $ bone $ EmbedIO a

ext :: MonadIO m => Value a -> (a -> m ()) -> m ()
ext v h = io (valueIO v) >>= \case
  Nothing -> return ()
  Just v' -> h v'

instance Affine Render where
  affine a b c d e f g = Render $ bone $ Affined a b c d e f g ()
  translate p a = Render $ bone $ Translated p a ()
  rotate    p a = Render $ bone $ Rotated    p a ()
  scale     p a = Render $ bone $ Scaled     p a ()

-- | 色の指定に使われる型です。R^4でEasingして'v4'で'Color'を作る、などすると良いとおもいます。
type Color = (E,E,E,E)

black, white :: Color
black = (0,0,0,1)
white = (1,1,1,1)

extColor :: Color -> IO G.Color
extColor (r,g,b,a) = do
  let
    clamp x = max 0 $ min 255 $ floor $ x*256
    clamp' x = max 0 $ min 1 x
  r' <- clamp <$> fromMaybe 0 <$> valueIO r
  g' <- clamp <$> fromMaybe 0 <$> valueIO g
  b' <- clamp <$> fromMaybe 0 <$> valueIO b
  a' <- clamp' <$> fromMaybe 1 <$> valueIO a
  return $ G.RGBA r' g' b' a'

-- | @'fill' c s@で、色@c@で図形@s@を塗りつぶします。
fill :: Color -> Shape () -> Render ()
fill c s = Render $ bone $ EmbedDraw f () where
  f ctx = do
    c' <- extColor c
    setProp (Elem $ toAny ctx) "fillStyle" $ color2JSString c'
    jsBeginPath ctx
    execPath s ctx True
    jsFill ctx

-- | @'stroke' w c s@で、色@c@で図形@s@の輪郭を幅@w@で描画します。
stroke :: E -> Color -> Shape () -> Render ()
stroke w c s = Render $ bone $ EmbedDraw f () where
  f ctx = ext w $ \w' -> do
    c' <- extColor c
    setProp (Elem $ toAny ctx) "strokeStyle" $ color2JSString c'
    setProp (Elem $ toAny ctx) "lineWidth" $ toJSString w'
    jsBeginPath ctx
    execPath s ctx False
    jsStroke ctx

-- | @'clip' s a@で、図形sの領域内のみに描画するようにした状態でaを実行します。
clip :: Shape () -> Render () -> Render ()
clip s a = open >> a >> close where
  open = Render $ bone $ EmbedDraw f () where
    f ctx = do
      jsPushState ctx
      jsBeginPath ctx
      execPath s ctx True
      jsClip ctx
  close = Render $ bone $ EmbedDraw f () where
    f ctx = do
      jsPopState ctx

-- | @'shadowed' p d c act@で、位置@p@に深さ@d@の色@c@の影がついた状態で@act@を実行します。
shadowed :: E2 -> E -> Color -> Render () -> Render ()
shadowed (x,y) d c act = open >> act >> close where
  open = Render $ bone $ EmbedDraw f () where
    f ctx = ext x $ \x -> ext y $ \y -> ext d $ \d -> do
      c' <- extColor c
      jsPushState ctx
      setProp (Elem $ toAny ctx) "shadowColor" $ color2JSString c'
      setProp (Elem $ toAny ctx) "shadowOffsetX" $ toJSString x
      setProp (Elem $ toAny ctx) "shadowOffsetY" $ toJSString y
      setProp (Elem $ toAny ctx) "shadowBlur" $ toJSString d
      jsBeginPath ctx
  close = Render $ bone $ EmbedDraw f () where
    f ctx = do
      jsPopState ctx

-- clip :: Shape () -> Render () -> Render ()

-- | 'Value''から値を取り出して処理を行います。
withValue :: Value a          -- ^ 取り出す対象の'Value'
          -> (a -> Render b)  -- ^ 取り出した値を使って行う処理
          -> Render (Maybe b) -- ^ 取り出しに失敗すると'Nothing'が帰ります。
withValue v h = do
  v' <- liftIO $ valueIO v
  case v' of
    Nothing -> return Nothing
    Just x -> Just <$> h x

-- | 画像を表現します。
data Image = Image {
  _imageElem :: Elem,
  _imageDraw :: Render (),
  _imageDrawClipped :: E2 -> E2 -> Render ()
}

-- | 画像をURLから取得します。何度呼び出してもコスト掛からないので好きなときに使えば良いと思います。
getImage :: String -> IO Image
getImage str = io $ do
  img <- imageCache str
  return $ makeImage img

makeImage :: Elem -> Image
makeImage e = let
    draw = Render $ bone $ EmbedDraw f () where
      f ctx = jsDrawImage ctx e
    drawClipped (x,y) (w,h) = Render $ bone $ EmbedDraw f () where
      f ctx = ext x $ \x -> ext y $ \y -> ext w $ \w -> ext h $ \h -> do
          jsDrawImageClipped ctx e x y w h
  in Image e draw drawClipped

widthOf :: MonadIO m => Image -> m Double
widthOf i = read <$> fromJSStr <$> getProp (_imageElem i) "width"
heightOf :: MonadIO m => Image -> m Double
heightOf i = read <$> fromJSStr <$> getProp (_imageElem i) "height"

-- | 画像のサイズを取得します。
sizeOf :: MonadIO m => Image -> m (Double, Double)
sizeOf i = (,) <$> widthOf i <*> heightOf i

-- | 画像を左上の点を原点に描画します。Lensを使ってください。
--
-- @
-- image <- getImage "res/image.png"
-- render $ do
--   image^.draw
-- @
draw :: SimpleGetter Image (Render ())
draw = to (\i -> _imageDraw i)

-- | @'drawClipped' p s@で、左上の点を@p@でサイズを@s@とした矩形領域の画像を、左上の点を原点に描画するLensになります。
--
-- @
-- atlas \<- getImage "res/atlas.png"
-- w \<- po . (/4) . fst \<$> sizeOf atlas
-- h \<- po . snd \<$> sizeOf atlas
-- render $ forM_ [0..3] $ \i -> do
--   translate (i*w) 0 $ atlas^.drawClipped (i*w,0) (w,h)
-- @
drawClipped :: E2 -> E2 -> SimpleGetter Image (Render ())
drawClipped o s = to (\i -> _imageDrawClipped i o s)

-- | 描画結果のキャッシュを行います。制御値に変化があると再描画します。
cache :: HashableIO a => String -- ^ キャッシュに付ける一意な名前
      -> E2                     -- ^ 領域の左上座標
      -> E2                     -- ^ 領域のサイズ
      -> E2                     -- ^ キャッシュの解像度
      -> a                      -- ^ 制御値
      -> Render ()              -- ^ 描画内容
      -> Render ()
cache str (x,y) (w,h) (rx,ry) v act = ext x $ \x -> ext y $ \y -> ext w $ \w -> ext h $ \h -> ext rx $ \rx -> ext ry $ \ry -> do
  let
    drawAction = do
      v' <- io $ hashIO v
      ctx' <- io $ beginCache str x y w h rx ry v'
      when (ctx'/=nullValue) $ do
        ctx <- io $ fromAny ctx'
        Render $ bone $ WithCtx ctx act ()
        io $ endCache str v'
      img <- io $ makeImage <$> getCache str
      translate (po x,po y) $ scale (po w/po rx, po h/po ry) $ img^.draw
    worldAction = act
  Render $ bone $ Switch drawAction worldAction ()

embedTransformation :: (R -> R -> R -> R -> R -> R -> World ()) -> Render ()
embedTransformation f = Render $ bone $ EmbedWorld f () 

-- | 描画します。
render :: Canvas -> Render () -> IO ()
render cvs (Render f) = G.render cvs $ G.withContext $ shrinkIO f where
  shrinkIO :: Skeleton RenderF a -> Ctx -> IO a
  shrinkIO r ctx = case debone r of
    Return x -> return x
    EmbedDraw d x :>>= f -> do
      d ctx
      shrinkIO (f x) ctx
    EmbedIO   a :>>= f -> a >>= \x -> shrinkIO (f x) ctx
    EmbedWorld _ x :>>= f -> shrinkIO (f x) ctx
    WithCtx c (Render u) x :>>= f -> do
      shrinkIO u c
      shrinkIO (f x) ctx
    Affined a b c d e f (Render u) x :>>= h -> do
      affineR a b c d e f (shrinkIO u) ctx
      shrinkIO (h x) ctx
    Translated p (Render a) x :>>= f -> do
      translateR p (shrinkIO a) ctx
      shrinkIO (f x) ctx
    Rotated p (Render a) x :>>= f -> do
      rotateR p (shrinkIO a) ctx
      shrinkIO (f x) ctx
    Scaled p (Render a) x :>>= f -> do
      scaleR p (shrinkIO a) ctx
      shrinkIO (f x) ctx
    Switch (Render a) _ x :>>= f -> do
      shrinkIO a ctx
      shrinkIO (f x) ctx

affineR :: E -> E -> E -> E -> E -> E -> (Ctx -> IO ()) -> Ctx -> IO ()
affineR a b c d e f h ctx = ext a $ \a -> ext b $ \b -> ext c $ \c -> ext d $ \d -> ext e $ \e -> ext f $ \f -> do
  jsPushState ctx
  jsTransform ctx a b c d e f
  h ctx
  jsPopState ctx
translateR :: E2 -> (Ctx -> IO ()) -> Ctx -> IO ()
translateR (a,b) f ctx = ext a $ \a -> ext b $ \b -> do
  jsPushState ctx
  jsTranslate ctx a b
  f ctx
  jsPopState ctx
rotateR :: E -> (Ctx -> IO ()) -> Ctx -> IO ()
rotateR a f ctx = ext a $ \a -> do
  jsPushState ctx
  jsRotate ctx a
  f ctx
  jsPopState ctx
scaleR :: E2 -> (Ctx -> IO ()) -> Ctx -> IO ()
scaleR (a,b) f ctx = ext a $ \a -> ext b $ \b -> do
  jsPushState ctx
  jsScale ctx a b
  f ctx
  jsPopState ctx

-- | 'Core.View.View'をレンダリングしたときの座標を取得し、実際の位置を移動させます。
-- 使うときは、'render'に渡したものと同じ@Render ()@を毎フレーム'applyTransform'にも渡せば良いです。
applyTransform :: Render () -> World ()
applyTransform (Render f) = world f 1 0 0 0 1 0 where
  affProd :: R -> R -> R -> R -> R -> R -> R -> R -> R -> R -> R -> R -> (R -> R -> R -> R -> R -> R -> a) -> a
  affProd a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 f = let
      c0 = a0 * b0 + a3 * b1
      c1 = a1 * b0 + a4 * b1
      c2 = a2 * b0 + a5 * b1 + b2
      c3 = a0 * b3 + a3 * b4
      c4 = a1 * b3 + a4 * b4
      c5 = a2 * b3 + a5 * b4 + b5
    in f c0 c1 c2 c3 c4 c5
  world :: Skeleton RenderF a -> R -> R -> R -> R -> R -> R -> World a
  world r a b c d e f = case debone r of
    Return x -> return x
    EmbedDraw _ x :>>= h -> world (h x) a b c d e f
    EmbedIO act :>>= h -> liftIO act >>= \x -> world (h x) a b c d e f
    EmbedWorld w x :>>= h -> do
      w a b c d e f
      world (h x) a b c d e f
    WithCtx _ (Render u) x :>>= h -> do
      world u a b c d e f
      world (h x) a b c d e f
    Affined a' b' c' d' e' f' (Render act) x :>>= h -> do
      a' <- valueOf a'
      b' <- valueOf b'
      c' <- valueOf c'
      d' <- valueOf d'
      e' <- valueOf e'
      f' <- valueOf f'
      affProd a' b' c' d' e' f' a b c d e f $ world act
      world (h x) a b c d e f
    Translated (p',q') (Render act) x :>>= h -> do
      p <- valueOf p'
      q <- valueOf q'
      affProd 1 0 p 0 1 q a b c d e f $ world act
      world (h x) a b c d e f
    Rotated p' (Render act) x :>>= h -> do
      p <- valueOf p'
      let
        ca = cos p
        sa = sin p
      affProd ca (-sa) 0 sa ca 0 a b c d e f $ world act
      world (h x) a b c d e f
    Scaled (p',q') (Render act) x :>>= h -> do
      p <- valueOf p'
      q <- valueOf q'
      affProd p 0 0 0 q 0 a b c d e f $ world act
      world (h x) a b c d e f
    Switch _ (Render u) x :>>= h -> do
      world u a b c d e f
      world (h x) a b c d e f