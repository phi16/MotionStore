{-# LANGUAGE PackageImports #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

{- | なんだかんだ一番力を入れたところ。
     Easingをいつでも楽に扱えるようになってる、はず、です・・・ -}
module Core.Ease (
  -- * Base types
  Ease, Morph(..),
  -- * Ease構築
  ease, immediate,
  -- * Ease発動
  easeTo, easeWait, easeHandle, forceTo,
  -- * Ease operators
  (~~>), (==>), (~~>!), (~~>?),
  -- * Easing functions
  Easing,
  -- ** 基本
  -- | デフォルトは'easeIn'です。
  -- 
  -- > ease 0 200 $ quint
  linear, quad, cubic, quart, quint, smooth, expo, back,
  -- ** 挙動指定
  -- | 最初に付けます。
  --
  -- > ease 0 100 $ easeInOut.expo
  easeIn, easeOut, easeInOut,
  -- ** 特殊
  sequent, reflect,
  -- * Value型
  Value, valueOf, valueIO,
  v2, v3, v4,
  -- * Valueへ持ち上げる
  po, act, morph,
  -- * なにかで使うかも
  target, duration, easing, reflected,
  -- * Renderのcache制御用
  HashableIO(..)) where

import Haste.Concurrent
import "mtl" Control.Monad.State.Strict
import Core.Util
import Core.World.Internal (easeRegister)
import Core.World
import Control.Applicative
import Data.String
import Data.Hashable
import Data.Bits (xor)

-- | Easingを管理する値です。こいつを保持しておけば後でうにょうにょ動かせる。
-- 'ease'で構築、'easeTo'で操作、'morph'で利用、とかです。
data Ease a = Ease R Easing (MVar (a,(a,a,R,Bool)))

-- | Easing可能な型です。線形補間が出来ればOK。あとで追加しても良いです。
class Morph a where
  lerp :: R -> a -> a -> a

instance Morph Double where
  lerp a x y = x*(1-a)+y*a
instance (Morph a, Morph b) => Morph (a,b) where
  lerp a (x1,x2) (y1,y2) = (lerp a x1 y1, lerp a x2 y2)
instance (Morph a, Morph b, Morph c) => Morph (a,b,c) where
  lerp a (x1,x2,x3) (y1,y2,y3) = (lerp a x1 y1, lerp a x2 y2, lerp a x3 y3)
instance (Morph a, Morph b, Morph c, Morph d) => Morph (a,b,c,d) where
  lerp a (x1,x2,x3,x4) (y1,y2,y3,y4) = (lerp a x1 y1, lerp a x2 y2, lerp a x3 y3, lerp a x4 y4)
instance (Morph a) => Morph [a] where
  lerp a xs ys = zipWith (lerp a) xs ys

-- | Easingを構築します。
ease :: a              -- ^ 初期値
     -> Double         -- ^ 時間
     -> Easing         -- ^ Easing function
     -> World (Ease a) -- ^ Easeオブジェクト
ease x dur e = Ease dur e <$> newMVar (x,(x,x,0,False))

-- | 瞬時に移動するタイプのEasingを構築します。文字列とかにも使えます。
immediate :: a -> World (Ease a)
immediate x = ease x 1 linear

-- | うにょーんって目的地まで動かします。一度指定すればあとは勝手にシステムが動かしてくれます。
easeTo :: Morph a => Ease a -> a -> World ()
easeTo e v = easeHandle e v $ const $ return () 

-- | 目的地に到達するまでそこで待機します。
easeWait :: Morph a => Ease a -> a -> World ()
easeWait e v = waitUntil $ \done -> easeHandle e v $ const done

-- | 目的地に到達したら与えられたハンドラを実行します。
easeHandle :: Morph a => Ease a  -- ^ Easingオブジェクト
           -> a                  -- ^ 目的地
           -> (Bool -> World ()) -- ^ ハンドラ。引数は「正常終了なら'True'」です。
           -> World ()
easeHandle (Ease dur easing e) v act = do
  let
    from = _2._1
    to = _2._2
    cur = _2._3
  withMVar e $ do
    (fromV,toV,curV,_) <- use _2
    from .= lerp (easing id $ curV / dur) fromV toV
    to .= v
    cur .= 0
  let protect e = withMVar e $ _2._4 .= False
  easeRegister (protect e) $ withMVar e $ do
    proceed <- use $ _2._4
    if not proceed
      then do
        cur += 1
        cur %= min dur
        (fromV,toV,curV,_) <- use _2
        _1 .= lerp (easing id $ curV / dur) fromV toV
        _2._4 .= True
        if curV < dur
          then return True
          else lift (act True) >> return False
      else lift (act False) >> return False

-- | 瞬時に目的地に移動します。
forceTo :: Ease a -> a -> World ()
forceTo (Ease _ _ e) v = do
  (!_,(!_,!_,!_,!_)) <- liftW $ readMVar e
  withMVar e $ do
    let
      from = _2._1
      to = _2._2
      cur = _2._3
    from .= v
    to .= v
    cur .= 1
    _1 .= v

infix 2 ~~>, ==>, ~~>!, ~~>?
(==>) :: Ease a -> a -> World ()
(~~>), (~~>!) :: Morph a => Ease a -> a -> World ()
(~~>?) :: Morph a => Ease a -> a -> (Bool -> World ()) -> World ()
-- | 'easeTo'です
(~~>) = easeTo
-- | 'forceTo'です
(==>) = forceTo
-- | 'easeWait'です
(~~>!) = easeWait
-- | 'easeHandle'です
(~~>?) = easeHandle

-- | Easing functionはこれで指定します。'.'で合成ができます。
type Easing = (R -> R) -> (R -> R)

linear,quad,cubic,quart,quint :: Easing
linear f x = f x
quad f x = f x^2
cubic f x = f x^3
quart f x = f x^4
quint f x = f x^5
smooth :: Easing
smooth f x = f $ x*x*(3-x)/2
expo :: Easing
expo f x = f $ 2**(-(1-x)*10)
back :: Easing
back f x = f $ x*x*(2.70158*x-1.70158)
easeIn,easeOut,easeInOut :: Easing
easeIn f x = f x
easeOut f x = 1 - f (1-x)
easeInOut f x
  | x < 0.5   = f (x*2) / 2
  | otherwise = 1 - f (2-2*x) / 2

-- | 複数のオブジェクトを微妙にずらしてEaseするような挙動をします。
--
-- >  es <- forM [0..9] $ \i -> ease 0 100 $ sequent i 10 0.3.easeInOut.expo
sequent :: Int    -- ^ インデックス
        -> Int    -- ^ 全体の数
        -> R      -- ^ 実行する時間(0 < x < 1)
        -> Easing
sequent i' s' d f x = f $ bound p where
  (i,s) = (i',s') & both %~ fromIntegral
  p = x/d - i/(s-1)*(1/d-1)
  bound x = max 0 $ min 1 x

-- | easeInとeaseOutを反転させます。行って戻る動きに使ってください。(cf : 'reflected')
reflect :: Easing
reflect f x = 1 - f (1 - x)

-- | Easingオブジェクトの目的地を取得します。
target :: Ease a -> World a
target (Ease _ _ e) = withMVar e $ use $ _2._2

-- | Easingにかかる時間を取得します。逆に時間を書き換えることもできます(永続ではない)。
--
-- @
-- e <- ease 0 100 $ easeInOut . expo
-- (duration .~ 50) e ~~> 1
-- @
duration :: Lens' (Ease a) Double
duration = lens sa sbt where
  sa (Ease e1 e2 x) = e1
  sbt (Ease e1 e2 x) nw = Ease nw e2 x
-- | EasingFunctionを取得します。逆にEasingFunctionを書き換えることもできます(永続ではない。)。
--
-- @
-- e <- ease 0 100 $ easeInOut . expo
-- (easing .~ linear) e ~~> 1
-- @
easing :: Lens' (Ease a) Easing
easing = lens sa sbt where
  sa (Ease e1 e2 x) = e2
  sbt (Ease e1 e2 x) nw = Ease e1 nw x

-- | Easeの向きを反転します。
--
-- @
-- y <- ease 0 25 $ easeOut . quad
-- fork $ forever $ do
--   y ~~>! 100
--   reflected y ~~>! 0
-- @
reflected :: Ease a -> Ease a
reflected = easing %~ (reflect.)

-- | 描画時に用いられる型です。'IO'や'Ease'は'Value'になれるので、わざわざ値を取り出す必要がないのです。
data Value a = Exact a
             | Action (IO a)
             | forall e. Morph (Ease e) (e -> a)
             | forall e. MorphAct (Ease e) (e -> IO a)

instance Functor Value where
  fmap f (Exact x) = Exact $ f x
  fmap f (Morph e h) = Morph e $ f.h
  fmap f (MorphAct e h) = MorphAct e $ fmap f.h
  fmap f (Action a) = Action $ fmap f a

opLift :: (a -> a -> a) -> Value a -> Value a -> Value a
opLift o (Exact x) (Exact y) = Exact $ x`o`y
opLift o (Exact x) (Morph e f) = Morph e $ (x`o`).f
opLift o (Exact x) (MorphAct e f) = MorphAct e $ fmap (x`o`).f
opLift o (Exact x) (Action y) = Action $ (x`o`) <$> y
opLift o (Morph e f) (Exact y) = Morph e $ (`o`y).f
opLift o (Morph e f) (Action y) = MorphAct e $ \e -> (f e`o`) <$> y
opLift o (MorphAct e f) (Exact y) = MorphAct e $ fmap (`o`y).f
opLift o (MorphAct e f) (Action y) = MorphAct e $ \e -> liftA2 o (f e) y
opLift o (Action x) (Exact y) = Action $ (`o`y) <$> x
opLift o (Action x) (Morph e f) = MorphAct e $ \e -> (`o`f e) <$> x
opLift o (Action x) (MorphAct e f) = MorphAct e $ \e -> liftA2 o x (f e)
opLift o (Action x) (Action y) = Action $ liftA2 o x y
opLift o e1 e2 = Action $ do
  v1 <- valueIO e1
  v2 <- valueIO e2
  case (v1,v2) of
    (Just x, Just y) -> return $ x`o`y
    _ -> error "Unable to operate opLift"

instance Num a => Num (Value a) where
  (+) = opLift (+)
  (*) = opLift (*)
  abs = fmap abs
  negate = fmap negate
  signum = fmap signum
  fromInteger i = Exact $ fromInteger i

instance Fractional a => Fractional (Value a) where
  (/) = opLift (/)
  fromRational r = Exact $ fromRational r

instance Floating a => Floating (Value a) where
  pi = Exact pi
  exp = fmap exp
  log = fmap log
  sqrt = fmap sqrt
  (**) = opLift (**)
  logBase = opLift logBase
  sin = fmap sin
  cos = fmap cos
  tan = fmap tan
  asin = fmap asin
  acos = fmap acos
  atan = fmap atan
  sinh = fmap sinh
  cosh = fmap cosh
  tanh = fmap tanh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh

instance IsString (Value String) where
  fromString = Exact

-- | Easingオブジェクトも'Value'になれます。
morph :: Ease a -> Value a
morph e = Morph e id

-- | 値を取り出します。条件分岐とかに使ってください。
valueOf :: Value a -> World a
valueOf (Exact x) = return x
valueOf (Action x) = io x
valueOf (Morph (Ease _ _ e) f) = liftW $ f <$> fst <$> readMVar e
valueOf (MorphAct (Ease _ _ e) f) = liftW $ io . f =<< fst <$> readMVar e

-- | 'IO'でも取り出せますが、失敗するかも(しないはず)なので'Maybe'がつきます。
valueIO :: Value a -> IO (Maybe a)
valueIO (Exact x) = return $ Just x
valueIO (Morph (Ease _ _ e) f) = fmap (f.fst) <$> peekMVar e
valueIO (MorphAct (Ease _ _ e) f) = peekMVar e >>= \case
  Nothing -> return Nothing
  Just (x,_) -> Just <$> f x
valueIO (Action x) = Just <$> x

-- | 描画時はそれぞれのEasingを渡す必要があるので、適当に分配してください。
--
-- > rect (0,0) (v2 $ act screenSize)
v2 :: Functor f => f (a,b) -> (f a, f b)
v3 :: Functor f => f (a,b,c) -> (f a, f b, f c)
v4 :: Functor f => f (a,b,c,d) -> (f a, f b, f c, f d)
v2 v = (view _1 <$> v, view _2 <$> v)
v3 v = (view _1 <$> v, view _2 <$> v, view _3 <$> v)
v4 v = (view _1 <$> v, view _2 <$> v, view _3 <$> v, view _4 <$> v)

-- | ただの値は'Value'になれます。
po :: a -> Value a
po = Exact

-- | 'IO'の値も'Value'になれます。
act :: IO a -> Value a
act = Action

-- | 'Core.Render.cache'時に制御値として使える型です。
class HashableIO a where
  hashIO :: a -> IO Int

combine :: Int -> Int -> Int
combine h1 h2 = (h1 * 16777619) `xor` h2

instance Hashable a => HashableIO (IO a) where
  hashIO x = x >>= return . hash
instance HashableIO Bool where
  hashIO = return . hash
instance HashableIO Char where
  hashIO = return . hash
instance HashableIO Double where
  hashIO = return . hash
instance HashableIO Float where
  hashIO = return . hash
instance HashableIO Int where
  hashIO = return . hash
instance HashableIO Integer where
  hashIO = return . hash
instance HashableIO () where
  hashIO = return . hash
instance HashableIO Void where
  hashIO = return . hash
instance HashableIO a => HashableIO (Maybe a) where
  hashIO Nothing = return 0
  hashIO (Just x) = combine 1 <$> hashIO x
instance HashableIO a => HashableIO [a] where
  hashIO xs = foldr combine 0 <$> mapM hashIO xs
instance HashableIO a => HashableIO (Ease a) where
  hashIO x = hashIO $ morph x
instance HashableIO a => HashableIO (Value a) where
  hashIO x = valueIO x >>= hashIO
instance (HashableIO a, HashableIO b) => HashableIO (a,b) where
  hashIO (a,b) = do
    a' <- hashIO a
    b' <- hashIO b
    return $ a'`combine`b'
instance (HashableIO a, HashableIO b, HashableIO c) => HashableIO (a,b,c) where
  hashIO (a,b,c) = do
    a' <- hashIO a
    b' <- hashIO b
    c' <- hashIO c
    return $ a'`combine`b'`combine`c'
instance (HashableIO a, HashableIO b, HashableIO c, HashableIO d) => HashableIO (a,b,c,d) where
  hashIO (a,b,c,d) = do
    a' <- hashIO a
    b' <- hashIO b
    c' <- hashIO c
    d' <- hashIO d
    return $ a'`combine`b'`combine`c'`combine`d'
instance (HashableIO a, HashableIO b, HashableIO c, HashableIO d, HashableIO e) => HashableIO (a,b,c,d,e) where
  hashIO (a,b,c,d,e) = do
    a' <- hashIO a
    b' <- hashIO b
    c' <- hashIO c
    d' <- hashIO d
    e' <- hashIO e
    return $ a'`combine`b'`combine`c'`combine`d'`combine`e'
instance (HashableIO a, HashableIO b, HashableIO c, HashableIO d, HashableIO e, HashableIO f) => HashableIO (a,b,c,d,e,f) where
  hashIO (a,b,c,d,e,f) = do
    a' <- hashIO a
    b' <- hashIO b
    c' <- hashIO c
    d' <- hashIO d
    e' <- hashIO e
    f' <- hashIO f
    return $ a'`combine`b'`combine`c'`combine`d'`combine`e'`combine`f'
instance (HashableIO a, HashableIO b, HashableIO c, HashableIO d, HashableIO e, HashableIO f, HashableIO g) => HashableIO (a,b,c,d,e,f,g) where
  hashIO (a,b,c,d,e,f,g) = do
    a' <- hashIO a
    b' <- hashIO b
    c' <- hashIO c
    d' <- hashIO d
    e' <- hashIO e
    f' <- hashIO f
    g' <- hashIO g
    return $ a'`combine`b'`combine`c'`combine`d'`combine`e'`combine`f'`combine`g'