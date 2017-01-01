{-# LANGUAGE PackageImports #-}
{-# LANGUAGE LambdaCase #-}

{- | とりあえずimportしておけばいいモジュールです。
     よく使う便利な関数とかが入ってます。
     ほしいものがあったら好きに追加してください。 -}

module Core.Util (
  -- * Exports
  -- | Lens, State Monadなどの良く使うやつをexportしています。
  module Data.Void,
  module Control.Monad.State.Strict,
  module Lens.Micro,
  module Lens.Micro.Mtl,
  -- ** Haste.Concurrent
  MonadConc(..), concurrent,
  MVar, newMVar, newEmptyMVar, takeMVar, putMVar, peekMVar, readMVar,
  Outbox, Inbox, spawn, (!), (<!), receive,
  -- * よく使う型
  Z, R, R2,
  -- * IO系
  io, makeMVar, withMVar,
  -- * Monad系
  (??), onJust,
  -- * ループ系
  while, loop, waitFor,
  -- * 条件式
  -- | 基本的には条件ラムダ式をそのまま論理演算するためのものです。
  -- 
  -- > (==3) |?| (==5) ≡ \x -> x == 3 || x == 5
  (&?&),(|?|),
  -- * 添字付きループ
  -- | 添字付きで'forM'を使いたいときのための関数です。
  --
  -- >>> iforM_ [2,5,6] $ \i x -> print (i,x)
  -- (0,2)
  -- (1,5)
  -- (2,6)
  iforM, iforM_) where

import Data.Void
import Lens.Micro
import Lens.Micro.GHC
import Lens.Micro.Mtl
import "mtl" Control.Monad.State.Strict
import "mtl" Control.Monad.Cont
import Control.Applicative
import Control.Monad
import Haste
import Haste.Concurrent

type Z = Integer
type R = Double
type R2 = (R,R)

-- | 'IO' Actionを持ち上げます。
-- 'MonadIO'制約は使うときは大体は'm' = 'Core.World.World'だとおもいます。
--
-- >>> io $ print 42
-- 42
io :: MonadIO m => IO a -> m a
io = liftIO

-- | 簡単に言うと変数を作ります。
makeMVar :: MonadIO m => a -> m (MVar a)
makeMVar = io . newMVar

-- | 変数の中身を取り出した状態で計算を行います。
-- Stata Monad上で動くのでLensでうまいこと操作したり'lift'関数で持ち上げたりすることになります。
--
-- @
-- do
--   x <- makeMVar 0
--   withMVar x $ do
--     id += 5
--   x' <- liftW $ readMVar x
--   io $ print x' -- 5
-- @
withMVar :: (MonadIO m, MonadConc m) => MVar a -> StateT a m b -> m b
withMVar v act = do
  x <- liftConc $ takeMVar v
  (res,x') <- runStateT act x
  liftConc $ putMVar v x'
  return res

-- | 'runStateT'するときに便利だけど使わないかも
(??) :: Functor f => f (a -> b) -> a -> f b
fab ?? a = ($a) <$> fab

-- | 'Just'のときに処理を行うときに便利。
onJust :: Monad m => Maybe a -> (a -> m ()) -> m Bool
onJust Nothing h = return False
onJust (Just x) h = h x >> return True

-- | 条件を満たす間ループします。
while :: Monad m => m Bool -> m ()
while a = a >>= \case
  False -> return ()
  True -> while a

-- | 引数に渡された'exit'関数を呼ぶまで処理をループします。m = 'World'だとおもいます、だいたい。
loop :: MonadCont m => a         -- ^ 初期値
     -> ((b -> m c) -> a -> m a) -- ^ 'exit'関数と前回の状態を受取り、次の状態を返す関数
     -> m b                      -- ^ 結果 : 'exit'に渡された引数
loop ini run = callCC $ \exit -> let
    proc x = run exit x >>= proc
  in proc ini

-- | 条件を満たす値が来るまでループします。満たした値を返すのが'while'との違い。
waitFor :: Monad m => (a -> Bool) -> m a -> m a
waitFor f a = a >>= \case
  x | f x -> return x
    | otherwise -> waitFor f a

infixl 3 &?&, |?|

(&?&), (|?|) :: Applicative m => m Bool -> m Bool -> m Bool
(&?&) = liftA2 (&&)
(|?|) = liftA2 (||)

iforM :: Monad m => [a] -> (Int -> a -> m b) -> m [b]
iforM xs f = mapM (uncurry f) $ zip [0..] xs
iforM_ :: Monad m => [a] -> (Int -> a -> m b) -> m ()
iforM_ xs f = void $ iforM xs f