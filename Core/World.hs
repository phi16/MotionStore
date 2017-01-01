{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

{- | 最も重要な'World'モナドの定義や操作関数のモジュールです。
     多分これも常にimportすることになります。 -}
module Core.World (
  -- * World Monad
  World, liftW, runWorld,
  -- * スレッド系
  -- | 基本的にはスレッドはいくらでも立てて良いです。
  -- 
  -- スレッド間通信の為に'Core.Util.Inbox' / 'Core.Util.Outbox'というものがあります。
  -- 
  -- 'Core.Util.spawn'関数で起動、'Core.Util.!' 関数で通信ができます。
  --
  -- 詳しくは"Core.Util"の"Haste.Concurrent"を参照。
  Handler, Emitter, emitting,
  sleep, handle, switch,
  waitUntil, distribute, division, consume,
  -- * 相互参照スレッド
  -- | 2つのスレッドで相互にメッセージを送りたい事があると思います。
  -- ですが順番に'Core.Util.spawn'するため'Core.Util.Outbox'を片方しか得ることができません。
  -- 
  -- 一度'hole'を作り、1つ目のスレッドで'obtain'することで「後で得た'Core.Util.Outbox'」を拾ってくることができます。
  --
  -- 'Core.Util.spawn'の代わりに'incarnate'することで'hole'に'Core.Util.Outbox'の実体を入れることができます。
  --
  -- @
  -- do
  --   a' \<- hole
  --   b \<- spawn $ \box -> do
  --     a \<- obtain a'
  --     forever $ do
  --       x \<- receive box
  --       a ! x
  --   incarnate a $ \box -> do
  --     forever $ do
  --       x <- receive box
  --       b ! (x+1)
  --   b ! 0
  -- @
  Hole, hole, obtain, incarnate,
  -- * 返事待ちスレッド
  -- | わざわざ'hole'するのもめんどくさいと思ったので作りました。
  Mail, interpret, (!!), (!?), oneway) where

import Prelude hiding ((!!))
import Core.World.Internal