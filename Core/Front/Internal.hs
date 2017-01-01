{-# OPTIONS_HADDOCK hide #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}

module Core.Front.Internal (
  screenSize,
  start,
  imageCache,
  beginCache, endCache, getCache,
  onFrame,
  handle,
  handCursor, autoCursor,
  connect,
  nya
) where

import Haste.Prim
import Haste.DOM
import Haste.Foreign
import Haste.Graphics.Canvas
import Haste.Graphics.AnimationFrame
import Haste.WebSockets
import Control.Monad
import "mtl" Control.Monad.State.Strict
import Core.Util
import Core.World

-- | キャンバスのサイズです。好きにつかってください。
screenSize :: IO (R, R)
screenSize = (,) <$> w () <*> h () where
  w = ffi "(function(){return Util.width;})"
  h = ffi "(function(){return Util.height;})"

-- | 'Main.main'関数の一番最初に呼び出してください。
start :: IO ()
start = ffi "(Util.onload)" ()

imageCache :: String -> IO Elem
imageCache name = ffi "(Util.imageCache)" $ toJSStr name

beginCache :: String -> R -> R -> R -> R -> R -> R -> Int -> IO JSAny
beginCache = ffi "(Util.beginCache)"

endCache :: String -> Int -> IO ()
endCache = ffi "(Util.endCache)"

getCache :: String -> IO Elem
getCache = ffi "(Util.getCache)"

-- | 毎フレーム呼び出される関数を指定します。
onFrame :: MVar s       -- ^ 使う状態の変数
        -> (s -> IO ()) -- ^ 描画処理などをするAction
        -> World ()
onFrame s h = io $ let
    proc _ = void $ do
      s' <- peekMVar s
      maybe (return ()) h s'
      requestAnimationFrame proc
  in proc undefined

-- | リンクを押しそうなやつ
handCursor :: World ()
handCursor = io $ ffi "(function(){document.body.style.cursor = \"hand\";})" ()
-- | いつもの
autoCursor :: World ()
autoCursor = io $ ffi "(function(){document.body.style.cursor = \"auto\";})" ()

-- | 通信します。
connect :: String                  -- ^ 相手先のアドレス
        -> Outbox (Maybe JSString) -- ^ メッセージ受信用'Outbox'。接続に失敗すると'Nothing'が来ます。
        -> Handler JSString        -- ^ 'spawn'するとメッセージ送信用'Outbox'を得ることができます。
connect url outbox inbox = liftW $ withWebSocket url rec err act where
  rec ws str = outbox ! Just str
  err = outbox ! Nothing
  act ws = forever $ receive inbox >>= wsSend ws

-- | JS側から値を拾ってこれます。@Util.nya[name]=value;@とすることで値を入れ込めます。初期値は0です。
nya :: JSString -> IO R
nya = ffi "(Util.nyaGet)"