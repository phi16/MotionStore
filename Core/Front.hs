{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TupleSections #-}

{- | Hasteや生JS/HTMLに近い方の管理をします。 -}
module Core.Front (
  -- * Haste export
  module Haste.Events,
  -- * 画面サイズ
  screenSize,
  -- * 起動
  start,
  -- * 描画用関数
  onFrame,
  -- * イベント取得
  handle,
  -- * カーソル変更
  handCursor, autoCursor,
  -- * WebSocket通信
  connect,
  -- * デバッグ用
  nya
) where
  
import Haste.Events
import Core.Front.Internal