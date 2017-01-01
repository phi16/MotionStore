{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

{- | 描画に用いる'Render'の定義などです。
     ついでに"Core.View"の位置補正なども行います。 -}
module Core.Render (
  -- * Render
  Render, fill, stroke, clip, shadowed, withValue,
  -- * Color
  Color, black, white,
  -- * Canvas
  getCanvasById, Canvas,
  -- * レンダリング
  render,
  -- * 画像
  Image, getImage, sizeOf, draw, drawClipped,
  -- * キャッシュ
  cache,
  -- * View関連
  applyTransform) where

import Core.Render.Internal