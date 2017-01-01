{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

{- | 図形を表す'Shape'の定義などです。
     "Core.View"での当たり判定や、"Core.Render"での描画領域の指定に使います。 -}
module Core.Shape (
  -- * Shape Monad
  Shape, E, E2,
  -- * 図形
  bezier, line, circle, rect, centerRect, roundRect, polygon,
  Font, TextAlign(..), TextBase(..), text,
  -- * 無効領域
  disable,
  -- * 図形の変換
  Affine(..),
  -- * 当たり判定
  inside) where

import Core.Shape.Internal