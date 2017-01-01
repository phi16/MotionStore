{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

{- | 局所変数を使って自由にレンダリングできる'View'の定義などです。
     外部からは'post'と'Outbox'を使ってメッセージを送ることを想定しています。 -}
module Core.View (
  -- * View
  View, rendering, post,
  -- * 通常のView
  FocusEvent(..), makeView,
  -- * TextInput View
  InputEvent(..), makeInput, readInput) where

import Core.Util
import Core.World.Internal (withWorldState, viewManager)
import Core.World
import Core.Shape
import Core.Ease
import Core.Render.Internal (embedTransformation)
import Core.Render
import Data.List (intercalate)
import qualified Data.IntMap.Strict as IM
import Haste.DOM
import Haste.Events hiding (Focus)
import qualified Haste.Events as E
import Haste.Prim

-- | Viewです。
data View a = View !Int (Render ()) !(Outbox a)

-- | レンダリングするときはこれを使ってください。
--
-- > render $ view^.rendering
rendering :: SimpleGetter (View a) (Render ())
rendering = to (\(View _ r _) -> r)

-- | Viewに対してメッセージを投げるときに使います。
--
-- > (view^.post) ! message
post :: SimpleGetter (View a) (Outbox a)
post = to (\(View _ _ b) -> b)

-- | 'View'に渡ってくるイベントです。マウスの位置に応じて7種類飛んできます。
data FocusEvent = Enter   -- ^ View内部に来たとき
                | Move    -- ^ View内部でカーソルを移動したとき
                | Leave   -- ^ View内部から外に出たとき
                | Press   -- ^ View内部でマウスクリックしたとき
                | Drag    -- ^ マウスクリックした状態でカーソルを移動したとき
                | Release -- ^ マウスクリックした状態でView内部でクリックをやめたとき
                | Cancel  -- ^ マウスクリックした状態でView外部でクリックをやめたとき
  deriving (Eq,Show)

-- | Viewを構成します。
--
-- 'rendering'を ('applyTransform'で) 実行すると、その描画領域に実際の'View'の当たり判定が移動します。
-- なので気にせず好きなように'Affine'変換してください。
makeView :: (FocusEvent -> Maybe a) -- ^ 'FocusEvent'をViewに渡す方法です。'Nothing'にするとイベントが渡らなくなります。
         -> Shape ()                -- ^ 'View'の領域を指定する'Shape'です。
         -> Render ()               -- ^ 'View'の描画を指定する'Render'です。
         -> Handler a               -- ^ 'View'に送られてきたイベントを処理する'Handler'です。
         -> World (View a)
makeView focus shape render handler = do
  box <- spawn handler
  a' <- immediate 1
  b' <- immediate 0
  c' <- immediate 0
  d' <- immediate 0
  e' <- immediate 1
  f' <- immediate 0
  let
    shape' = affine
      (morph a') (morph b') (morph c')
      (morph d') (morph e') (morph f') shape
    fire evt = case focus evt of
      Nothing -> return ()
      Just x -> box ! x
  proc <- spawn $ \box -> do
    let
      recv :: World (Either Bool Bool)
      recv = receive box >>= \case
        Left r -> return $ Left r
        Right p -> io $ Right <$> inside p shape'
      outOfShape :: World Bool
      outOfShape = recv >>= \case
        Right True -> fire Enter >> hovering
        _ -> outOfShape
      hovering :: World Bool
      hovering = recv >>= \case
        Right False -> fire Leave >> outOfShape
        Left True -> fire Press >> dragging
        Right True -> fire Move >> hovering
        _ -> hovering
      dragging :: World Bool
      dragging = recv >>= \case
        Right False -> fire Leave >> dragOut
        Left False -> fire Release >> hovering
        Right True -> fire Drag >> dragging
        _ -> dragging
      dragOut :: World Bool
      dragOut = recv >>= \case
        Right True -> fire Enter >> dragging
        Left False -> fire Cancel >> outOfShape
        Right False -> fire Drag >> dragOut
        _ -> dragOut
    outOfShape
    return ()
  cnt <- withWorldState $ do
    count <- viewManager._1 <<%= (+1)
    viewManager._2 %= IM.insert count proc
    return count
  let
    render' = do
      render
      embedTransformation $ \a b c d e f -> do
        a' ==> a
        b' ==> b
        c' ==> c
        d' ==> d
        e' ==> e
        f' ==> f
        return ()
  return $ View cnt render' box

-- | 文字入力イベントです。とりあえず4種類あります。
data InputEvent = Focus         -- ^ テキストボックスをクリックしてフォーカスが当たったとき
                | Update String -- ^ 文字列が更新されたとき
                | Return String -- ^ フォーカスが当たっている状態でリターンキーを押したとき
                | Lost          -- ^ フォーカスが外れたとき
  deriving (Eq,Show)

-- | TextInput Viewを構成します。
--
-- 'rendering'を ('applyTransform'で) 実行すると、その描画領域に実際の'View'の位置が移動します。
-- なので気にせず好きな場所にTextInputを置いてください。
makeInput :: (InputEvent -> Maybe a) -- ^ 'InputEvent'をViewに渡す方法です。'Nothing'にするとイベントが渡らなくなります。
          -> E2                      -- ^ 左上の座標です。
          -> E2                      -- ^ サイズです。
          -> [Attribute]             -- ^ TextInputに指定できる属性です。色とか文字サイズとか。
          -> Handler a               -- ^ 'View'に送られてきたイベントを処理する'Handler'です。
          -> World (View a)
makeInput focus (x,y) (w,h) attrs handler = do
  box <- spawn handler
  let
    fire evt = case focus evt of
      Nothing -> return ()
      Just x -> box ! x
  dust <- spawn consume
  cnt <- withWorldState $ do
    count <- viewManager._1 <<%= (+1)
    viewManager._2 %= IM.insert count dust
    return count
  input <- newElem "input" `with` ([
    attr "type" =: "text",
    attr "name" =: ("input" ++ show cnt),
    attr "id" =: ("input" ++ show cnt),
    style "position" =: "absolute",
    style "outline" =: "0",
    style "background-color" =: "rgba(0,0,0,0.3)",
    style "border-color" =: "rgba(0,0,0,0)"] ++ attrs)
  appendChild documentBody input
  onEvent input KeyDown $ \dat -> do
    str <- getProp input "value"
    case keyCode dat of
      13 -> fire $ Return str
      _  -> fire $ Update str
  onEvent input KeyUp $ \dat -> do
    str <- getProp input "value"
    fire $ Update str
  onEvent input E.Focus $ \_ -> fire Focus
  onEvent input E.Blur  $ \_ -> fire Lost
  let
    render = translate (x,y) $ translate (w/2,h/2) $ do
      embedTransformation $ \a b c d e f -> io $ do
        x <- valueIO x; y <- valueIO y; w <- valueIO w; h <- valueIO h;
        case sequence [x,y,w,h] of
          Just [x,y,w,h] -> do
            let xs = intercalate "," $ map show [a,d,b,e,c,f]
            setStyle input "left"   $ show (-w/2) ++ "px"
            setStyle input "top"    $ show (-h/2) ++ "px"
            setStyle input "width"  $ show w ++ "px"
            setStyle input "height" $ show h ++ "px"
            setStyle input "transform" $ "matrix(" ++ xs ++ ")"
          Nothing -> return ()
      return ()
  return $ View cnt render box

-- | 'View'に入力された文字列を取得します。'makeView'で作った'View'に使うと'Nothing'が帰ってきます。
readInput :: View a -> World (Maybe String)
readInput (View d _ _) = io $ do
  e <- elemById $ "input" ++ show d
  case e of
    Just p -> getValue p
    Nothing -> return Nothing
