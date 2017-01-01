{-# LANGUAGE LambdaCase #-}

module Core.UI (button) where

import Core.Util
import Core.World
import Core.Front
import Core.View

-- | ぼたんです。勝手にマウスポインタが変わります。
button :: World () -- ^ マウスが'View'に載ってないときのアクションです。
       -> World () -- ^ マウスが'View'に載っているときのアクションです。
       -> World () -- ^ マウスがボタンをクリックしたときのアクションです。
       -> Handler FocusEvent
button def hov act box = forever $ do
  def
  waitFor (==Enter) $ receive box
  hov
  -- handCursor
  waitFor (==Leave) $ receive box >>= \case
    Press -> do
      u <- waitFor ((==Cancel)|?|(==Release)) $ receive box
      if u == Cancel
        then return Leave
        else act >> return u
    e -> return e
  -- autoCursor