{-# OPTIONS_HADDOCK hide #-}

{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

module Core.World.Internal (
  World, liftW, runWorld,
  withWorldState, viewManager, easeRegister, 
  Handler, Emitter, emitting,
  sleep, handle, switch,
  waitUntil, distribute, division, consume,
  Hole, hole, obtain, incarnate,
  Mail, interpret, (!!), (!?), oneway) where

import Prelude hiding ((!!))
import Core.Util
import Haste.DOM (document)
import Haste.Concurrent
import Haste.Events
import "mtl" Control.Monad.State.Strict
import "mtl" Control.Monad.Cont.Class
import qualified "monads-tf" Control.Monad.Cont.Class as CC
import Data.PQueue.Min hiding ((!!))
import qualified Data.IntMap.Strict as IM
import Data.Void

data Framed a = Framed Int a
instance Eq (Framed a) where
  Framed x _ == Framed y _ = x == y
instance Ord (Framed a) where
  Framed x _ `compare` Framed y _ = x`compare`y

type EaseHandler = [(World (), World Bool)]
type FrameCount = Int
type QueueHandler = MinQueue (Framed (MVar ()))
type ViewManager = (Int, IM.IntMap (Outbox (Either Bool R2)))
data WorldState = WorldState !EaseHandler !FrameCount !QueueHandler !ViewManager

easeListener :: Lens' WorldState EaseHandler
easeListener = lens sa sbt where
  sa (WorldState ls fc sq vm) = ls
  sbt (WorldState ls fc sq vm) b = WorldState b fc sq vm
frameCount :: Lens' WorldState FrameCount
frameCount = lens sa sbt where
  sa (WorldState ls fc sq vm) = fc
  sbt (WorldState ls fc sq vm) b = WorldState ls b sq vm
sleepQueue :: Lens' WorldState QueueHandler
sleepQueue = lens sa sbt where
  sa (WorldState ls fc sq vm) = sq
  sbt (WorldState ls fc sq vm) b = WorldState ls fc b vm
viewManager :: Lens' WorldState ViewManager
viewManager = lens sa sbt where
  sa (WorldState ls fc sq vm) = vm
  sbt (WorldState ls fc sq vm) b = WorldState ls fc sq b

initialWorldState :: WorldState
initialWorldState = WorldState [] 0 empty (0,IM.empty)

instance MonadCont CIO where
  callCC = CC.callCC

-- | IO, Event Handling, Concurrent Execution, First Class Continuationなど、
-- なんでもありのモナドです。基本的にはこれをベースに用います。
newtype World a = World (StateT (MVar WorldState) CIO a)
  deriving (Functor,Applicative,Monad,MonadIO,MonadCont,MonadState (MVar WorldState))

withWorldState :: StateT WorldState World a -> World a
withWorldState a = get >>= \v -> withMVar v a

instance MonadConc World where
  liftConc = World . lift
  fork (World a) = World $ do
    s <- get
    lift $ fork $ void $ execStateT a s
    return ()

instance MonadEvent World where
  mkHandler h = World $ do
    s <- get
    lift $ mkHandler $ \v -> let
        World h' = h v
      in void $ execStateT h' s

-- | 'readMVar'などの'CIO' Actionを'World'に持ち上げます。
liftW :: CIO a -> World a
liftW = liftConc

easeRegister :: World () -> World Bool -> World ()
easeRegister p h = withWorldState $ do
  easeListener %= ((p,h):)

-- | 'spawn'関数に渡す関数の型です。'Inbox'から値を'receive'関数で受け取ることができます。
--
-- @
-- thread \<- spawn $ \box -> do
--   x <- receive box
--   io $ print x
-- thread ! 5
-- @
type Handler a = Inbox a -> World ()
-- | 何も受信しないスレッドです。大体は'fork'で済むのであまり使わないです。
--
-- > void . spawn . emitting ≡ fork
type Emitter = Handler Void

-- | 'Emitter'を作るときはこれで明示すると良いとおもいます。
emitting :: World () -> Emitter
emitting = const

frameHandler :: World ()
frameHandler = forever $ do
  liftW $ wait 16
  -- Easing
  ls <- withWorldState $ use easeListener
  forM ls fst
  ls' <- filterM snd ls
  withWorldState $ easeListener .= ls'
  -- Sleep Queue
  fc <- withWorldState $ use frameCount
  while $ do
    m <- withWorldState $ getMin <$> use sleepQueue
    case m of
      Nothing -> return False
      Just (Framed c v)
        | c > fc -> return False
        | otherwise -> do
          liftW $ putMVar v ()
          withWorldState $ sleepQueue %= deleteMin
          return True
  withWorldState $ frameCount += 1

mouseHandler :: Handler (MouseEvent, MouseData)
mouseHandler e = forever $ do
  evt <- receive e
  vm <- withWorldState $ use $ viewManager._2
  let po b = forM_ vm (!b)
  case evt of
    (MouseUp  , _) -> po $ Left False
    (MouseDown, _) -> po $ Left True
    (MouseMove, p) -> po $ Right $ mouseCoords p & both %~ fromIntegral
    _ -> return ()

initWorld :: World a -> World a
initWorld w = do
  fork frameHandler
  mh <- spawn mouseHandler
  handle MouseDown (MouseDown,) mh
  handle MouseMove (MouseMove,) mh
  handle MouseUp (MouseUp,) mh
  w

-- | 大体は'concurrent'と一緒に使うとおもいます。
runWorld :: World a -> CIO a
runWorld w = do
  ws <- newMVar initialWorldState
  let World w' = initWorld w
  evalStateT w' ws

-- | 与えられたフレーム数待ちます。
sleep :: Int -> World ()
sleep i = do
  c <- withWorldState $ use frameCount
  v <- newEmptyMVar
  withWorldState $ sleepQueue %= insert (Framed (c+i) v)
  liftW $ takeMVar v
  return ()

-- | "Haste.Events"に従ってイベントを受信するようにします。
handle :: Event evt => evt     -- ^ 取得するイベント('MouseDown'など)
       -> (EventData evt -> t) -- ^ イベントデータの受け取り方
       -> Outbox t             -- ^ イベント送信先
       -> World ()
handle e h box = void $ onEvent document e ((box!) . h)

-- | コンテキストスイッチします。なんか無限ループが起きたらこれをいれよう。
switch :: World ()
switch = liftW $ wait 0

-- | 'exit'関数が呼ばれるまでそこで待ちます。'!!'とか'Core.Ease.easeHandle'と共に使うことを想定しています。
waitUntil :: (World () -> World ()) -- ^ 引数が'exit'関数です。
          -> World ()               -- ^ そのうち戻ってきます。
waitUntil h = do
  v <- io $ newEmptyMVar
  h $ liftW $ putMVar v ()
  liftW $ takeMVar v
  switch
  return ()

-- | 'Inbox'を'Either'に従って分配します。
distribute :: Inbox (Either a b) -> (Outbox a, Outbox b) -> World ()
distribute box (o1,o2) = forever $ receive box >>= \case
  Left  a -> o1 ! a
  Right b -> o2 ! b

-- | 'Inbox'を条件に従って分配します。
division :: Inbox a -> (a -> Bool) -> (Outbox a, Outbox a) -> World ()
division box f (o1,o2) = forever $ receive box >>= \x -> if f x
  then o1 ! x
  else o2 ! x

-- | 何もしないタイプの'Handler'です。特にすることないときはこれを使おう。
consume :: Handler a
consume box = fork $ forever $ receive box

-- Mutual communication technique
newtype Hole a = Hole (MVar (Outbox a))

-- | 後で'Outbox'を入れるための穴を構成します。
hole :: World (Hole a)
hole = Hole <$> newEmptyMVar

-- | 穴から'Outbox'を取り出します。
obtain :: Hole a -> World (Outbox a)
obtain (Hole h) = liftW $ takeMVar h

-- | 穴に'Outbox'を詰めます。
incarnate :: Hole a -> Handler a -> World (Outbox a)
incarnate (Hole x) h = do
  box <- spawn h
  liftW $ putMVar x box
  return box

-- | 基本的には「メッセージ'a'の返事'b'を貰う」型です。
data Mail a b = Mail a (b -> World ())

-- | 'receive'の代わりに'interpret'を使うことで返事を返すことができます。(強制)
--
-- @
-- do
--   double \<- spawn $ \box -> forever $ do
--     interpret box $ \x -> do
--       return $ 2*x
--   y \<- double !? 5
--   io $ print y
-- @
interpret :: Inbox (Mail a b) -> (a -> World b) -> World ()
interpret box f = do
  Mail x cont <- receive box
  y <- f x
  cont y

postMail :: Outbox (Mail a b) -> a -> (b -> World ()) -> World ()
postMail box x cont = box ! Mail x cont

-- | 返事が来たら与えたActionを実行します。
(!!) :: Outbox (Mail a ()) -> a -> World () -> World ()
(box !! x) act = postMail box x (const act)

-- | 返事が来るまでその場で待ちます。
(!?) :: Outbox (Mail a b) -> a -> World b
box !? x = do
  v <- newEmptyMVar
  postMail box x $ \y -> liftW $ putMVar v y
  liftW $ takeMVar v

-- | 返事が来ても何もしないタイプのメールを作ります。そのまま'!'で送りましょう。
oneway :: a -> Mail a b
oneway x = Mail x (const $ return ())