import Control.Concurrent.STM
import Control.Concurrent
import Control.Monad.State (StateT, liftIO, MonadTrans (lift))
import Control.Monad (join, forM_)
import GHC.IO (unsafePerformIO)
import Runtime (Runtime)

-- mutex for print

type Mutex = MVar ()

createMutex :: IO Mutex
createMutex = newMVar ()

createSafePrint :: Mutex -> String -> IO ()
createSafePrint mutex = withMVar mutex . const . putStrLn

-- base concurrency

children :: MVar [MVar ()]
{-# NOINLINE children #-}
children = unsafePerformIO (newMVar [])

waitForChildren :: IO ()
waitForChildren = do
    cs <- takeMVar children
    case cs of
        []   -> return ()
        m:ms -> do
            putMVar children ms
            takeMVar m
            waitForChildren

go :: IO () -> IO ThreadId
go io = do
    mvar <- newEmptyMVar
    childs <- takeMVar children
    putMVar children (mvar:childs)
    forkFinally io (\_ -> putMVar mvar ())

-- chanells 

makeCh :: IO (TChan a)
makeCh = newTChanIO

readCh :: TChan a -> IO a
readCh = atomically . readTChan

writeCh :: TChan a -> a -> IO ()
writeCh ch v = atomically $ writeTChan ch v


-- consumer :: TChan Int -> MVar () -> STM (IO ())
-- consumer ch mu = do
--     v <- readTChan ch
--     return $ createSafePrint mu (show v)

-- producer :: TChan Int -> Int -> STM ()
-- producer = writeTChan

-- main :: IO ()
-- main = do
--     mutex <- newMVar ()
--     c1 <- newTChanIO
--     forM_ [0..5]  (forkChild . atomically . producer c1)
--     forM_ [0..10] (const $ forkChild $ join $ atomically $ consumer c1 mutex)
--     forM_ [0..5]  (forkChild . atomically . producer c1)
--     waitForChildren