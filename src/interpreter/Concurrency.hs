module Concurrency where
import Control.Concurrent (MVar, newMVar, withMVar, forkIO, ThreadId, threadDelay, takeMVar, putMVar, newEmptyMVar, forkFinally)
import Control.Concurrent.STM (TChan, newTChanIO, atomically, readTChan, writeTChan)

type Mutex = MVar ()

-- channels

makeCh :: IO (TChan a)
makeCh = newTChanIO

readCh :: TChan a -> IO a
readCh = atomically . readTChan

writeCh :: TChan a -> a -> IO ()
writeCh ch v = atomically $ writeTChan ch v

-- threads

fork :: IO () -> IO Mutex
fork f = do
    handle <- newEmptyMVar
    _ <- forkFinally f (\_ -> putMVar handle ())
    return handle

wait :: Mutex -> IO ()
wait = takeMVar

