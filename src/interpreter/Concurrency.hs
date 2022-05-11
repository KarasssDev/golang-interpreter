module Concurrency where
import Control.Concurrent (MVar, newMVar, withMVar, forkIO, ThreadId, threadDelay, takeMVar, putMVar, newEmptyMVar, forkFinally)
import Control.Concurrent.STM (TChan, newTChanIO, atomically, readTChan, writeTChan)

-- mutex

type Mutex = MVar ()

newMutex :: IO Mutex
newMutex = newMVar ()

safePrint :: Mutex -> String -> IO ()
safePrint mutex = withMVar mutex . const . putStrLn

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

-- must be deleted 

act :: Mutex -> Int -> String -> IO ()
act m t s = do
    threadDelay t
    safePrint m s

withDelay :: Int -> IO () -> IO ()
withDelay t f = threadDelay t >> f

cmain :: IO ()
cmain = do
    m <- newMutex
    let pr = safePrint m
    fork $ withDelay 1000 $ pr "lol"
    x <- fork $ withDelay 2000 $ pr "kek"
    fork $ withDelay 3000 $ pr "lmao"
    wait x
