module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift)
import Prelude hiding (lookup, head)
import Errors
import Control.Monad.Except
import Types

data RVarType = RConst | RVar
type RVar = (GoType, GoValue, RVarType)
type Scope = Map Id RVar

type Exception = String

data Frame = Frame {
    scopes    :: [Scope],
    returnVal :: GoValue,
    jumpSt    :: Maybe JumpStatement
}

emptyFrame :: Frame
emptyFrame = Frame {
    scopes    = [],
    returnVal = VNil,
    jumpSt    = Nothing
}


data GoRuntime = GoRuntime {
    scope      :: Scope,
    frameStack :: [Frame]
}

emptyGoRuntime :: GoRuntime
emptyGoRuntime = GoRuntime {
    scope      = empty,
    frameStack  = []
}

getRVarType :: RVar -> GoType
getRVarType (t, _, _) = t

getRVarValue :: RVar -> GoValue
getRVarValue (_, v, _) = v

getRVarRType :: RVar -> RVarType
getRVarRType (_, _, rt) = rt

lookupVarInScope :: Id -> Scope -> Maybe RVar
lookupVarInScope = lookup

lookupVar :: Id -> [Scope] -> Maybe RVar
lookupVar idr [] = Nothing
lookupVar idr (x:xs) = case lookupVarInScope idr x of
  Just v  -> Just v
  Nothing -> lookupVar idr xs

containVar :: Id -> Scope -> Bool
containVar idr sc = case lookupVarInScope idr sc of
  Just v  -> True
  Nothing -> False

getOrError :: Id -> Runtime RVar
getOrError idr = do
  r <- get
  let scs = scopes (headOrValue (frameStack r) emptyFrame)
  case (lookupVar idr scs, lookupVarInScope idr (scope r)) of
    (Just x, Just y)  -> return x
    (Just x, Nothing) -> return x
    (Nothing, Just y) ->  return y
    (Nothing, Nothing) -> throwError $ exceptionVarNotInScope idr

type Runtime a = ExceptT String (StateT GoRuntime IO) a

-- Frames 

changeFrames :: ([Frame] -> [Frame]) -> Runtime ()
changeFrames f = do
  r <- get
  let newFrames = f $ frameStack r
  put $ r { frameStack = newFrames }


changeTopFrame :: (Frame -> Frame) -> Runtime ()
changeTopFrame f = do
  r <- get
  let fs = frameStack r
  case fs of
      (fr:frs) -> do
        let newFrame = f fr
        put $ r { frameStack = newFrame:frs}
      []  -> throwError internalErrorEmptyFrameStack

getFrame :: Runtime Frame
getFrame = do
  frames <- getFrames
  case frames of
    (fr:frs) -> return fr
    []       -> throwError internalErrorEmptyFrameStack

getFrames :: Runtime [Frame]
getFrames = frameStack <$> get

pushFrame :: Runtime ()
pushFrame = changeFrames (emptyFrame:)

popFrame :: Runtime Frame
popFrame = do
  fr <- getFrame
  changeFrames tail
  return fr

isEmptyStack :: Runtime Bool
isEmptyStack = do
  r <- get
  case frameStack r of
    (fr:frs) -> return False
    []       -> return True

-- Scopes 

changeGlobalScope :: (Scope -> Scope) -> Runtime ()
changeGlobalScope f = do
  r <- get
  put $ r { scope = f $ scope r }

changeScopes :: ([Scope] -> [Scope]) -> Runtime ()
changeScopes f = do
  r <- get
  changeTopFrame $ \fr -> fr {scopes = f (scopes fr)}

getScope :: Runtime Scope
getScope =  getScopes >>= headOrException internalErrorEmptyScopes

getScopes :: Runtime [Scope]
getScopes = scopes <$> getFrame

changeScope :: (Scope -> Scope) -> Runtime ()
changeScope f = do
  scs <- getScopes
  newScs <- changeHeadOrException f internalErrorEmptyScopes scs
  changeScopes $ const newScs

pushScope :: Runtime ()
pushScope = changeScopes (empty:)

popScope :: Runtime ()
popScope = changeScopes tail

-- vars and consts 

getVarValue :: Id -> Runtime GoValue
getVarValue idr = do
  x <- getOrError idr
  return $ getRVarValue x

getVarType :: Id -> Runtime GoType
getVarType idr = do
  x <- getOrError idr
  return $ getRVarType x

isConst :: Id -> Runtime Bool
isConst idr = do
  rv <-  getOrError idr
  case getRVarRType rv  of
        RConst -> return True
        RVar   -> return False

putRVar :: Id -> RVar -> Runtime ()
putRVar idr v = do
  frames <- getFrames
  case frames of
    []       -> changeGlobalScope $ insert idr v
    (fr:frs) -> changeScope $ insert idr v

putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar idr (t, v) = putRVar idr (t, v, RVar)

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst idr (t, v) = do
  r <- get
  isCs <- isConst idr
  if isCs then
    throwError $ exceptionRedeclarationConst idr
  else
    putRVar idr (t, v, RConst)

changeVar :: Id -> GoValue -> Runtime ()
changeVar idr v = do
    r <- get
    t <- getVarType idr
    let typeCh = typeCheckVT v t
    let exep   = exceptionAssigmnetsType idr v t
    checkWithException typeCh exep
    if containVar idr (scope r) then
      changeGlobalScope $ insert idr (t,v,RVar)
    else do
      scs <- getScopes
      let newScope = changeElem (containVar idr) (insert idr (t,v,RVar)) scs
      case newScope of
        Just v  -> changeScopes $ const v
        Nothing -> throwError $ exceptionVarNotInScope idr

-- jump statements 

getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = jumpSt <$> getFrame

putJumpSt :: Maybe JumpStatement  -> Runtime ()
putJumpSt s = changeTopFrame (\x -> x {jumpSt = s})

-- functions

putArgs :: [GoValue] -> [(Id, GoType)] -> Runtime ()
putArgs argv argsign = do
  let args = zip3 (map fst argsign) (map snd argsign) argv
  forM_ args (\(idr, t, v) -> putVar idr (t,v))

putReturnValue :: GoValue -> Runtime ()
putReturnValue v = changeTopFrame (\x -> x {returnVal = v})


-- helper functions

splitBy :: (a -> Bool) -> [a] -> Maybe ([a], a, [a])
splitBy p lst = case find p lst of
    Just x  -> Just (takeWhile (not . p) lst, x, tail (dropWhile (not . p) lst))
    Nothing -> Nothing
    where
      find p (x:xs) = if p x then Just x else find p xs
      find p []     = Nothing

changeElem :: (a -> Bool) -> (a -> a) -> [a] -> Maybe [a]
changeElem p f lst = case splitBy p lst of
    Just (l,x,r) -> Just $ l ++ [f x] ++ r
    Nothing      -> Nothing

headOrValue :: [a] -> a -> a
headOrValue (x:xs) v = x
headOrValue []     v = v

headOrException :: Exception -> [a] -> Runtime a
headOrException e (x:xs) = return x
headOrException e []     = throwError e

changeHeadOrException :: (a -> a) -> Exception -> [a] -> Runtime [a]
changeHeadOrException  _ e []     = throwError e
changeHeadOrException  f _ (x:xs) = return  $ f x:xs

checkWithException :: Bool -> Exception -> Runtime ()
checkWithException flag e = if flag then return () else throwError e 
