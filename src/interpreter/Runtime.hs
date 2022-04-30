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
getRVarType (t, v, rt) = t

getRVarValue :: RVar -> GoValue
getRVarValue (t, v, rt) = v

getRVarRType :: RVar -> RVarType
getRVarRType (t, v, rt) = rt

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
  let scs = scopes (headOr (frameStack r) emptyFrame) ++ [scope r]
  case lookupVar idr scs of
    Just x  -> return x
    Nothing -> throwError $ exceptionVarNotInScope idr



type Runtime a = ExceptT String (StateT GoRuntime IO) a

pushFrame :: Runtime ()
pushFrame = do
  r <- get
  put $ r {frameStack = emptyFrame:frameStack r }

popFrame :: Runtime Frame
popFrame = do
  r <- get
  case head (frameStack r) of
    (Just fr) -> do  
      put $ r {frameStack = tail (frameStack r)}
      return fr
    Nothing   -> throwError internalErrorEmptyFrameStack

pushScope :: Runtime ()
pushScope = changeScopes (empty:)

popScope :: Runtime ()
popScope = changeScopes tail

changeScopes :: ([Scope] -> [Scope]) -> Runtime ()
changeScopes f = do
  r <- get
  let stack    = frameStack r
  case head stack of
    (Just topFrame) -> do
        let newFrame = topFrame {scopes = f (scopes topFrame)}
        put $ r {frameStack = newFrame:tail stack}
    Nothing         -> error "fix me"


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
  r <- get
  let stack = frameStack r
  case stack of
    []     -> put $ r {scope = insert idr v (scope r)}
    (x:xs) -> case head (scopes x) of
      (Just scope) -> do
        let newScope = insert idr v scope
        let newFrame = x {scopes = newScope:tail (scopes x) }
        put $ r {frameStack = newFrame : xs}
      Nothing -> throwError $ error "fix me"


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
  (t,_,_) <- getOrError idr
  if not (typeCheckVT v t) then 
    throwError $ exceptionAssigmnetsType idr v t
  else
    if containVar idr (scope r) then
      put $ r {scope = insert idr (t,v,RVar) (scope r)}
    else do
      case head (frameStack r) of
        (Just x) -> do
          newFrame <- changeVarInFrame idr v x
          put $ r {frameStack = newFrame : tail (frameStack r)}
        Nothing -> throwError internalErrorEmptyFrameStack

changeVarInFrame :: Id -> GoValue -> Frame -> Runtime Frame
changeVarInFrame idr v fr = case scopes fr of
  lst@(x:xs) -> do
    t <- getVarType idr
    let newScopes = changeElem lst (containVar idr) (insert idr (t,v,RVar))
    return $ fr {scopes = newScopes}
  []     -> throwError $ exceptionVarNotInScope idr




getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = do
  r <- get
  case head (frameStack r) of
    Just x -> return  $ jumpSt x
    Nothing -> throwError internalErrorEmptyFrameStack

putJumpSt :: Maybe JumpStatement  -> Runtime ()
putJumpSt s = changeTopFrame (\x -> x {jumpSt = s})


putArgs :: [GoValue] -> [(Id, GoType)] -> Runtime ()
putArgs argv argsign = do
  let args = zip3 (map fst argsign) (map snd argsign) argv
  putAll args
  where
    putAll [] = return ()
    putAll ((idr,t,v):xs) = do
      putVar idr (t,v)
      putAll xs

putReturnValue :: GoValue -> Runtime ()
putReturnValue v = changeTopFrame (\x -> x {returnVal = v})


-- helper functions
splitBy :: [a] -> (a -> Bool) -> ([a], a, [a])
splitBy lst p = helper lst p []
  where
    helper (x:xs) p l = if p x then (l, x, xs) else helper xs p (l ++ [x])
    helper []     p l = undefined

changeElem :: [a] -> (a -> Bool) -> (a -> a) -> [a]
changeElem lst p f = l ++ [f x] ++ r
  where
    (l,x,r) = splitBy lst p

changeTopFrame :: (Frame -> Frame) -> Runtime ()
changeTopFrame f = do
  r <- get
  let fs = frameStack r
  case head fs of
      (Just topFrame) -> do
        let newFrame = f topFrame
        put $ r { frameStack = newFrame:tail fs}
      Nothing  -> throwError internalErrorEmptyFrameStack
  

head :: [a] -> Maybe a
head (x:xs) = Just x
head []     = Nothing

headOr :: [a] -> a -> a
headOr (x:xs) e = x
headOr []     e = e