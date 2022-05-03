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
  let scs = scopes (headOr (frameStack r) emptyFrame)
  case (lookupVar idr scs, lookupVarInScope idr (scope r)) of
    (Just x, Just y)  -> return x
    (Just x, Nothing) -> return x
    (Nothing, Just y) ->  return y
    (Nothing, Nothing) -> throwError $ exceptionVarNotInScope idr



type Runtime a = ExceptT String (StateT GoRuntime IO) a

pushFrame :: Runtime ()
pushFrame = do
  r <- get
  put $ r {frameStack = emptyFrame:frameStack r }

popFrame :: Runtime Frame
popFrame = do
  r <- get
  case frameStack r of
    (fr:frs) -> do
      put $ r {frameStack = frs}
      return fr
    []   -> throwError internalErrorEmptyFrameStack

pushScope :: Runtime ()
pushScope = changeScopes (empty:)

popScope :: Runtime ()
popScope = changeScopes tail

changeScopes :: ([Scope] -> [Scope]) -> Runtime ()
changeScopes f = do
  r <- get
  case frameStack r of
    (fr:frs) -> do
        let newFrame = fr {scopes = f (scopes fr)}
        put $ r {frameStack = newFrame:frs}
    []         -> error "fix me"


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
    (x:xs) -> case scopes x of
      (sc:scs) -> do
        let newScope = insert idr v sc
        let newFrame = x {scopes = newScope:scs}
        put $ r {frameStack = newFrame : xs}
      [] -> throwError $ error "fix me"


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
      case frameStack r of
        (fr:frs) -> do
          newFrame <- changeVarInFrame idr v fr
          put $ r {frameStack = newFrame : frs}
        [] -> throwError internalErrorEmptyFrameStack

changeVarInFrame :: Id -> GoValue -> Frame -> Runtime Frame
changeVarInFrame idr v fr = case scopes fr of
  lst@(x:xs) -> do
    t <- getVarType idr
    let newScopes = changeElem (containVar idr) lst (insert idr (t,v,RVar))
    case newScopes of
      Just s  -> return $ fr {scopes = s}
      Nothing -> throwError $ exceptionVarNotInScope idr
  []     -> throwError $ exceptionVarNotInScope idr

getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = do
  r <- get
  case frameStack r of
    (fr:frs) -> return  $ jumpSt fr
    [] -> throwError internalErrorEmptyFrameStack

putJumpSt :: Maybe JumpStatement  -> Runtime ()
putJumpSt s = changeTopFrame (\x -> x {jumpSt = s})


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

changeElem :: (a -> Bool) -> [a] -> (a -> a) -> Maybe [a]
changeElem p lst f = case splitBy p lst of
    Just (l,x,r) -> Just $ l ++ [f x] ++ r
    Nothing      -> Nothing

changeTopFrame :: (Frame -> Frame) -> Runtime ()
changeTopFrame f = do
  r <- get
  let fs = frameStack r
  case fs of
      (fr:frs) -> do
        let newFrame = f fr
        put $ r { frameStack = newFrame:frs}
      []  -> throwError internalErrorEmptyFrameStack


headOr :: [a] -> a -> a
headOr (x:xs) e = x
headOr []     e = e