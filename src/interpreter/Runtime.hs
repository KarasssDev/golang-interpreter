module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift)
import Prelude hiding (lookup, head)
import Errors
import Control.Monad.Except

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
lookupVar id [] = Nothing
lookupVar id (x:xs) = case lookupVarInScope id x of
  Just v  -> Just v
  Nothing -> lookupVar id xs

containVar :: Id -> Scope -> Bool
containVar id sc = case lookupVarInScope id sc of
  Just v  -> True
  Nothing -> False

getOrError :: Id -> Runtime RVar
getOrError id = do
  r <- get
  let scs = scopes (headOr (frameStack r) emptyFrame) ++ [scope r]
  case lookupVar id scs of
    Just x  -> return x
    Nothing -> throwError $ exceptionVarNotInScope id



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
getVarValue id = do
  x <- getOrError id
  return $ getRVarValue x

getVarType :: Id -> Runtime GoType
getVarType id = do
  x <- getOrError id
  return $ getRVarType x

isConst :: Id -> Runtime Bool
isConst id = do
  rv <-  getOrError id
  case getRVarRType rv  of
        RConst -> return True
        RVar   -> return False


putRVar :: Id -> RVar -> Runtime ()
putRVar id v = do
  r <- get
  let stack = frameStack r
  case stack of
    []     -> put $ r {scope = insert id v (scope r)}
    (x:xs) -> case head (scopes x) of
      (Just scope) -> do
        let newScope = insert id v scope
        let newFrame = x {scopes = newScope:tail (scopes x) }
        put $ r {frameStack = newFrame : xs}
      Nothing -> throwError $ error "fix me"


putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar id (t, v) = putRVar id (t, v, RVar)

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst id (t, v) = do
  r <- get
  isCs <- isConst id
  if isCs then
    throwError $ exceptionRedeclarationConst id
  else
    putRVar id (t, v, RConst)

changeVar :: Id -> GoValue -> Runtime () -- add type check
changeVar id v = do
  r <- get
  (t,_,_) <- getOrError id
  if containVar id (scope r) then
    put $ r {scope = insert id (t,v,RVar) (scope r)}
  else do
    case head (frameStack r) of
      (Just x) -> do
        newFrame <- changeVarInFrame id v x
        put $ r {frameStack = newFrame : tail (frameStack r)}
      Nothing -> throwError internalErrorEmptyFrameStack

changeVarInFrame :: Id -> GoValue -> Frame -> Runtime Frame
changeVarInFrame id v fr = case scopes fr of
  lst@(x:xs) -> do
    t <- getVarType id
    let newScopes = changeElem lst (containVar id) (insert id (t,v,RVar))
    return $ fr {scopes = newScopes}
  []     -> throwError $ exceptionVarNotInScope id




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
    putAll ((id,t,v):xs) = do
      putVar id (t,v)
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