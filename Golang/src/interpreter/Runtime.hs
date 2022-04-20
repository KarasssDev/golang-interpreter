module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT, lift)
import Prelude hiding (lookup, head)
import Errors

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
lookupVar id (x:xs) = case (lookupVarInScope id x) of
  Just v  -> Just v
  Nothing -> lookupVar id xs

containVar :: Id -> Scope -> Bool
containVar id sc = case (lookupVarInScope id sc) of
  Just v  -> True
  Nothing -> False

getOrError :: Id -> GoRuntime -> RVar
getOrError id r = case (lookupVar id scs) of
  Just x -> x
  Nothing -> errorVarNotInScope id
  where
    scs = (scopes (head (frameStack r) (emptyFrame))) ++ [(scope r)]


type Runtime a = StateT GoRuntime IO a


pushFrame :: Runtime ()
pushFrame = do
  r <- get
  put $ r {frameStack = emptyFrame:(frameStack r) }

popFrame :: Runtime Frame
popFrame = do
  r <- get
  let f = head (frameStack r) internalErrorEmptyFrameStack
  put $ r {frameStack = tail (frameStack r)}
  return f

pushScope :: Runtime ()
pushScope = do
  r <- get
  let stack    = frameStack r
  let topFrame = head stack (error "fix me")
  let newFrame = topFrame {scopes = empty : (scopes topFrame)}
  put $ r {frameStack = newFrame:(tail stack)}

popScope :: Runtime ()
popScope = do
  r <- get
  let stack    = frameStack r
  let topFrame = head stack (error "fix me")
  let newFrame = topFrame {scopes = tail (scopes topFrame)}
  put $ r {frameStack = newFrame:(tail stack)}

getVarValue :: Id -> Runtime GoValue
getVarValue id = gets (getRVarValue . getOrError id)

getVarType :: Id -> Runtime GoType
getVarType id = gets (getRVarType . getOrError id)

isConst :: Id -> Runtime Bool
isConst id = do
  r <- get
  let rv = getOrError id r
  case (getRVarRType rv)  of
        RConst -> return True
        RVar   -> return False


putRVar :: Id -> RVar -> Runtime ()  
putRVar id v = do
  r <- get
  let stack = frameStack r
  case stack of
    []     -> put $ r {scope = insert id v (scope r)}
    (x:xs) -> do
      let scope    = head (scopes x) (error "empty scopes")
      let newScope = insert id v scope
      let newFrame = x {scopes = newScope:(tail (scopes x)) }
      put $ r {frameStack = newFrame : xs}

putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar id (t, v) = putRVar id (t, v, RVar)

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst id (t, v) = do
  r <- get
  isCs <- isConst id
  if isCs then
    errorRedeclarationConst id
  else
    putRVar id (t, v, RConst)

changeVar :: Id -> GoValue -> Runtime () -- add type check
changeVar id v = do
  r <- get
  let (t,_,_) = getOrError id r
  if (containVar id (scope r)) then
    put $ r {scope = insert id (t,v,RVar) (scope r)} 
  else do
    newFrame <- changeVarInFrame id v (head (frameStack r) internalErrorEmptyFrameStack)
    put $ r {frameStack = newFrame : (tail (frameStack r))}

changeVarInFrame :: Id -> GoValue -> Frame -> Runtime Frame
changeVarInFrame id v fr = case (scopes fr) of
  lst@(x:xs) -> do
    t <- getVarType id
    let newScopes = changeElem lst (\e -> containVar id e) (\e -> insert id (t,v,RVar) e)
    return $ fr {scopes = newScopes}
  []     -> errorVarNotInScope id




getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = do 
  r <- get
  return $ jumpSt $ head (frameStack r) internalErrorEmptyFrameStack
  
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
    helper (x:xs) p l = if (p x) then (l, x, xs) else helper xs p (l ++ [x])
    helper []     p l = undefined

changeElem :: [a] -> (a -> Bool) -> (a -> a) -> [a]
changeElem lst p f = l ++ [(f x)] ++ r
  where
    (l,x,r) = splitBy lst p

changeTopFrame :: (Frame -> Frame) -> Runtime ()
changeTopFrame f = do
  r <- get
  let fs = frameStack r
  let topFrame = head fs internalErrorEmptyFrameStack
  let newFrame = f topFrame
  put $ r { frameStack = newFrame:(tail fs)}

head :: [a] -> a -> a
head (x:xs) e = x
head []     e = e