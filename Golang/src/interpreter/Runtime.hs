module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT )
import Prelude hiding (lookup)
import Errors

data RVarType = RConst | RVar
type RVar = (GoType, GoValue, RVarType)
type VarsMap = Map Id RVar
type Scope = VarsMap


data GoRuntime = GoRuntime {
    scope     :: Scope,
    callStack :: [Scope],
    returnVal :: Maybe GoValue,
    jumpSt    :: Maybe JumpStatement
}

emptyGoRuntime :: GoRuntime
emptyGoRuntime = GoRuntime {
    scope      = empty,
    callStack  = [],
    returnVal  = Nothing,
    jumpSt     = Nothing
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
getOrError id r = case (lookupVar id scopes) of
  Just x -> x
  Nothing -> errorVarNotInScope id
  where
    scopes = (callStack r) ++ [(scope r)]


-- runtime monad

type Runtime a = StateT GoRuntime IO a


push :: Runtime ()
push = do
  r <- get
  put $ r {callStack = empty:(callStack r) }

pop :: Runtime ()
pop = do
  r <- get 
  put $ r {callStack = tail (callStack r)}


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
  case (callStack r) of
    []     -> put $ r {scope = insert id v (scope r)}
    (x:xs) -> put $ r {callStack = (insert id v x) : xs}

putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar id (t, v) = putRVar id (t, v, RVar)


changeVar :: Id -> GoValue -> Runtime()
changeVar id v = do
  r <- get
  let (t,_,_) = getOrError id r
  if not (containVar id (scope r)) then
    put $ r {callStack = helper [] (callStack r) id v r}
  else
    put $ r {scope = insert id (t,v, RVar) (scope r)} 
  where 
    helper lst (x:xs) id v r = if (containVar id x) 
      then let (t,_,_) = (getOrError id r) in (lst ++ [(insert id (t,v,RVar) x)] ++ xs)
      else helper (lst ++ [x]) xs id v r
    helper lst [] id v r = errorVarNotInScope id

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst id (t, v) = do
  r <- get
  isCs <- isConst id
  if isCs then
    errorRedeclarationConst id
  else
    putRVar id (t, v, RConst)

getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = do 
  r <- get 
  return $ jumpSt r
  
putJumpSt :: Maybe JumpStatement  -> Runtime ()
putJumpSt s = do
  r <- get
  put $ r { jumpSt = s }

getReturnVal :: Runtime (Maybe GoValue)
getReturnVal = do
  r <- get
  return $ returnVal r

putReturnVal :: Maybe GoValue -> Runtime ()
putReturnVal s = do
  r <- get
  put r { returnVal = s }

-- putArgs :: [GoExpr] -> [Id] -> Runtime ()
