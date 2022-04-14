module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State.Lazy (gets, evalState, MonadState(get, put), StateT )
import Prelude hiding (lookup)
import Errors

data GoRuntime = GoRuntime {
    vars    :: Map Id (GoType, GoValue),
    consts  :: Map Id (GoType, GoValue),
    jumpSt  :: Maybe JumpStatement
}

emptyGoRuntime :: GoRuntime
emptyGoRuntime = GoRuntime {
    vars    = empty ,
    consts  = empty,
    jumpSt  = Nothing
}

getOrError :: Id -> GoRuntime -> (GoType, GoValue)
getOrError id r = case lookup id (vars r) of
    Just x -> x
    Nothing -> case lookup id (consts r) of
        Just x -> x
        Nothing -> errorVarNotInScope id


-- runtime monad

type Runtime a = StateT GoRuntime IO a

getVarValue :: Id -> Runtime GoValue
getVarValue id = gets (snd . getOrError id)

getVarType :: Id -> Runtime GoType
getVarType id = gets (fst . getOrError id)

isConst :: Id -> Runtime Bool
isConst id = do
  r <- get
  case lookup id (consts r) of
        Just x -> return True
        Nothing -> return False

putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar id (t, v) = do
  r <- get
  put r {vars = insert id (t,v) (vars r)}

getConst :: Id -> Runtime GoValue
getConst id = gets (snd . getOrError id)

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst id (t, v) = do
  r <- get
  if member id (consts r) then
    errorRedeclarationConst id
  else
    put r { consts = insert id (t,v) (consts r) }

getJumpSt :: Runtime (Maybe JumpStatement)
getJumpSt = do --gets jumpSt
  r <- get 
  return $ jumpSt r
  
putJumpSt :: Maybe JumpStatement  -> Runtime ()
putJumpSt s = do
  r <- get
  put r { jumpSt = s }