module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert, member)
import Control.Monad.State (gets, evalState, MonadState(get, put), State )
import Prelude hiding (lookup)
import Errors

data GoRuntime = GoRuntime {
    vars    :: Map Id (GoType, GoValue),
    consts  :: Map Id (GoType, GoValue),
    toPrint :: [String]
}

emptyGoRuntime :: GoRuntime
emptyGoRuntime = GoRuntime {
    vars = empty ,
    consts = empty,
    toPrint=[]
}

getOrError :: Id -> GoRuntime -> (GoType, GoValue)
getOrError id r = case lookup id (vars r) of
    Just x -> x
    Nothing -> case lookup id (consts r) of
        Just x -> x
        Nothing -> errorVarNotInScope id


-- runtime monad

type Runtime a = State GoRuntime a

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
  put GoRuntime {vars = insert id (t,v) (vars r), consts = consts r, toPrint = toPrint r}

getConst :: Id -> Runtime GoValue
getConst id = gets (snd . getOrError id)

putConst :: Id -> (GoType, GoValue) -> Runtime ()
putConst id (t, v) = do
  r <- get
  if member id (consts r) then
    errorRedeclarationConst id
  else
    put GoRuntime {vars = vars r, consts = insert id (t,v) (consts r), toPrint = toPrint r}

goPrint :: GoValue -> Runtime ()
goPrint v = do
  r <- get
  put GoRuntime {vars = vars r, consts = consts r, toPrint = show v : toPrint r}