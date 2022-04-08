module Runtime where
import Ast
import Data.Map (Map, lookup, empty, insert)
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

getOrError :: Id -> GoRuntime -> GoValue
getOrError id r = case lookup id (vars r) of
    Just (t, v) -> v
    Nothing -> errorVarNotInScope id


-- runtime monad

type Runtime a = State GoRuntime a

getVar :: Id -> Runtime GoValue
getVar id = gets (getOrError id)

putVar :: Id -> (GoType, GoValue) -> Runtime ()
putVar id (t, v) = do
  r <- get
  put GoRuntime {vars = insert id (t,v) (vars r), consts = consts r, toPrint = toPrint r}

goPrint :: GoValue -> Runtime ()
goPrint v = do
  r <- get
  put GoRuntime {vars = vars r, consts = consts r, toPrint = show v : toPrint r}