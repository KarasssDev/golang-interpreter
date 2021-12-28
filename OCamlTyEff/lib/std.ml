open Ast

(* used by interpreter to access native function parameter *)
let native_prm = "x"
let e_native_fun = e_fun native_prm (TVar "_")

(**
  [sneaky_eff f] returns a function calling [f] without exposing
  some or all of the [f]'s side effects to the type system
  (e.g. [(sneaky_eff println) "Debug info"] can be used to print
  ["Debug info"] from a pure function)
*)
let stdlib =
  [ { name = "println"
    ; is_rec = false
    ; ty = TFun (TString, EffSet.singleton EffIO, TTuple [])
    ; expr = e_native_fun (ENative NPrintln)
    }
  ; { name = "raise1"
    ; is_rec = false
    ; ty = TFun (TTuple [], EffSet.singleton (EffExc Exc1), TVar "a")
    ; expr = e_native_fun (ENative (NRaise Exc1))
    }
  ; { name = "raise2"
    ; is_rec = false
    ; ty = TFun (TTuple [], EffSet.singleton (EffExc Exc2), TVar "a")
    ; expr = e_native_fun (ENative (NRaise Exc2))
    }
  ; { name = "ref"
    ; is_rec = false
    ; ty = TFun (TVar "a", EffSet.empty, TRef (TVar "a"))
    ; expr = e_native_fun (ENative NRef)
    }
  ; { name = "sneaky_eff"
    ; is_rec = false
    ; ty =
        TFun
          ( TFun (TVar "a", EffSet.singleton (EffVar "e"), TVar "b")
          , EffSet.empty
          , TFun (TVar "a", EffSet.singleton (EffVar "e2"), TVar "b") )
    ; expr = e_native_fun (ENative NSneakyEff)
    }
  ]
;;
