(* Source: https://github.com/bozhnyukAlex/mini_java/blob/master/Java/lib/hashtbl_p.ml *)

module Hashtbl_p = struct
  type ('k, 's) t = ('k, 's) Hashtbl.t

  let pp pp_key pp_value ppf values =
    Format.fprintf ppf "[["
    |> fun () ->
    Hashtbl.iter
      (fun key data ->
        Format.fprintf ppf "@[<1>%a@ ->@ %a@]@\n@." pp_key key pp_value data )
      values
    |> fun () -> Format.fprintf ppf "]]@\n"
end