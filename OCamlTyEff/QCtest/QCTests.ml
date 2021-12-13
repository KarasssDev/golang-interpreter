(* open Format
open QCheck.Gen
open OCaml_typed_effects_lib
open OCaml_typed_effects_lib.Utils

let varname = map Char.chr (int_range (Char.code 'a') (Char.code 'z'))

let lam_gen =
  QCheck.Gen.(
    sized
    @@ fix (fun self n ->
           match n with
           | 0 -> map var varname
           | n ->
             frequency
               [ 1, map2 abs varname (self (n / 2))
               ; 1, map2 app (self (n / 2)) (self (n / 2))
               ]))
;;

let __ () =
  List.iter
    (fprintf std_formatter "%a\n" (Printast.pp Format.pp_print_char))
    (QCheck.Gen.generate ~n:20 lam_gen)
;;

let arbitrary_lam =
  let open QCheck.Iter in
  let rec shrink_lam = function
    | Ast.Var i -> QCheck.Shrink.char i >|= var
    | Abs (c, b) -> of_list [ b ] <+> (shrink_lam b >|= fun b' -> abs c b')
    | App (a, b) ->
      of_list [ a; b ]
      <+> (shrink_lam a >|= fun a' -> app a' b)
      <+> (shrink_lam b >|= fun b' -> app a b')
  in
  QCheck.make
    lam_gen
    ~print:(asprintf "%a" (Printast.pp Format.pp_print_char))
    ~shrink:shrink_lam
;;

let rec pp ppf = function
  | Ast.Var c -> Format.fprintf ppf "%c" c
  | App (l, r) -> Format.fprintf ppf "(%a %a)" pp l pp r
  (*
    | App (l, r) ->
        Format.fprintf ppf "%a %a" pp l pp r (* Buggy implementation *)
        *)
  | Abs (x, b) -> Format.fprintf ppf "(\\%c . %a)" x pp b
;;

let print_parse_is_identity =
  QCheck.(
    Test.make arbitrary_lam (fun l ->
        Caml.Result.ok l
        = Angstrom.parse_string
            ~consume:Angstrom.Consume.Prefix
            Parser.(parse_lam.single parse_lam)
            (Format.asprintf "%a" pp l)))
;;

let run () = QCheck_base_runner.run_tests [ print_parse_is_identity ] *)
