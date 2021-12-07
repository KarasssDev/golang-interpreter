open Angstrom
open Ast

let parse p s = parse_string ~consume:All p s

let is_keyword = function
  | "break" | "case" | "continue" | "return" | "else" | "for" | "if" | "while"
    ->
      true
  | _ -> false

let types_keywords = [ "int"; "char"; "void" ]

let is_whitespace = function ' ' | '\t' -> true | _ -> false

let is_end_of_line = function '\n' | '\r' -> true | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false

let is_valid_id_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
  | _ -> false

let space = take_while is_whitespace

let space1 = take_while1 is_whitespace

let token s = space *> string s

let number =
  let integer = take_while1 is_digit in
  space *> integer >>= fun whole -> return @@ CINT (int_of_string whole)

let identifier =
  let is_valid_first_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false
  in
  space *> peek_char >>= function
  | Some c when is_valid_first_char c ->
      take_while is_valid_id_char >>= fun id ->
      if is_keyword id then
        pos >>= fun col ->
        fail ("ERROR: " ^ Int.to_string col ^ " " ^ id ^ " is a reserved word")
      else return id
  | _ -> pos >>= fun num -> fail (Int.to_string num ^ " invalid identifier")

let include_stats =
  space *> string "#include " *> char '<' *> identifier >>= fun id ->
  string ".h" >>= (fun part -> return @@ id ^ part) <* char '>'

let indexer idd expr =
  token "[" *> expr <* token "]" >>= fun exp -> return @@ INDEXER (idd, exp)

let char_value =
  char '\'' *> any_char <* char '\'' >>= fun ch -> return @@ CCHAR ch

(**EXPRESSION PARSING FUNCTIONS*)

let add = token "+" *> return (fun e1 e2 -> ADD (e1, e2))

let sub = token "-" *> return (fun e1 e2 -> SUB (e1, e2))

let mul = token "*" *> return (fun e1 e2 -> MUL (e1, e2))

let div = token "/" *> return (fun e1 e2 -> DIV (e1, e2))

let _mod = token "%" *> return (fun e1 e2 -> MOD (e1, e2))

let _not = token "!" *> return (fun e1 -> NOT e1)

let _and = token "&&" *> return (fun e1 e2 -> AND (e1, e2))

let _or = token "||" *> return (fun e1 e2 -> OR (e1, e2))

let _eq = token "==" *> return (fun e1 e2 -> EQUAL (e1, e2))

let _neq = token "!=" *> return (fun e1 e2 -> NOT_EQUAL (e1, e2))

let _lt = token "<" *> return (fun e1 e2 -> LT (e1, e2))

let _gt = token ">" *> return (fun e1 e2 -> GT (e1, e2))

let _lte = token "<=" *> return (fun e1 e2 -> LTE (e1, e2))

let _gte = token ">=" *> return (fun e1 e2 -> GTE (e1, e2))

let factop = mul <|> div <|> _mod <?> "'*' or '/' or '%' expected" <* space

let termop = space *> add <|> sub <?> "'+' or '-' expected" <* space

let cmpop =
  _lte <|> _lt <|> _gte <|> _gt <|> _neq <|> _eq <?> "compare operator expected"
  <* space

let left_of p1 p = p <* space <* p1

let right_of p1 p = p1 *> space *> p

let between p1 p2 p = left_of p2 (right_of p1 p)

let parens p = between (token "(") (token ")") p

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let rec chainr1 e op =
  e >>= fun a -> op >>= (fun f -> chainr1 e op >>| f a) <|> return a

let rec build_ptr n acc = if n = 0 then acc else build_ptr (n - 1) (CT_PTR acc)

let ptr value =
  space *> many (token "*") >>= fun num_ptrs ->
  return (build_ptr (List.length num_ptrs) value)

let get_number = function CINT v -> return v | _ -> fail "expected int"

let token_datatypes =
  pos >>= fun col ->
  token "int" *> ptr CT_INT
  <|> token "char" *> ptr CT_CHAR
  <|> token "void" *> ptr CT_VOID
  <|> (token "struct" *> identifier >>= fun idd -> ptr (CT_STRUCT idd))
  <|> fail @@ "Unrecognized data type at col " ^ Int.to_string col

let expr =
  fix (fun expr ->
      let indexer_exp = identifier >>= fun idd -> indexer idd expr in
      let var_name = identifier >>= fun id -> return @@ VAR_NAME id in
      let access l r = ACCESOR (l, r) in
      let arrow_cast l r = ACCESOR (DEREFERENCE l, r) in
      let accesor =
        let accessible = indexer_exp <|> var_name in
        accessible >>= fun h ->
        many1 @@ (token "." *> accessible) >>= fun a ->
        return @@ List.fold_left access h a
      in
      let arrow =
        indexer_exp <|> parens var_name <|> var_name >>= fun h ->
        many @@ (token "->" *> (indexer_exp <|> parens var_name <|> var_name))
        >>= fun a -> return @@ List.fold_left arrow_cast h a
      in

      let arg_sizeof = token_datatypes >>= fun t -> return @@ TYPE t in
      let func_call =
        (* accesor <|> arrow <|> indexer_exp <|> var_name  *)
        identifier >>= fun idd ->
        token "(" *> sep_by (token ",") (arg_sizeof <|> expr) <* token ")"
        >>= fun arg_list -> return @@ FUNC_CALL (idd, arg_list)
      in
      let literal_num = number >>= fun num -> return @@ LITERAL num in
      let literal_char = char_value >>= fun cchar -> return @@ LITERAL cchar in
      let const =
        space *> peek_char_fail >>= function
        | '\'' -> literal_char
        | _ -> literal_num
      in
      let defr_op =
        fix (fun defr_op ->
            token "*"
            *> (parens expr <|> indexer_exp <|> var_name <|> defr_op <|> expr)
            >>= function
            | ACCESOR _ -> fail "accesor ptr"
            | dexp -> return @@ DEREFERENCE dexp)
      in
      let addr_op =
        token "&" *> (indexer_exp <|> parens expr <|> var_name <|> expr)
        >>= fun pvar -> return @@ ADDRESS pvar
      in
      let null = token "NULL" *> (return @@ LITERAL CNULL) in
      let other =
        choice
          [
            null;
            func_call;
            defr_op;
            accesor;
            arrow;
            indexer_exp;
            addr_op;
            var_name;
            const;
          ]
      in
      let neg =
        let un_minus = return (fun e -> SUB (LITERAL (CINT 0), e)) in
        un_minus <* space <*> expr
      in
      let power =
        let predict =
          space *> peek_char_fail >>= function
          | '(' -> parens expr
          | '-' -> (
              advance 1 *> peek_char_fail >>= function
              | '-' -> fail "double neg - need parens!"
              | _ -> neg)
          | _ -> other
        in
        choice [ predict; other ]
      in
      let term1 = chainl1 power factop in
      let arexpr = chainl1 term1 termop in
      let compare = chainl1 arexpr cmpop in
      let bfactor =
        fix (fun bfactor ->
            let nnot = _not <* space <*> bfactor in
            choice [ nnot; compare ])
      in
      let bterm = chainl1 bfactor (_and <* space) in

      let oldexpr = chainl1 bterm (_or <* space) in

      (* let inc =
           accesor <|> arrow <|> indexer_exp <|> var_name <* string "++" >>= fun v ->
           return @@ ADD (v, LITERAL (CINT 1))
         in
         let dec =
           accesor <|> arrow <|> indexer_exp <|> var_name <* string "--" >>= fun v ->
           return @@ SUB (v, LITERAL (CINT 1))
         in *)
      let newexpr =
        fix (fun newexpr -> (* inc <|> dec <|>  *)
                            oldexpr <|> parens newexpr)
      in
      newexpr)

(** STATEMENTS PARSING FUNCTIONS *)

let struct_decl =
  let tkd =
    token "int" *> identifier
    >>= (fun idd ->
          between (token "[") (token "]") number >>= fun v ->
          get_number v >>= fun n -> return @@ CARGS (CT_ARRAY (n, CT_INT), idd))
    <|> ( token_datatypes >>= fun tdd ->
          identifier >>= fun idd -> return @@ CARGS (tdd, idd) )
  in

  let content =
    token "{"
    *> skip_while (fun c -> is_whitespace c || is_end_of_line c)
    *> many1
         (tkd <* token ";"
         <* skip_while (fun c -> is_whitespace c || is_end_of_line c))
    >>= fun cont_ls -> token "}" *> return cont_ls
  in
  skip_while (fun c -> is_whitespace c || is_end_of_line c)
  *> token "struct" *> identifier
  >>= fun idd ->
  skip_while (fun c -> is_whitespace c || is_end_of_line c) *> content
  >>= fun cont -> token ";" *> (return @@ TOP_STRUCT_DECL (idd, cont))

let struct_initialize =
  fix (fun struct_initialize ->
      token "{" *> space
      *> sep_by1 (token "," *> space) (expr <|> struct_initialize)
      >>= fun ls_init -> token "}" *> (return @@ INITIALIZER ls_init))

let var_decl =
  let p_array =
    token "[" *> take_while1 is_digit <* token "]" >>= fun intt ->
    return @@ int_of_string intt
  in
  let transformate ls =
    let size = List.length ls in
    let rec helper acc i =
      if i < size then helper (acc @ [ (*i,*) List.nth ls i ]) (i + 1) else acc
    in
    helper [] 0
  in
  let rec get_value idd = function
    | CT_INT -> expr >>= fun num -> return @@ VAR_DECL (idd, CT_INT, Some num)
    | CT_CHAR ->
        char_value
        >>= (fun ch -> return @@ VAR_DECL (idd, CT_CHAR, Some (LITERAL ch)))
        <|> ( expr >>= fun e ->
              match e with
              | LITERAL CNULL -> return @@ VAR_DECL (idd, CT_CHAR, Some e)
              | _ -> fail "char can't be an expression" )
    | CT_PTR typ -> (
        match typ with
        | CT_VOID | CT_CHAR | CT_STRUCT _ ->
            expr >>= fun x -> return @@ VAR_DECL (idd, CT_PTR typ, Some x)
        | _ -> (
            get_value idd typ >>= function
            | VAR_DECL (idd, tt, v) -> return @@ VAR_DECL (idd, CT_PTR tt, v)
            | _ -> fail "Wrong Initial value"))
    | CT_ARRAY (len, bt) -> (
        struct_initialize >>= function
        | INITIALIZER inits ->
            return
            @@ VAR_DECL
                 ( idd,
                   CT_ARRAY (len, bt),
                   Some (LITERAL (CARRAY (transformate inits))) )
        | _ -> fail "wrong init for array")
    | CT_STRUCT name -> (
        struct_initialize <|> expr >>= fun init_ls ->
        match init_ls with
        | INITIALIZER _ | FUNC_CALL _ | DEREFERENCE _
        | LITERAL CNULL
        | VAR_NAME _ | INDEXER _ ->
            (*VARNAAAAME *)
            return @@ VAR_DECL (idd, CT_STRUCT name, Some init_ls)
        | _ -> fail "Struct can't be an expression")
    | CT_VOID -> fail "VOID cannot be a type for variable declaration"
  in
  let rec is_initialized idd t =
    space *> peek_char >>= function
    | Some '[' -> p_array >>= fun arl -> is_initialized idd (CT_ARRAY (arl, t))
    | Some '=' ->
        advance 1 *> space *> get_value idd t >>= fun v -> token ";" *> return v
    | Some ';' -> (
        advance 1
        *>
        match t with
        | CT_ARRAY _ ->
            return (VAR_DECL (idd, t, None (* Some (LITERAL (CARRAY [])) *)))
        | _ -> return (VAR_DECL (idd, t, None)))
    | None | _ -> fail "ERROR"
  in
  token_datatypes >>= fun t ->
  match t with
  | CT_VOID -> fail "VOID cannot be a type for variable declaration"
  | _ -> identifier >>= fun idd -> is_initialized idd t

let arg_decl =
  token_datatypes <* space >>= fun td ->
  identifier >>= fun idd -> return @@ CARGS (td, idd)

let return_ =
  token "return" *> space *> peek_char >>= function
  | Some ';' -> advance 1 *> (return @@ RETURN (LITERAL CVOID))
  | Some _ -> expr >>= fun exp -> token ";" *> (return @@ RETURN exp)
  | _ -> fail "Unrecognized char at return instruction"

let var_assign_proc_call no_ends_semic =
  let rec build_def n acc =
    if n = 0 then acc else build_def (n - 1) (DEREFERENCE acc)
  in
  let assign p name exprr = ASSIGN (build_def p name, exprr) in
  let ass_add p name exprr = ASSIGN_ADD (build_def p name, exprr) in
  let ass_sub p name exprr = ASSIGN_SUB (build_def p name, exprr) in
  let ass_mul p name exprr = ASSIGN_MUL (build_def p name, exprr) in
  let ass_div p name exprr = ASSIGN_DIV (build_def p name, exprr) in
  let ass_mod p name exprr = ASSIGN_MOD (build_def p name, exprr) in
  let func_call f = token ";" >>= fun _ -> return @@ EXPRESSION f in
  let assign_left_cons num_ptrs left_cons =
    let assign_op op =
      struct_initialize <|> expr >>= fun r ->
      if no_ends_semic then return @@ op r else token ";" *> (return @@ op r)
    in
    let assign_unop un_op num_ptrs left_cons =
      let ret = return @@ un_op num_ptrs left_cons (LITERAL (CINT 1)) in
      if no_ends_semic then ret else ret <* token ";"
    in

    space *> peek_char_fail <* space >>= function
    | '=' -> token "=" *> (assign_op @@ assign num_ptrs left_cons)
    | '+' ->
        advance 1 *> token "=" *> (assign_op @@ ass_add num_ptrs left_cons)
        <|> advance 1 *> token "+" *> assign_unop ass_add num_ptrs left_cons
    | '-' ->
        advance 1 *> token "=" *> (assign_op @@ ass_sub num_ptrs left_cons)
        <|> advance 1 *> token "-" *> assign_unop ass_sub num_ptrs left_cons
    | '*' -> advance 1 *> token "=" *> (assign_op @@ ass_mul num_ptrs left_cons)
    | '/' -> advance 1 *> token "=" *> (assign_op @@ ass_div num_ptrs left_cons)
    | '%' -> advance 1 *> token "=" *> (assign_op @@ ass_mod num_ptrs left_cons)
    | otherwise -> fail @@ String.make 1 otherwise ^ " ..?"
  in
  many (token "*") >>= fun num_ptrs ->
  expr >>= fun e ->
  match e with
  | FUNC_CALL _ when num_ptrs == [] -> func_call e
  | ACCESOR _ when num_ptrs == [] -> assign_left_cons (List.length num_ptrs) e
  | INDEXER _ | VAR_NAME _ -> assign_left_cons (List.length num_ptrs) e
  | _ when num_ptrs <> [] -> assign_left_cons (List.length num_ptrs) e
  | _ -> fail "a"

let del_space_newline =
  take_while (fun c -> is_whitespace c || is_end_of_line c)

let block stmtss =
  del_space_newline *> token "{"
  *> many1 (del_space_newline *> stmtss <* del_space_newline)
  <* token "}"
  >>= fun stat_list -> del_space_newline *> (return @@ BLOCK stat_list)

let func_decl stmtss =
  token_datatypes >>= fun ret_typ ->
  space *> identifier >>= fun idd ->
  token "(" *> sep_by (token ",") arg_decl <* token ")" *> skip_many end_of_line
  >>= fun arg_ls ->
  skip_while (fun c -> is_whitespace c || is_end_of_line c) *> block stmtss
  >>= fun blk ->
  skip_while (fun c -> is_whitespace c || is_end_of_line c)
  *> (return @@ TOP_FUNC_DECL (ret_typ, idd, arg_ls, blk))

let if_stmt stmts =
  token "if" *> token "(" *> expr <* token ")" >>= fun rel_expr ->
  block stmts >>= fun blk -> return @@ IF (rel_expr, blk)

let if_else_stmts stmtss =
  token "if" *> token "(" *> expr <* token ")" >>= fun rel_expr ->
  block stmtss >>= fun blk_if ->
  token "else" *> block stmtss >>= fun blk_else ->
  return @@ IF_ELSE (rel_expr, blk_if, blk_else)

let for_statement stmtss =
  token "for" *> token "("
  *> (var_decl
     >>= (fun var -> return @@ Some var)
     <|> (return None <* token ";"))
  >>= fun var ->
  expr >>= (fun re -> return @@ Some re) <|> return None >>= fun re ->
  token ";"
  *> (var_assign_proc_call true
     >>= (fun step -> return @@ Some step)
     <|> return None)
  >>= fun step ->
  token ")"
  *> skip_while (fun c -> is_whitespace c || is_end_of_line c)
  *> block stmtss
  >>= fun blk -> return @@ FOR (var, re, step, blk)

let _continue = token "continue" *> token ";" *> return CONTINUE

let _break = token "break" *> token ";" *> return BREAK

let while_stmt stmtss =
  token "while" *> token "(" *> expr <* token ")" >>= fun re ->
  block stmtss >>= fun blk -> return @@ WHILE (re, blk)

let top_decl_c (retype, name, args, blk) =
  TOP_FUNC_DECL (retype, name, args, blk)

let multi_includes =
  many1 (include_stats <* end_of_line) >>= fun includes_list ->
  return @@ C_INCLUDE includes_list

let stmts =
  fix (fun stmts ->
      block stmts <|> if_else_stmts stmts <|> if_stmt stmts <|> while_stmt stmts
      <|> for_statement stmts <|> var_assign_proc_call false <|> var_decl
      <|> _continue <|> _break <|> return_)

let top_decl_var =
  var_decl >>= function
  | VAR_DECL (idd, typ, right_cons) ->
      return @@ TOP_VAR_DECL (idd, typ, right_cons)
  | _ -> fail "Not a var"

let prog =
  del_space_newline *> multi_includes >>= fun mincl ->
  del_space_newline
  *> sep_by del_space_newline (func_decl stmts <|> struct_decl <|> top_decl_var)
  >>= fun f_decl -> return @@ C_PROG (mincl :: f_decl)
