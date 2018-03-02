type var = string

type routine_name = string

type expr=
  E_lit of int
| E_var of var
| E_add of (expr * expr)
| E_sub of (expr * expr)
| E_mul of (expr * expr)

type bexpr =
  B_eq of (expr * expr)
| B_lt of (expr * expr)
| B_not of bexpr
| B_and of (bexpr * bexpr)

type predicate = 
  Pred of (expr * string)


type asn =
| BAsn of (bexpr)
| PAsn of predicate
| IfAsn of (bexpr * asn * asn)
| AndAsn of (asn * asn)

type cmd =
  Assign of (var * expr)
| IfCmd of (bexpr * cmd * cmd)
| While of (bexpr * asn * cmd)
| Call of (var * string * expr list)
| Seq of (cmd * cmd)
| Return of expr

type routine = 
  Rtn_def of (routine_name * var list * asn * asn * cmd)

type 'a option=
| None
| Some of ('a)

let chars_of_string s =
  let n = String.length s in
  let rec iter k =
    if k = n then [] else s.[k]::iter (k + 1)
  in
  iter 0

let string_of_chars cs =
  let buffer = Buffer.create 10 in
  let rec iter cs =
    match cs with
    | [] -> Buffer.contents buffer
    | c::cs -> Buffer.add_char buffer c; iter cs
  in
  iter cs

type token = Ident of string | Keyword of string | IntLit of int

let keywords = ["if"; "then"; "else"; "while"; "inv"; "do"; "return"; "routine"; "req"; "ens"]

exception Not_Supported_Token of string;;

let tokens_of_string text =
  let rec tokens_of cs =
    match cs with
    | [] -> []
    | (' '|'\r'|'\n'|'\t'|'#')::cs -> tokens_of cs
    | ('A'..'Z'|'a'..'z') as c::cs -> ident_of [c] cs
    | '0'..'9' as c::cs -> number_of [c] cs
    | ('+'|'-'|'*'|'='|'<'|'!'|'('|')'|';'|','|'&'|'^'|'/'|'['|']') as c::cs -> Keyword (string_of_chars [c])::tokens_of cs
    | ':'::'='::cs -> Keyword ":="::tokens_of cs
    | _::cs -> raise (Not_Supported_Token "\n\nNot Supported Token in tokens_of\n\n") 
  and ident_of ident_cs cs =
    match cs with
    | ('A'..'Z'|'a'..'z'|'0'..'9') as c::cs -> ident_of (c::ident_cs) cs
    | cs ->
      let x = string_of_chars (List.rev ident_cs) in
      let tok = if List.mem x keywords then Keyword x else Ident x in
      tok::tokens_of cs
  and number_of num_cs cs =
    match cs with
    | '0'..'9' as c::cs -> number_of (c::num_cs) cs
    | cs ->
      IntLit (int_of_string (string_of_chars (List.rev num_cs)))::tokens_of cs
  in
  tokens_of (chars_of_string text)

let rec parse_comments ts=
  match ts with
    Keyword "/"::ts -> ts
  | tk::ts -> parse_comments ts

let rec parse_params_rest xs ts =
  match ts with
    Keyword ","::Ident x::ts -> parse_params_rest (x::xs) ts
  | ts -> (List.rev xs, ts)

let parse_params ts =
  match ts with
    Ident x::ts -> parse_params_rest [x] ts
  | ts -> ([], ts)

let rec parse_expr ts =
  let parse_primary_expr ts =
    match ts with
      IntLit n::ts -> E_lit n, ts
    | Ident x::ts -> E_var x, ts
    | Keyword "("::ts -> let e, Keyword ")"::ts = parse_expr ts in e, ts
  in
  let rec parse_mul_expr ts =
    let e1, ts = parse_primary_expr ts in
    match ts with
      Keyword "*"::ts ->
      let e2, ts = parse_mul_expr ts in
      E_mul (e1, e2), ts
    | ts ->
      e1, ts
  in
  let rec parse_add_expr_rest e1 ts =
    match ts with
    | Keyword "+"::ts ->
      let e2, ts = parse_mul_expr ts in
      parse_add_expr_rest (E_add (e1, e2)) ts
    | Keyword "-"::ts ->
      let e2, ts = parse_mul_expr ts in
      parse_add_expr_rest (E_sub (e1, e2)) ts
    | ts ->
      e1, ts
  in
  let parse_add_expr ts =
    let e1, ts = parse_mul_expr ts in
    parse_add_expr_rest e1 ts
  in
  parse_add_expr ts

let rec parse_bexpr ts =
let rec parse_bexpr1 ts =(
  match ts with
  | Keyword "!"::ts ->
    let b, ts = parse_bexpr1 ts in
    B_not b, ts
(*  | Keyword "("::ts ->
    let b, Keyword ")"::ts = parse_bexpr ts in
    b, ts
*)
  | ts ->
    let e1, ts = parse_expr ts in
    match ts with
    | Keyword "="::ts ->
      let e2, ts = parse_expr ts in
      B_eq (e1, e2), ts
    | Keyword "<"::ts ->
      let e2, ts = parse_expr ts in
      B_lt (e1, e2), ts
)in
  let b, ts = parse_bexpr1 ts in
  match ts with
  | Keyword "^"::ts ->
    let b2, ts = parse_bexpr ts in
    B_and (b, b2), ts
  | ts -> b, ts

let rec parse_asn2 ts =
  match ts with
  | Keyword "["::ts -> 
	let e, ts = parse_expr ts in
	let Keyword "]"::Ident name::ts = ts in
	let predicate = Pred (e, name) in
	PAsn(predicate), ts
  | ts -> 
	let b, ts = parse_bexpr ts in
	BAsn(b), ts

let rec parse_asn ts =
let parse_asn1 ts =(
  match ts with
  | Keyword "["::ts -> 
	let e, ts = parse_expr ts in
	let Keyword "]"::Ident name::ts = ts in
	let predicate = Pred (e, name) in
	PAsn(predicate), ts
  | Keyword "if"::ts -> 
	let b, ts = parse_bexpr ts in
	let Keyword "then"::ts = ts in
	let a1, ts = parse_asn ts in
	let Keyword "else"::ts = ts in
	let a2, ts = parse_asn ts in
	IfAsn(b, a1, a2), ts
  | ts -> 
	let b, ts = parse_bexpr ts in
	BAsn(b), ts
) in
let a1, ts = parse_asn1 ts in
match ts with
  | Keyword "&"::ts ->
	let a2, ts = parse_asn ts in
	AndAsn(a1, a2), ts
  | ts -> a1, ts


let rec parse_cmd ts =
  let rec parse_primary_cmd ts =
    match ts with
    | Keyword "("::ts ->
      let c, Keyword ")"::ts = parse_cmd ts in
      c, ts
    | Keyword "/"::ts ->
      let ts = parse_comments ts in
      parse_cmd ts
    | Ident x::Keyword ":="::ts ->
      let e, ts = parse_expr ts in
      begin match ts with
      | Keyword "("::ts ->
        let E_var r = e in
        let rec parse_args_rest es ts =
          match ts with
          | Keyword ")"::ts -> List.rev es, ts
          | Keyword ","::ts ->
            let e, ts = parse_expr ts in
            parse_args_rest (e::es) ts
        in
        let parse_args ts =
          match ts with
          | Keyword ")"::ts -> [], ts
          | ts ->
            let e, ts = parse_expr ts in
            parse_args_rest [e] ts
        in
        let es, ts = parse_args ts in
        Call (x, r, es), ts
      | ts ->
        Assign (x, e), ts
      end
    | Keyword "if"::ts ->
      let b, ts = parse_bexpr ts in
      let Keyword "then"::ts = ts in
      let c1, ts = parse_cmd ts in
      let Keyword "else"::ts = ts in
      let c2, ts = parse_primary_cmd ts in
      IfCmd (b, c1, c2), ts
    | Keyword "while"::ts ->
      let b, ts = parse_bexpr ts in
      let Keyword "inv"::ts = ts in
      let inv, ts = parse_asn ts in
      let Keyword "do"::ts = ts in
      let body, ts = parse_primary_cmd ts in
      While (b, inv, body), ts
    | Keyword "return"::ts ->
      let e, ts = parse_expr ts in
      Return e, ts
  in
  let c1, ts = parse_primary_cmd ts in
  match ts with
    Keyword ";"::ts ->
    let c2, ts = parse_cmd ts in
    Seq (c1, c2), ts
  | ts ->
    c1, ts

let parse_routine ts =
  let Keyword "routine"::Ident r::Keyword "("::ts = ts in
  let xs, ts = parse_params ts in
  let Keyword ")"::Keyword "req"::ts = ts in
  let req, ts = parse_asn ts in
  let Keyword "ens"::ts = ts in
  let ens, ts = parse_asn ts in
  let Keyword "do"::ts = ts in
  let body, ts = parse_cmd ts in
  Rtn_def (r, xs, req, ens, body), ts

let parse_program text=
  let ts = tokens_of_string text in
  let rec parse_routines ts=
    match ts with
      [] -> []
    | ts -> let routine, ts = parse_routine ts in
            routine::(parse_routines ts)
  in
  parse_routines ts

