(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

{
  module P = Proprs

  let newline lb =
    Lexing.(
      lb.lex_curr_p <- { lb.lex_curr_p with
        pos_bol = lb.lex_curr_p.pos_cnum ;
        pos_lnum = lb.lex_curr_p.pos_lnum + 1 ;
      }
    )

  let process_ident =
    let kwds : (string, P.token) Hashtbl.t = Hashtbl.create 19 in
    Hashtbl.replace kwds "forall" P.FORALL ;
    Hashtbl.replace kwds "exists" P.EXISTS ;
    fun ident ->
      match Hashtbl.find kwds ident with
      | tok -> tok
      | exception Not_found -> P.IDENT ident

}

let ident_initial = ['A'-'Z' 'a'-'z']
let ident_body    = ident_initial | ['0'-'9' '_']
let ident         = ident_initial ident_body*

let space         = ' ' | '\t'
let newline       = '\r''\n' | '\n'

rule token = parse
| '%'              { line_comment lexbuf }

| space            { token lexbuf }
| newline          { newline lexbuf ; token lexbuf }

| ident            { process_ident @@ Lexing.lexeme lexbuf }

| "\\lambda"       { P.LAMBDA }
| "\\and" | '&'    { P.AND }
| "\\or"  | '|'    { P.OR }
| "\\to"  | "=>"   { P.TO }
| "\\if"  | "<="   { P.FROM }

| "->"             { P.ARROW }

| ':'              { P.COLON }
| ','              { P.COMMA }
| '('              { P.LPAREN }
| ')'              { P.RPAREN }
| '['              { P.LBRACK }
| ']'              { P.RBRACK }

| '.'              { P.DOT }

| eof              { P.EOS }
| _                { raise P.Error }

and line_comment = parse
| newline          { newline lexbuf ; token lexbuf }
| eof              { P.EOS }
| _                { line_comment lexbuf }
