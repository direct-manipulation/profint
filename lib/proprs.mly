(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  (*
  let rec make_quant q vs f =
    begin match vs with
    | [] -> f
    | v :: vs -> q v (make_quant q vs f)
    end
  *)

  let rec make_app ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | f :: t :: ts -> make_app (Uterm.App (f, t) :: ts)
%}

%token  EOS PREC_MIN PREC_MAX
%token  <Util.ident> IDENT
%token  LPAREN RPAREN LBRACK RBRACK COMMA
%token  ARROW
%token  LAMBDA COLON
%token  LNOT EQ NEQ
%token  AND OR TO FROM BOT TOP
%token  FORALL EXISTS DOT

%nonassoc PREC_MIN
%left     FROM
%right    TO ARROW
%left     OR
%left     AND
%nonassoc PREC_MAX

%start  <Uterm.uterm> one_term
%start  <Uterm.uty>   one_ty

%%

one_term:
| t=term EOS
  { t }

one_ty:
| ty=ty EOS
  { ty }

term:
| ts=nonempty_list(wrapped_term)
  { make_app ts }
| LAMBDA xty=id_ty DOT bod=term
  { let (x, ty) = xty in Uterm.Abs (x, ty, bod) }
| vs=delimited(LBRACK, separated_nonempty_list(COMMA, id_ty), RBRACK)
  bod=term
  { List.fold_right (fun (x, ty) t -> Uterm.Abs (x, ty, t)) vs bod }

id_ty:
| x=IDENT COLON ty=ty
  { (x, Some ty) }
| x=IDENT
  { (x, None) }

wrapped_term:
| v=IDENT
  { Uterm.Var v }
| LPAREN t=term RPAREN
  { t }

ty:
| b=IDENT
  { Uterm.Basic b }
| a=ty ARROW b=ty
  { Uterm.Arrow (a, b) }
| LPAREN ty=ty RPAREN
  { ty }

%inline plist(X):
| xs=loption(delimited(LBRACK, separated_nonempty_list(COMMA, X), RBRACK))
  { xs }
