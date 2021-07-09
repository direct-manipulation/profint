(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  let make_quant q vs bod =
    List.fold_right
      (fun (x, ty) f -> Uterm.(App (Kon (q, None), Abs (x, ty, f))))
      vs bod

  let rec make_app ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | f :: t :: ts -> make_app (Uterm.App (f, t) :: ts)
%}

%token  EOS PREC_MIN PREC_MAX
%token  <Util.ident> IDENT
%token  LPAREN RPAREN LBRACK RBRACK COMMA COLON
%token  ARROW
%token  EQ NEQ
%token  AND OR TO FROM BOT TOP
%token  FORALL EXISTS

%nonassoc PREC_MIN
%left     FROM
%right    TO ARROW
%left     OR
%left     AND
%nonassoc PREC_MAX

%start  <Uterm.uterm> one_term
%start  <Uterm.uty>   one_ty
%start  <Uterm.uterm> one_form

%%

one_term:
| t=term EOS
  { t }

one_ty:
| ty=ty EOS
  { ty }

one_form:
| f=form EOS
  { f }

term:
| vs=lambda bod=app_term
  { List.fold_right (fun (x, ty) t -> Uterm.Abs (x, ty, t)) vs bod }

%inline app_term:
| ts=nonempty_list(wrapped_term)
  { make_app ts }

lambda:
| vss=nonempty_list(delimited(LBRACK, ids_ty, RBRACK))
  { List.concat vss }

ids_ty:
| xs=separated_nonempty_list(COMMA, IDENT) COLON ty=ty
  { let ty = Some ty in
    List.map (fun x -> (x, ty)) xs }
| xs=separated_nonempty_list(COMMA, IDENT)
  { List.map (fun x -> (x, None)) xs }

wrapped_term:
| v=IDENT
  { Uterm.Var v }
| LPAREN t=term RPAREN
  { t }

form:
| TOP
  { Uterm.(Kon (k_top, None)) }
| BOT
  { Uterm.(Kon (k_bot, None)) }
| fa=form AND fb=form
  { Uterm.(App (App (Kon (k_and, None), fa), fb)) }
| fa=form OR fb=form
  { Uterm.(App (App (Kon (k_or, None), fa), fb)) }
| fa=form TO fb=form
  { Uterm.(App (App (Kon (k_imp, None), fa), fb)) }
| fa=form FROM fb=form
  { Uterm.(App (App (Kon (k_imp, None), fb), fa)) }
| FORALL vs=lambda bod=form %prec PREC_MIN
  { make_quant Uterm.k_all vs bod }
| EXISTS vs=lambda bod=form %prec PREC_MIN
  { make_quant Uterm.k_ex vs bod }
| a=IDENT ts=list(wrapped_term)
  { make_app (Uterm.Kon (a, None) :: ts) }
| LPAREN f=form RPAREN
  { f }

ty:
| b=IDENT
  { Uterm.Basic b }
| a=ty ARROW b=ty
  { Uterm.Arrow (a, b) }
| LPAREN ty=ty RPAREN
  { ty }
