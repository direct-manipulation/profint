(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  let make_quant q vs bod =
    List.fold_right
      (fun (x, ty) f -> Utypes.(App (Kon (q, None), Abs (x, ty, f))))
      vs bod

  let rec make_app ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | f :: t :: ts -> make_app (Utypes.App (f, t) :: ts)
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

%start  <Utypes.uterm> one_term
%start  <Utypes.uty>   one_ty
%start  <Utypes.uterm> one_form

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
  { List.fold_right (fun (x, ty) t -> Utypes.Abs (x, ty, t)) vs bod }

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
  { Utypes.Var v }
| LPAREN t=term RPAREN
  { t }

form:
| TOP
  { Utypes.(Kon (Consts.k_top, None)) }
| BOT
  { Utypes.(Kon (Consts.k_bot, None)) }
| fa=form AND fb=form
  { Utypes.(App (App (Kon (Consts.k_and, None), fa), fb)) }
| fa=form OR fb=form
  { Utypes.(App (App (Kon (Consts.k_or, None), fa), fb)) }
| fa=form TO fb=form
  { Utypes.(App (App (Kon (Consts.k_imp, None), fa), fb)) }
| fa=form FROM fb=form
  { Utypes.(App (App (Kon (Consts.k_imp, None), fb), fa)) }
| FORALL vs=lambda bod=form %prec PREC_MIN
  { make_quant Utypes.Consts.k_all vs bod }
| EXISTS vs=lambda bod=form %prec PREC_MIN
  { make_quant Utypes.Consts.k_ex vs bod }
| a=IDENT ts=list(wrapped_term)
  { make_app (Utypes.Kon (a, None) :: ts) }
| LPAREN f=form RPAREN
  { f }

ty:
| b=IDENT
  { Utypes.Basic b }
| a=ty ARROW b=ty
  { Utypes.Arrow (a, b) }
| LPAREN ty=ty RPAREN
  { ty }
