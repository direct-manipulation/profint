(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  let make_quant q vs bod =
    List.fold_right
      (fun (x, ty) f -> Types.(App (Kon (q, None), Abs (x, ty, f))))
      vs bod

  let rec make_app ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | f :: t :: ts -> make_app (Types.App (f, t) :: ts)
%}

%token  EOS PREC_MIN PREC_MAX
%token  <Util.ident> IDENT
%token  LPAREN RPAREN LBRACK RBRACK COMMA COLON
%token  ARROW OMICRON IOTA
%token  EQ NEQ
%token  AND OR TO FROM BOT TOP
%token  FORALL EXISTS

%nonassoc PREC_MIN
%left     FROM
%right    TO ARROW
%left     OR
%left     AND
%nonassoc PREC_MAX

%start  <Types.uterm> one_term
%start  <Types.ty>   one_ty
%start  <Types.uterm> one_form

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
  { List.fold_right (fun (x, ty) t -> Types.Abs (x, ty, t)) vs bod }

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
  { Types.Var v }
| LPAREN t=term RPAREN
  { t }

form:
| TOP
  { Types.(Kon (k_top, None)) }
| BOT
  { Types.(Kon (k_bot, None)) }
| fa=form AND fb=form
  { Types.(App (App (Kon (k_and, None), fa), fb)) }
| fa=form OR fb=form
  { Types.(App (App (Kon (k_or, None), fa), fb)) }
| fa=form TO fb=form
  { Types.(App (App (Kon (k_imp, None), fa), fb)) }
| fa=form FROM fb=form
  { Types.(App (App (Kon (k_imp, None), fb), fa)) }
| FORALL vs=lambda bod=form %prec PREC_MIN
  { make_quant Types.k_all vs bod }
| EXISTS vs=lambda bod=form %prec PREC_MIN
  { make_quant Types.k_ex vs bod }
| a=IDENT ts=list(wrapped_term)
  { make_app (Types.Kon (a, None) :: ts) }
| LPAREN f=form RPAREN
  { f }

ty:
| OMICRON
  { Types.ty_o }
| IOTA
  { Types.ty_i }
| b=IDENT
  { Types.Basic b }
| a=ty ARROW b=ty
  { Types.Arrow (a, b) }
| LPAREN ty=ty RPAREN
  { ty }
