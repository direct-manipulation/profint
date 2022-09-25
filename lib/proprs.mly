(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  open Base
  open Types
  module Printf = Caml.Printf   (* [HACK] Menhir inserts calls to Printf *)

  let make_quant q vs bod =
    List.fold_right
      ~f:(fun (x, ty) f -> U.(App (Kon (q, None), Abs (x, ty, f))))
      ~init:bod vs

  let rec make_app ts =
    match ts with
    | [] -> assert false
    | [t] -> t
    | f :: t :: ts -> make_app (U.App (f, t) :: ts)

  type sig_one =
    | Basic of Ident.t
    | Const of Ident.t * Ty.t

  let assemble_signature things =
    let rec aux sigma = function
      | [] -> sigma
      | Basic t :: things ->
         aux (add_basic sigma t) things
      | Const (k, ty) :: things ->
         aux (add_const sigma k { nvars = 0 ; ty }) things
    in
    aux sigma0 things
%}

%token  EOS PREC_MIN (* PREC_MAX *)
%token  <Ident.t> IDENT
%token  LPAREN RPAREN LBRACK RBRACK COMMA COLON DOT
%token  ARROW OMICRON TYPE
%token  EQ
%token  AND OR TO FROM BOT TOP
%token  FORALL EXISTS

%nonassoc PREC_MIN
%left     FROM
%right    TO ARROW
%right    OR
%right    AND
(* %nonassoc PREC_MAX *)

%start <U.term> one_term
%start <Ty.t> one_ty
%start <U.term> one_form
%start <Types.sigma> signature

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
| vs=loption(lambda) bod=app_term
  { List.fold_right ~f:(fun (x, ty) t -> U.Abs (x, ty, t)) ~init:bod vs }

app_term:
| ts=nonempty_list(wrapped_term)
  { make_app ts }

lambda:
| vss=nonempty_list(delimited(LBRACK, ids_ty, RBRACK))
  { List.concat vss }

ids_ty:
| xs=separated_nonempty_list(COMMA, IDENT) COLON ty=ty
  { let ty = Some ty in
    List.map ~f:(fun x -> (x, ty)) xs }
| xs=separated_nonempty_list(COMMA, IDENT)
  { List.map ~f:(fun x -> (x, None)) xs }

wrapped_term:
| v=IDENT
  { U.Var v }
| LPAREN t=term RPAREN
  { t }

form:
| TOP
  { U.(Kon (K.k_top, None)) }
| BOT
  { U.(Kon (K.k_bot, None)) }
| fa=form AND fb=form
  { U.(App (App (Kon (K.k_and, None), fa), fb)) }
| fa=form OR fb=form
  { U.(App (App (Kon (K.k_or, None), fa), fb)) }
| fa=form TO fb=form
  { U.(App (App (Kon (K.k_imp, None), fa), fb)) }
| fa=form FROM fb=form
  { U.(App (App (Kon (K.k_imp, None), fb), fa)) }
| FORALL vs=lambda bod=form %prec PREC_MIN
  { make_quant K.k_all vs bod }
| EXISTS vs=lambda bod=form %prec PREC_MIN
  { make_quant K.k_ex vs bod }
| EQ ta=wrapped_term tb=wrapped_term
  { U.(App (App (Kon (K.k_eq, None), ta), tb)) }
| a=IDENT ts=list(wrapped_term)
  { make_app (U.Kon (a, None) :: ts) }
| LPAREN f=form RPAREN
  { f }

ty:
| OMICRON
  { Ty.o }
| b=IDENT
  { Ty.Basic b }
| a=ty ARROW b=ty
  { Ty.Arrow (a, b) }
| LPAREN ty=ty RPAREN
  { ty }

signature:
| sss=list(signature_elem) EOS
  { assemble_signature (List.concat sss) }

signature_elem:
| vs=separated_nonempty_list(COMMA, IDENT) COLON ty=ty DOT
  { List.map ~f:(fun v -> Const (v, ty)) vs }
| vs=separated_nonempty_list(COMMA, IDENT) COLON TYPE DOT
  { List.map ~f:(fun v -> Basic v) vs }
