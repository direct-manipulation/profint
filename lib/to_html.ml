(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Plain HTML output *)

open! Util
open! Types
open! Term
open! Form4

let wrap_numbers str =
  let rec spin exts f1 t1 f2 t2 pos str =
    match String.find_left_index ~pos str f1 with
    | Some dpos ->
        let sub = String.sub str pos (dpos - pos) in
        spin ((t1, sub) :: exts) f2 t2 f1 t1 dpos str
    | None ->
        let sub = String.drop_prefix str pos in
        (t1, sub) :: exts
  in
  spin [] Char.is_digit `v Char.is_nondigit `n 0 str |>
  List.filter_map begin fun (t, sub) ->
    if String.length sub = 0 then None else
    match t with
    | `n -> Some ({|<span class="num">|} ^ sub ^ "</span>")
    | _ -> Some sub
  end |>
  List.rev |>
  String.concat ""

type font = IT | SF

let fontify font str =
  match font with
  | IT -> {|<span class="ident">|} ^ str ^ {|</span>|}
  | SF -> str

let string_to_doc ?(font=IT) str =
  let texify id =
    match String.split_on_char '_' id |>
          List.filter (fun s -> String.length s <> 0) |>
          List.rev with
    | [] -> id
    | last :: rev_rest ->
        List.fold_left begin fun n i ->
          (wrap_numbers i) ^ "_{" ^ n ^ "}"
        end (wrap_numbers last) rev_rest
  in
  Doc.string_as (String.length str)
  @@ fontify font (texify str)

let ident_to_doc ?font id = string_to_doc ?font (Ident.to_string id)

let rep_arrow : Doc.doc = Doc.(string_as 2 {|\to|} ++ cut)

let rec ty_to_exp ty =
  match ty with
  | Ty.Basic a ->
      let rep = if Ident.equal a Ty.k_o then "o" else (Ident.to_string a) in
      Doc.(Atom (string_to_doc ~font:SF rep))
  | Ty.Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (rep_arrow, Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Ty.Var v -> begin
      match v.subst with
      | None -> Doc.(Atom (string_as 1 "&#x5F;"))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_linear out

let rep_lambda var : Doc.doc =
  Format.dprintf {|&#x3BB;%s.@,|} var
let rep_appl : Doc.doc =
  Format.dprintf {|&#x2009;@,|}

let rec termx_to_exp_ ~cx t =
  match t with
  | T.Abs { var ; body } ->
      with_var cx { var ; ty = K.ty_any } begin fun vty cx ->
        Doc.(Appl (1, Prefix (rep_lambda (Ident.to_string vty.var), termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } ->
      head_to_exp_ ~cx head
  | T.App { head ; spine } ->
      let head = head_to_exp_ ~cx head in
      let spine = List.map (termx_to_exp_ ~cx) spine in
      Doc.(Appl (100, Infix (rep_appl, Left, (head :: spine))))

and head_to_exp_ ~cx head =
  match head with
  | T.Const (k, _) ->
      let k = Ident.to_string k in
      Doc.(Atom (string_to_doc ~font:SF k))
  | T.Index n ->
      let v = Ident.to_string (List.nth cx.linear n).var in
      Doc.(Atom (string_to_doc v))

let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_linear out

let rep_eq  : Doc.doc = Format.dprintf "@<2>%s@," {|&#x2250;|}
let rep_and : Doc.doc = Format.dprintf "@<2>%s@," {|&#x2227;|}
let rep_top : Doc.doc = Format.dprintf "@<2>%s@," {|&#x22A4;|}
let rep_or  : Doc.doc = Format.dprintf "@<2>%s@," {|&#x2228;|}
let rep_bot : Doc.doc = Format.dprintf "@<2>%s@," {|&#x27C2;|}
let rep_imp : Doc.doc = Format.dprintf "@<2>%s@," {|&#x21D2;|}
let rep_forall vty : Doc.doc =
  let v = Ident.to_string vty.var in
  Format.dprintf {|@<4>%s%t@<1>%s%a.@<1>%s@,|}
    {|&#x2200;|}
    (string_to_doc v)
    {|:|} pp_ty vty.ty {| |}
let rep_exists vty : Doc.doc  =
  let v = Ident.to_string vty.var in
  Format.dprintf {|@<4>%s%t@<1>%s%a.@<1>%s@,|}
    {|&#x2203;|}
    (string_to_doc v)
    {|:|} pp_ty vty.ty {| |}

let wrap path doc =
  let lbra = Printf.sprintf {|<span data-path="%s">|} (Path.to_string path) in
  Doc.(Wrap (Transparent, string_as 0 lbra, doc, string_as 0 "</span>"))

let rec formx_to_exp_ ~cx (path : path) f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a |> wrap path
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (rep_eq, Non, [s ; t]))) |> wrap path
  | And (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (30, Infix (rep_and, Right, [a ; b]))) |> wrap path
  | Top -> Doc.(Atom rep_top) |> wrap path
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (20, Infix (rep_or, Right, [a ; b]))) |> wrap path
  | Bot -> Doc.(Atom rep_bot) |> wrap path
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx (Path.snoc path L) a in
      let b = formx_to_exp_ ~cx (Path.snoc path R) b in
      Doc.(Appl (10, Infix (rep_imp, Right, [a ; b]))) |> wrap path
  | Forall (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Path.snoc path L) b in
        Doc.(Appl (5, Prefix (rep_forall vty, b))) |> wrap path
      end
  | Exists (vty, b) ->
      with_var cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Path.snoc path L) b in
        Doc.(Appl (5, Prefix (rep_exists vty, b))) |> wrap path
      end
  | Mdata (md, _, f) -> begin
      let doc = formx_to_exp_ ~cx path f in
      match md with
      | T.App { head = Const ({base = "src" ; _}, _) ; _ } ->
          Doc.(Wrap (Transparent,
                     string_as 0 "\\lnsrc{",
                     doc, string_as 0 "}"))
      | T.App { head = Const ({base = "dest" ; _}, _) ; _ } ->
          Doc.(Wrap (Transparent,
                     string_as 0 "\\lndest{",
                     doc, string_as 0 "}"))
      | _ -> assert false
    end

let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx Path.empty fx.data

let formx_to_sout fx =
  let sob = Format.make_symbolic_output_buffer () in
  let sout = Format.formatter_of_symbolic_output_buffer sob in
  Format.pp_set_geometry sout ~margin:80 ~max_indent:79 ;
  formx_to_exp fx |> Doc.bracket |> Doc.pp sout ;
  Format.pp_print_flush sout () ;
  Format.flush_symbolic_output_buffer sob

let formx_to_string fx =
  let buf = Buffer.create 19 in
  formx_to_sout fx |>
  List.iter begin fun item ->
    match item with
    | Format.Output_newline -> Buffer.add_string buf "<br>"
    | Output_string str -> Buffer.add_string buf str
    | ( Output_spaces n | Output_indent n ) when n > 0 ->
        Printf.sprintf {|<span data-spec="%d"></span>|} n |>
        Buffer.add_string buf
    | _ -> ()
  end ;
  Buffer.contents buf

let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_linear out

let pp_sigma out sg =
  Format.pp_print_string out {|\displaystyle{\begin{array}{lll}|};
  Ident.Set.iter begin fun i ->
    if Ident.Set.mem i sigma0.basics then () else
      Format.fprintf out {|%t&\mkern -7mu{:}&\mkern -7mu \mathsf{type}.\\|} (ident_to_doc ~font:SF i)
  end sg.basics ;
  Ident.Map.iter begin fun k ty ->
    if Ident.Map.mem k sigma0.consts then () else
      Format.fprintf out {|%t&\mkern -7mu{:}&\mkern -7mu \mathsf{%a}.\\|}
        (ident_to_doc ~font:SF k) pp_ty (thaw_ty ty)
  end sg.consts ;
  Format.pp_print_string out {|\end{array}}|}

let pp_path out (path : path) =
  Format.pp_print_string out @@ Path.to_string path
  (* Path.to_list path |> *)
  (* Format.pp_print_list *)
  (*   ~pp_sep:(fun out () -> Format.pp_print_string out ", ") *)
  (*   Path.Dir.(fun out -> function *)
  (*       | L -> Format.pp_print_string out "l" *)
  (*       | R -> Format.pp_print_string out "r") out *)

let pp_deriv out (sg, deriv) =
  pp_sigma out sg ;
  Format.fprintf out "%a@." pp_formx deriv.Cos.top ;
  List.iter begin fun (_, rule, concl) ->
    Format.fprintf out "%a :: %a@."
      pp_path rule.Cos.path
      Cos.pp_rule_name rule.Cos.name ;
    Format.fprintf out "%a@." pp_formx concl ;
  end deriv.middle

let pp_header _out () = ()
let pp_footer _out () = ()
let pp_comment out str =
  Format.( pp_print_string out "% " ;
           pp_print_string out str ;
           pp_print_newline out () )

let name = "html"
let files _ = invalid_arg "To.Html.files"
let build () = invalid_arg "To.Html.build"
