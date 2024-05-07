(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** Output suitable for processing with katex

    https://katex.org *)

open Base

open! Util
open! Types
open! Term
open! Form4

let is_digit _ c = Char.('0' <= c && c <= '9')
let is_nondigit _ c = Char.(c < '0' || c > '9')

let wrap_numbers str =
  let rec spin exts f1 t1 f2 t2 pos str =
    match String.lfindi str ~pos ~f:f1 with
    | Some dpos ->
        let sub = String.sub str ~pos ~len:(dpos - pos) in
        spin ((t1, sub) :: exts) f2 t2 f1 t1 dpos str
    | None ->
        let sub = String.drop_prefix str pos in
        (t1, sub) :: exts
  in
  spin [] is_digit `v is_nondigit `n 0 str |>
  List.rev_filter_map ~f:(
    fun (t, sub) ->
      if String.is_empty sub then None else
      match t with
      | `n -> Some ("\\mathrm{" ^ sub ^ "}")
      | _ -> Some sub) |>
  String.concat ~sep:""

let string_to_doc ?(font="it") str =
  let texify id =
    match String.split ~on:'_' id |>
          List.rev_filter ~f:(fun s -> not @@ String.is_empty s) with
    | [] -> id
    | last :: rev_rest ->
        List.fold_left ~f:begin fun n i ->
          (wrap_numbers i) ^ "_{" ^ n ^ "}"
        end ~init:(wrap_numbers last) rev_rest
  in
  Doc.string_as (String.length str)
  @@ {|\math|} ^ font ^ "{" ^ (texify str) ^ "}"

let ident_to_doc ?font id = string_to_doc ?font (Ident.to_string id)

let rep_arrow : Doc.doc = Doc.(string_as 2 {|\to|} ++ cut)

let rec ty_to_exp ty =
  match ty with
  | Ty.Basic a ->
      let rep = if Ident.equal a Ty.k_o then "o" else (Ident.to_string a) in
      Doc.(Atom (string_to_doc ~font:"sf" rep))
  | Ty.Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (rep_arrow, Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Ty.Var v -> begin
      match v.subst with
      | None -> Doc.(Atom (string_as 1 "\\_"))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_linear out

let rep_lambda var : Doc.doc =
  Stdlib.Format.dprintf {|\lambda{%s}.\,@,|} var
let rep_appl : Doc.doc = Stdlib.Format.dprintf {|\,@,|}

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
      let spine = List.map ~f:(termx_to_exp_ ~cx) spine in
      Doc.(Appl (100, Infix (rep_appl, Left, (head :: spine))))

and head_to_exp_ ~cx head =
  match head with
  | T.Const (k, _) ->
      let k = Ident.to_string k in
      Doc.(Atom (string_to_doc ~font:"sf" k))
  | T.Index n ->
      let v = Ident.to_string (List.nth_exn cx.linear n).var in
      Doc.(Atom (string_to_doc v))

let termx_to_exp tx = termx_to_exp_ ~cx:tx.tycx tx.data
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_linear out

let rep_eq  : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\mathbin{\doteq}|}
let rep_and : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\mathbin{\land}|}
let rep_top : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\top|}
let rep_or  : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\mathbin{\lor}|}
let rep_bot : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\bot|}
let rep_imp : Doc.doc = Stdlib.Format.dprintf "@<2>%s@," {|\mathbin{\Rightarrow}|}
let rep_forall vty : Doc.doc =
  let v = Ident.to_string vty.var in
  Stdlib.Format.dprintf {|@<4>%s%t@<1>%s%a.@<1>%s@,|}
    {|\forall{|}
    (string_to_doc v)
    {|}{:}|} pp_ty vty.ty {|\,|}
let rep_exists vty : Doc.doc  =
  let v = Ident.to_string vty.var in
  Stdlib.Format.dprintf {|@<4>%s%t@<1>%s%a.@<1>%s@,|}
    {|\exists{|}
    (string_to_doc v)
    {|}{:}|} pp_ty vty.ty {|\,|}

let wrap path doc =
  let lbra = Printf.sprintf "\\htmlData{path=%s}{" (Path.to_string path) in
  Doc.(Wrap (Transparent, string_as 0 lbra, doc, string_as 0 "}"))

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
  let sob = Stdlib.Format.make_symbolic_output_buffer () in
  let sout = Stdlib.Format.formatter_of_symbolic_output_buffer sob in
  Stdlib.Format.pp_set_geometry sout ~margin:80 ~max_indent:79 ;
  formx_to_exp fx |> Doc.bracket |> Doc.pp sout ;
  Stdlib.Format.pp_print_flush sout () ;
  Stdlib.Format.flush_symbolic_output_buffer sob

let formx_to_string fx =
  let buf = Buffer.create 19 in
  formx_to_sout fx |>
  List.iter ~f:Stdlib.Format.(fun item ->
      match item with
      | Output_newline -> Buffer.add_string buf "\\htmlClass{brk}{}"
      | Output_string str -> Buffer.add_string buf str
      | ( Output_spaces n | Output_indent n ) when n > 0 ->
          Buffer.add_string buf "\\htmlData{spc=" ;
          Buffer.add_string buf (Int.to_string n) ;
          Buffer.add_string buf "}{}"
      | _ -> ()
    ) ;
  Buffer.contents buf

let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_linear out

let pp_sigma out sg =
  Stdlib.Format.pp_print_string out {|\displaystyle{\begin{array}{lll}|};
  Set.iter ~f:begin fun i ->
    if Set.mem sigma0.basics i then () else
      Stdlib.Format.fprintf out {|%t&\mkern -7mu{:}&\mkern -7mu \mathsf{type}.\\|} (ident_to_doc ~font:"sf" i)
  end sg.basics ;
  Map.iteri ~f:begin fun ~key:k ~data:ty ->
    if Map.mem sigma0.consts k then () else
      Stdlib.Format.fprintf out {|%t&\mkern -7mu{:}&\mkern -7mu \mathsf{%a}.\\|}
        (ident_to_doc ~font:"sf" k) pp_ty (thaw_ty ty)
  end sg.consts ;
  Stdlib.Format.pp_print_string out {|\end{array}}|}

let pp_path out (path : path) =
  Stdlib.Format.pp_print_string out @@ Path.to_string path
  (* Path.to_list path |> *)
  (* Stdlib.Format.pp_print_list *)
  (*   ~pp_sep:(fun out () -> Stdlib.Format.pp_print_string out ", ") *)
  (*   Path.Dir.(fun out -> function *)
  (*       | L -> Stdlib.Format.pp_print_string out "l" *)
  (*       | R -> Stdlib.Format.pp_print_string out "r") out *)

let pp_deriv out (sg, deriv) =
  pp_sigma out sg ;
  Stdlib.Format.fprintf out "%a@." pp_formx deriv.Cos.top ;
  List.iter ~f:begin fun (_, rule, concl) ->
    Stdlib.Format.fprintf out "%a :: %a@."
      pp_path rule.Cos.path
      Cos.pp_rule_name rule.Cos.name ;
    Stdlib.Format.fprintf out "%a@." pp_formx concl ;
  end deriv.middle

let pp_header _out () = ()
let pp_footer _out () = ()
let pp_comment out str =
  Stdlib.Format.( pp_print_string out "% " ;
           pp_print_string out str ;
           pp_print_newline out () )

let name = "katex"
let files _ = invalid_arg "To.Katex.files"
let build () = invalid_arg "To.Katex.build"
