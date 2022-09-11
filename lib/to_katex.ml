(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open! Util
open! Types
open! Term
open! Form4

let rep_arr =
  Doc.Fmt
    Format.(fun out ->
      pp_print_as out 2 {|\to|} ;
      pp_print_cut out ())

let texify id =
  match String.split_on_char '_' id |>
        List.filter (fun s -> s <> "") |>
        List.rev with
  | [] -> id
  | last :: rev_rest ->
      List.fold_left begin fun n i ->
        i ^ "_{" ^ n ^ "}"
      end last rev_rest

let rec ty_to_exp ty =
  match ty with
  | Basic a ->
      let rep = if a = K.k_o then "Prop" else a in
      let len = String.length rep in
      let rep = "\\mathsf{" ^ texify rep ^ "}" in
      Doc.(Atom (StringAs (len, rep)))
  | Arrow (ta, tb) ->
      Doc.(Appl (1, Infix (rep_arr, Right,
                           [ty_to_exp ta ; ty_to_exp tb])))
  | Tyvar v -> begin
      match v.subst with
      | None -> Doc.(Atom (StringAs (1, "\\_")))
      | Some ty -> ty_to_exp ty
    end

let pp_ty out ty = ty_to_exp ty |> Doc.bracket |> Doc.pp_lin_doc out

let rep_lambda var =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 "\\lambda{" ;
      pp_print_string out var ;
      pp_print_as out 1 "}.\\," ;
      pp_print_cut out ()
    )
let rep_appl =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 "\\," ;
      pp_print_cut out () ;
    )

let fresh_id =
  let count = ref 0 in
  fun () -> incr count ; !count

let rec termx_to_exp_ ~cx t =
  match t with
  | T.Abs { var ; body } ->
      with_var ~fresh:true cx { var ; ty = K.ty_any } begin fun vty cx ->
        Doc.(Appl (1, Prefix (rep_lambda vty.var, termx_to_exp_  ~cx body)))
      end
  | T.App { head ; spine = [] } -> begin
      match Term.head_to_exp ~cx head with
      | Doc.(Atom (String h)) ->
          Doc.(Atom (StringAs (String.length h, texify h)))
      | _ -> assert false
    end
  | T.App { head ; spine } ->
      let head = Term.head_to_exp ~cx head in
      let spine = List.map (termx_to_exp_ ~cx) spine in
      Doc.(Appl (100, Infix (rep_appl, Left, (head :: spine))))

let termx_to_exp tx =
  Doc.(Wrap (Transparent,
             StringAs (0, Printf.sprintf "\\htmlId{t%d}{" @@ fresh_id ()),
             termx_to_exp_ ~cx:tx.tycx tx.data,
             StringAs (0, "}")))
let pp_termx out tx = termx_to_exp tx |> Doc.bracket |> Doc.pp_lin_doc out

let rep_eq =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 2 {|\mathbin{\doteq}|} ;
      pp_print_cut out ())
let rep_and =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 2 {|\mathbin{\land}|} ;
      pp_print_cut out ())
let rep_top =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 {|\top|})
let rep_or =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 2 {|\mathbin{\lor}|} ;
      pp_print_cut out ())
let rep_bot =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 {|\bot|})
let rep_imp =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 2 {|\mathbin{\Rightarrow}|} ;
      pp_print_cut out ())
let rep_forall vty =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 "\\forall{" ;
      pp_print_as out (String.length vty.var) (texify vty.var) ;
      pp_print_as out 1 "{:}" ;
      pp_ty out vty.ty ;
      pp_print_as out 1 "}.\\," ;
      pp_print_cut out ()
    )
let rep_exists vty =
  Doc.Fmt Format.(fun out ->
      pp_print_as out 1 "\\exists{" ;
      pp_print_as out (String.length vty.var) (texify vty.var) ;
      pp_print_as out 1 "{:}" ;
      pp_ty out vty.ty ;
      pp_print_as out 1 "}.\\," ;
      pp_print_cut out ()
    )

let dir_to_string (d : dir) =
  match d with
  | `l -> "l"
  | `r -> "r"
  | `d -> "d"
  | `i x -> "i(" ^ x ^ ")"
let path_to_string path =
  path
  |> Q.to_list
  |> List.map dir_to_string
  |> String.concat ";"

let wrap path doc =
  let lbra =
    Printf.sprintf "\\htmlId{f%d}{\\htmlData{path=%s}{"
      (fresh_id ())
      (path_to_string path)
  in
  Doc.(Wrap (Transparent, StringAs (0, lbra), doc, StringAs (0, "}}")))

let rec formx_to_exp_ ~cx (path : path) f =
  match expose f with
  | Atom a -> termx_to_exp_ ~cx a |> wrap path
  | Eq (s, t, _) ->
      let s = termx_to_exp_ ~cx s in
      let t = termx_to_exp_ ~cx t in
      Doc.(Appl (40, Infix (rep_eq, Non, [s ; t]))) |> wrap path
  | And (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (30, Infix (rep_and, Right, [a ; b]))) |> wrap path
  | Top -> Doc.(Atom rep_top) |> wrap path
  | Or (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (20, Infix (rep_or, Right, [a ; b]))) |> wrap path
  | Bot -> Doc.(Atom rep_bot) |> wrap path
  | Imp (a, b) ->
      let a = formx_to_exp_ ~cx (Q.snoc path `l) a in
      let b = formx_to_exp_ ~cx (Q.snoc path `r) b in
      Doc.(Appl (10, Infix (rep_imp, Right, [a ; b]))) |> wrap path
  | Forall (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Q.snoc path (`i vty.var)) b in
        Doc.(Appl (5, Prefix (rep_forall vty, b))) |> wrap path
      end
  | Exists (vty, b) ->
      with_var ~fresh:true cx vty begin fun vty cx ->
        let b = formx_to_exp_ ~cx (Q.snoc path (`i vty.var)) b in
        Doc.(Appl (5, Prefix (rep_exists vty, b))) |> wrap path
      end
  | Mdata (md, _, f) -> begin
      let doc = formx_to_exp_ ~cx path f in
      match md with
      | T.App { head = Const ("src", _) ; _ } ->
          Doc.(Wrap (Transparent,
                     StringAs (0, "\\lnsrc{"),
                     doc, StringAs (0, "}")))
      | T.App { head = Const ("dest", _) ; _ } ->
          Doc.(Wrap (Transparent,
                     StringAs (0, "\\lndest{"),
                     doc, StringAs (0, "}")))
      | _ -> assert false
    end

let formx_to_exp fx = formx_to_exp_ ~cx:fx.tycx Q.empty fx.data
let pp_formx out fx = formx_to_exp fx |> Doc.bracket |> Doc.pp_lin_doc out

let pp_sigma out sg =
  Format.pp_open_vbox out 0 ; begin
    IdSet.iter begin fun i ->
      if IdSet.mem i sigma0.basics then () else
        Format.fprintf out {|%s : \mathsf{type}.@,|} i
    end sg.basics ;
    IdMap.iter begin fun k ty ->
      if IdMap.mem k sigma0.consts then () else
        Format.fprintf out {|%s : %a.@,|} k pp_ty (thaw_ty ty)
    end sg.consts
  end ; Format.pp_close_box out ()

let pp_path out (path : path) =
  Q.to_seq path |>
  Format.pp_print_seq
    ~pp_sep:(fun out () -> Format.pp_print_string out ", ")
    (fun out -> function
       | `l -> Format.pp_print_string out "l"
       | `r -> Format.pp_print_string out "r"
       | `d -> Format.pp_print_string out "d"
       | `i x ->
           Format.pp_print_string out "i " ;
           Format.pp_print_string out x) out

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

let name = "katex"
let files _ = invalid_arg "To.Katex.files"
let build () = invalid_arg "To.Katex.build"
