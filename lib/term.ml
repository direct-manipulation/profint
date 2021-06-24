open Syntax

type ty =
  | Basic of ident
  | Arrow of ty list * ty
[@@deriving show]

type term =
  | Const of ident
  | Index of int
  | App of term * term list
  | Abs of ident * ty * term
[@@deriving show]

type sub =
  | Shift of int
  | Dot of sub * term
[@@deriving show]

let rec app_term sub tm =
  match tm with
  | Const _ -> tm
  | Index n -> app_index sub n
  | App (tf, targs) ->
      do_app (app_term sub tf) (List.map (app_term sub) targs)
  | Abs (x, ty, tbod) ->
      Abs (x, ty, app_term (bump sub) tbod)

and app_index sub n =
  match sub with
  | Shift j -> Index(j + n)
  | Dot (sub, t) -> begin
      match n with
      | 0 -> t
      | _ -> app_index sub (n - 1)
    end

and do_app tf targs =
  match tf, targs with
  | Abs (_, _, tf), (targ :: targs) ->
      let tf = app_term (Dot (Shift 0, targ)) tf in
      do_app tf targs
  | _ -> App (tf, targs)

and bump sub = Dot (seq sub (Shift 1), Index 0)

and seq sub1 sub2 =
  match sub1, sub2 with
  | Shift j, Shift k -> Shift (j + k)
  | Shift 0, sub
  | sub, Shift 0 -> sub
  | Dot (sub1, _), Shift j -> seq sub1 (Shift (j - 1))
  | _, Dot (sub2, tm) -> Dot (seq sub1 sub2, app_term sub1 tm)

module Test = struct
  let tf = Abs ("x", Basic "a", Abs ("y", Basic "b", Index 1))
  let tf2 = Abs ("x", Arrow ([Basic "a" ; Basic "b"], Basic "c"),
                 Abs ("y", Arrow ([Basic "a"], Basic "b"),
                      Abs ("z", Basic "a",
                           App (Index 2, [Index 0 ; App (Index 1, [Index 0])]))))
end
