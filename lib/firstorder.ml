type ident = string
[@@deriving show]

type ty =
  | Basic of ident
  | Arrow of ty list * ty
[@@deriving show]

type term =
  | Const of ident
  | Index of int
  | App of term * term list
  | Abs of ident * ty * term list
[@@deriving show]

type bin =
  | AND | OR
[@@deriving show]

type nul =
  | TOP | BOT
[@@deriving show]

type q =
  | FORALL | EXISTS
[@@deriving show]

type quant = {
  q : q ;
  var : ident ;
  ty : ty ;
}
[@@deriving show]

type 'a form =
  | Ext of 'a
  | Atom of ident * term list
  | Bin of 'a form * bin * 'a form
  | Nul of nul
  | Impl of 'a form * 'a form
  | Quant of quant * 'a form
[@@deriving show]

type void = |

type 'a succ =
  | CHole
  | CBinL of 'a succ * bin * 'a form
  | CBinR of 'a form * bin * 'a succ
  | CQuant of quant * 'a succ
  | CSucc of 'a form * 'a succ
  | CAnte of 'a ante * 'a form
[@@deriving show]

and 'a ante =
  | ABinL of 'a ante * bin * 'a form
  | ABinR of 'a form * bin * 'a ante
  | AQuant of quant * 'a ante
  | ASucc of 'a form * 'a ante
  | AAnte of 'a succ * 'a form
[@@deriving show]

let rec std_succ cx f =
  match cx with
  | CHole -> f
  | CBinL(cx, b, g) -> Bin(std_succ cx f, b, g)
  | CBinR(g, b, cx) -> Bin(g, b, std_succ cx f)
  | CQuant(q, cx) -> Quant(q, std_succ cx f)
  | CSucc(g, cx) -> Impl(g, std_succ cx f)
  | CAnte(ax, g) -> Impl(std_ante ax f, g)

and std_ante ax f =
  match ax with
  | ABinL(ax, b, g) -> Bin(std_ante ax f, b, g)
  | ABinR(g, b, ax) -> Bin(g, b, std_ante ax f)
  | AQuant(q, ax) -> Quant(q, std_ante ax f)
  | ASucc(g, ax) -> Impl(g, std_ante ax f)
  | AAnte(cx, g) -> Impl(std_succ cx f, g)

module Test = struct
  let a = Atom("a", [])
  let b = Atom("b", [])
  let c = Atom("c", [])
  let d = Atom("d", [])
  let e = Atom("e", [])

  let cx = CBinR(a, AND, CBinL(CSucc(b, CHole), OR, d))
  let f = Impl(c, Nul BOT)
end
