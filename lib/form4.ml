(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2021  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(******************************************************************************)
(* Form4 Library *)

module Core     = Form4_core
include Core
module Paths    = Form4_paths
type dir = Paths.dir
type path = Paths.path
module Cos      = Form4_cos
(* module Simplify = Form4_simplify *)
include Form4_simplify
include Form4_dmanip
