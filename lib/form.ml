open Syntax

type form_ =
  | Atom  of ident
  | And   of form * form | Top
  | Or    of form * form | Bot
  | Impl  of form * form
[@@deriving show]

and form = {
  skel : form_ ;
  id : int ;
}
[@@deriving show]

let make_form =
  let count = ref 0 in
  fun skel ->
    incr count ;
    { skel ; id = !count }

let f_atom a   = make_form @@ Atom a
let f_and f g  = make_form @@ And (f, g)
let f_top ()   = make_form Top
let f_or f g   = make_form @@ Or (f, g)
let f_bot ()   = make_form Bot
let f_impl f g = make_form @@ Impl (f, g)

type path = int list

let rec at ~(path:path) f =
  let open Result in
  let path0 = path in
  match path with
  | [] -> Ok f
  | 0 :: path -> begin
      match f.skel with
      | And (f, _) | Or (f, _) | Impl (f, _) ->
          at ~path f
      | _ -> Error path0
    end
  | 1 :: path -> begin
      match f.skel with
      | And (_, f) | Or (_, f) | Impl (_, f) ->
          at ~path f
      | _ -> Error path0
    end
  | _ -> Error path0

type fpath = {
  form : form ;
  path : path ;
}

let fpath form path = {form ; path}

let rec resolve_cx lfp rfp =
  match lfp.form.skel, rfp.form.skel with
  | Atom a, Atom b when a = b ->
      assert (lfp.path = [] && rfp.path = []) ;
      f_top ()
  | _ when lfp.path = [] && rfp.path = [] ->
      f_impl lfp.form rfp.form
  | Or (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_and
            (resolve_cx (fpath f1 lpath) rfp)
            (f_impl f2 rfp.form)
      | 1 :: lpath ->
          f_and
            (f_impl f1 rfp.form)
            (resolve_cx (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | Bot, _ -> f_top ()
  | _, Impl (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_impl
            (resolve_ax lfp (fpath g1 rpath))
            g2
      | 1 :: rpath ->
          f_impl g1 (resolve_cx lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | _, And (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_and g1 (resolve_cx lfp (fpath g2 rpath))
      | 1 :: rpath ->
          f_and (resolve_cx lfp (fpath g1 rpath)) g2
      | _ -> assert false
    end
  | _, Top -> f_top ()
  | _, Or (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          resolve_cx lfp (fpath g2 rpath)
      | 1 :: rpath ->
          resolve_cx lfp (fpath g1 rpath)
      | _ -> assert false
    end
  | And (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          resolve_cx (fpath f1 lpath) rfp
      | 1 :: lpath ->
          resolve_cx (fpath f2 lpath) rfp
      | _ -> assert false
    end
  | Impl (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 1 :: lpath ->
          f_and f1 (resolve_cx (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _ -> assert false

and resolve_ax lfp rfp =
  match lfp.form.skel, rfp.form.skel with
  | _, Top -> lfp.form
  | _, And (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_and (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_and g1 (resolve_ax lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Top, _ -> rfp.form
  | And (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_and (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_and f1 (resolve_ax (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _, Or (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_or (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_or g1 (resolve_ax lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Or (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_or (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_or f1 (resolve_ax (fpath f2 lpath) rfp)
      | _ -> assert false
    end
  | _, Impl (g1, g2) when rfp.path <> [] -> begin
      match rfp.path with
      | 0 :: rpath ->
          f_impl (resolve_ax lfp (fpath g1 rpath)) g2
      | 1 :: rpath ->
          f_impl g1 (resolve_cx lfp (fpath g2 rpath))
      | _ -> assert false
    end
  | Impl (f1, f2), _ when lfp.path <> [] -> begin
      match lfp.path with
      | 0 :: lpath ->
          f_impl (resolve_ax (fpath f1 lpath) rfp) f2
      | 1 :: lpath ->
          f_impl f1 (resolve_cx rfp (fpath f2 lpath))
      | _ -> assert false
    end
  | _ -> assert false
