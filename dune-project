(lang dune 3.0)

(name profint)

(version 0.9.2)

(license Apache-2.0)

(authors "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")
(maintainers "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")

(source (github chaudhuri/profound-intuitionistic))

(homepage "https://chaudhuri.info/research/profint")

(generate_opam_files true)

(using menhir 2.0)

(package
 (name profint)
 (synopsis "Profound: Intuitionistic Version")
 (depends
  (ocaml (>= 4.12))
;  (containers-data (>= 3.8))
  (js_of_ocaml (>= 3.9.0))
  (js_of_ocaml-ppx (>= 4.0.0))
  (ppx_blob (>= 0.7.2))
;  (yojson (>= 2.0))
;  (ppx_yojson_conv (>= "v0.15"))
  (fileutils (>= 0.6.3))
  (ppx_base (>= "v0.15"))
  (ppx_expect (and (>= "v0.15") :with-test))
  ))