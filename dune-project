(lang dune 3.17)

(name profint)

(version 0.9.2)

(license Apache-2.0)

(authors "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")
(maintainers "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")

(source (github direct-manipulation/profint))

(homepage "https://chaudhuri.info/research/profint")

(generate_opam_files true)

(using menhir 2.0)

(package
 (name profint)
 (synopsis "Profound: Intuitionistic Version")
 (depends
  (ocaml (>= 4.12))
  (zarith (>= 1.12))
  (zarith_stubs_js (>= "v0.15"))
  (js_of_ocaml (>= 3.9.0))
  (js_of_ocaml-ppx (>= 4.0.0))
  (fileutils (>= 0.6.3))
  (crunch (>= 4.0.0))
  ))