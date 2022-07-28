(lang dune 2.7)

(name profint)

(version 0.8.1)

(license BSD-2-Clause)

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
;  (containers (>= 3.8))
  (ounit2 (>= 2.2.6))
  (js_of_ocaml (>= 3.9.0))
  (js_of_ocaml-ppx (>= 4.0.0))))