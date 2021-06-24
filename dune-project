(lang dune 2.7)

(name profint)

(version 1.1.0~beta)

(license CECILL-B)

(authors "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")
(maintainers "Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>")

(source (github chaudhuri/profound-intuitionistic))

(homepage "https://chaudhuri.info/research/profint")

(generate_opam_files true)

(package
 (name profint)
 (synopsis "Profound: Intuitionistic Version")
 (depends
  (ocaml (>= 4.12))
  (js_of_ocaml (>= 3.9.0))))