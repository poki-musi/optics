(lang dune 2.0)
(name optics)
(version 0.1.0)

(generate_opam_files true)
(source (github poki-musi/optics))
(maintainers "Poki Musi <poki.musi@gmail.com>")
(authors "Poki Musi <poki.musi@gmail.com>")

(package
 (name optics)
 (synopsis "Existential optics in OCaml")
 (depends
   (ocaml (>= 4.12.0))))
