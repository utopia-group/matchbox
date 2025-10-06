(lang dune 3.19)
(using menhir 3.0)

(name stijl)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name stijl)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  (core
   (>= v0.16.2))
  (core_unix
   (>= v0.16.0))
  gpl
  alcotest)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
