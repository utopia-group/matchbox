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
  (dune (>= 3.19))
  (core (>= v0.16.2))
  (core_unix (>= v0.16.0))
  gpl
  (ke (>= 0.6))
  (yojson (>= 2.2.2))
  (ppx_jane (>= v0.16.0))
  (ppx_deriving_yojson (>= 3.9.1))
  (menhir (>= 20240715))
  (alcotest (>= 1.9.0)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
