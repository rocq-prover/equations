(lang dune 3.21)
(using rocq 0.11)
(name rocq-equations)
(source (github mattam82/Coq-Equations))
(license LGPL-2.1-only)
(authors "Matthieu Sozeau <matthieu.sozeau@inria.fr>"  "Cyprien Mangin <cyprien.mangin@m4x.org>")
(maintainers "Matthieu Sozeau <matthieu.sozeau@inria.fr>")
(homepage "https://mattam82.github.io/Coq-Equations")

(package 
 (name rocq-equations)
 (synopsis "A function definition package for Rocq")
 (description "Equations is a function definition plugin for Rocq, that allows the \
  definition of functions by dependent pattern-matching and well-founded, \
  mutual or nested structural recursion and compiles them into core \
  terms. It automatically derives the clauses equations, the graph of the \
  function and its associated elimination principle.")
 (tags ("keyword:dependent pattern-matching"
  "keyword:functional elimination"
  "category:Miscellaneous/Coq Extensions"
  "logpath:Equations"))
 (depends
   (ocaml (>= 4.10.0))
   (rocq-prover (>= "9.0~"))
   (ppx_optcomp :build)
   (ocaml-lsp-server :with-dev-setup)))

(package 
 (name rocq-equations-hott)
 (synopsis "A function definition package for Rocq - HoTT variant")
 (description "Equations is a function definition plugin for Rocq, that allows the \
  definition of functions by dependent pattern-matching and well-founded, \
  mutual or nested structural recursion and compiles them into core \
  terms. It automatically derives the clauses equations, the graph of the \
  function and its associated elimination principle.")
 (tags ("keyword:dependent pattern-matching"
  "keyword:functional elimination"
  "category:Miscellaneous/Coq Extensions"
  "logpath:Equations"))
 (depends
   (ocaml (>= 4.10.0))
   (rocq-prover (>= "9.0~"))
   (ppx_optcomp :build)
   (ocaml-lsp-server :with-dev-setup)
   rocq-equations
   coq-hott))

(generate_opam_files)
 
(package
 (name rocq-equations-examples)
 (synopsis "Examples")
 (description "Examples of use of Equations")
 (depends rocq-equations))

(package
 (name rocq-equations-tests)
 (synopsis "Technical package to run tests")
 (description "Do not install")
 (depends rocq-equations))
