(lang dune 3.21)
(using rocq 0.11)

(name LogicTransformers)

(generate_opam_files true)

(source
 (github CharlesAverill/LogicTransformers))

(authors
 "Charles Averill <charlesaverill20@gmail.com>")

(maintainers
 "Charles Averill <charlesaverill20@gmail.com>")

(license MIT)

(documentation https://github.com/CharlesAverill/LogicTransformers)

(package
 (name LogicTransformers)
 (synopsis "Formally verified transformations between program logics")
 (description "Explicit, verified functions from program logics to program logics, e.g. along the edges of the Cousot cube")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
