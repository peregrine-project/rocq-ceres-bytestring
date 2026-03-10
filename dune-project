(lang dune 2.8)
(using coq 0.2)
(name rocq-ceres-bytestring)
(version dev)

(generate_opam_files true)

(source (github peregrine-project/rocq-ceres-bytestring))
(license MIT)
(authors "Li-yao Xia")
(maintainers "The Peregrine team")

(package
 (name rocq-ceres-bytestring)
 (synopsis "Library for serialization via S-expressions using bytestrings")
 (depends (coq (>= 9.0~)) (rocq-metarocq-utils (>= 1.4~)))
)
