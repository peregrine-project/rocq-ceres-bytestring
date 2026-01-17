From Ceres Require Import CeresParser.
From Ceres Require Import Ceres.

From Coq Require Import Ascii.
From Coq Require Import List.
Import ListNotations.

From Coq Require Import String.
Open Scope string_scope.

Definition exp : sexp := Atom_ (Str "hello world ∃ ? .- ၍").
Definition s : string := string_of_sexp exp.
Definition exp' := parse_sexp s.
Definition exp'' := parse_sexp """hello world ∃ ? .- ၍""".

Compute exp.
Compute s.
Compute exp'.
Compute exp''.
