# External-Axiom Register

This repository declares **zero** custom Lean `axiom` statements and **zero** hypothesis-bundle structures. Every exported theorem in `LogarithmicRigidity` and `comparator/Challenge.lean` depends exclusively on Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`.

Results from the manuscript that depend on classical theories not yet formalized in Mathlib `v4.35.0` (Deligne 1971, Carnicer 1994, Harnack 1876, Serre duality on `ℙ²`, Camacho–Lins Neto–Sad 1984, Giacomini–Llibre–Viano 1996) are not claimed as proved in this repository and are listed explicitly in `README.md` and `PROOF-PATH.md`.
