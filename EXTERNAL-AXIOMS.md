# External-Axiom Register

This repository declares **zero** custom Lean `axiom` statements. Every exported theorem depends exclusively on the standard Lean 4 kernel axioms `[propext, Classical.choice, Quot.sound]`.

Classical peer-reviewed theorems external to the manuscript's contribution are packaged as explicit typed hypothesis structures in `comparator/ChallengeDefs.lean`:

1. **Carnicer (1994)**, *The Poincaré problem in the non-dicritical case*, Ann. of Math. (2) **140**, 289–294 (`BlowUpStepData.nonDicritical`, `StandardSystemData.carnicer_deg`, `RNonZeroSystemData.carnicer_deg`).
2. **Deligne (1971)**, *Théorie de Hodge. II*, Publ. Math. IHÉS **40**, 5–57, Cor. 3.2.14 (`Section3ClassicalData.residues`).
3. **Harnack (1876)**, *Ueber die Vieltheiligkeit der ebenen algebraischen Curven*, Math. Ann. **10**, 189–199 (`StandardSystemData.harnack_bound`, `RNonZeroSystemData.harnack_bound`).
4. **Giacomini, Llibre, Viano (1996)**, *On the nonexistence, existence and uniqueness of limit cycles*, Nonlinearity **9**, 501–516 (`RealLogCenterObstruction`).
5. **Camacho, Lins Neto, Sad (1984)**, *Topological invariants and equidesingularization for holomorphic vector fields*, J. Differential Geom. **20**, 143–174 (local classification of non-degenerate singularities used with Lemma 2.1).
6. **Dimca (2013)**, *Syzygies of Jacobian ideals and defects of linear systems*, Bull. Math. Soc. Sci. Math. Roumanie **56(104)**, 191–203 (cohomological defect formula in Proposition 5.1(2)).
