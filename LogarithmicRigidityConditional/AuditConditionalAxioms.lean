/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import LogarithmicRigidityConditional

/-!
# Axiom Audit for Conditional Full-Manuscript Theorems

Prints the exact axiom dependencies of every headline theorem in `LogarithmicRigidityConditional`.
Every dependency must be in `[propext, Classical.choice, Quot.sound]` or an explicitly documented
external literature axiom in `LogarithmicRigidityConditional/ExternalLiterature.lean`.
-/

#print axioms LogarithmicRigidityConditional.lemma_2_1_nondicritical_criterion
#print axioms LogarithmicRigidityConditional.lemma_3_1_blowup_propagation
#print axioms LogarithmicRigidityConditional.prop_3_2_logarithmic_residues
#print axioms LogarithmicRigidityConditional.theorem_1_1_logarithmic_rigidity
#print axioms LogarithmicRigidityConditional.prop_4_1_real_logarithmic_obstruction
#print axioms LogarithmicRigidityConditional.theorem_1_2_standard_upper_bound
#print axioms LogarithmicRigidityConditional.theorem_1_2_standard_sharpness
#print axioms LogarithmicRigidityConditional.theorem_1_3_part1_smooth_nonexistence
#print axioms LogarithmicRigidityConditional.theorem_1_3_part2_existence
#print axioms LogarithmicRigidityConditional.theorem_1_4_part1_r_nonzero_bounds
#print axioms LogarithmicRigidityConditional.theorem_1_4_part2_counterexample
