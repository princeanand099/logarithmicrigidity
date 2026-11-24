# Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations

Lean 4 (`v4.35.0`) formalization of Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*.

## Build & Verification

```bash
lake exe cache get
lake build LogarithmicRigidity Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake comparator
```

## Module Structure

- `comparator/ChallengeDefs.lean` — Public definitions, explicit polynomial families, and classical-literature hypothesis bundles.
- `comparator/Challenge.lean` — Locked headline theorem statements for `lake comparator`.
- `comparator/Solution.lean` — Solution export module checked against `Challenge.lean`.
- `LogarithmicRigidity/Preliminaries.lean` — Section 2 (Eq. 2.1, Lemma 2.1, Lemma 2.4).
- `LogarithmicRigidity/LogarithmicRigidity.lean` — Section 3 (Lemma 3.1, Proposition 3.2, Theorem 1.1).
- `LogarithmicRigidity/RealLogarithmic.lean` — Section 4 (Proposition 4.1, Theorem 1.2).
- `LogarithmicRigidity/JacobianSyzygies.lean` — Section 5 (Proposition 5.1, Lemma 5.2, Lemma 5.3, Proposition 5.4, Theorem 1.3).
- `LogarithmicRigidity/CaseRNonZero.lean` — Section 6 Part A (Theorem 1.4(1), Lemma 6.1).
- `LogarithmicRigidity/CounterexampleCert.lean` — Section 6 Part B & Appendix A (Proposition 6.2, Proposition 6.3, Theorem 1.4(2)).
- `LogarithmicRigidity/SanityChecks.lean` — Small-case and non-vacuity checks.
- `LogarithmicRigidity/AuditAxioms.lean` — `#print axioms` audit on every headline theorem.

## Documentation

- `PROOF-PATH.md` — Manuscript-to-Lean theorem correspondence and dependency DAG.
- `PROGRESS.md` — Continuous formalization progress record.
- `EXTERNAL-AXIOMS.md` — External-axiom register (zero custom `axiom` declarations; classical literature results packaged as explicit hypothesis structures).
- `ATTRIBUTION.md` & `CITATION.cff` — Citation and attribution metadata.
