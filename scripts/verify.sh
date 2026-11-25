#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. STATIC HYGIENE CHECK (Unconditional Core) ==="
hygiene_hits=$(grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' \
  LogarithmicRigidity.lean LogarithmicRigidity/ comparator/ChallengeDefs.lean comparator/Solution.lean \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|/[-!]|/-)' \
  | grep -vE 'AuditAxioms\.lean' || true)
if [ -n "$hygiene_hits" ]; then
  echo "HYGIENE_CHECK_FAILED:"
  echo "$hygiene_hits"
  exit 1
fi
echo "HYGIENE_CHECK_PASSED (0 forbidden constructs)"

echo "=== 2. LAKE BUILD ==="
lake exe cache get || true
lake build LogarithmicRigidity LogarithmicRigidityConditional Solution

echo "=== 3. AXIOM AUDITS ==="
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake env lean LogarithmicRigidityConditional/AuditConditionalAxioms.lean

echo "=== 4. COMPARATOR VERIFICATION ==="
lake comparator --paranoid
