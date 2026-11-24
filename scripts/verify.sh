#!/usr/bin/env bash
set -euo pipefail
lake exe cache get || true
lake build LogarithmicRigidity Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake comparator --paranoid
