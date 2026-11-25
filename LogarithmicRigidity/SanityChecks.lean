/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries

/-!
# Small-Case Sanity Checks
-/

namespace LogarithmicRigidity

example : Hnodal 1 = 0 := by rfl
example : Hnodal 2 = 1 := by rfl
example : Hnodal 3 = 1 := by rfl
example : Hnodal 4 = 4 := by rfl
example : hBound 0 = 0 := by rfl
example : hBound 1 = 0 := by rfl
example : hBound 2 = 1 := by rfl
example : hBound 3 = 1 := by rfl
example : hBound 4 = 4 := by rfl
example : rNonZeroBound 1 = 0 := by rfl
example : rNonZeroBound 2 = 1 := by rfl
example : rNonZeroBound 3 = 2 := by rfl
example : rNonZeroBound 4 = 5 := by rfl

end LogarithmicRigidity
