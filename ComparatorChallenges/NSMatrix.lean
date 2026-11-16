import Mathlib

/-!
# Comparator challenge: `FastMuon.NSMatrix.muon_norm_le` (`FastMuon/NSMatrix.lean`)

Imports only Mathlib.  `MatrixFacts.frobNorm` and `NSMatrix.nsStep` are copied verbatim from
`FastMuon/MatrixFacts.lean` and `FastMuon/NSMatrix.lean`.  `‖·‖` is Mathlib's spectral norm
(`L2` operator norm).
-/

set_option linter.unusedSectionVars false

namespace FastMuon.MatrixFacts

open Matrix Polynomial

section Frobenius

open scoped Matrix.Norms.Frobenius

variable {s l : Type*} [Fintype s] [Fintype l]

/-- The Frobenius norm `‖M‖_F = √(∑ᵢⱼ Mᵢⱼ²)`, written out explicitly. -/
noncomputable def frobNorm (M : Matrix s l ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

end Frobenius

end FastMuon.MatrixFacts

namespace FastMuon.NSMatrix

open Matrix Polynomial FastMuon.MatrixFacts
open scoped Matrix.Norms.L2Operator

variable {s l : Type*} [Fintype s] [Fintype l] [DecidableEq s] [DecidableEq l]

/-- One step of Muon's Newton–Schulz iteration. -/
noncomputable def nsStep (X : Matrix s l ℝ) : Matrix s l ℝ :=
  (3.4445 : ℝ) • X + (-4.7750 : ℝ) • (X * Xᵀ * X) + (2.0315 : ℝ) • (X * Xᵀ * X * Xᵀ * X)

/-- **Muon's output has spectral norm at most `1.25`.**  For every real `M`, five Newton–Schulz
steps applied to `X₀ = M / ‖M‖_F` give `‖nsStep^[5] X₀‖₂ ≤ 1.25`. -/
theorem muon_norm_le (M : Matrix s l ℝ) : ‖nsStep^[5] ((1 / frobNorm M) • M)‖ ≤ 1.25 := by
  sorry

end FastMuon.NSMatrix
