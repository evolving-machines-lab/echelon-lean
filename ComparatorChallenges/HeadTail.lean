import Mathlib

/-!
# Comparator challenge: `FastMuon.HeadTail.htDir_norm_le_sqrt_two` (`FastMuon/HeadTail.lean`)

Imports only Mathlib.  `tail` and `htDir` are copied verbatim from `FastMuon/HeadTail.lean`.
The norm is Mathlib's spectral norm (`L2` operator norm, `open scoped Matrix.Norms.L2Operator`).
-/

set_option linter.unusedSectionVars false

namespace FastMuon.HeadTail

open Matrix
open scoped Matrix.Norms.L2Operator

variable {s l r : Type*} [Fintype s] [Fintype l] [Fintype r]
  [DecidableEq s] [DecidableEq l] [DecidableEq r]

/-- The tail of `X` outside the column span of `U`. -/
def tail (U : Matrix s r ℝ) (X : Matrix s l ℝ) : Matrix s l ℝ := X - U * (Uᵀ * X)

/-- The head–tail direction `U P + τ⁻¹ • tail U X`. -/
noncomputable def htDir (U : Matrix s r ℝ) (P : Matrix r l ℝ) (τ : ℝ) (X : Matrix s l ℝ) :
    Matrix s l ℝ :=
  U * P + τ⁻¹ • tail U X

/-- **`β ≤ √2`.** If `Uᵀ U = 1`, `‖P‖ ≤ 1` and `‖T‖ ≤ τ`, then `‖O‖ ≤ √2`. -/
theorem htDir_norm_le_sqrt_two {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) {P : Matrix r l ℝ} {τ : ℝ}
    {X : Matrix s l ℝ} (hP : ‖P‖ ≤ 1) (hτ : 0 < τ) (hT : ‖tail U X‖ ≤ τ) :
    ‖htDir U P τ X‖ ≤ Real.sqrt 2 := by
  sorry

end FastMuon.HeadTail
