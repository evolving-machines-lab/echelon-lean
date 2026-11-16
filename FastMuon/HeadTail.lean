import Mathlib

/-!
# The head–tail direction is a certified oracle

For a momentum matrix `X : s × l`, the head–tail oracle keeps an orthonormal frame `U : s × r`
(`Uᵀ U = 1`, a warm-started estimate of the top-`r` left singular subspace) and returns

  `O = U P + τ⁻¹ • T`,   `T = X - U (Uᵀ X)`   (the tail, outside the span of `U`),

where `P` is the polar factor of the small `r × l` matrix `H = Uᵀ X` and `τ ≈ ‖T‖₂`.
Everything costs `O(s l r)` instead of Newton–Schulz's `O(s² l)`.

We prove, for the spectral norm `‖·‖` (Mathlib's `L2` operator norm) and the Frobenius pairing:

* `tail_perp`: `Uᵀ T = 0` (the tail is orthogonal to the head),
* `gram_split`: `Oᵀ O = Pᵀ P + τ⁻² Tᵀ T` — no cross terms, **whatever `U` is**, as long as it is orthonormal,
* `htDir_norm_sq_le` / `htDir_norm_le_sqrt_two`: `‖O‖² ≤ ‖P‖² + ‖T‖²/τ²`, hence `‖O‖ ≤ √2` when
  `‖P‖ ≤ 1` and `τ ≥ ‖T‖` (the `β` of the certificate),
* `head_isometry`: `‖U P‖ = ‖P‖`,
* `align`: `⟪X, O⟫ = ⟪Uᵀ X, P⟫ + ‖T‖_F² / τ`, so `O` is always a descent direction (`align_nonneg`).

The remaining certificate constant `α` (how much of the nuclear norm `⟪X, O⟫` captures) depends on the
spectrum of `X` and on how well `U` tracks the top-`r` subspace; we measure it, we do not prove it.
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

/-- Frobenius pairing `⟪A, B⟫ = tr (Aᵀ B)`. -/
def frob (A B : Matrix s l ℝ) : ℝ := (Aᵀ * B).trace

theorem tail_perp {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (X : Matrix s l ℝ) :
    Uᵀ * tail U X = 0 := by
  simp [tail, Matrix.mul_sub, ← Matrix.mul_assoc, hU]

theorem tail_perp' {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (X : Matrix s l ℝ) :
    (tail U X)ᵀ * U = 0 := by
  have h := congrArg transpose (tail_perp hU X)
  simpa [transpose_mul] using h

/-- **No cross terms.** `Oᵀ O = Pᵀ P + τ⁻² Tᵀ T` for any orthonormal frame `U`. -/
theorem gram_split {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (P : Matrix r l ℝ) (τ : ℝ)
    (X : Matrix s l ℝ) :
    (htDir U P τ X)ᵀ * htDir U P τ X = Pᵀ * P + (τ⁻¹ * τ⁻¹) • ((tail U X)ᵀ * tail U X) := by
  set T := tail U X with hT
  have h1 : Uᵀ * T = 0 := tail_perp hU X
  have h2 : Tᵀ * U = 0 := tail_perp' hU X
  have expand : (htDir U P τ X)ᵀ * htDir U P τ X =
      Pᵀ * (Uᵀ * U) * P + τ⁻¹ • (Pᵀ * (Uᵀ * T)) + τ⁻¹ • (Tᵀ * U * P) +
        (τ⁻¹ * τ⁻¹) • (Tᵀ * T) := by
    simp only [htDir, ← hT, transpose_add, transpose_smul, transpose_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    abel
  rw [expand, hU, h1, h2]
  simp

/-- The head part is an isometric embedding of `P`: `‖U P‖ = ‖P‖`. -/
theorem head_isometry {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (P : Matrix r l ℝ) :
    ‖U * P‖ = ‖P‖ := by
  have h : ‖U * P‖ * ‖U * P‖ = ‖P‖ * ‖P‖ := by
    rw [← l2_opNorm_conjTranspose_mul_self, ← l2_opNorm_conjTranspose_mul_self,
      conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial,
      transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  have h0 : 0 ≤ ‖U * P‖ := norm_nonneg _
  have h0' : 0 ≤ ‖P‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U * P‖ - ‖P‖), sq_nonneg (‖U * P‖ + ‖P‖)]

/-- **Spectral-norm bound (`β`).** `‖O‖² ≤ ‖P‖² + ‖T‖² / τ²`. -/
theorem htDir_norm_sq_le {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (P : Matrix r l ℝ) (τ : ℝ)
    (X : Matrix s l ℝ) :
    ‖htDir U P τ X‖ * ‖htDir U P τ X‖ ≤
      ‖P‖ * ‖P‖ + (τ⁻¹ * τ⁻¹) * (‖tail U X‖ * ‖tail U X‖) := by
  rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial,
    gram_split hU P τ X]
  calc ‖Pᵀ * P + (τ⁻¹ * τ⁻¹) • ((tail U X)ᵀ * tail U X)‖
      ≤ ‖Pᵀ * P‖ + ‖(τ⁻¹ * τ⁻¹) • ((tail U X)ᵀ * tail U X)‖ := norm_add_le _ _
    _ = ‖P‖ * ‖P‖ + (τ⁻¹ * τ⁻¹) * (‖tail U X‖ * ‖tail U X‖) := by
      rw [norm_smul, ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self,
        ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self,
        Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg τ⁻¹)]

/-- **`β ≤ √2`.** If the head factor is a contraction (`‖P‖ ≤ 1`, true for an exact or clamped polar
factor) and the tail scale dominates the tail (`‖T‖ ≤ τ`), then `‖O‖ ≤ √2`. -/
theorem htDir_norm_le_sqrt_two {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) {P : Matrix r l ℝ} {τ : ℝ}
    {X : Matrix s l ℝ} (hP : ‖P‖ ≤ 1) (hτ : 0 < τ) (hT : ‖tail U X‖ ≤ τ) :
    ‖htDir U P τ X‖ ≤ Real.sqrt 2 := by
  have h := htDir_norm_sq_le hU P τ X
  have hP2 : ‖P‖ * ‖P‖ ≤ 1 := by nlinarith [norm_nonneg P]
  have hT2 : (τ⁻¹ * τ⁻¹) * (‖tail U X‖ * ‖tail U X‖) ≤ 1 := by
    have hq : τ⁻¹ * ‖tail U X‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hτ]; linarith
    have hq0 : 0 ≤ τ⁻¹ * ‖tail U X‖ := mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _)
    nlinarith
  have hsq : ‖htDir U P τ X‖ ^ 2 ≤ 2 := by nlinarith
  calc ‖htDir U P τ X‖ = Real.sqrt (‖htDir U P τ X‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hsq

/-- `⟪X, T⟫ = ‖T‖_F²`: the tail is the orthogonal projection of `X`. -/
theorem frob_tail {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (X : Matrix s l ℝ) :
    frob X (tail U X) = frob (tail U X) (tail U X) := by
  have h2 : (tail U X)ᵀ * U = 0 := tail_perp' hU X
  unfold frob
  congr 1
  conv_rhs => rw [show (tail U X)ᵀ = Xᵀ - (Uᵀ * X)ᵀ * Uᵀ by
    simp [tail, transpose_sub, transpose_mul]]
  rw [Matrix.sub_mul, Matrix.mul_assoc, tail_perp hU X, Matrix.mul_zero, sub_zero]

/-- **Alignment identity.** `⟪X, O⟫ = ⟪Uᵀ X, P⟫ + ‖T‖_F² / τ`. -/
theorem align {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (P : Matrix r l ℝ) (τ : ℝ)
    (X : Matrix s l ℝ) :
    frob X (htDir U P τ X) = frob (Uᵀ * X) P + τ⁻¹ * frob (tail U X) (tail U X) := by
  have hT := frob_tail hU X
  unfold frob at *
  simp only [htDir, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul]
  rw [hT, transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem frob_self_nonneg (A : Matrix s l ℝ) : 0 ≤ frob A A := by
  unfold frob
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mul_self_nonneg (A i j)

/-- **Always a descent direction.** If the head factor is aligned with the head (`⟪H, P⟫ ≥ 0`, true for
any polar factor of `H`) and `τ > 0`, then `⟪X, O⟫ ≥ ‖T‖_F²/τ ≥ 0`. -/
theorem align_nonneg {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) {P : Matrix r l ℝ} {τ : ℝ}
    {X : Matrix s l ℝ} (hP : 0 ≤ frob (Uᵀ * X) P) (hτ : 0 < τ) :
    τ⁻¹ * frob (tail U X) (tail U X) ≤ frob X (htDir U P τ X) ∧ 0 ≤ frob X (htDir U P τ X) := by
  rw [align hU P τ X]
  have h0 : 0 ≤ τ⁻¹ * frob (tail U X) (tail U X) :=
    mul_nonneg (inv_nonneg.mpr hτ.le) (frob_self_nonneg _)
  constructor <;> linarith

/-- Muon is the full-rank member of the family: with a square orthogonal frame the tail vanishes and
`O = U P`. -/
theorem full_rank_tail_zero {U : Matrix s s ℝ} (hU' : U * Uᵀ = 1) (X : Matrix s l ℝ) :
    tail U X = 0 := by
  simp [tail, ← Matrix.mul_assoc, hU']

end FastMuon.HeadTail
