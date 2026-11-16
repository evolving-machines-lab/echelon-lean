import FastMuon.NSPoly
import FastMuon.MatrixFacts

/-!
# Muon's Newton–Schulz quintic at the matrix level

`NSPoly.lean` proves that the scalar quintic `nsP x = a x + b x³ + c x⁵`,
`(a, b, c) = (3.4445, -4.7750, 2.0315)`, maps `[0, 1.25]` into itself, and appeals to spectral
calculus for the matrix statement.  Here we prove the matrix statement directly, for the spectral
norm `‖·‖` (Mathlib's `L2` operator norm) on real `s × l` matrices:

* `nsStep X = a • X + b • (X Xᵀ X) + c • (X Xᵀ X Xᵀ X)` is one Newton–Schulz step;
* `nsStep_eq`: `nsStep X = X q(XᵀX)` with `q(λ) = a + bλ + cλ²`;
* `nsStep_gram`: `(nsStep X)ᵀ (nsStep X) = g(XᵀX)` with `g(λ) = λ q(λ)²`;
* `nsG_eval_eq`: `g(λ) = nsP(√λ)²` for `λ ≥ 0`;
* `nsStep_norm_le`: `‖X‖ ≤ 1.25 → ‖nsStep X‖ ≤ 1.25`;
* `nsStep_iterate_norm_le`: the same for every iterate;
* `muon_norm_le`: Muon's output `nsStep^[5] (M / ‖M‖_F)` has spectral norm `≤ 1.25` for every real
  `M` (using `‖M‖₂ ≤ ‖M‖_F`).

The matrix step uses only `MatrixFacts.norm_aeval_le_of_posSemidef` (polynomial norm bound for a
PSD matrix, via Mathlib's isometric continuous functional calculus on real matrices), so the scalar
bound `NSPoly.nsP_mem` now transfers to matrices with no unformalized step.
-/

set_option linter.unusedSectionVars false

namespace FastMuon.NSMatrix

open Matrix Polynomial FastMuon.NSPoly FastMuon.MatrixFacts
open scoped Matrix.Norms.L2Operator

variable {s l : Type*} [Fintype s] [Fintype l] [DecidableEq s] [DecidableEq l]

/-- One step of Muon's Newton–Schulz iteration. -/
noncomputable def nsStep (X : Matrix s l ℝ) : Matrix s l ℝ :=
  (3.4445 : ℝ) • X + (-4.7750 : ℝ) • (X * Xᵀ * X) + (2.0315 : ℝ) • (X * Xᵀ * X * Xᵀ * X)

/-- `q(λ) = a + bλ + cλ²`, so that `nsStep X = X q(XᵀX)`. -/
noncomputable def nsQ : ℝ[X] := C 3.4445 + C (-4.7750) * X + C 2.0315 * X ^ 2

/-- `g(λ) = λ q(λ)²`, so that `(nsStep X)ᵀ (nsStep X) = g(XᵀX)`. -/
noncomputable def nsG : ℝ[X] := X * nsQ ^ 2

theorem nsQ_eval (x : ℝ) : nsQ.eval x = 3.4445 + -4.7750 * x + 2.0315 * x ^ 2 := by
  simp [nsQ]

theorem nsG_eval (x : ℝ) : nsG.eval x = x * (3.4445 + -4.7750 * x + 2.0315 * x ^ 2) ^ 2 := by
  simp [nsG, nsQ]

/-- `g(λ) = nsP(√λ)²` for `λ ≥ 0`. -/
theorem nsG_eval_eq {x : ℝ} (hx : 0 ≤ x) : nsG.eval x = nsP (Real.sqrt x) ^ 2 := by
  rw [nsG_eval, nsP]
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have h3 : Real.sqrt x ^ 3 = Real.sqrt x * x := by rw [pow_succ, hs, mul_comm]
  have h5 : Real.sqrt x ^ 5 = Real.sqrt x * x ^ 2 := by
    rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hs, mul_comm]
  rw [h3, h5]
  have : (3.4445 * Real.sqrt x - 4.7750 * (Real.sqrt x * x) + 2.0315 * (Real.sqrt x * x ^ 2)) =
      Real.sqrt x * (3.4445 + -4.7750 * x + 2.0315 * x ^ 2) := by ring
  rw [this, mul_pow, hs]

/-- On `[0, 1.25²]`, `0 ≤ g ≤ 1.25²` (from the scalar bound `nsP_mem`). -/
theorem nsG_eval_mem {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.5625) :
    0 ≤ nsG.eval x ∧ nsG.eval x ≤ 1.5625 := by
  rw [nsG_eval_eq hx]
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hy1 : Real.sqrt x ≤ 1.25 := by
    calc Real.sqrt x ≤ Real.sqrt (1.25 ^ 2) := Real.sqrt_le_sqrt (by norm_num; linarith)
      _ = 1.25 := Real.sqrt_sq (by norm_num)
  obtain ⟨h0, h1⟩ := nsP_mem hy0 hy1
  exact ⟨sq_nonneg _, by nlinarith⟩

theorem nsStep_eq (X : Matrix s l ℝ) : nsStep X = X * aeval (Xᵀ * X) nsQ := by
  simp only [nsStep, nsQ, map_add, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, pow_two, Matrix.mul_assoc]

theorem aeval_nsQ_transpose (X : Matrix s l ℝ) :
    (aeval (Xᵀ * X) nsQ)ᵀ = aeval (Xᵀ * X) nsQ := by
  simp [nsQ, Algebra.algebraMap_eq_smul_one, transpose_add, transpose_smul, transpose_pow,
    transpose_mul]

/-- **Gram identity.** `(nsStep X)ᵀ (nsStep X) = g(XᵀX)`. -/
theorem nsStep_gram (X : Matrix s l ℝ) : (nsStep X)ᵀ * nsStep X = aeval (Xᵀ * X) nsG := by
  set A := Xᵀ * X with hA
  set Q := aeval A nsQ with hQ
  have hcomm : Commute A Q := by
    simpa only [aeval_X] using (Commute.all (Polynomial.X : ℝ[X]) nsQ).map (aeval A)
  have hQt : Qᵀ = Q := aeval_nsQ_transpose X
  rw [nsStep_eq, transpose_mul, hQt, nsG, map_mul, map_pow, aeval_X, ← hQ]
  calc Q * Xᵀ * (X * Q) = Q * A * Q := by simp only [hA, Matrix.mul_assoc]
    _ = A * Q * Q := by rw [hcomm.eq]
    _ = A * Q ^ 2 := by rw [pow_two, Matrix.mul_assoc]

/-- **One Newton–Schulz step keeps the spectral norm at most `1.25`.** -/
theorem nsStep_norm_le {X : Matrix s l ℝ} (hX : ‖X‖ ≤ 1.25) : ‖nsStep X‖ ≤ 1.25 := by
  have hpsd : (Xᵀ * X).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self X
  have hAn : ‖Xᵀ * X‖ = ‖X‖ * ‖X‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self]
  have hA : ‖Xᵀ * X‖ ≤ 1.5625 := by rw [hAn]; nlinarith [norm_nonneg X]
  have hG : ‖aeval (Xᵀ * X) nsG‖ ≤ 1.5625 :=
    norm_aeval_le_of_posSemidef hpsd nsG (by norm_num) fun x hx0 hx1 => by
      obtain ⟨h0, h1⟩ := nsG_eval_mem hx0 (hx1.trans hA)
      rw [abs_le]; constructor <;> linarith
  have hN : ‖nsStep X‖ * ‖nsStep X‖ ≤ 1.5625 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial, nsStep_gram]
    exact hG
  nlinarith [norm_nonneg (nsStep X)]

/-- **Every Newton–Schulz iterate keeps the spectral norm at most `1.25`.** -/
theorem nsStep_iterate_norm_le (k : ℕ) {X : Matrix s l ℝ} (hX : ‖X‖ ≤ 1.25) :
    ‖nsStep^[k] X‖ ≤ 1.25 := by
  induction k with
  | zero => simpa using hX
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nsStep_norm_le ih

/-- Muon's normalisation `X₀ = M / ‖M‖_F` is a spectral contraction (`‖M‖₂ ≤ ‖M‖_F`). -/
theorem muon_init_norm_le_one (M : Matrix s l ℝ) : ‖(1 / frobNorm M) • M‖ ≤ 1 := by
  have hF := frobNorm_nonneg M
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr hF)]
  rcases hF.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [one_div, inv_mul_le_iff₀ h, mul_one]
    exact l2_opNorm_le_frobNorm M

/-- **Muon's output has spectral norm at most `1.25`.**  For every real `M`, five Newton–Schulz
steps applied to `X₀ = M / ‖M‖_F` give `‖nsStep^[5] X₀‖₂ ≤ 1.25`.  (No `M ≠ 0` hypothesis is needed:
for `M = 0`, `X₀ = 0`.) -/
theorem muon_norm_le (M : Matrix s l ℝ) : ‖nsStep^[5] ((1 / frobNorm M) • M)‖ ≤ 1.25 :=
  nsStep_iterate_norm_le 5 ((muon_init_norm_le_one M).trans (by norm_num))

/-- The same, for any number of steps. -/
theorem muon_iterate_norm_le (k : ℕ) (M : Matrix s l ℝ) :
    ‖nsStep^[k] ((1 / frobNorm M) • M)‖ ≤ 1.25 :=
  nsStep_iterate_norm_le k ((muon_init_norm_le_one M).trans (by norm_num))

end FastMuon.NSMatrix

