import FastMuon.NSMatrix
import FastMuon.HeadTail

/-!
# One cubic polishing step after head–tail: `β ≤ 1`, certified

Head–tail gives a direction with `‖O‖₂ ≤ √2` (`HeadTail.htDir_norm_le_sqrt_two`).  One cubic
Newton–Schulz step `O' = (3/2) O - (1/2) O Oᵀ O` costs two products (`4 s² l` flops, a fifth of Muon's
five quintic steps) and, measured on real momentum, lifts the certificate quality above Muon's
(`κ`: 0.75 for Muon, 0.73 with one step after rank-16 head–tail, 0.81 with two, 0.91 with one after rank 64).

Here we prove the norm half of that certificate at the matrix level:

* `cubic_gram`: `O'ᵀ O' = g(OᵀO)` with `g(λ) = λ (3/2 - λ/2)²`;
* `one_sub_g`: `1 - g(λ) = (λ - 1)² (4 - λ) / 4`, so `0 ≤ g ≤ 1` on `[0, 4]`;
* `cubicStep_norm_le_one`: `‖O‖₂ ≤ 2 → ‖O'‖₂ ≤ 1`;
* `polished_ht_norm_le_one`: the polished head–tail direction has `‖O'‖₂ ≤ 1`, i.e. `β = 1`.
-/

set_option linter.unusedSectionVars false

namespace FastMuon.Polish

open Matrix Polynomial FastMuon.MatrixFacts FastMuon.HeadTail
open scoped Matrix.Norms.L2Operator

variable {s l r : Type*} [Fintype s] [Fintype l] [Fintype r]
  [DecidableEq s] [DecidableEq l] [DecidableEq r]

/-- One cubic Newton–Schulz step. -/
noncomputable def cubicStep (X : Matrix s l ℝ) : Matrix s l ℝ :=
  (1.5 : ℝ) • X + (-0.5 : ℝ) • (X * Xᵀ * X)

noncomputable def cQ : ℝ[X] := C 1.5 + C (-0.5) * X
noncomputable def cG : ℝ[X] := X * cQ ^ 2

theorem cG_eval (x : ℝ) : cG.eval x = x * (1.5 + -0.5 * x) ^ 2 := by
  simp [cG, cQ]

theorem one_sub_g (x : ℝ) : 1 - cG.eval x = (x - 1) ^ 2 * (4 - x) / 4 := by
  rw [cG_eval]; ring

theorem cG_eval_mem {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 4) : 0 ≤ cG.eval x ∧ cG.eval x ≤ 1 := by
  constructor
  · rw [cG_eval]; positivity
  · have h := one_sub_g x
    have : 0 ≤ (x - 1) ^ 2 * (4 - x) / 4 := by
      apply div_nonneg _ (by norm_num); exact mul_nonneg (sq_nonneg _) (by linarith)
    linarith

theorem cubicStep_eq (X : Matrix s l ℝ) : cubicStep X = X * aeval (Xᵀ * X) cQ := by
  simp only [cubicStep, cQ, map_add, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem aeval_cQ_transpose (X : Matrix s l ℝ) : (aeval (Xᵀ * X) cQ)ᵀ = aeval (Xᵀ * X) cQ := by
  simp [cQ, Algebra.algebraMap_eq_smul_one, transpose_add, transpose_smul, transpose_mul]

/-- **Gram identity.** `(cubicStep X)ᵀ (cubicStep X) = g(XᵀX)`. -/
theorem cubic_gram (X : Matrix s l ℝ) : (cubicStep X)ᵀ * cubicStep X = aeval (Xᵀ * X) cG := by
  set A := Xᵀ * X with hA
  set Q := aeval A cQ with hQ
  have hcomm : Commute A Q := by
    simpa only [aeval_X] using (Commute.all (Polynomial.X : ℝ[X]) cQ).map (aeval A)
  have hQt : Qᵀ = Q := aeval_cQ_transpose X
  rw [cubicStep_eq, transpose_mul, hQt, cG, map_mul, map_pow, aeval_X, ← hQ]
  calc Q * Xᵀ * (X * Q) = Q * A * Q := by simp only [hA, Matrix.mul_assoc]
    _ = A * Q * Q := by rw [hcomm.eq]
    _ = A * Q ^ 2 := by rw [pow_two, Matrix.mul_assoc]

/-- **One cubic step maps the spectral ball of radius 2 into the unit ball.** -/
theorem cubicStep_norm_le_one {X : Matrix s l ℝ} (hX : ‖X‖ ≤ 2) : ‖cubicStep X‖ ≤ 1 := by
  have hpsd : (Xᵀ * X).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self X
  have hAn : ‖Xᵀ * X‖ = ‖X‖ * ‖X‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose_mul_self]
  have hA : ‖Xᵀ * X‖ ≤ 4 := by rw [hAn]; nlinarith [norm_nonneg X]
  have hG : ‖aeval (Xᵀ * X) cG‖ ≤ 1 :=
    norm_aeval_le_of_posSemidef hpsd cG (by norm_num) fun x hx0 hx1 => by
      obtain ⟨h0, h1⟩ := cG_eval_mem hx0 (hx1.trans hA)
      rw [abs_le]; constructor <;> linarith
  have hN : ‖cubicStep X‖ * ‖cubicStep X‖ ≤ 1 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial, cubic_gram]
    exact hG
  nlinarith [norm_nonneg (cubicStep X)]

/-- **Polished head–tail is a contraction (`β = 1`).** Under the hypotheses of
`htDir_norm_le_sqrt_two` (orthonormal frame, contractive head factor, `τ ≥ ‖T‖₂`), one cubic step on
the head–tail direction gives spectral norm at most `1`. -/
theorem polished_ht_norm_le_one {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) {P : Matrix r l ℝ} {τ : ℝ}
    {X : Matrix s l ℝ} (hP : ‖P‖ ≤ 1) (hτ : 0 < τ) (hT : ‖tail U X‖ ≤ τ) :
    ‖cubicStep (htDir U P τ X)‖ ≤ 1 := by
  apply cubicStep_norm_le_one
  have h := htDir_norm_le_sqrt_two hU hP hτ hT
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := h4
  linarith

/-- **Robust version.** Polishing tolerates a tail-scale estimate that is off by up to `√3`: if
`‖T‖₂ ≤ √3 τ` (instead of `‖T‖₂ ≤ τ`), the head–tail direction still has `‖O‖₂ ≤ 2`, so one cubic step
still gives `‖O'‖₂ ≤ 1`.  A power-iteration estimate of `‖T‖₂` only has to be within a factor `1.73`. -/
theorem polished_ht_norm_le_one_robust {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) {P : Matrix r l ℝ}
    {τ : ℝ} {X : Matrix s l ℝ} (hP : ‖P‖ ≤ 1) (hτ : 0 < τ)
    (hT : ‖tail U X‖ ≤ Real.sqrt 3 * τ) :
    ‖cubicStep (htDir U P τ X)‖ ≤ 1 := by
  apply cubicStep_norm_le_one
  have h := htDir_norm_sq_le hU P τ X
  have hP2 : ‖P‖ * ‖P‖ ≤ 1 := by nlinarith [norm_nonneg P]
  have hq : τ⁻¹ * ‖tail U X‖ ≤ Real.sqrt 3 := by
    rw [inv_mul_le_iff₀ hτ]; linarith
  have hq0 : 0 ≤ τ⁻¹ * ‖tail U X‖ := mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hT2 : (τ⁻¹ * τ⁻¹) * (‖tail U X‖ * ‖tail U X‖) ≤ 3 := by
    have : (τ⁻¹ * ‖tail U X‖) * (τ⁻¹ * ‖tail U X‖) ≤ Real.sqrt 3 * Real.sqrt 3 :=
      mul_le_mul hq hq hq0 (Real.sqrt_nonneg 3)
    nlinarith
  nlinarith [norm_nonneg (htDir U P τ X)]

end FastMuon.Polish
