import Mathlib

/-!
# Matrix facts for the matrix-level Newton–Schulz bound

All norms are Mathlib's spectral norm (`L2` operator norm, `open scoped Matrix.Norms.L2Operator`)
unless stated otherwise.

* `spectrum_mem_Icc_of_posSemidef`: the spectrum of a real PSD matrix lies in `[0, ‖A‖]`;
* `norm_aeval_le` (**polynomial norm bound for symmetric matrices**): for a real symmetric `A` and
  a real polynomial `p`, `‖p(A)‖ ≤ M` as soon as `|p| ≤ M` on the spectrum of `A`.  This goes through
  Mathlib's isometric continuous functional calculus on `Matrix n n ℝ`
  (`Matrix.instIsometricContinuousFunctionalCalculus`, `cfc_polynomial`, `norm_cfc_le`);
* `norm_aeval_le_of_posSemidef`: the same with the spectrum replaced by the interval `[0, ‖A‖]`;
* `psd_norm_le_trace`: `‖A‖ ≤ tr A` for real PSD `A`;
* `frobNorm`, `frobNorm_eq_frobenius_norm` (it is Mathlib's Frobenius norm) and
  `l2_opNorm_le_frobNorm`: `‖M‖₂ ≤ ‖M‖_F`.

## Provenance

`psd_norm_le_trace` is copied, with whitespace and naming adapted to Mathlib v4.35.0, from
`OAI/Probability/LogConcave/TensorGraphs/Vertex.lean` (namespace
`OAI.LogConcaveSampling.TraceMoment`, lemma `psd_norm_le_trace`) in OpenAI's Lean repository
(https://github.com/openai/math, directory `lean/`), which is licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0).  Changes: the proof was re-indented and stated in this
file's namespace; no mathematical change.  Everything else in this file is original.
-/

set_option linter.unusedSectionVars false

namespace FastMuon.MatrixFacts

open Matrix Polynomial

section Frobenius

open scoped Matrix.Norms.Frobenius

variable {s l : Type*} [Fintype s] [Fintype l]

/-- The Frobenius norm `‖M‖_F = √(∑ᵢⱼ Mᵢⱼ²)`, written out explicitly. -/
noncomputable def frobNorm (M : Matrix s l ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- `frobNorm` is Mathlib's Frobenius norm (`open scoped Matrix.Norms.Frobenius`). -/
theorem frobNorm_eq_frobenius_norm (M : Matrix s l ℝ) : frobNorm M = ‖M‖ := by
  rw [frobenius_norm_def, frobNorm, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

end Frobenius

open scoped Matrix.Norms.L2Operator

variable {n s l : Type*} [Fintype n] [DecidableEq n] [Fintype s] [Fintype l]
  [DecidableEq s] [DecidableEq l]

theorem norm_one_le : ‖(1 : Matrix n n ℝ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix n n ℝ)
  rw [conjTranspose_one, Matrix.one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix n n ℝ)]

/-- The spectrum of a real positive semidefinite matrix lies in `[0, ‖A‖]`. -/
theorem spectrum_mem_Icc_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) {x : ℝ}
    (hx : x ∈ spectrum ℝ A) : 0 ≤ x ∧ x ≤ ‖A‖ := by
  refine ⟨?_, ?_⟩
  · rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA.eigenvalues_nonneg i
  · have h := spectrum.norm_le_norm_mul_of_mem hx
    rw [Real.norm_eq_abs] at h
    calc x ≤ |x| := le_abs_self x
      _ ≤ ‖A‖ * ‖(1 : Matrix n n ℝ)‖ := h
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left norm_one_le (norm_nonneg _)
      _ = ‖A‖ := mul_one _

/-- **Polynomial norm bound for real symmetric matrices.** If `|p(x)| ≤ M` for every `x` in the
spectrum of the symmetric matrix `A`, then `‖p(A)‖ ≤ M`. -/
theorem norm_aeval_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X]) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ spectrum ℝ A, |p.eval x| ≤ M) : ‖aeval A p‖ ≤ M := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  exact norm_cfc_le hM fun x hx => by simpa only [Real.norm_eq_abs] using h x hx

/-- **Polynomial norm bound for real PSD matrices.** If `|p(x)| ≤ M` on `[0, ‖A‖]`, then
`‖p(A)‖ ≤ M`. -/
theorem norm_aeval_le_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) (p : ℝ[X]) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x : ℝ, 0 ≤ x → x ≤ ‖A‖ → |p.eval x| ≤ M) : ‖aeval A p‖ ≤ M :=
  norm_aeval_le hA.1 p hM fun x hx =>
    h x (spectrum_mem_Icc_of_posSemidef hA hx).1 (spectrum_mem_Icc_of_posSemidef hA hx).2

/-- `‖A‖ ≤ tr A` for a real PSD matrix.  Copied from OpenAI's Lean repository
(`OAI/Probability/LogConcave/TensorGraphs/Vertex.lean`, Apache-2.0); see the module docstring. -/
theorem psd_norm_le_trace {A : Matrix n n ℝ} (hA : A.PosSemidef) : ‖A‖ ≤ A.trace := by
  have hn : 0 ≤ ∑ i, hA.1.eigenvalues i := Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i)
  rw [hA.1.trace_eq_sum_eigenvalues]
  conv_lhs => rw [hA.1.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (hA.eigenvalues_nonneg i)] using
    (Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i))

/-- `tr (Mᵀ M) = ∑ᵢⱼ Mᵢⱼ²`. -/
theorem trace_transpose_mul_self (M : Matrix s l ℝ) :
    (Mᵀ * M).trace = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]
  simp [sq]

/-- **Spectral norm ≤ Frobenius norm**: `‖M‖₂ ≤ ‖M‖_F`. -/
theorem l2_opNorm_le_frobNorm (M : Matrix s l ℝ) : ‖M‖ ≤ frobNorm M := by
  have hpsd : (Mᵀ * M).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self M
  have h1 : ‖M‖ * ‖M‖ ≤ ∑ i, ∑ j, M i j ^ 2 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial,
      ← trace_transpose_mul_self]
    exact psd_norm_le_trace hpsd
  rw [frobNorm]
  calc ‖M‖ = Real.sqrt (‖M‖ * ‖M‖) := (Real.sqrt_mul_self (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := Real.sqrt_le_sqrt h1

theorem frobNorm_nonneg (M : Matrix s l ℝ) : 0 ≤ frobNorm M := Real.sqrt_nonneg _

end FastMuon.MatrixFacts
