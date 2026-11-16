import Mathlib

/-!
# Error bound for Muon's own Newton–Schulz step (scalar / singular-value level)

Muon applies the odd quintic `p(x) = 3.4445 x - 4.7750 x³ + 2.0315 x⁵` five times to `X / ‖X‖_F`.
For an odd polynomial, `p(X) = U p(Σ) Vᵀ`; the matrix-level norm bound is proved in `NSMatrix.lean` (`muon_norm_le`), so the
singular values of the output are `p^[5]` of the normalised singular values `x ∈ [0, 1]`.
We prove the scalar facts:

* `[0, 1.25]` is invariant (`nsP_mem`): so Muon's output has spectral norm `β ≤ 1.25`;
* `nsP_iter_ge`: after `k` steps, `p^[k] x ≥ min(0.6, 3^k x)`.

So five steps map every normalised singular value `x ≥ 0.6/243 ≈ 0.0025` into `[0.6, 1.25]`:
Muon itself is an `(α, β)`-certified oracle with `β ≤ 1.25`, and `α ≥ 0.6` on the part of the spectrum
above `0.0025 ‖X‖_F` — it is *not* the exact polar factor, which is why `Certificate.lean` is stated
for general `(α, β)`.
-/

namespace FastMuon.NSPoly

/-- Muon's quintic. -/
noncomputable def nsP (x : ℝ) : ℝ := 3.4445 * x - 4.7750 * x ^ 3 + 2.0315 * x ^ 5

theorem nsP_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ nsP x := by
  unfold nsP
  have : 0 ≤ 3.4445 - 4.7750 * x ^ 2 + 2.0315 * x ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 1.1752)]
  nlinarith [mul_nonneg hx this]

theorem nsP_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) : nsP x ≤ 1.25 := by
  unfold nsP
  nlinarith [sq_nonneg (x - 0.5545), sq_nonneg (x ^ 2 - 0.3075),
    mul_nonneg hx (sq_nonneg (x ^ 2 - 0.3075)), mul_nonneg hx (sq_nonneg (x - 0.5545)),
    mul_nonneg (sub_nonneg.mpr hx1) hx,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1) hx) (sq_nonneg (x - 0.5545)),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1) hx) (sq_nonneg (x - 1.05))]

theorem nsP_mem {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) : 0 ≤ nsP x ∧ nsP x ≤ 1.25 :=
  ⟨nsP_nonneg hx, nsP_le hx hx1⟩

/-- Small singular values at least triple. -/
theorem nsP_ge_three {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 0.3) : 3 * x ≤ nsP x := by
  unfold nsP
  have hx2 : x ^ 2 ≤ 0.09 := by nlinarith
  have : 0 ≤ 0.4445 - 4.7750 * x ^ 2 + 2.0315 * x ^ 4 := by nlinarith [sq_nonneg (x ^ 2)]
  nlinarith [mul_nonneg hx this]

/-- Mid and large singular values land in `[0.6, 1.25]`. -/
theorem nsP_ge_band {x : ℝ} (hx : 0.3 ≤ x) (hx1 : x ≤ 1.25) : 0.6 ≤ nsP x := by
  unfold nsP
  nlinarith [sq_nonneg (x - 1.05), sq_nonneg (x ^ 2 - 1.1028),
    mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx1)) (sq_nonneg (x - 1.05)),
    mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x - 1.05)),
    mul_nonneg (sub_nonneg.mpr hx1) (sq_nonneg (x - 1.05)),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)) (sub_nonneg.mpr hx1)]

theorem nsP_iter_mem (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) :
    0 ≤ nsP^[k] x ∧ nsP^[k] x ≤ 1.25 := by
  induction k with
  | zero => exact ⟨hx, hx1⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nsP_mem ih.1 ih.2

/-- **NS error bound.** After `k` steps every normalised singular value `x ∈ [0, 1.25]` satisfies
`min(0.6, 3^k x) ≤ p^[k] x ≤ 1.25`. -/
theorem nsP_iter_ge (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) :
    min 0.6 (3 ^ k * x) ≤ nsP^[k] x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h0, h1⟩ := nsP_iter_mem k hx hx1
    by_cases hk : 0.3 ≤ nsP^[k] x
    · exact (min_le_left _ _).trans (nsP_ge_band hk h1)
    · rw [not_le] at hk
      have h3 := nsP_ge_three h0 hk.le
      have hmin : min 0.6 (3 ^ k * x) = 3 ^ k * x := by
        rcases min_cases (0.6 : ℝ) (3 ^ k * x) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h] at ih; linarith
        · exact h
      rw [hmin] at ih
      calc min 0.6 (3 ^ (k + 1) * x) ≤ 3 ^ (k + 1) * x := min_le_right _ _
        _ = 3 * (3 ^ k * x) := by ring
        _ ≤ 3 * nsP^[k] x := by linarith
        _ ≤ nsP (nsP^[k] x) := h3

/-- Muon's five steps: every normalised singular value `x ≥ 0.6/243` ends in `[0.6, 1.25]`. -/
theorem muon_five_steps {x : ℝ} (hx : 0.6 / 243 ≤ x) (hx1 : x ≤ 1.25) :
    0.6 ≤ nsP^[5] x ∧ nsP^[5] x ≤ 1.25 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  refine ⟨?_, (nsP_iter_mem 5 hx0 hx1).2⟩
  have h := nsP_iter_ge 5 hx0 hx1
  have : (0.6 : ℝ) ≤ 3 ^ 5 * x := by
    have : (3 : ℝ) ^ 5 = 243 := by norm_num
    rw [this]; linarith [show (0.6:ℝ) / 243 * 243 = 0.6 by norm_num, mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ) ≤ 243)]
  rwa [min_eq_left this] at h

end FastMuon.NSPoly
