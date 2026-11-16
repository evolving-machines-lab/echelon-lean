import FastMuon.MuonVsSVD

/-!
# Separation: neither Muon nor the cheap head–tail oracle dominates

The certificate quality of a direction `O` for a matrix `M` is `κ = ⟨M, O⟩ / (‖M‖_* ‖O‖₂)`
(the rate in `Certificate.lean` degrades by `1/κ`; the exact polar factor has `κ = 1`).
For a spectral map `σ ↦ φ(σ)` (any odd matrix polynomial, the exact polar factor, or head–tail with an
exact subspace), `⟨M, O⟩ = Σ σᵢ φ(σᵢ)`, `‖M‖_* = Σ σᵢ`, `‖O‖₂ = maxᵢ φ(σᵢ)` — standard spectral calculus,
which we take as the bridge and do not re-prove here.

**Spiked spectrum** (one singular value `1`, `4095` equal to `ε = 4·10⁻⁴`, i.e. a 4096 × 4096 matrix):

* Muon's five Frobenius-normalised Newton–Schulz steps give `κ ≤ 0.57` (`ns5_spiked_kappa`; numerically 0.551);
* rank-1 head–tail with tail scale `τ = ε` gives `κ = 1` (`ht_spiked_kappa`), at `O(mn)` cost
  instead of `O(mn²)`.

So "Newton–Schulz is the gold standard and cheaper methods can only lose" is false; on the power-law
spectra we measured in training the comparison goes the other way at small rank, so neither dominates.
-/

namespace FastMuon.Separation

open FastMuon.NSPoly FastMuon.MuonVsSVD

/-- On `[0, 1.25]` the quintic is below its linear part: `p x ≤ 3.4445 x`. -/
theorem nsP_le_lin {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) : nsP x ≤ 3.4445 * x := by
  unfold nsP
  have hx2 : x ^ 2 ≤ 1.5625 := by nlinarith
  nlinarith [mul_nonneg (pow_nonneg hx 3) (by nlinarith : (0:ℝ) ≤ 4.7750 - 2.0315 * x ^ 2)]

/-- Small singular values grow at most geometrically: `p^[k] x ≤ 3.4445^k x`. -/
theorem iter_le_lin (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1.25) :
    nsP^[k] x ≤ 3.4445 ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h0, h1⟩ := nsP_iter_mem k hx hx1
    calc nsP (nsP^[k] x) ≤ 3.4445 * nsP^[k] x := nsP_le_lin h0 h1
      _ ≤ 3.4445 * (3.4445 ^ k * x) := by linarith
      _ = 3.4445 ^ (k + 1) * x := by ring

lemma step0 {x : ℝ} (h0 : 0.99 ≤ x) (h1 : x ≤ 1) : 0.69 ≤ nsP x ∧ nsP x ≤ 0.73 := by
  unfold nsP
  have a := sub_nonneg.mpr h0; have b := sub_nonneg.mpr h1
  constructor <;> nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg a b) a, mul_nonneg (mul_nonneg a b) b,
    mul_nonneg (mul_nonneg a a) a, mul_nonneg (mul_nonneg b b) b, sq_nonneg (x - 1)]

/-- The top singular value, normalised by a Frobenius norm within 1% of it, ends in `[0.65, 0.90]`. -/
theorem five_steps_near_one {x : ℝ} (h0 : 0.99 ≤ x) (h1 : x ≤ 1) :
    0.65 ≤ nsP^[5] x ∧ nsP^[5] x ≤ 0.90 := by
  have h := step0 h0 h1
  have hA := stepA h.1 h.2
  have hB := stepB hA.1 hA.2
  have hC := stepC hB.1 hB.2
  have hD := stepD hC.1 hC.2
  simpa [Function.iterate_succ_apply'] using hD

/-- **Muon on a spiked spectrum.** `F` is the Frobenius norm `√(1 + 4095 ε²)`, `ε = 4·10⁻⁴`
(any `1 ≤ F ≤ 1/0.99` works). With `y = p^[5](1/F)`, `z = p^[5](ε/F)` the singular values Muon outputs,
the certificate quality is at most `0.57`. -/
theorem ns5_spiked_kappa (F : ℝ) (hF1 : 1 ≤ F) (hF2 : F ≤ 1 / 0.99) :
    (nsP^[5] (1 / F) + 4095 * 4e-4 * nsP^[5] (4e-4 / F)) /
        ((1 + 4095 * 4e-4) * max (nsP^[5] (1 / F)) (nsP^[5] (4e-4 / F))) ≤ 0.57 := by
  have hFpos : 0 < F := by linarith
  have hx0 : (0.99 : ℝ) ≤ 1 / F := by
    rw [le_div_iff₀ hFpos]
    have h := mul_le_mul_of_nonneg_left hF2 (by norm_num : (0:ℝ) ≤ 0.99)
    have e : (0.99 : ℝ) * (1 / 0.99) = 1 := by norm_num
    linarith
  have hx1 : 1 / F ≤ 1 := by rw [div_le_one hFpos]; exact hF1
  obtain ⟨hy0, hy1⟩ := five_steps_near_one hx0 hx1
  have he0 : (0 : ℝ) ≤ 4e-4 / F := by positivity
  have he1 : 4e-4 / F ≤ 4e-4 := by
    rw [div_le_iff₀ hFpos]; nlinarith
  have hz0 := (nsP_iter_mem 5 he0 (by linarith)).1
  have hz1 : nsP^[5] (4e-4 / F) ≤ 3.4445 ^ 5 * 4e-4 :=
    (iter_le_lin 5 he0 (by linarith)).trans (mul_le_mul_of_nonneg_left he1 (by positivity))
  set y := nsP^[5] (1 / F)
  set z := nsP^[5] (4e-4 / F)
  have hmax : y ≤ max y z := le_max_left _ _
  have hden : 0 < (1 + 4095 * 4e-4) * max y z := by
    have : (0:ℝ) < max y z := lt_of_lt_of_le (by linarith) hmax
    positivity
  rw [div_le_iff₀ hden]
  have hzsmall : z ≤ 0.19396 := by
    have : (3.4445 : ℝ) ^ 5 * 4e-4 ≤ 0.19396 := by norm_num
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ) ≤ 0.57 * (1 + 4095 * 4e-4))]

/-- **Rank-1 head–tail on the same spectrum.** With the exact top singular direction and `τ = ε`, the
spectral map is `φ(1) = 1`, `φ(ε) = ε/τ = 1`, so `κ = 1` — at `O(mn)` cost. -/
theorem ht_spiked_kappa :
    (1 * (1 : ℝ) + 4095 * 4e-4 * ((4e-4 : ℝ) / 4e-4)) /
      ((1 + 4095 * 4e-4) * max (1 : ℝ) ((4e-4 : ℝ) / 4e-4)) = 1 := by
  norm_num

end FastMuon.Separation
