import FastMuon.NSPoly
import FastMuon.Cost

/-!
# Checking three common claims about Muon's Newton–Schulz step

A popular write-up states three theorems about Muon's quintic `p(σ) = 3.4445σ - 4.7750σ³ + 2.0315σ⁵`
(left as `sorry` there).  Lean says:

1. "one step contracts the error `|p σ - 1| < |σ - 1|` on `[0.5, 1.5]`" — **false** (`claimed_contraction_false`):
   at `σ = 1` the error goes from `0` to `0.299`.
2. "five steps land within `0.05` of `1` on `[0.5, 1.5]`" — **false**, twice over:
   at `σ = 1.5` the iteration diverges (`claimed_five_step_false`), and even at `σ = 1`
   five steps end in `[0.65, 0.90]` (`five_steps_from_one`).  Muon's quintic is tuned to be fast, not
   accurate: the true guarantee is the band `[0.6, 1.25]` of `NSPoly.muon_five_steps`, after normalising
   by the Frobenius norm.
3. "five NS steps need fewer flops than SVD once `m, n ≥ 4096`" (with the write-up's own cost formulas) —
   **false** (`claimed_efficiency_false`, e.g. `m = 8192, n = 4096`).  With a correct NS count, five NS steps
   need **2.5×–5× more flops** than a Golub–Reinsch SVD (`ns_vs_svd`).  Muon's speed comes from hardware
   (matmuls run at tensor-core peak in bf16; SVD is sequential), which no flop count can show.
   Head–tail (`Cost.htCost`) is cheaper than both by a factor that grows like `s / r` (`ht_vs_svd`).
-/

namespace FastMuon.MuonVsSVD

open FastMuon.NSPoly FastMuon.Cost

/-! ## 1. One step does not contract the error -/

theorem claimed_contraction_false :
    ¬ ∀ σ : ℝ, 0.5 ≤ σ → σ ≤ 1.5 → |nsP σ - 1| < |σ - 1| := by
  intro h
  have h1 := h 1 (by norm_num) (by norm_num)
  norm_num [nsP] at h1

/-! ## 2. Five steps do not converge to within 0.05 -/

theorem nsP_ge_two {x : ℝ} (hx : 2 ≤ x) : 2 ≤ nsP x := by
  unfold nsP
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hin : 1 ≤ 2.0315 * x ^ 4 - 4.7750 * x ^ 2 + 3.4445 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sub_nonneg.mpr hx2)]
  nlinarith [mul_le_mul_of_nonneg_left hin (by linarith : (0 : ℝ) ≤ x)]

theorem iter_ge_two (k : ℕ) {x : ℝ} (hx : 2 ≤ x) : 2 ≤ nsP^[k] x := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact nsP_ge_two ih

/-- Without Frobenius normalisation the iteration blows up: `σ = 1.5` is a counterexample. -/
theorem claimed_five_step_false :
    ¬ ∀ σ : ℝ, 0.5 ≤ σ → σ ≤ 1.5 → |nsP^[5] σ - 1| < 0.05 := by
  intro h
  have h1 := h 1.5 (by norm_num) (by norm_num)
  have hp : 2 ≤ nsP 1.5 := by norm_num [nsP]
  have h5 : 2 ≤ nsP^[5] 1.5 := by
    rw [Function.iterate_succ_apply]; exact iter_ge_two 4 hp
  have := (abs_lt.mp h1).2
  linarith

-- interval steps for the orbit of σ = 1: 1 ↦ 0.701 ↦ [1.05,1.15] ↦ [0.66,0.80] ↦ [0.95,1.18] ↦ [0.65,0.90]
lemma stepA {x : ℝ} (h0 : 0.69 ≤ x) (h1 : x ≤ 0.73) : 1.05 ≤ nsP x ∧ nsP x ≤ 1.15 := by
  unfold nsP
  have a := sub_nonneg.mpr h0; have b := sub_nonneg.mpr h1
  constructor <;> nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg a b) a, mul_nonneg (mul_nonneg a b) b,
    mul_nonneg (mul_nonneg a a) a, mul_nonneg (mul_nonneg b b) b, sq_nonneg (x - 0.71)]

lemma stepB {x : ℝ} (h0 : 1.05 ≤ x) (h1 : x ≤ 1.15) : 0.66 ≤ nsP x ∧ nsP x ≤ 0.80 := by
  unfold nsP
  have a := sub_nonneg.mpr h0; have b := sub_nonneg.mpr h1
  constructor <;> nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg a b) a, mul_nonneg (mul_nonneg a b) b,
    mul_nonneg (mul_nonneg a a) a, mul_nonneg (mul_nonneg b b) b, sq_nonneg (x - 1.05)]

lemma stepC {x : ℝ} (h0 : 0.66 ≤ x) (h1 : x ≤ 0.80) : 0.95 ≤ nsP x ∧ nsP x ≤ 1.18 := by
  unfold nsP
  have a := sub_nonneg.mpr h0; have b := sub_nonneg.mpr h1
  constructor <;> nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg a b) a, mul_nonneg (mul_nonneg a b) b,
    mul_nonneg (mul_nonneg a a) a, mul_nonneg (mul_nonneg b b) b, sq_nonneg (x - 0.73)]

lemma stepD {x : ℝ} (h0 : 0.95 ≤ x) (h1 : x ≤ 1.18) : 0.65 ≤ nsP x ∧ nsP x ≤ 0.90 := by
  unfold nsP
  have a := sub_nonneg.mpr h0; have b := sub_nonneg.mpr h1
  constructor <;> nlinarith [mul_nonneg a b, mul_nonneg (mul_nonneg a b) a, mul_nonneg (mul_nonneg a b) b,
    mul_nonneg (mul_nonneg a a) a, mul_nonneg (mul_nonneg b b) b, sq_nonneg (x - 1.05)]

/-- Even from an already-orthogonal direction (`σ = 1`), five Muon steps end in `[0.65, 0.90]`. -/
theorem five_steps_from_one : 0.65 ≤ nsP^[5] 1 ∧ nsP^[5] 1 ≤ 0.90 := by
  have e1 : nsP 1 = 0.701 := by norm_num [nsP]
  have hA := stepA (x := nsP 1) (by rw [e1]; norm_num) (by rw [e1]; norm_num)
  have hB := stepB hA.1 hA.2
  have hC := stepC hB.1 hB.2
  have hD := stepD hC.1 hC.2
  simpa [Function.iterate_succ_apply'] using hD

theorem five_steps_from_one_not_close : 0.05 < |nsP^[5] 1 - 1| := by
  have h := five_steps_from_one
  rw [abs_sub_comm, abs_of_pos (by linarith [h.2])]
  linarith [h.2]

/-! ## 3. Flops: NS is not cheaper than SVD; head–tail is cheaper than both -/

/-- The write-up's NS cost (one `m·n·m` matmul per step). -/
def claimedNsCost (m n steps : ℕ) : ℕ := steps * (2 * m * n * m)
/-- Golub–Reinsch SVD (`Σ` and `V`) of an `m × n` matrix, `m ≥ n`, as in the write-up. -/
def svdCost (m n : ℕ) : ℕ := 4 * m * n ^ 2 + 8 * n ^ 3

theorem claimed_efficiency_false :
    ¬ ∀ m n : ℕ, 4096 ≤ m → 4096 ≤ n → claimedNsCost m n 5 < svdCost m n := by
  intro h
  have := h 8192 4096 (by norm_num) (by norm_num)
  norm_num [claimedNsCost, svdCost] at this

/-- **NS vs SVD in flops.** For an `s × l` matrix with `s ≤ l`, five correctly-counted NS steps
(`Cost.nsCost`) need between 2.5× and 5× the flops of a Golub–Reinsch SVD. -/
theorem ns_vs_svd (s l : ℕ) (hsl : s ≤ l) :
    5 * svdCost l s ≤ 2 * nsCost s l 5 ∧ nsCost s l 5 ≤ 5 * svdCost l s := by
  unfold svdCost nsCost
  have : s ^ 3 ≤ s ^ 2 * l := by
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ s ^ 2 * l := Nat.mul_le_mul_left _ hsl
  constructor <;> nlinarith

/-- **Head–tail vs SVD.** `s · htCost ≤ 12 r · svdCost`: the head–tail oracle is at least
`s / (12 r)` times cheaper than an SVD, in flops. -/
theorem ht_vs_svd (s l r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsl : s ≤ l) :
    s * htCost s l r ≤ 12 * r * svdCost l s := by
  have h1 := speedup s l r hr hrs hsl
  have h2 := (ns_vs_svd s l hsl).2
  have : 5 * (s * htCost s l r) ≤ 5 * (12 * r * svdCost l s) := by
    calc 5 * (s * htCost s l r) = 5 * s * htCost s l r := by ring
      _ ≤ 12 * r * nsCost s l 5 := h1
      _ ≤ 12 * r * (5 * svdCost l s) := Nat.mul_le_mul_left _ h2
      _ = 5 * (12 * r * svdCost l s) := by ring
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

end FastMuon.MuonVsSVD
