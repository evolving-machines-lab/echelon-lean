import Mathlib

/-!
# Cost model: head–tail vs Newton–Schulz

Flop counts for one oracle call on an `s × l` matrix with `s ≤ l` (a multiply–add counts as 2 flops).
These are the formulas used in `py/ortho.py :: flops`.  The theorems below are exact statements about
these counting functions; whether wall-clock time follows the flop count is an empirical question
(see the benchmark in the write-up).

* Newton–Schulz with `k` quintic steps: each step forms `A = X Xᵀ` (`2 s² l`), `A²` (`2 s³`),
  and `B X` (`2 s² l`): `k (4 s² l + 2 s³)`.
* Head–tail with rank `r`: `H = Uᵀ X`, `U (P - H/τ)`, `X Hᵀ` (`6 s l r`), the small polar factor and the
  QR of the next frame (`6 (s + l) r² + 20 r³`, generous), and the tail-scale power iteration plus the
  elementwise work (`10 s l`).
-/

namespace FastMuon.Cost

/-- Flops of `k` Newton–Schulz quintic steps on an `s × l` matrix (`s ≤ l`). -/
def nsCost (s l k : ℕ) : ℕ := k * (4 * s ^ 2 * l + 2 * s ^ 3)

/-- Flops of one head–tail call with rank `r`. -/
def htCost (s l r : ℕ) : ℕ := 6 * s * l * r + 6 * (s + l) * r ^ 2 + 20 * r ^ 3 + 10 * s * l

/-- The head–tail cost is linear in each of `s`, `l`, `r` up to a constant: at most `48 s l r`. -/
theorem htCost_le (s l r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsl : s ≤ l) :
    htCost s l r ≤ 48 * s * l * r := by
  unfold htCost
  have h1 : (s + l) * r ^ 2 ≤ 2 * s * l * r := by
    have : (s + l) * r ≤ 2 * l * s := by nlinarith
    calc (s + l) * r ^ 2 = ((s + l) * r) * r := by ring
      _ ≤ (2 * l * s) * r := Nat.mul_le_mul_right _ this
      _ = 2 * s * l * r := by ring
  have h2 : r ^ 3 ≤ s * l * r := by
    have : r * r ≤ s * l := Nat.mul_le_mul hrs (hrs.trans hsl)
    calc r ^ 3 = (r * r) * r := by ring
      _ ≤ (s * l) * r := Nat.mul_le_mul_right _ this
  have h3 : s * l ≤ s * l * r := Nat.le_mul_of_pos_right _ hr
  nlinarith

/-- Five Newton–Schulz steps cost at least `20 s² l`. -/
theorem nsCost_ge (s l : ℕ) : 20 * s ^ 2 * l ≤ nsCost s l 5 := by
  unfold nsCost; nlinarith [Nat.zero_le (s ^ 3)]

/-- **Speed-up guarantee.** For `1 ≤ r ≤ s ≤ l`, Muon's 5-step Newton–Schulz costs at least
`(5/12)·(s/r)` times the head–tail oracle:  `5 s · htCost ≤ 12 r · nsCost₅`.
For `s = 4096, r = 16` this is a ≥ 106× flop reduction even with these loose constants;
the exact formulas give 1151× (see `speedup_4096_16`). -/
theorem speedup (s l r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsl : s ≤ l) :
    5 * s * htCost s l r ≤ 12 * r * nsCost s l 5 := by
  have h1 := htCost_le s l r hr hrs hsl
  have h2 := nsCost_ge s l
  calc 5 * s * htCost s l r ≤ 5 * s * (48 * s * l * r) := Nat.mul_le_mul_left _ h1
    _ = 12 * r * (20 * s ^ 2 * l) := by ring
    _ ≤ 12 * r * nsCost s l 5 := Nat.mul_le_mul_left _ h2

/-- Concrete instance: a 4096 × 4096 layer, rank 16 — more than 1000× fewer flops. -/
theorem speedup_4096_16 : 1000 * htCost 4096 4096 16 ≤ nsCost 4096 4096 5 := by
  unfold htCost nsCost; norm_num

/-- Concrete instance: a 4096 × 16384 MLP layer, rank 32 — more than 400× fewer flops (exact ratio ≈ 452×). -/
theorem speedup_4096_16384_32 : 400 * htCost 4096 16384 32 ≤ nsCost 4096 16384 5 := by
  unfold htCost nsCost; norm_num

/-- The speed-up grows without bound: for any target factor `K`, every layer with `s ≥ 3 K r`
(and `1 ≤ r ≤ s ≤ l`) gets at least a `K`-fold flop reduction. -/
theorem speedup_unbounded (K s l r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsl : s ≤ l)
    (hK : 3 * K * r ≤ s) : K * htCost s l r ≤ nsCost s l 5 := by
  have h := speedup s l r hr hrs hsl
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  -- 5 s · K · ht ≤ K · 12 r · ns ≤ (12/15) s · ns  ⇒  K · ht ≤ ns (with room to spare)
  have : 5 * s * (K * htCost s l r) ≤ 5 * s * nsCost s l 5 := by
    calc 5 * s * (K * htCost s l r) = K * (5 * s * htCost s l r) := by ring
      _ ≤ K * (12 * r * nsCost s l 5) := Nat.mul_le_mul_left _ h
      _ = 4 * (3 * K * r) * nsCost s l 5 := by ring
      _ ≤ 4 * s * nsCost s l 5 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hK)
      _ ≤ 5 * s * nsCost s l 5 := Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left this (by omega)

end FastMuon.Cost
