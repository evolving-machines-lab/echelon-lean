import Mathlib

/-!
# Comparator challenge: `FastMuon.Cost.speedup`, `FastMuon.Cost.speedup_4096_16` (`FastMuon/Cost.lean`)

Imports only Mathlib.  The flop-count functions `nsCost` and `htCost` are copied verbatim from
`FastMuon/Cost.lean`.
-/

namespace FastMuon.Cost

/-- Flops of `k` Newton–Schulz quintic steps on an `s × l` matrix (`s ≤ l`). -/
def nsCost (s l k : ℕ) : ℕ := k * (4 * s ^ 2 * l + 2 * s ^ 3)

/-- Flops of one head–tail call with rank `r`. -/
def htCost (s l r : ℕ) : ℕ := 6 * s * l * r + 6 * (s + l) * r ^ 2 + 20 * r ^ 3 + 10 * s * l

/-- **Speed-up guarantee.** For `1 ≤ r ≤ s ≤ l`: `5 s · htCost ≤ 12 r · nsCost₅`. -/
theorem speedup (s l r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsl : s ≤ l) :
    5 * s * htCost s l r ≤ 12 * r * nsCost s l 5 := by
  sorry

/-- Concrete instance: a 4096 × 4096 layer, rank 16 — more than 1000× fewer flops. -/
theorem speedup_4096_16 : 1000 * htCost 4096 4096 16 ≤ nsCost 4096 4096 5 := by
  sorry

end FastMuon.Cost
