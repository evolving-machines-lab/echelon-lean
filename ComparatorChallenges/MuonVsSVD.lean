import Mathlib

/-!
# Comparator challenge: `FastMuon.MuonVsSVD.claimed_contraction_false`, `FastMuon.MuonVsSVD.ns_vs_svd`
(`FastMuon/MuonVsSVD.lean`)

Imports only Mathlib.  `NSPoly.nsP`, `Cost.nsCost` and `MuonVsSVD.svdCost` are copied verbatim from
`FastMuon/NSPoly.lean`, `FastMuon/Cost.lean` and `FastMuon/MuonVsSVD.lean`.
-/

namespace FastMuon.NSPoly

/-- Muon's quintic. -/
noncomputable def nsP (x : ℝ) : ℝ := 3.4445 * x - 4.7750 * x ^ 3 + 2.0315 * x ^ 5

end FastMuon.NSPoly

namespace FastMuon.Cost

/-- Flops of `k` Newton–Schulz quintic steps on an `s × l` matrix (`s ≤ l`). -/
def nsCost (s l k : ℕ) : ℕ := k * (4 * s ^ 2 * l + 2 * s ^ 3)

end FastMuon.Cost

namespace FastMuon.MuonVsSVD

open FastMuon.NSPoly FastMuon.Cost

/-- One Newton–Schulz step does not contract the error on `[0.5, 1.5]`. -/
theorem claimed_contraction_false :
    ¬ ∀ σ : ℝ, 0.5 ≤ σ → σ ≤ 1.5 → |nsP σ - 1| < |σ - 1| := by
  sorry

/-- Golub–Reinsch SVD (`Σ` and `V`) of an `m × n` matrix, `m ≥ n`, as in the write-up. -/
def svdCost (m n : ℕ) : ℕ := 4 * m * n ^ 2 + 8 * n ^ 3

/-- **NS vs SVD in flops.** For `s ≤ l`, five NS steps need between 2.5× and 5× the flops of SVD. -/
theorem ns_vs_svd (s l : ℕ) (hsl : s ≤ l) :
    5 * svdCost l s ≤ 2 * nsCost s l 5 ∧ nsCost s l 5 ≤ 5 * svdCost l s := by
  sorry

end FastMuon.MuonVsSVD
