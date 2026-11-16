import Mathlib

/-!
# Comparator challenge: `FastMuon.Separation.ns5_spiked_kappa` (`FastMuon/Separation.lean`)

Imports only Mathlib.  `NSPoly.nsP` is copied verbatim from `FastMuon/NSPoly.lean`.
-/

namespace FastMuon.NSPoly

/-- Muon's quintic. -/
noncomputable def nsP (x : ℝ) : ℝ := 3.4445 * x - 4.7750 * x ^ 3 + 2.0315 * x ^ 5

end FastMuon.NSPoly

namespace FastMuon.Separation

open FastMuon.NSPoly

/-- **Muon on a spiked spectrum.** With `y = p^[5](1/F)`, `z = p^[5](ε/F)`, `ε = 4·10⁻⁴`, the
certificate quality `κ` is at most `0.57`. -/
theorem ns5_spiked_kappa (F : ℝ) (hF1 : 1 ≤ F) (hF2 : F ≤ 1 / 0.99) :
    (nsP^[5] (1 / F) + 4095 * 4e-4 * nsP^[5] (4e-4 / F)) /
        ((1 + 4095 * 4e-4) * max (nsP^[5] (1 / F)) (nsP^[5] (4e-4 / F))) ≤ 0.57 := by
  sorry

end FastMuon.Separation
