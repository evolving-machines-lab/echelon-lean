import Mathlib

/-!
# The certificate-optimal tail scale for head–tail

For the head–tail direction `O = U P + c • T`, `HeadTail.lean` proves
`⟪X, O⟫ = a + c b` with `a = ⟪Uᵀ X, P⟫`, `b = ‖T‖_F²`, and `‖O‖₂ ≤ √(p² + c² t²)` with `p = ‖P‖₂`,
`t = ‖T‖₂`.  So the *certified* quality `⟪X, O⟫ / β_bound` of a tail scale `c` is
`(a + c b) / √(p² + c² t²)`.

* `certified_ratio_le`: for every `c ≥ 0`, `(a + c b) ≤ √((a/p)² + (b/t)²) · √(p² + c² t²)`
  (Cauchy–Schwarz);
* `certified_ratio_opt`: equality at `c* = b p² / (a t²)`.

So the best tail scale for the guarantee is `c* = ‖T‖_F² ‖P‖² / (⟪H, P⟫ ‖T‖₂²)`, computable in `O(s l)`
from quantities the oracle already has; `py/ortho.py` exposes it as `tau_mode="opt"`.  Note that `c*` can
exceed `1/‖T‖₂`: the guarantee sometimes prefers to over-weight the tail.
-/

namespace FastMuon.OptimalTail

theorem certified_ratio_le {a b t p c : ℝ} (ht : 0 < t) (hp : 0 < p) :
    a + c * b ≤ Real.sqrt ((a / p) ^ 2 + (b / t) ^ 2) * Real.sqrt (p ^ 2 + c ^ 2 * t ^ 2) := by
  set u := a / p with hu
  set v := b / t with hv
  have ha : a = u * p := by rw [hu]; field_simp
  have hb : b = v * t := by rw [hv]; field_simp
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  rw [ha, hb]
  nlinarith [sq_nonneg (u * (c * t) - v * p)]

theorem certified_ratio_opt {a b t p : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (ht : 0 < t) (hp : 0 < p) :
    let c := b * p ^ 2 / (a * t ^ 2)
    a + c * b = Real.sqrt ((a / p) ^ 2 + (b / t) ^ 2) * Real.sqrt (p ^ 2 + c ^ 2 * t ^ 2) := by
  intro c
  have hc : 0 ≤ c := by positivity
  rw [← Real.sqrt_mul (by positivity)]
  have hlhs : 0 ≤ a + c * b := by positivity
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) hlhs]
  simp only [c]
  field_simp

end FastMuon.OptimalTail
