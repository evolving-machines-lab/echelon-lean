import Mathlib

/-!
# Comparator challenge: `FastMuon.Geometry.muon_family_rate` (`FastMuon/Certificate.lean`)

Imports only Mathlib.  The structures `Geometry` and `Geometry.Smooth` are copied verbatim from
`FastMuon/Certificate.lean`; `lake comparator` checks that they are identical constants in the
solution and that the solution proves exactly the statement below.
-/

namespace FastMuon

open Finset

/-- The geometry: a bilinear pairing and two seminorms related by Hölder's inequality. -/
structure Geometry (E : Type*) [AddCommGroup E] [Module ℝ E] where
  ip : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  N : Seminorm ℝ E
  D : Seminorm ℝ E
  holder : ∀ x y, |ip x y| ≤ D x * N y

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace Geometry

variable (G : Geometry E)

/-- An `L`-smooth objective in the geometry `(N, D)`: the descent-lemma upper bound and a
`D`-Lipschitz gradient. -/
structure Smooth (f : E → ℝ) (grad : E → E) (L : ℝ) : Prop where
  L_nonneg : 0 ≤ L
  upper : ∀ x y, f y ≤ f x + G.ip (grad x) (y - x) + L / 2 * G.N (y - x) ^ 2
  lip : ∀ x y, G.D (grad y - grad x) ≤ L * G.N (y - x)

/-- **Main theorem (Muon family with momentum).**
`avg_t D(∇f(x t)) ≤ (f x₀ - f_low)/(α η T) + L η β²/(2α) + (α+β)/α · (μ L η β/(1-μ) + σ)`. -/
theorem muon_family_rate {f : E → ℝ} {grad : E → E} {L : ℝ} (hf : G.Smooth f grad L)
    {x d m ghat : ℕ → E} {η α β μ σ flow : ℝ} (hη : 0 < η) (hα : 0 < α) (hβ : 0 ≤ β)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hstep : ∀ t, x (t + 1) = x t - η • d t)
    (horacle : ∀ t, α * G.D (m t) ≤ G.ip (m t) (d t)) (hN : ∀ t, G.N (d t) ≤ β)
    (hm0 : m 0 = ghat 0) (hm : ∀ t, m (t + 1) = μ • m t + (1 - μ) • ghat (t + 1))
    (hnoise : ∀ t, G.D (ghat t - grad (x t)) ≤ σ)
    (hlow : ∀ y, flow ≤ f y) {T : ℕ} (hT : 0 < T) :
    (∑ t ∈ range T, G.D (grad (x t))) / T ≤
      (f (x 0) - flow) / (α * η * T) + L * η * β ^ 2 / (2 * α) +
        (α + β) / α * (μ * (L * η * β) / (1 - μ) + σ) := by
  sorry

end Geometry

end FastMuon
