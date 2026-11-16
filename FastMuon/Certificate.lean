import Mathlib

/-!
# Certified steepest descent: when does a cheap orthogonaliser keep Muon's rate?

Muon updates a weight matrix with `W ← W - η · polar(M)`, where `polar(M)` is the steepest-descent
direction for the spectral norm.  We abstract that setting:

* `E` is the parameter space (e.g. `Matrix m n ℝ`),
* `ip` is the pairing between gradients and updates (the Frobenius inner product),
* `N` is the primal seminorm (the spectral norm), `D` the dual seminorm (the nuclear norm),
  related by Hölder's inequality `|ip x y| ≤ D x * N y`.

A *direction oracle* (exact polar factor, Newton–Schulz, or the cheap head–tail oracle) only has to
return a direction `d` with an `(α, β)`-*certificate*

  `ip m d ≥ α * D m`   and   `N d ≤ β`

for the matrix `m` it was given.  The exact polar factor has `α = β = 1`.  We prove that any certified
oracle keeps the nonconvex `O(1/√T)` stationarity rate of Muon, with the constants degraded only through
`α` and `β`, including heavy-ball momentum and bounded gradient noise.

Nothing about matrices is used here: the theorems hold for any pair of seminorms satisfying Hölder.
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
`D`-Lipschitz gradient.  (For a differentiable `f` both follow from the second one; we assume both.) -/
structure Smooth (f : E → ℝ) (grad : E → E) (L : ℝ) : Prop where
  L_nonneg : 0 ≤ L
  upper : ∀ x y, f y ≤ f x + G.ip (grad x) (y - x) + L / 2 * G.N (y - x) ^ 2
  lip : ∀ x y, G.D (grad y - grad x) ≤ L * G.N (y - x)

/-- **Perturbation lemma.** A direction certified for a proxy `m` (momentum) is still a descent
direction for the true gradient `g`, losing `(α + β) · D (g - m)`. -/
theorem certificate_transfer {α β : ℝ} (hα : 0 ≤ α) {g m d : E}
    (hcert : α * G.D m ≤ G.ip m d) (hN : G.N d ≤ β) :
    α * G.D g - (α + β) * G.D (g - m) ≤ G.ip g d := by
  have hsplit : G.ip g d = G.ip m d + G.ip (g - m) d := by
    have : g = m + (g - m) := by abel
    conv_lhs => rw [this]
    simp
  have h1 : -(G.D (g - m) * G.N d) ≤ G.ip (g - m) d := by
    have := G.holder (g - m) d
    linarith [neg_abs_le (G.ip (g - m) d)]
  have h2 : G.D (g - m) * G.N d ≤ G.D (g - m) * β :=
    mul_le_mul_of_nonneg_left hN (apply_nonneg _ _)
  have htri : G.D g ≤ G.D m + G.D (g - m) := by
    have := map_add_le_add G.D m (g - m)
    simpa using this
  have h3 : α * G.D g ≤ α * G.D m + α * G.D (g - m) := by
    have := mul_le_mul_of_nonneg_left htri hα
    linarith
  nlinarith [h1, h2, h3, hsplit, hcert]

/-- **One step.** If `d` is certified for the gradient up to an error `ε`, then the step
`x - η • d` decreases `f` by at least `η (α D(∇f) - ε) - L η² β² / 2`. -/
theorem one_step {f : E → ℝ} {grad : E → E} {L : ℝ} (hf : G.Smooth f grad L)
    {x d : E} {η α β ε : ℝ} (hη : 0 ≤ η)
    (hcert : α * G.D (grad x) - ε ≤ G.ip (grad x) d) (hN : G.N d ≤ β) :
    f (x - η • d) ≤ f x - η * (α * G.D (grad x) - ε) + L / 2 * η ^ 2 * β ^ 2 := by
  have h := hf.upper x (x - η • d)
  have hsub : x - η • d - x = -(η • d) := by abel
  rw [hsub] at h
  have hip : G.ip (grad x) (-(η • d)) = -(η * G.ip (grad x) d) := by simp
  have hN' : G.N (-(η • d)) = η * G.N d := by
    rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hη]
  rw [hip, hN'] at h
  have hNd : 0 ≤ G.N d := apply_nonneg _ _
  have hsq : (η * G.N d) ^ 2 ≤ η ^ 2 * β ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNd hN 2) (sq_nonneg η)
  have hL : L / 2 * (η * G.N d) ^ 2 ≤ L / 2 * (η ^ 2 * β ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by linarith [hf.L_nonneg])
  have hdesc : η * (α * G.D (grad x) - ε) ≤ η * G.ip (grad x) d :=
    mul_le_mul_of_nonneg_left hcert hη
  nlinarith [h, hL, hdesc]

/-- **Telescoped descent.** For iterates `x (t+1) = x t - η • d t` with per-step certificates
(`α`, `β`, errors `ε t`), the weighted sum of dual gradient norms is bounded. -/
theorem sum_bound {f : E → ℝ} {grad : E → E} {L : ℝ} (hf : G.Smooth f grad L)
    {x d : ℕ → E} {ε : ℕ → ℝ} {η α β : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ t, x (t + 1) = x t - η • d t)
    (hcert : ∀ t, α * G.D (grad (x t)) - ε t ≤ G.ip (grad (x t)) (d t))
    (hN : ∀ t, G.N (d t) ≤ β) (T : ℕ) :
    η * α * ∑ t ∈ range T, G.D (grad (x t)) ≤
      f (x 0) - f (x T) + η * ∑ t ∈ range T, ε t + T * (L / 2 * η ^ 2 * β ^ 2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hs := G.one_step hf hη (hcert T) (hN T)
    rw [← hstep T] at hs
    rw [sum_range_succ, sum_range_succ]
    push_cast
    nlinarith [hs, ih]

/-- **Rate.** With `f ≥ f_low`, the average dual gradient norm over `T` steps is at most
`(f x₀ - f_low)/(α η T) + L η β²/(2α) + (average error)/α`. -/
theorem avg_bound {f : E → ℝ} {grad : E → E} {L : ℝ} (hf : G.Smooth f grad L)
    {x d : ℕ → E} {ε : ℕ → ℝ} {η α β flow : ℝ} (hη : 0 < η) (hα : 0 < α)
    (hstep : ∀ t, x (t + 1) = x t - η • d t)
    (hcert : ∀ t, α * G.D (grad (x t)) - ε t ≤ G.ip (grad (x t)) (d t))
    (hN : ∀ t, G.N (d t) ≤ β) (hlow : ∀ y, flow ≤ f y) {T : ℕ} (hT : 0 < T) :
    (∑ t ∈ range T, G.D (grad (x t))) / T ≤
      (f (x 0) - flow) / (α * η * T) + L * η * β ^ 2 / (2 * α) +
        (∑ t ∈ range T, ε t) / (α * T) := by
  have hs := G.sum_bound hf hη.le hstep hcert hN T
  have hfT := hlow (x T)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hden : 0 < α * η * T := by positivity
  rw [div_le_iff₀ hTpos]
  have key : η * α * ∑ t ∈ range T, G.D (grad (x t)) ≤
      (f (x 0) - flow) + η * ∑ t ∈ range T, ε t + T * (L / 2 * η ^ 2 * β ^ 2) := by
    linarith
  have e1 : (f (x 0) - flow) / (α * η * T) * T = (f (x 0) - flow) / (α * η) := by
    field_simp
  have e2 : L * η * β ^ 2 / (2 * α) * T = (T * (L / 2 * η ^ 2 * β ^ 2)) / (α * η) := by
    field_simp
  have e3 : (∑ t ∈ range T, ε t) / (α * T) * T = (η * ∑ t ∈ range T, ε t) / (α * η) := by
    field_simp
  rw [add_mul, add_mul, e1, e2, e3, ← add_div, ← add_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Momentum error.** Heavy-ball EMA momentum `m (t+1) = μ m t + (1-μ) ĝ (t+1)` of noisy gradients
`ĝ t = g t + ξ t` with `D ξ ≤ σ`, where consecutive true gradients move by at most `δ` in `D`,
stays within `μ δ / (1-μ) + σ` of the true gradient. -/
theorem momentum_error {g ghat m : ℕ → E} {μ δ σ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hδ : 0 ≤ δ)
    (hm0 : m 0 = ghat 0) (hm : ∀ t, m (t + 1) = μ • m t + (1 - μ) • ghat (t + 1))
    (hnoise : ∀ t, G.D (ghat t - g t) ≤ σ) (hdrift : ∀ t, G.D (g t - g (t + 1)) ≤ δ) :
    ∀ t, G.D (m t - g t) ≤ μ * δ / (1 - μ) + σ := by
  have h1μ : 0 < 1 - μ := by linarith
  have hB : 0 ≤ μ * δ / (1 - μ) := div_nonneg (mul_nonneg hμ0 hδ) h1μ.le
  intro t
  induction t with
  | zero => rw [hm0]; linarith [hnoise 0]
  | succ t ih =>
    have hdecomp : m (t + 1) - g (t + 1) =
        μ • (m t - g t) + μ • (g t - g (t + 1)) + (1 - μ) • (ghat (t + 1) - g (t + 1)) := by
      rw [hm t]
      simp only [smul_sub, sub_smul, one_smul]
      abel
    rw [hdecomp]
    have tri := (map_add_le_add G.D (μ • (m t - g t) + μ • (g t - g (t + 1)))
      ((1 - μ) • (ghat (t + 1) - g (t + 1))))
    have tri2 := map_add_le_add G.D (μ • (m t - g t)) (μ • (g t - g (t + 1)))
    simp only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hμ0, abs_of_pos h1μ] at tri tri2
    have a1 : μ * G.D (m t - g t) ≤ μ * (μ * δ / (1 - μ) + σ) := mul_le_mul_of_nonneg_left ih hμ0
    have a2 : μ * G.D (g t - g (t + 1)) ≤ μ * δ := mul_le_mul_of_nonneg_left (hdrift t) hμ0
    have a3 : (1 - μ) * G.D (ghat (t + 1) - g (t + 1)) ≤ (1 - μ) * σ :=
      mul_le_mul_of_nonneg_left (hnoise (t + 1)) h1μ.le
    have alg : μ * (μ * δ / (1 - μ) + σ) + μ * δ + (1 - μ) * σ = μ * δ / (1 - μ) + σ := by
      field_simp
      ring
    linarith

/-- **Main theorem (Muon family with momentum).**  Run `x (t+1) = x t - η • d t` where the oracle sees
only the momentum `m t` and returns a direction with an `(α, β)` certificate for `m t`.  If gradients
are observed with noise at most `σ` (in `D`), then

`avg_t D(∇f(x t)) ≤ (f x₀ - f_low)/(α η T) + L η β²/(2α) + (α+β)/α · (μ L η β/(1-μ) + σ)`.

For the exact polar factor (`α = β = 1`) this is Muon's deterministic rate; a cheap oracle with a
certificate `(α, β)` pays only these constant factors. -/
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
  -- drift of true gradients: D(g t - g (t+1)) ≤ L N(x(t+1) - x t) = L η N(d t) ≤ L η β
  have hdrift : ∀ t, G.D (grad (x t) - grad (x (t + 1))) ≤ L * η * β := by
    intro t
    have h := hf.lip (x (t + 1)) (x t)
    have hx : x t - x (t + 1) = η • d t := by rw [hstep t]; abel
    rw [hx, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hη] at h
    have : L * (η * G.N (d t)) ≤ L * (η * β) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hN t) hη.le) hf.L_nonneg
    linarith
  have hδ : 0 ≤ L * η * β := mul_nonneg (mul_nonneg hf.L_nonneg hη.le) hβ
  have herr := G.momentum_error (g := fun t => grad (x t)) hμ0 hμ1 hδ hm0 hm hnoise hdrift
  set B := μ * (L * η * β) / (1 - μ) + σ with hBdef
  have hcert : ∀ t, α * G.D (grad (x t)) - (α + β) * B ≤ G.ip (grad (x t)) (d t) := by
    intro t
    have h := G.certificate_transfer hα.le (g := grad (x t)) (horacle t) (hN t)
    have he : G.D (grad (x t) - m t) ≤ B := by
      have := herr t
      rw [← map_neg_eq_map, neg_sub]
      simpa [hBdef, mul_assoc] using this
    have : (α + β) * G.D (grad (x t) - m t) ≤ (α + β) * B :=
      mul_le_mul_of_nonneg_left he (by linarith)
    linarith
  have h := G.avg_bound hf (ε := fun _ => (α + β) * B) hη hα hstep hcert hN hlow hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : (∑ t ∈ range T, (fun _ => (α + β) * B) t) / (α * T) = (α + β) / α * B := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [hsum] at h
  exact h

end Geometry

/-! ## The hypotheses are satisfiable

Euclidean geometry (`N = D = ‖·‖`, Cauchy–Schwarz) is an instance; for matrices with the spectral and
nuclear norms, Hölder is von Neumann's trace inequality (standard; not re-proved here). -/

/-- Any real inner-product space gives a `Geometry` with `N = D = ‖·‖`. -/
noncomputable def euclideanGeometry (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Geometry F where
  ip := innerₗ F
  N := normSeminorm ℝ F
  D := normSeminorm ℝ F
  holder x y := by
    simpa using abs_real_inner_le_norm x y

end FastMuon
