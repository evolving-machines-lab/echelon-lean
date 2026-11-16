import Mathlib

/-!
# O4: the certificate score does not determine one-step progress

Setting: square real matrices `Matrix n n ℝ`, Frobenius inner product `⟪A, B⟫ = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ`,
quadratic loss `f(W) = ½ ⟪W, H W⟫` with a Frobenius-self-adjoint linear operator `H`.
Its gradient is `G = H W`, and the step `W ↦ W - η d` decreases `f` by
`η ⟪G, d⟫ - η²/2 ⟪d, H d⟫`.

* `spec A` is Mathlib's ℓ²→ℓ² operator norm (the spectral norm, `Matrix.Norms.L2Operator`).
* `nuc A` is the nuclear norm, defined as the sum of the singular values
  `∑ᵢ √λᵢ(Aᵀ A)` using Mathlib's eigenvalues of the Hermitian matrix `Aᴴ A`.
* `kappa G d = ⟪G, d⟫ / (nuc G * spec d)` is the certificate.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace O4

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Frobenius inner product `⟪A, B⟫ = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ = tr(Aᵀ B)`. -/
def frob (A B : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Spectral norm: Mathlib's `ℓ² → ℓ²` operator norm of the matrix. -/
noncomputable def spec (A : Matrix n n ℝ) : ℝ := ‖A‖

/-- Nuclear norm: the sum of the singular values, `∑ᵢ √(eigenvalueᵢ (Aᴴ A))`. -/
noncomputable def nuc (A : Matrix n n ℝ) : ℝ :=
  ∑ i, Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The certificate `κ(G, d) = ⟪G, d⟫ / (‖G‖_* ‖d‖_op)`. -/
noncomputable def kappa (G d : Matrix n n ℝ) : ℝ := frob G d / (nuc G * spec d)

/-- Stable rank `‖d‖_F² / ‖d‖_op²`. -/
noncomputable def srank (d : Matrix n n ℝ) : ℝ := frob d d / spec d ^ 2

/-- Quadratic loss `f(W) = ½ ⟪W, H W⟫`. -/
noncomputable def loss (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (W : Matrix n n ℝ) : ℝ :=
  frob W (H W) / 2

/-- `H` is self-adjoint for the Frobenius inner product. -/
def SelfAdj (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) : Prop := ∀ A B, frob A (H B) = frob (H A) B

/-- The set of one-step decreases `f(W) - f(W - η d)`, `η ∈ ℝ`. Its greatest element is the
"best one-step decrease". -/
def decreases (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (W d : Matrix n n ℝ) : Set ℝ :=
  Set.range fun η : ℝ => loss H W - loss H (W - η • d)

/-! ### Bilinearity of `frob` -/

lemma frob_comm (A B : Matrix n n ℝ) : frob A B = frob B A := by
  simp [frob, mul_comm]

lemma frob_sub_left (A B C : Matrix n n ℝ) : frob (A - B) C = frob A C - frob B C := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]

lemma frob_sub_right (A B C : Matrix n n ℝ) : frob A (B - C) = frob A B - frob A C := by
  simp [frob, mul_sub, Finset.sum_sub_distrib]

lemma frob_add_left (A B C : Matrix n n ℝ) : frob (A + B) C = frob A C + frob B C := by
  simp [frob, add_mul, Finset.sum_add_distrib]

lemma frob_add_right (A B C : Matrix n n ℝ) : frob A (B + C) = frob A B + frob A C := by
  simp [frob, mul_add, Finset.sum_add_distrib]

lemma frob_smul_left (c : ℝ) (A B : Matrix n n ℝ) : frob (c • A) B = c * frob A B := by
  simp [frob, Finset.mul_sum, mul_assoc]

lemma frob_smul_right (c : ℝ) (A B : Matrix n n ℝ) : frob A (c • B) = c * frob A B := by
  simp [frob, Finset.mul_sum, mul_left_comm]

lemma frob_self_nonneg (A : Matrix n n ℝ) : 0 ≤ frob A A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A i j)

/-! ### General quadratic: exact one-step decrease -/

/-- Exact expansion: `f(W - η d) = f(W) - η ⟪H W, d⟫ + η²/2 ⟪d, H d⟫`, so `G = H W` is the
gradient and `⟪d, H d⟫` is the curvature along `d`. -/
theorem loss_step (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (hH : SelfAdj H) (W d : Matrix n n ℝ)
    (η : ℝ) :
    loss H (W - η • d) = loss H W - η * frob (H W) d + η ^ 2 / 2 * frob d (H d) := by
  have h1 : frob W (H d) = frob (H W) d := hH W d
  have h2 : frob d (H W) = frob (H W) d := frob_comm _ _
  simp only [loss, map_sub, map_smul, frob_sub_left, frob_sub_right, frob_smul_left,
    frob_smul_right, h1, h2]
  ring

/-- `G = H W` is the gradient of `f` at `W`: the directional derivative of `f` at `W`
along any `d` is `⟪H W, d⟫`. -/
theorem loss_hasDerivAt (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (hH : SelfAdj H)
    (W d : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => loss H (W + t • d)) (frob (H W) d) 0 := by
  have e : (fun t : ℝ => loss H (W + t • d)) =
      fun t => loss H W + t * frob (H W) d + t ^ 2 / 2 * frob d (H d) := by
    funext t
    have := loss_step H hH W d (-t)
    rw [show W - (-t) • d = W + t • d by rw [neg_smul, sub_neg_eq_add]] at this
    rw [this]; ring
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => loss H W + t * frob (H W) d) (frob (H W) d) 0 := by
    convert ((hasDerivAt_id' (0 : ℝ)).mul_const (frob (H W) d)).const_add (loss H W) using 1
    simp
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * frob d (H d)) 0 0 := by
    convert ((hasDerivAt_pow 2 (0 : ℝ)).div_const 2).mul_const (frob d (H d)) using 1
    simp
  convert h1.add h2 using 1
  simp

/-- **Best one-step decrease on a quadratic.** If the curvature along `d` is positive, the
largest decrease `f(W) - f(W - η d)` over all step sizes `η` is exactly
`⟪G, d⟫² / (2 ⟪d, H d⟫)` with `G = H W`, attained at `η = ⟪G, d⟫ / ⟪d, H d⟫`. -/
theorem best_step (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (hH : SelfAdj H) (W d : Matrix n n ℝ)
    (hq : 0 < frob d (H d)) :
    IsGreatest (decreases H W d) (frob (H W) d ^ 2 / (2 * frob d (H d))) := by
  refine ⟨⟨frob (H W) d / frob d (H d), ?_⟩, ?_⟩
  · simp only [loss_step H hH]
    field_simp
    ring
  · rintro _ ⟨η, rfl⟩
    simp only [loss_step H hH]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (frob d (H d) * η - frob (H W) d)]

/-- Same, restricted to nonnegative step sizes (when `⟪G, d⟫ ≥ 0`, i.e. `d` is a descent
direction): the optimum is unchanged. -/
theorem best_step_nonneg (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (hH : SelfAdj H)
    (W d : Matrix n n ℝ) (hq : 0 < frob d (H d)) (hg : 0 ≤ frob (H W) d) :
    IsGreatest ((fun η : ℝ => loss H W - loss H (W - η • d)) '' Set.Ici 0)
      (frob (H W) d ^ 2 / (2 * frob d (H d))) := by
  obtain ⟨⟨η, hη⟩, hub⟩ := best_step H hH W d hq
  refine ⟨⟨frob (H W) d / frob d (H d), Set.mem_Ici.2 (div_nonneg hg hq.le), ?_⟩, ?_⟩
  · simp only [loss_step H hH]
    field_simp
    ring
  · rintro _ ⟨η', -, rfl⟩
    exact hub ⟨η', rfl⟩

/-! ### What governs the decrease: the (H-weighted) stable rank -/

/-- **Exact characterization, general `H`.** The best decrease equals
`κ² ‖G‖_*² / (2 ρ_H(d))` where `ρ_H(d) = ⟪d, H d⟫ / ‖d‖_op²` is the `H`-weighted stable rank.
Pure algebra: holds for any positive normalisation `nuc G`. -/
theorem decrease_eq_kappa_general (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (G d : Matrix n n ℝ)
    (hN : nuc G ≠ 0) (hs : spec d ≠ 0) (hq : frob d (H d) ≠ 0) :
    frob G d ^ 2 / (2 * frob d (H d)) =
      kappa G d ^ 2 * nuc G ^ 2 / (2 * (frob d (H d) / spec d ^ 2)) := by
  unfold kappa
  field_simp

/-- **Exact characterization, `H = id` (f = ½‖W‖_F²).** The best decrease is
`κ² ‖G‖_*² / (2 · srank d)`: besides the certificate, it is governed by the stable rank
`‖d‖_F² / ‖d‖_op²` of the direction. -/
theorem decrease_eq_kappa_srank (G d : Matrix n n ℝ) (hN : nuc G ≠ 0) (hs : spec d ≠ 0)
    (hF : frob d d ≠ 0) :
    frob G d ^ 2 / (2 * frob d d) = kappa G d ^ 2 * nuc G ^ 2 / (2 * srank d) := by
  unfold kappa srank
  field_simp

/-- **Sandwich for general `H` with `m I ≼ H ≼ L I` along `d`.**
`κ²‖G‖_*² / (2 L srank d) ≤ best decrease ≤ κ²‖G‖_*² / (2 m srank d)`. -/
theorem decrease_sandwich (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (G d : Matrix n n ℝ)
    (m L : ℝ) (hm : 0 < m) (hN : nuc G ≠ 0) (hs : spec d ≠ 0) (hF : 0 < frob d d)
    (hlo : m * frob d d ≤ frob d (H d)) (hhi : frob d (H d) ≤ L * frob d d) :
    kappa G d ^ 2 * nuc G ^ 2 / (2 * L * srank d) ≤ frob G d ^ 2 / (2 * frob d (H d)) ∧
      frob G d ^ 2 / (2 * frob d (H d)) ≤ kappa G d ^ 2 * nuc G ^ 2 / (2 * m * srank d) := by
  have hq : 0 < frob d (H d) := lt_of_lt_of_le (mul_pos hm hF) hlo
  have hL : 0 < L := by nlinarith
  have hk : kappa G d ^ 2 * nuc G ^ 2 = frob G d ^ 2 / spec d ^ 2 := by
    unfold kappa; field_simp
  have hsr : srank d = frob d d / spec d ^ 2 := rfl
  have hs2 : 0 < spec d ^ 2 := by positivity
  rw [hk, hsr]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : frob G d ^ 2 / spec d ^ 2 * (2 * frob d (H d)) ≤
        frob G d ^ 2 / spec d ^ 2 * (2 * (L * frob d d)) := by gcongr
    calc frob G d ^ 2 / spec d ^ 2 * (2 * frob d (H d))
        ≤ frob G d ^ 2 / spec d ^ 2 * (2 * (L * frob d d)) := this
      _ = frob G d ^ 2 * (2 * L * (frob d d / spec d ^ 2)) := by field_simp
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : frob G d ^ 2 * (2 * (m * frob d d)) ≤ frob G d ^ 2 * (2 * frob d (H d)) := by
      gcongr
    calc frob G d ^ 2 * (2 * m * (frob d d / spec d ^ 2))
        = frob G d ^ 2 / spec d ^ 2 * (2 * (m * frob d d)) := by field_simp
      _ ≤ frob G d ^ 2 / spec d ^ 2 * (2 * frob d (H d)) := by
        gcongr

/-- **κ and the stable rank together determine the decrease (`H = id`), and with κ fixed the
decrease pins down the stable rank.** For two directions with the same nonzero certificate
`κ(G,d₁) = κ(G,d₂)`, their best one-step decreases are equal iff their stable ranks are. -/
theorem decrease_eq_iff_srank_eq (G d₁ d₂ : Matrix n n ℝ) (hN : nuc G ≠ 0)
    (hs₁ : spec d₁ ≠ 0) (hs₂ : spec d₂ ≠ 0) (hF₁ : frob d₁ d₁ ≠ 0) (hF₂ : frob d₂ d₂ ≠ 0)
    (hk : kappa G d₁ = kappa G d₂) (hk0 : kappa G d₁ ≠ 0) :
    frob G d₁ ^ 2 / (2 * frob d₁ d₁) = frob G d₂ ^ 2 / (2 * frob d₂ d₂) ↔
      srank d₁ = srank d₂ := by
  rw [decrease_eq_kappa_srank G d₁ hN hs₁ hF₁, decrease_eq_kappa_srank G d₂ hN hs₂ hF₂, ← hk]
  have hsr₁ : srank d₁ ≠ 0 := div_ne_zero hF₁ (pow_ne_zero 2 hs₁)
  have hsr₂ : srank d₂ ≠ 0 := div_ne_zero hF₂ (pow_ne_zero 2 hs₂)
  have hc : kappa G d₁ ^ 2 * nuc G ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    field_simp at h
    exact h.symm
  · intro h; rw [h]

/-- **Strict separation for any well-conditioned quadratic.** If `m ‖d‖_F² ≤ ⟪d, H d⟫ ≤ L ‖d‖_F²`
along both directions, the certificates are equal and nonzero, and the stable ranks differ by
more than the condition number (`L · srank d₁ < m · srank d₂`), then `d₁` gives a strictly
larger best one-step decrease than `d₂`. -/
theorem strict_gap (H : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) (G d₁ d₂ : Matrix n n ℝ) (m L : ℝ)
    (hm : 0 < m) (hN : nuc G ≠ 0) (hs₁ : spec d₁ ≠ 0) (hs₂ : spec d₂ ≠ 0)
    (hF₁ : 0 < frob d₁ d₁) (hF₂ : 0 < frob d₂ d₂)
    (hlo₁ : m * frob d₁ d₁ ≤ frob d₁ (H d₁)) (hhi₁ : frob d₁ (H d₁) ≤ L * frob d₁ d₁)
    (hlo₂ : m * frob d₂ d₂ ≤ frob d₂ (H d₂)) (hhi₂ : frob d₂ (H d₂) ≤ L * frob d₂ d₂)
    (hk : kappa G d₁ = kappa G d₂) (hk0 : kappa G d₁ ≠ 0)
    (hsr : L * srank d₁ < m * srank d₂) :
    frob G d₂ ^ 2 / (2 * frob d₂ (H d₂)) < frob G d₁ ^ 2 / (2 * frob d₁ (H d₁)) := by
  obtain ⟨lo₁, -⟩ := decrease_sandwich H G d₁ m L hm hN hs₁ hF₁ hlo₁ hhi₁
  obtain ⟨-, hi₂⟩ := decrease_sandwich H G d₂ m L hm hN hs₂ hF₂ hlo₂ hhi₂
  have hsr₁ : 0 < srank d₁ := div_pos hF₁ (by positivity)
  have hL : 0 < L := by nlinarith
  have hc : 0 < kappa G d₁ ^ 2 * nuc G ^ 2 := by positivity
  rw [← hk] at hi₂
  calc frob G d₂ ^ 2 / (2 * frob d₂ (H d₂))
      ≤ kappa G d₁ ^ 2 * nuc G ^ 2 / (2 * m * srank d₂) := hi₂
    _ < kappa G d₁ ^ 2 * nuc G ^ 2 / (2 * L * srank d₁) := by
      apply div_lt_div_of_pos_left hc (by positivity)
      nlinarith
    _ ≤ frob G d₁ ^ 2 / (2 * frob d₁ (H d₁)) := lo₁

/-! ### Norm computations -/

/-- For an orthogonal projection (`Pᴴ P = P`) all singular values are `0` or `1`, so the
nuclear norm is the trace. -/
lemma nuc_of_proj (P : Matrix n n ℝ) (hP : Pᴴ * P = P) : nuc P = P.trace := by
  have hA : (Pᴴ * P).IsHermitian := isHermitian_conjTranspose_mul_self P
  have h1 : Pᴴ * P = Pᴴ := by
    have := congrArg conjTranspose hP
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at this
  have hsym : Pᴴ = P := h1.symm.trans hP
  have hidem : (Pᴴ * P) * (Pᴴ * P) = Pᴴ * P := by
    rw [hP]; nth_rewrite 1 [← hsym]; exact hP
  have hev : ∀ i, hA.eigenvalues i * hA.eigenvalues i = hA.eigenvalues i := by
    intro i
    set v : n → ℝ := ⇑(hA.eigenvectorBasis i)
    have hv : (Pᴴ * P) *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
    have hv0 : v ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
    have h2 : (Pᴴ * P) *ᵥ ((Pᴴ * P) *ᵥ v) = (Pᴴ * P) *ᵥ v := by
      rw [mulVec_mulVec, hidem]
    rw [hv, mulVec_smul, hv, smul_smul] at h2
    have h3 : (hA.eigenvalues i * hA.eigenvalues i - hA.eigenvalues i) • v = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h hv0
  have hsqrt : ∀ i, Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i := by
    intro i
    have h := hev i
    have : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
      have : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases this with h | h <;> rw [h] <;> simp
  calc nuc P = ∑ i, Real.sqrt (hA.eigenvalues i) := rfl
    _ = ∑ i, hA.eigenvalues i := Finset.sum_congr rfl fun i _ => hsqrt i
    _ = (Pᴴ * P).trace := by rw [hA.trace_eq_sum_eigenvalues]; simp
    _ = P.trace := by rw [hP]

/-- Every entry is bounded by the spectral norm: `|Dᵢⱼ| = |eᵢᵀ D eⱼ| ≤ ‖D‖_op`. -/
lemma entry_le_spec (D : Matrix n n ℝ) (i j : n) : |D i j| ≤ spec D := by
  have h := l2_opNorm_mulVec D (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv n ℝ).symm (D *ᵥ (EuclideanSpace.single j (1 : ℝ)))) i
  simp at h h2
  exact h2.trans h

lemma norm_fin2 (a b : ℝ) : ‖(![a, b] : Fin 2 → ℝ)‖ = max |a| |b| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).2 ?_
    intro i; fin_cases i <;> simp
  · refine max_le ?_ ?_
    · simpa using norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 0
    · simpa using norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 1

lemma frob_single_left (i₀ j₀ : n) (c : ℝ) (D : Matrix n n ℝ) :
    frob (single i₀ j₀ c) D = c * D i₀ j₀ := by
  simp [frob, single_apply, ite_mul, Finset.sum_ite_eq, ite_and]

lemma frob_one_one : frob (1 : Matrix n n ℝ) 1 = Fintype.card n := by
  simp [frob, one_apply]

lemma selfAdj_id : SelfAdj (LinearMap.id : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ) := fun _ _ => rfl

/-- Best decrease for `f(W) = ½‖W‖_F²` (`H = id`, gradient `G = W`). -/
lemma best_step_id (W d : Matrix n n ℝ) (hF : 0 < frob d d) :
    IsGreatest (decreases LinearMap.id W d) (frob W d ^ 2 / (2 * frob d d)) := by
  simpa using best_step LinearMap.id selfAdj_id W d (by simpa using hF)

/-! ### Counterexample 1 (2×2, maximal certificate κ = 1)

`f(W) = ½‖W‖_F²` at `W = G₀ = diag(1,0)` (gradient `G₀`). Both `d₁ = diag(1,0)` and `d₂ = I`
have spectral norm 1 and maximise `⟪G₀, D⟫` over the spectral unit ball (both are exact
spectral-norm steepest-descent / LMO directions), so `κ = 1` for both; yet the best one-step
decreases are `1/2` and `1/4`. -/

/-- `G₀ = diag(1, 0)`: the weight matrix, and also the gradient of `½‖W‖_F²` there. -/
def G₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
/-- `d₁ = diag(1, 0)`, stable rank 1. -/
def d₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
/-- `d₂ = I`, stable rank 2. -/
def d₂ : Matrix (Fin 2) (Fin 2) ℝ := 1

lemma G₀_eq_diag : G₀ = diagonal ![1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [G₀]

lemma nuc_G₀ : nuc G₀ = 1 := by
  rw [nuc_of_proj]
  · simp [G₀, trace_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [G₀, Matrix.mul_apply, Fin.sum_univ_two]

lemma spec_d₁ : spec d₁ = 1 := by
  have : d₁ = G₀ := rfl
  rw [this, spec, G₀_eq_diag, l2_opNorm_diagonal, norm_fin2]; norm_num

lemma spec_d₂ : spec d₂ = 1 := norm_one

theorem counterexample_2x2 :
    kappa G₀ d₁ = 1 ∧ kappa G₀ d₂ = 1 ∧
    spec d₁ = 1 ∧ spec d₂ = 1 ∧
    (∀ D : Matrix (Fin 2) (Fin 2) ℝ, spec D ≤ 1 → frob G₀ D ≤ frob G₀ d₁) ∧
    frob G₀ d₁ = frob G₀ d₂ ∧
    (LinearMap.id : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) G₀ = G₀ ∧
    IsGreatest (decreases LinearMap.id G₀ d₁) (1 / 2) ∧
    IsGreatest (decreases LinearMap.id G₀ d₂) (1 / 4) := by
  have f1 : frob G₀ d₁ = 1 := by simp [frob, G₀, d₁, Fin.sum_univ_two]
  have f2 : frob G₀ d₂ = 1 := by simp [frob, G₀, d₂, Fin.sum_univ_two]
  have f11 : frob d₁ d₁ = 1 := by simp [frob, d₁, Fin.sum_univ_two]
  have f22 : frob d₂ d₂ = 2 := by norm_num [frob, d₂, one_apply]
  refine ⟨?_, ?_, spec_d₁, spec_d₂, ?_, by rw [f1, f2], rfl, ?_, ?_⟩
  · simp [kappa, f1, nuc_G₀, spec_d₁]
  · simp [kappa, f2, nuc_G₀, spec_d₂]
  · intro D hD
    have : frob G₀ D = D 0 0 := by simp [frob, G₀, Fin.sum_univ_two]
    rw [this, f1]
    exact (le_abs_self _).trans ((entry_le_spec D 0 0).trans hD)
  · have := best_step_id G₀ d₁ (by rw [f11]; norm_num)
    rw [f1, f11] at this
    convert this using 1; norm_num
  · have := best_step_id G₀ d₂ (by rw [f22]; norm_num)
    rw [f2, f22] at this
    convert this using 1; norm_num

/-- **The claim, formalised, is false.** "For every Frobenius-self-adjoint `H`, every `W`, and
directions `d₁, d₂` with positive curvature, equal certificates `κ(H W, d₁) = κ(H W, d₂)` force
equal best one-step decreases." -/
theorem kappa_does_not_determine_decrease :
    ¬ ∀ (H : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ), SelfAdj H →
      ∀ (W d d' : Matrix (Fin 2) (Fin 2) ℝ) (D D' : ℝ),
        0 < frob d (H d) → 0 < frob d' (H d') →
        kappa (H W) d = kappa (H W) d' →
        IsGreatest (decreases H W d) D → IsGreatest (decreases H W d') D' → D = D' := by
  intro h
  obtain ⟨k1, k2, -, -, -, -, -, g1, g2⟩ := counterexample_2x2
  have := h LinearMap.id selfAdj_id G₀ d₁ d₂ _ _
    (by simp [frob, d₁, Fin.sum_univ_two]) (by simp [frob, d₂, one_apply])
    (by simpa using k1.trans k2.symm) g1 g2
  norm_num at this

/-! ### Counterexample 2 (n×n family: the gap is a factor `n`)

`G = e_{i₀} e_{i₀}ᵀ`, `d₁ = G` (stable rank 1), `d₂ = I_n` (stable rank n): both κ = 1, both are
LMO directions, best decreases `1/2` and `1/(2n)`. So κ does not even determine the decrease
up to a dimension-free constant. -/

theorem counterexample_family [Nonempty n] (i₀ : n) :
    kappa (single i₀ i₀ (1 : ℝ)) (single i₀ i₀ 1) = 1 ∧
    kappa (single i₀ i₀ (1 : ℝ)) 1 = 1 ∧
    (∀ D : Matrix n n ℝ, spec D ≤ 1 → frob (single i₀ i₀ (1 : ℝ)) D ≤ 1) ∧
    IsGreatest (decreases LinearMap.id (single i₀ i₀ (1 : ℝ)) (single i₀ i₀ 1)) (1 / 2) ∧
    IsGreatest (decreases LinearMap.id (single i₀ i₀ (1 : ℝ)) 1)
      (1 / (2 * Fintype.card n)) := by
  have hnuc : nuc (single i₀ i₀ (1 : ℝ)) = 1 := by
    rw [nuc_of_proj, trace_single_eq_same]
    rw [conjTranspose_single, single_mul_single_same]; simp
  have hspec : spec (single i₀ i₀ (1 : ℝ)) = 1 := by
    have : (single i₀ i₀ (1 : ℝ)) = diagonal (Pi.single i₀ 1) := by
      ext i j
      rw [single_apply, diagonal_apply]
      by_cases h : i = j
      · subst h; by_cases h' : i = i₀
        · subst h'; simp
        · simp [h', Ne.symm h']
      · simp [h]; rintro rfl h2; exact h h2
    rw [spec, this, l2_opNorm_diagonal, Pi.norm_single]; simp
  have hspec1 : spec (1 : Matrix n n ℝ) = 1 := norm_one
  have f1 : frob (single i₀ i₀ (1 : ℝ)) (single i₀ i₀ 1) = 1 := by
    rw [frob_single_left]; simp
  have f2 : frob (single i₀ i₀ (1 : ℝ)) 1 = 1 := by
    rw [frob_single_left]; simp
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [kappa, f1, hnuc, hspec]
  · simp [kappa, f2, hnuc, hspec1]
  · intro D hD
    rw [frob_single_left, one_mul]
    exact (le_abs_self _).trans ((entry_le_spec D i₀ i₀).trans hD)
  · have := best_step_id (single i₀ i₀ (1 : ℝ)) (single i₀ i₀ 1) (by rw [f1]; norm_num)
    rw [f1] at this
    convert this using 1; norm_num
  · have := best_step_id (single i₀ i₀ (1 : ℝ)) 1 (by rw [frob_one_one]; exact hcard)
    rw [f2, frob_one_one] at this
    convert this using 1; norm_num

/-! ### Counterexample 3 (full-rank gradient `G = I₂`, κ = 3/5)

Rules out "it is only a rank-deficient-gradient artefact": at `W = I` (gradient `I`, nuclear norm
2), `e₁ = diag(1, 1/5)` and `e₂ = [[3,4],[-4,3]]` (= 5 × rotation) both have κ = 3/5, with best
decreases `9/13` and `9/25`. -/

noncomputable def e₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1 / 5]
def e₂ : Matrix (Fin 2) (Fin 2) ℝ := !![3, 4; -4, 3]

lemma nuc_one2 : nuc (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
  rw [nuc_of_proj]
  · simp
  · simp

lemma spec_e₁ : spec e₁ = 1 := by
  have : e₁ = diagonal ![1, 1 / 5] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₁]
  rw [spec, this, l2_opNorm_diagonal, norm_fin2]; norm_num

lemma spec_e₂ : spec e₂ = 5 := by
  have h := l2_opNorm_conjTranspose_mul_self e₂
  have : e₂ᴴ * e₂ = diagonal ![25, 25] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e₂, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [this, l2_opNorm_diagonal, norm_fin2] at h
  have h0 := norm_nonneg e₂
  norm_num at h
  rw [spec]; nlinarith

theorem counterexample_fullrank :
    kappa 1 e₁ = 3 / 5 ∧ kappa 1 e₂ = 3 / 5 ∧
    IsGreatest (decreases LinearMap.id 1 e₁) (9 / 13) ∧
    IsGreatest (decreases LinearMap.id 1 e₂) (9 / 25) := by
  have f1 : frob 1 e₁ = 6 / 5 := by
    simp [frob, e₁, Fin.sum_univ_two, one_apply]; norm_num
  have f2 : frob 1 e₂ = 6 := by
    simp [frob, e₂, Fin.sum_univ_two, one_apply]; norm_num
  have f11 : frob e₁ e₁ = 26 / 25 := by simp [frob, e₁, Fin.sum_univ_two]; norm_num
  have f22 : frob e₂ e₂ = 50 := by simp [frob, e₂, Fin.sum_univ_two]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kappa, f1, nuc_one2, spec_e₁]; norm_num
  · rw [kappa, f2, nuc_one2, spec_e₂]; norm_num
  · have := best_step_id 1 e₁ (by rw [f11]; norm_num)
    rw [f1, f11] at this
    convert this using 1; norm_num
  · have := best_step_id 1 e₂ (by rw [f22]; norm_num)
    rw [f2, f22] at this
    convert this using 1; norm_num

end O4

#print axioms O4.best_step
#print axioms O4.loss_hasDerivAt
#print axioms O4.decrease_eq_kappa_srank
#print axioms O4.decrease_eq_kappa_general
#print axioms O4.decrease_sandwich
#print axioms O4.decrease_eq_iff_srank_eq
#print axioms O4.strict_gap
#print axioms O4.counterexample_2x2
#print axioms O4.kappa_does_not_determine_decrease
#print axioms O4.counterexample_family
#print axioms O4.counterexample_fullrank
