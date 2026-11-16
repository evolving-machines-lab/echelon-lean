import FastMuon.Certificate
import FastMuon.HeadTail

/-!
# Muon's geometry on real matrices, and the end-to-end head–tail theorem

We instantiate `Geometry` on `Matrix s l ℝ` with

* the Frobenius pairing `⟪A, B⟫ = tr (Aᵀ B)`,
* `N` = Mathlib's spectral norm (`L2` operator norm),
* `D` = **the dual norm of the spectral norm**, `nuc G = sup_{‖O‖₂ ≤ 1} ⟪G, O⟫`
  (mathematically this is the nuclear norm; we never need its singular-value formula).

Hölder's inequality then holds by construction, so `Geometry.muon_family_rate` applies to matrices in
exactly the geometry where Muon is steepest descent.

On top of that we prove:

* `nuc_frame_le`: an orthonormal frame cannot increase the nuclear norm: `nuc (U H) ≤ nuc H`;
* `ht_alignment_lower` (**alignment error bound**): for the head–tail direction `O`,
  `⟪X, O⟫ ≥ α_h nuc X - (α_h nuc T - ‖T‖_F²/τ)`, where `α_h` is the head factor's own certificate
  (`α_h = 1` for an exact polar factor).  The only loss is the tail's nuclear mass not recovered by
  the scaled tail;
* `ht_muon_rate`: **HT-Muon with momentum converges at Muon's rate**, with `β = √2` and
  `α = α_h - (tail loss fraction)`.
-/

set_option linter.unusedSectionVars false

namespace FastMuon.Spectral

open Matrix FastMuon.HeadTail Finset
open scoped Matrix.Norms.L2Operator

variable {s l r : Type*} [Fintype s] [Fintype l] [Fintype r]
  [DecidableEq s] [DecidableEq l] [DecidableEq r]

/-- Frobenius pairing as a bilinear map. -/
def frobBilin : Matrix s l ℝ →ₗ[ℝ] Matrix s l ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B => frob A B)
    (fun A₁ A₂ B => by simp [frob, transpose_add, Matrix.add_mul, trace_add])
    (fun c A B => by simp [frob, transpose_smul, Matrix.smul_mul, trace_smul])
    (fun A B₁ B₂ => by simp [frob, Matrix.mul_add, trace_add])
    (fun c A B => by simp [frob, Matrix.mul_smul, trace_smul])

@[simp] theorem frobBilin_apply (A B : Matrix s l ℝ) : frobBilin A B = frob A B := rfl

/-- `G ↦ ⟪G, ·⟫` as a continuous functional on `(Matrix s l ℝ, ‖·‖₂)`. -/
noncomputable def frobCLM : Matrix s l ℝ →ₗ[ℝ] (Matrix s l ℝ →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap : (Matrix s l ℝ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ frobBilin

@[simp] theorem frobCLM_apply (A B : Matrix s l ℝ) : frobCLM A B = frob A B := rfl

/-- The nuclear norm as the dual of the spectral norm. -/
noncomputable def nuc : Seminorm ℝ (Matrix s l ℝ) :=
  (normSeminorm ℝ (Matrix s l ℝ →L[ℝ] ℝ)).comp frobCLM

theorem nuc_apply (A : Matrix s l ℝ) : nuc A = ‖frobCLM A‖ := rfl

/-- Hölder / von Neumann: `|⟪A, B⟫| ≤ ‖A‖_* ‖B‖₂`. -/
theorem holder (A B : Matrix s l ℝ) : |frob A B| ≤ nuc A * ‖B‖ := by
  have := (frobCLM A).le_opNorm B
  simpa [nuc_apply, Real.norm_eq_abs] using this

/-- Muon's geometry on `s × l` real matrices. -/
noncomputable def geometry : Geometry (Matrix s l ℝ) where
  ip := frobBilin
  N := normSeminorm ℝ _
  D := nuc
  holder A B := by simpa [coe_normSeminorm] using holder A B

theorem norm_one_le : ‖(1 : Matrix r r ℝ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix r r ℝ)
  rw [conjTranspose_one, Matrix.one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix r r ℝ)]

/-- An orthonormal frame is a contraction. -/
theorem frame_norm_le {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self U
  rw [conjTranspose_eq_transpose_of_trivial, hU] at h
  nlinarith [norm_nonneg U, norm_one_le (r := r)]

theorem frob_frame (U : Matrix s r ℝ) (H : Matrix r l ℝ) (O : Matrix s l ℝ) :
    frob (U * H) O = frob H (Uᵀ * O) := by
  simp [frob, transpose_mul, Matrix.mul_assoc]

/-- An orthonormal frame cannot increase the nuclear norm: `‖U H‖_* ≤ ‖H‖_*`. -/
theorem nuc_frame_le {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (H : Matrix r l ℝ) :
    nuc (U * H) ≤ nuc H := by
  rw [nuc_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _) fun O => ?_
  rw [frobCLM_apply, frob_frame, Real.norm_eq_abs]
  calc |frob H (Uᵀ * O)| ≤ nuc H * ‖Uᵀ * O‖ := holder _ _
    _ ≤ nuc H * (‖Uᵀ‖ * ‖O‖) :=
        mul_le_mul_of_nonneg_left (l2_opNorm_mul _ _) (apply_nonneg _ _)
    _ ≤ nuc H * (1 * ‖O‖) := by
        apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
        exact frame_norm_le hU
    _ = nuc H * ‖O‖ := by ring

/-- **Alignment error bound for the head–tail direction.** If the head factor `P` is
`α_h`-certified for the head `H = Uᵀ X`, then
`⟪X, O⟫ ≥ α_h ‖X‖_* - (α_h ‖T‖_* - ‖T‖_F² / τ)`. -/
theorem ht_alignment_lower {U : Matrix s r ℝ} (hU : Uᵀ * U = 1) (P : Matrix r l ℝ) (τ : ℝ)
    (X : Matrix s l ℝ) {αh : ℝ} (hαh : 0 ≤ αh) (hP : αh * nuc (Uᵀ * X) ≤ frob (Uᵀ * X) P) :
    αh * nuc X - (αh * nuc (tail U X) - τ⁻¹ * frob (tail U X) (tail U X)) ≤
      frob X (htDir U P τ X) := by
  rw [align hU P τ X]
  have hsplit : X = U * (Uᵀ * X) + tail U X := by simp [tail]
  have htri : nuc X ≤ nuc (U * (Uᵀ * X)) + nuc (tail U X) := by
    conv_lhs => rw [hsplit]
    exact map_add_le_add _ _ _
  have hfr := nuc_frame_le hU (Uᵀ * X)
  have h1 : αh * nuc X ≤ αh * nuc (Uᵀ * X) + αh * nuc (tail U X) := by
    have := mul_le_mul_of_nonneg_left (htri.trans (add_le_add_left hfr _)) hαh
    linarith
  linarith

/-- **HT-Muon converges at Muon's rate.**  Run `x (t+1) = x t - η • O t` with the head–tail direction
`O t = htDir (U t) (P t) (τ t) (m t)` computed from the EMA momentum `m t` of noisy gradients.
Assume, at every step: the frame is orthonormal, the head factor is a contraction with certificate
`α_h`, the tail scale dominates the tail (`‖T‖₂ ≤ τ`), and the tail loss is small:
`α_h ‖T‖_* - ‖T‖_F²/τ ≤ (α_h - α) ‖m‖_*`.  Then, with `β = √2`,

`avg_t ‖∇f(x t)‖_* ≤ (f x₀ - f_low)/(α η T) + L η·2/(2α) + (α+√2)/α · (μ L η √2/(1-μ) + σ)`. -/
theorem ht_muon_rate {f : Matrix s l ℝ → ℝ} {grad : Matrix s l ℝ → Matrix s l ℝ} {L : ℝ}
    (hf : (geometry (s := s) (l := l)).Smooth f grad L)
    {x m ghat : ℕ → Matrix s l ℝ} {U : ℕ → Matrix s r ℝ} {P : ℕ → Matrix r l ℝ} {τ : ℕ → ℝ}
    {η α αh μ σ flow : ℝ} (hη : 0 < η) (hα : 0 < α) (hαh : α ≤ αh) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hU : ∀ t, (U t)ᵀ * U t = 1) (hP : ∀ t, ‖P t‖ ≤ 1)
    (hPc : ∀ t, αh * nuc ((U t)ᵀ * m t) ≤ frob ((U t)ᵀ * m t) (P t))
    (hτ : ∀ t, 0 < τ t) (hT : ∀ t, ‖tail (U t) (m t)‖ ≤ τ t)
    (hloss : ∀ t, αh * nuc (tail (U t) (m t)) - (τ t)⁻¹ * frob (tail (U t) (m t)) (tail (U t) (m t))
      ≤ (αh - α) * nuc (m t))
    (hstep : ∀ t, x (t + 1) = x t - η • htDir (U t) (P t) (τ t) (m t))
    (hm0 : m 0 = ghat 0) (hm : ∀ t, m (t + 1) = μ • m t + (1 - μ) • ghat (t + 1))
    (hnoise : ∀ t, nuc (ghat t - grad (x t)) ≤ σ)
    (hlow : ∀ y, flow ≤ f y) {T : ℕ} (hT0 : 0 < T) :
    (∑ t ∈ range T, nuc (grad (x t))) / T ≤
      (f (x 0) - flow) / (α * η * T) + L * η * Real.sqrt 2 ^ 2 / (2 * α) +
        (α + Real.sqrt 2) / α * (μ * (L * η * Real.sqrt 2) / (1 - μ) + σ) := by
  have hαh0 : 0 ≤ αh := le_trans hα.le hαh
  have horacle : ∀ t, α * (geometry (s := s) (l := l)).D (m t) ≤
      (geometry (s := s) (l := l)).ip (m t) (htDir (U t) (P t) (τ t) (m t)) := by
    intro t
    have h := ht_alignment_lower (hU t) (P t) (τ t) (m t) hαh0 (hPc t)
    show α * nuc (m t) ≤ frob (m t) (htDir (U t) (P t) (τ t) (m t))
    nlinarith [hloss t, h]
  have hN : ∀ t, (geometry (s := s) (l := l)).N (htDir (U t) (P t) (τ t) (m t)) ≤ Real.sqrt 2 := by
    intro t
    show ‖htDir (U t) (P t) (τ t) (m t)‖ ≤ Real.sqrt 2
    exact htDir_norm_le_sqrt_two (hU t) (hP t) (hτ t) (hT t)
  exact (geometry (s := s) (l := l)).muon_family_rate hf hη hα (Real.sqrt_nonneg 2) hμ0 hμ1
    hstep horacle hN hm0 hm hnoise hlow hT0

end FastMuon.Spectral
