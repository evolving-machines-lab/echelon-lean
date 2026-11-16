import Mathlib

/-!
# Comparator challenge: `FastMuon.Spectral.ht_muon_rate` (`FastMuon/Spectral.lean`)

Imports only Mathlib.  Copied verbatim from the source (and checked constant-for-constant by
`lake comparator`, proofs inside definitions included):

* `Geometry`, `Geometry.Smooth` from `FastMuon/Certificate.lean`;
* `tail`, `htDir`, `frob` from `FastMuon/HeadTail.lean`;
* `frobBilin`, `frobCLM`, `nuc` (the dual of the spectral norm), `holder` (Hölder's inequality, used
  inside `geometry`), `geometry` (Muon's geometry on `Matrix s l ℝ`) and their `@[simp]` /
  `rfl` lemmas from `FastMuon/Spectral.lean`.
-/

namespace FastMuon

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

end Geometry

end FastMuon

set_option linter.unusedSectionVars false

namespace FastMuon.HeadTail

open Matrix
open scoped Matrix.Norms.L2Operator

variable {s l r : Type*} [Fintype s] [Fintype l] [Fintype r]
  [DecidableEq s] [DecidableEq l] [DecidableEq r]

/-- The tail of `X` outside the column span of `U`. -/
def tail (U : Matrix s r ℝ) (X : Matrix s l ℝ) : Matrix s l ℝ := X - U * (Uᵀ * X)

/-- The head–tail direction `U P + τ⁻¹ • tail U X`. -/
noncomputable def htDir (U : Matrix s r ℝ) (P : Matrix r l ℝ) (τ : ℝ) (X : Matrix s l ℝ) :
    Matrix s l ℝ :=
  U * P + τ⁻¹ • tail U X

/-- Frobenius pairing `⟪A, B⟫ = tr (Aᵀ B)`. -/
def frob (A B : Matrix s l ℝ) : ℝ := (Aᵀ * B).trace

end FastMuon.HeadTail

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

/-- **HT-Muon converges at Muon's rate.**  With `β = √2`,
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
  sorry

end FastMuon.Spectral
