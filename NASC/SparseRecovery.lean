module

public import NASC.LowRankApproximation

/-!
# Sparse recovery

The null space property, robust recovery, the restricted isometry threshold, and
Gaussian measurements. The Gaussian law is the independent entry law of the range finder.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix BigOperators ENNReal NNReal

/-- Sum of absolute coordinates over a finite subset. -/
def restrictedL1 {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (S : Finset (Fin n)) (x : Fin n → 𝕜) : ℝ :=
  ∑ i ∈ S, ‖x i‖

/-- Euclidean length restricted to a finite subset of coordinates. -/
def restrictedL2 {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (S : Finset (Fin n)) (x : Fin n → 𝕜) : ℝ :=
  Real.sqrt (∑ i ∈ S, ‖x i‖ ^ 2)

/-- The vector is supported on at most $s$ coordinates. -/
def IsSparse {𝕜 : Type*} [Zero 𝕜] {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ s ∧ ∀ i ∉ S, x i = 0

/-- **Gap 13.12.** The strict null space inequality is necessary and sufficient
for exact basis pursuit on every sparse input. -/
theorem basisPursuit_unique_iff_nullSpaceProperty {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (s : ℕ) :
    (∀ v : Fin n → 𝕜, v ≠ 0 → A *ᵥ v = 0 →
      ∀ S : Finset (Fin n), S.card ≤ s → restrictedL1 S v < restrictedL1 Sᶜ v) ↔
    (∀ x, IsSparse s x → ∀ z, A *ᵥ z = A *ᵥ x → z ≠ x →
      restrictedL1 Finset.univ x < restrictedL1 Finset.univ z) := by
  sorry

/-- The robust Euclidean null space property with constants $\rho,\tau$. -/
def HasRobustNullSpaceProperty {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (s : ℕ) (ρ τ : ℝ) : Prop :=
  ∀ (v : Fin n → 𝕜) (S : Finset (Fin n)), S.card ≤ s →
    restrictedL2 S v ≤ ρ / Real.sqrt s * restrictedL1 Sᶜ v +
      τ * restrictedL2 Finset.univ (A *ᵥ v)

/-- **Gap 13.13.** Robust null space control yields the quantitative Euclidean
recovery error, for any choice of a support of size at most $s$. -/
theorem recovery_error_le_of_robustNullSpace {m n s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin m) (Fin n) ℂ) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hτ : 0 < τ)
    (hA : HasRobustNullSpaceProperty A s ρ τ) (x z : Fin n → ℂ)
    (S : Finset (Fin n)) (hS : S.card ≤ s) :
    restrictedL2 Finset.univ (z - x) ≤ (1 + ρ) ^ 2 / ((1 - ρ) * Real.sqrt s) *
      (restrictedL1 Finset.univ z - restrictedL1 Finset.univ x + 2 * restrictedL1 Sᶜ x) +
      (3 + ρ) * τ / (1 - ρ) * restrictedL2 Finset.univ (A *ᵥ (z - x)) := by
  sorry

/-- A restricted isometry estimate for all vectors of sparsity at most $s$. -/
def HasRestrictedIsometry {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, IsSparse s x →
    (1 - δ) * restrictedL2 Finset.univ x ^ 2 ≤ restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ∧
    restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ≤ (1 + δ) * restrictedL2 Finset.univ x ^ 2

/-- **Gap 13.14.** Restricted isometry below the $4/\sqrt{41}$ threshold implies the
robust null space property. -/
theorem hasRobustNullSpaceProperty_of_restrictedIsometry {m n s : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hs : 0 < s)
    {δ : ℝ} (h₀ : 0 ≤ δ) (hδ : δ < 4 / Real.sqrt 41)
    (hA : HasRestrictedIsometry A (2 * s) δ) :
    let d := Real.sqrt (1 - δ ^ 2) - δ / 4
    HasRobustNullSpaceProperty A s (δ / d) (Real.sqrt (1 + δ) / d) := by
  sorry

/-- **Gap 13.15.** Independent Gaussian measurements satisfy restricted isometry
with the specified failure probability and sample dimension. -/
theorem gaussianMatrixLaw_not_restrictedIsometry_le {m n s : ℕ}
    (hm : 0 < m) (hs : 0 < s) (hsn : s ≤ n) {η ε : ℝ}
    (hη : 0 < η) (hη' : η < 1) (hε : 0 < ε) (hε' : ε < 1)
    (hsize : 2 / η ^ 2 * (s * Real.log (Real.exp 1 * n / s) + Real.log (2 / ε)) ≤ m) :
    let γ := (Real.sqrt (2 * Real.log (Real.exp 1 * n / s)))⁻¹
    let δ := 2 * (1 + γ) * η + (1 + γ) ^ 2 * η ^ 2
    gaussianMatrixLaw m n (1 / (m : ℝ≥0))
      {G | ¬HasRestrictedIsometry (show Matrix (Fin m) (Fin n) ℝ from G) s δ} ≤
      ENNReal.ofReal ε := by
  sorry

end NASC
