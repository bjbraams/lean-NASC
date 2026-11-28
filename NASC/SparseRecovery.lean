module

public import NASC.Support.GaussianMatrix

/-!
# Sparse recovery

The null space property, robust recovery, the restricted isometry threshold, and
Gaussian measurements. The Gaussian law is the independent entry law of the range finder.
Coordinates are indexed by an arbitrary finite type `ι` and scalars lie in an `RCLike` field;
the Gaussian measurement theorem is stated for real matrices with `Fin` indices.

## Main definitions

* `NASC.restrictedL1`, `NASC.restrictedL2`: the `ℓ¹` and `ℓ²` norms over a set of coordinates.
* `NASC.IsSparse`: at most `s` nonzero coordinates.
* `NASC.HasNullSpaceProperty`: the strict null space property of order `s`.
* `NASC.HasRobustNullSpaceProperty`: the robust `ℓ²` null space property with constants `ρ, τ`.
* `NASC.HasRestrictedIsometry`: the restricted isometry property of order `s` with constant `δ`.

## Main results

* `NASC.nullSpaceProperty_iff_basisPursuit_unique`: exact recovery by basis pursuit.
* `NASC.recovery_error_le_of_robustNullSpace`: the robust recovery error bound.
* `NASC.hasRobustNullSpaceProperty_of_restrictedIsometry`: the `4/√41` threshold.
* `NASC.gaussianMatrixLaw_not_restrictedIsometry_le`: Gaussian matrices have the restricted
  isometry property with high probability.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix ENNReal NNReal

variable {𝕜 ι κ : Type*}

/-- Sum of absolute coordinates over a finite subset. -/
def restrictedL1 [RCLike 𝕜] (S : Finset ι) (x : ι → 𝕜) : ℝ :=
  ∑ i ∈ S, ‖x i‖

/-- The defining formula of `restrictedL1`. -/
theorem restrictedL1_def [RCLike 𝕜] (S : Finset ι) (x : ι → 𝕜) :
    restrictedL1 S x = ∑ i ∈ S, ‖x i‖ := by
  rfl

/-- Euclidean length restricted to a finite subset of coordinates. -/
def restrictedL2 [RCLike 𝕜] (S : Finset ι) (x : ι → 𝕜) : ℝ :=
  Real.sqrt (∑ i ∈ S, ‖x i‖ ^ 2)

/-- The defining formula of `restrictedL2`. -/
theorem restrictedL2_def [RCLike 𝕜] (S : Finset ι) (x : ι → 𝕜) :
    restrictedL2 S x = Real.sqrt (∑ i ∈ S, ‖x i‖ ^ 2) := by
  rfl

/-- The vector is supported on at most $s$ coordinates. -/
def IsSparse [Zero 𝕜] (s : ℕ) (x : ι → 𝕜) : Prop :=
  ∃ S : Finset ι, S.card ≤ s ∧ ∀ i ∉ S, x i = 0

/-- The defining property of `IsSparse`. -/
theorem isSparse_iff [Zero 𝕜] (s : ℕ) (x : ι → 𝕜) :
    IsSparse s x ↔ ∃ S : Finset ι, S.card ≤ s ∧ ∀ i ∉ S, x i = 0 :=
  Iff.rfl

/-- The strict null space property of order $s$: on every nonzero kernel vector, the `ℓ¹`
mass on any set of at most $s$ coordinates is smaller than the mass on its complement. -/
def HasNullSpaceProperty [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι 𝕜) (s : ℕ) : Prop :=
  ∀ v : ι → 𝕜, v ≠ 0 → A *ᵥ v = 0 →
    ∀ S : Finset ι, S.card ≤ s → restrictedL1 S v < restrictedL1 Sᶜ v

/-- The defining property of `HasNullSpaceProperty`. -/
theorem hasNullSpaceProperty_iff [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι 𝕜) (s : ℕ) :
    HasNullSpaceProperty A s ↔ ∀ v : ι → 𝕜, v ≠ 0 → A *ᵥ v = 0 →
      ∀ S : Finset ι, S.card ≤ s → restrictedL1 S v < restrictedL1 Sᶜ v :=
  Iff.rfl

/-- **Gap 13.12.** The strict null space property is necessary and sufficient
for exact basis pursuit on every sparse input. -/
theorem nullSpaceProperty_iff_basisPursuit_unique [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι 𝕜) (s : ℕ) :
    HasNullSpaceProperty A s ↔
      ∀ x, IsSparse s x → ∀ z, A *ᵥ z = A *ᵥ x → z ≠ x →
        restrictedL1 Finset.univ x < restrictedL1 Finset.univ z := by
  sorry

/-- The robust Euclidean null space property with constants $\rho,\tau$. -/
def HasRobustNullSpaceProperty [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι 𝕜) (s : ℕ) (ρ τ : ℝ) : Prop :=
  ∀ (v : ι → 𝕜) (S : Finset ι), S.card ≤ s →
    restrictedL2 S v ≤ ρ / Real.sqrt s * restrictedL1 Sᶜ v +
      τ * restrictedL2 Finset.univ (A *ᵥ v)

/-- The defining property of `HasRobustNullSpaceProperty`. -/
theorem hasRobustNullSpaceProperty_iff [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι 𝕜) (s : ℕ) (ρ τ : ℝ) :
    HasRobustNullSpaceProperty A s ρ τ ↔ ∀ (v : ι → 𝕜) (S : Finset ι), S.card ≤ s →
      restrictedL2 S v ≤ ρ / Real.sqrt s * restrictedL1 Sᶜ v +
        τ * restrictedL2 Finset.univ (A *ᵥ v) :=
  Iff.rfl

/-- **Gap 13.13.** Robust null space control yields the quantitative Euclidean
recovery error, for any choice of a support of size at most $s$. -/
theorem recovery_error_le_of_robustNullSpace [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [Fintype κ] {s : ℕ} (hs : 0 < s)
    (A : Matrix κ ι 𝕜) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hτ : 0 < τ)
    (hA : HasRobustNullSpaceProperty A s ρ τ) (x z : ι → 𝕜)
    (S : Finset ι) (hS : S.card ≤ s) :
    restrictedL2 Finset.univ (z - x) ≤ (1 + ρ) ^ 2 / ((1 - ρ) * Real.sqrt s) *
      (restrictedL1 Finset.univ z - restrictedL1 Finset.univ x + 2 * restrictedL1 Sᶜ x) +
      (3 + ρ) * τ / (1 - ρ) * restrictedL2 Finset.univ (A *ᵥ (z - x)) := by
  sorry

/-- A restricted isometry estimate for all vectors of sparsity at most $s$. -/
def HasRestrictedIsometry [RCLike 𝕜] [Fintype ι] [Fintype κ]
    (A : Matrix κ ι 𝕜) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, IsSparse s x →
    (1 - δ) * restrictedL2 Finset.univ x ^ 2 ≤ restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ∧
    restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ≤ (1 + δ) * restrictedL2 Finset.univ x ^ 2

/-- The defining property of `HasRestrictedIsometry`. -/
theorem hasRestrictedIsometry_iff [RCLike 𝕜] [Fintype ι] [Fintype κ]
    (A : Matrix κ ι 𝕜) (s : ℕ) (δ : ℝ) :
    HasRestrictedIsometry A s δ ↔ ∀ x, IsSparse s x →
      (1 - δ) * restrictedL2 Finset.univ x ^ 2 ≤ restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ∧
      restrictedL2 Finset.univ (A *ᵥ x) ^ 2 ≤ (1 + δ) * restrictedL2 Finset.univ x ^ 2 :=
  Iff.rfl

/-- **Gap 13.14.** Restricted isometry below the $4/\sqrt{41}$ threshold implies the
robust null space property. At `s = 0` only `S = ∅` occurs and the conclusion is trivial. -/
theorem hasRobustNullSpaceProperty_of_restrictedIsometry [RCLike 𝕜] [Fintype ι]
    [DecidableEq ι] [Fintype κ] {s : ℕ} (A : Matrix κ ι 𝕜)
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
      {G | ¬HasRestrictedIsometry (Matrix.of G) s δ} ≤ ENNReal.ofReal ε := by
  sorry

end NASC
