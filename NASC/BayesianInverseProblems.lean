module

public import NASC.Regularization
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic

/-!
# Bayesian inverse problems

Gaussian prior coordinates, observation likelihoods, Hellinger stability and variational
MAP estimators. The linear-Gaussian update uses Mathlib's multivariate Gaussian law.
-/

public section

noncomputable section

namespace NASC

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix BigOperators Topology

/-- **Gap 22.11.** An infinite Cameron--Martin coordinate range is null
under a Gaussian law with independent nondegenerate normalized coordinates. -/
theorem measure_cameronMartin_coordinates_eq_zero {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (Z : ℕ → H → ℝ)
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hlaw : ∀ j, μ.map (Z j) = gaussianReal 0 1) :
    μ {x | Summable (fun j ↦ (Z j x) ^ 2)} = 0 := by
  sorry

/-- Likelihood of a scalar potential, before normalization. -/
def likelihood {X : Type*} (Φ : X → ℝ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Φ x))

/-- Reweight a prior by the exponential of the negative potential and normalize. -/
def posteriorMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X) (Φ : X → ℝ) :
    Measure X :=
  (∫⁻ x, likelihood Φ x ∂μ)⁻¹ • μ.withDensity (likelihood Φ)

/-- Quadratic observation potential of a positive definite covariance matrix. -/
def gaussianObservationPotential {q : ℕ} (Γ : Matrix (Fin q) (Fin q) ℝ)
    (z : EuclideanSpace ℝ (Fin q)) : ℝ :=
  inner ℝ z ((Γ⁻¹).toEuclideanLin z) / 2

/-- **Gap 22.12.** With independent nondegenerate Gaussian noise, the normalized
likelihood disintegrates the joint law of observation and state. -/
theorem gaussian_posterior_disintegrates {X : Type*} [MeasurableSpace X]
    {q : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (G : X → EuclideanSpace ℝ (Fin q)) (hG : Measurable G)
    (Γ : Matrix (Fin q) (Fin q) ℝ) (hΓ : Γ.PosDef) :
    let joint := (μ.prod (multivariateGaussian 0 Γ)).map
      (fun p : X × EuclideanSpace ℝ (Fin q) ↦ (G p.1 + p.2, p.1))
    let Φ := fun y x ↦ gaussianObservationPotential Γ (y - G x)
    let π := fun y ↦ posteriorMeasure μ (Φ y)
    (∀ y, 0 < (∫⁻ x, likelihood (Φ y) x ∂μ) ∧ (∫⁻ x, likelihood (Φ y) x ∂μ) ≤ 1) ∧
    ∀ (A : Set (EuclideanSpace ℝ (Fin q))) (B : Set X),
      MeasurableSet A → MeasurableSet B →
      Measurable (fun y ↦ π y B) ∧
        joint (A ×ˢ B) = ∫⁻ y in A, π y B ∂(joint.map Prod.fst) := by
  sorry

/-- **Gap 22.13.** The quantitative likelihood conditions and a Fernique bound
give local Lipschitz continuity of the posterior in Hellinger distance.
The conclusion is written for the squared distance. -/
theorem hellingerSq_le_of_exponential_moment {X Y : Type*}
    [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (Φ : X → Y → ℝ)
    (hΦ : ∀ y, Measurable (fun x ↦ Φ x y))
    (hmom : ∃ a > (0 : ℝ), Integrable (fun x : X ↦ Real.exp (a * ‖x‖ ^ 2)) μ)
    (hlow : ∀ ε r : ℝ, 0 < ε → 0 < r →
      ∃ M : ℝ, ∀ x y, ‖y‖ ≤ r → M - ε * ‖x‖ ^ 2 ≤ Φ x y)
    (hupp : ∀ r > (0 : ℝ), ∃ M : ℝ, ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → Φ x y ≤ M)
    (hLip : ∀ ε r : ℝ, 0 < ε → 0 < r →
      ∃ C ≥ (0 : ℝ), ∀ x y z, ‖y‖ ≤ r → ‖z‖ ≤ r →
        |Φ x y - Φ x z| ≤ C * Real.exp (ε * ‖x‖ ^ 2) * ‖y - z‖)
    {r : ℝ} (hr : 0 < r) :
    let Z := fun y ↦ ∫ x, Real.exp (-Φ x y) ∂μ
    let rootDensity := fun y x ↦ Real.sqrt (Real.exp (-Φ x y) / Z y)
    ∃ C ≥ (0 : ℝ), ∀ y z, ‖y‖ ≤ r → ‖z‖ ≤ r →
      0 < Z y ∧ 0 < Z z ∧
      (∫ x, (rootDensity y x - rootDensity z x) ^ 2 ∂μ) / 2 ≤ C * ‖y - z‖ ^ 2 := by
  sorry

/-- **Gap 22.14.** A continuous, subquadratically bounded potential on the
compactly embedded Cameron--Martin space admits a MAP minimizer. Every
minimizing sequence has a strongly convergent subsequence. -/
theorem exists_mapEstimator_compactEmbedding {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : E →L[ℝ] X) (hJ : IsCompactOperator J)
    (Φ : X → ℝ) (hΦ : Continuous Φ)
    (hlow : ∀ ε > (0 : ℝ), ∃ M, ∀ x, M - ε * ‖x‖ ^ 2 ≤ Φ x) :
    let I := fun x : E ↦ ‖x‖ ^ 2 / 2 + Φ (J x)
    ∃ x : E, (∀ y, I x ≤ I y) ∧ ∀ u : ℕ → E,
      Tendsto (fun n ↦ I (u n)) atTop (𝓝 (I x)) →
      ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 y) ∧ I y = I x := by
  sorry

/-- **Gap 22.15.** One prediction and observation step of the Kalman recursion,
including the posterior mean and covariance in information form. -/
theorem kalman_posterior_eq_gaussian {n p : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin p) (Fin n) ℝ)
    (C Q : Matrix (Fin n) (Fin n) ℝ) (Γ : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.PosDef) (hQ : Q.PosDef) (hΓ : Γ.PosDef)
    (m : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    let pred := (multivariateGaussian m C).prod (multivariateGaussian 0 Q)
    let μ := pred.map (fun p ↦ M.toEuclideanLin p.1 + p.2)
    let Ĉ := M * C * Mᵀ + Q
    let Cnew := (Ĉ⁻¹ + Hᵀ * Γ⁻¹ * H)⁻¹
    let mnew := Cnew.toEuclideanLin
      ((Ĉ⁻¹).toEuclideanLin (M.toEuclideanLin m) + (Hᵀ * Γ⁻¹).toEuclideanLin y)
    μ = multivariateGaussian (M.toEuclideanLin m) Ĉ ∧
    Cnew.PosDef ∧
    posteriorMeasure μ (fun x ↦ gaussianObservationPotential Γ (y - H.toEuclideanLin x)) =
      multivariateGaussian mnew Cnew := by
  sorry

end NASC
