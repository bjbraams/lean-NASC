module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Gaussian measures and stochastic Galerkin approximation

Covariance trace, Gaussian shifts, Karhunen--Loève truncation and stochastic Galerkin
solvability. The covariance statements use Mathlib's uncentered operator on the centered law.

## Main results

* `NASC.IsGaussian.covariance_trace_eq`: the covariance of a Gaussian measure is trace class,
  with trace the centered second moment.
* `NASC.IsGaussian.shift_equivalent_iff_squareRoot_range`: the Cameron–Martin dichotomy.
* `NASC.existsUnique_gaussian_of_summable_spectrum`: Gaussian measures with prescribed mean and
  trace-class covariance.
* `NASC.karhunenLoeve_projection_error_sq`: the Karhunen–Loève truncation error.
* `NASC.existsUnique_stochasticGalerkin`: well-posedness of stochastic Galerkin.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

section Covariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **Gap 24.13.** Covariance of a Gaussian measure has finite trace, equal to
the centered second moment in any countable orthonormal basis. -/
theorem IsGaussian.covariance_trace_eq {ι : Type*} [Countable ι]
    (μ : Measure H) [IsGaussian μ] (b : HilbertBasis ι ℝ H) :
    let m := ∫ x : H, x ∂μ
    let C := covarianceOperator (μ.map fun x : H ↦ x - m)
    (∀ x, 0 ≤ inner ℝ (C x) x) ∧
      Summable (fun i ↦ inner ℝ (C (b i)) (b i)) ∧
      (∑' i, inner ℝ (C (b i)) (b i)) = ∫ x, ‖x - m‖ ^ 2 ∂μ := by
  sorry

/-- **Gap 24.13.** The Cameron--Martin dichotomy in a covariance eigenbasis.
The square-root range is expressed by the existence of square-summable preimage
coordinates via a vector of the Hilbert space. The eigenvalues `σ i` are nonnegative
because the covariance is positive. -/
theorem IsGaussian.shift_equivalent_iff_squareRoot_range {ι : Type*} [Countable ι]
    (μ : Measure H) [IsGaussian μ] (b : HilbertBasis ι ℝ H) (σ : ι → ℝ)
    (hC : ∀ i, covarianceOperator (μ.map fun x : H ↦ x - ∫ y : H, y ∂μ) (b i) = σ i • b i)
    (h : H) :
    let μh := μ.map fun x : H ↦ x + h
    let E := ∃ v : H, ∀ i, inner ℝ h (b i) = Real.sqrt (σ i) * inner ℝ v (b i)
    ((μh.AbsolutelyContinuous μ ∧ μ.AbsolutelyContinuous μh) ↔ E) ∧
      (¬E → μh.MutuallySingular μ) := by
  sorry

/-- **Gap 24.13.** A nonnegative summable diagonal covariance on a Hilbert basis
determines a unique Borel Gaussian law with the prescribed mean. -/
theorem existsUnique_gaussian_of_summable_spectrum {ι : Type*} [Countable ι]
    (m : H) (C : H →L[ℝ] H) (b : HilbertBasis ι ℝ H) (σ : ι → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hs : Summable σ) (hC : ∀ i, C (b i) = σ i • b i) :
    ∃! μ : Measure H, IsGaussian μ ∧ (∫ x : H, x ∂μ) = m ∧
      covarianceOperator (μ.map (fun x : H ↦ x - m)) = C := by
  sorry

/-- **Gap 24.14.** Karhunen--Loève covariance truncation has exact mean-square
error equal to the omitted eigenvalue sum, for finite or countable index sets. -/
theorem karhunenLoeve_projection_error_sq {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : Ω → H) (hL : MemLp u 2 P)
    (b : HilbertBasis ι ℝ H) (ν : ι → ℝ)
    (hC : ∀ i, covarianceOperator (P.map fun x ↦ u x - ∫ y, u y ∂P) (b i) = ν i • b i)
    (S : Finset ι) :
    let m := ∫ x, u x ∂P
    Summable ν ∧
      (∫ x, ‖(u x - m) - ∑ i ∈ S, (inner ℝ (u x - m) (b i)) • b i‖ ^ 2 ∂P) =
        ∑' i, if i ∈ S then 0 else ν i := by
  sorry

end Covariance

/-- **Gap 24.16.** Coercive stochastic Galerkin on a closed subspace of the
Bochner space has a unique solution. The coefficients and forcing are
integrated against the same probability law. -/
theorem existsUnique_stochasticGalerkin {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → V →L[ℝ] StrongDual ℝ V) (hA : AEStronglyMeasurable A P)
    (F : Lp (StrongDual ℝ V) 2 P)
    {α M : ℝ} (hα : 0 < α)
    (hbound : ∀ᵐ ω ∂P, ‖A ω‖ ≤ M ∧ ∀ v, α * ‖v‖ ^ 2 ≤ A ω v v)
    (S : Submodule ℝ (Lp V 2 P)) (hS : IsClosed (S : Set (Lp V 2 P))) :
    ∃! u : S, ∀ v : S,
      (∫ ω, A ω (u.val ω) (v.val ω) ∂P) = ∫ ω, F ω (v.val ω) ∂P := by
  sorry

end NASC
