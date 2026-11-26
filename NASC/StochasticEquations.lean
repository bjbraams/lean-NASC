module

public import NASC.MonteCarlo
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Wiener

/-!
# Stochastic equations and time stepping

Scalar strong solutions, the local Itô--Taylor expansion, Euler--Maruyama and Milstein
errors, mean-square theta stability, and a spectral approximation of stochastic convolution.
Itô and deterministic Wiener integrals use TauCeti's Brownian motion APIs.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory ProbabilityTheory Set Filter TauCeti.Probability
open scoped ENNReal NNReal Topology BigOperators

section ScalarSDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Scalar strong solution using the bundled filtration and Itô integral predicate. -/
def IsScalarStrongSDESolution (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0 → ℝ → ℝ) (X₀ : Ω → ℝ)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted ℱ X ∧ (∀ᵐ ω ∂P, Continuous fun t ↦ X t ω) ∧
    (∀ t, Integrable (fun ω ↦ X t ω ^ 2) P) ∧
    ∃ I, IsItoIntegral ℱ P W (fun t ω ↦ b t (X t ω)) I ∧
      ∀ᵐ ω ∂P, ∀ t, X t ω = X₀ ω +
        (∫ s, a s (X s ω) ∂timeMeasure t) + I t ω

/-- **Gap 23.9.** Scalar strong existence and pathwise uniqueness for globally
Lipschitz drift and diffusion with square-integrable initial data. -/
theorem exists_scalarStrongSDESolution {ℱ : Filtration ℝ≥0 mΩ} (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWcont : ∀ᵐ x ∂P, Continuous (fun t ↦ W t x))
    (hcomplete : ∀ t (s : Set Ω), P s = 0 → MeasurableSet[ℱ t] s)
    (a b : ℝ≥0 → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |a t x - a t y| + |b t x - b t y| ≤ L * |x - y|)
    (hgr : ∀ t x, |a t x| + |b t x| ≤ L * (1 + |x|))
    (X₀ : Ω → ℝ) (hX₀ : Measurable[ℱ 0] X₀) (hI : Integrable (fun ω ↦ (X₀ ω) ^ 2) P) :
    ∃ X, IsScalarStrongSDESolution ℱ P W a b X₀ X ∧
      (∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ≤ T, (∫ ω, X t ω ^ 2 ∂P) ≤ C) ∧
      ∀ Y, IsScalarStrongSDESolution ℱ P W a b X₀ Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  sorry

/-- **Gap 23.10.** The scalar Itô--Taylor expansion through the second stochastic
order. Its retained terms are the drift, the Brownian increment and the
centered-square Milstein correction. -/
theorem exists_itoTaylor_local_remainder_bound {ℱ : Filtration ℝ≥0 mΩ}
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (a b : ℝ → ℝ) (ha : ContDiff ℝ 3 a) (hb : ContDiff ℝ 3 b)
    (hbd : ∃ L, ∀ (k : ℕ), k ≤ 3 → ∀ x, |iteratedDeriv k a x| + |iteratedDeriv k b x| ≤ L)
    (x : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (hX : IsScalarStrongSDESolution ℱ P W (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ x) X) :
    ∃ C ≥ (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ≥0) 1,
      let e := fun ω ↦ X h ω - x - (h : ℝ) * a x - b x * (W h ω - W 0 ω) -
        deriv b x * b x / 2 * ((W h ω - W 0 ω) ^ 2 - h)
      (∫ ω, e ω ^ 2 ∂P) ≤ C * (h : ℝ) ^ 3 := by
  sorry

/-- **Gap 23.11.** Strong terminal error of scalar Euler--Maruyama with
time-Hölder coefficients and the specified initial mean-square error. -/
theorem exists_eulerMaruyama_strong_error_bound {ℱ : Filtration ℝ≥0 mΩ}
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (a b : ℝ≥0 → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |a t x - a t y| + |b t x - b t y| ≤ L * |x - y|)
    (hgr : ∀ t x, |a t x| + |b t x| ≤ L * (1 + |x|))
    (htime : ∀ s t x,
      |a t x - a s x| + |b t x - b s x| ≤ L * (1 + |x|) * Real.sqrt |(t : ℝ) - s|)
    (X₀ : Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (hX : IsScalarStrongSDESolution ℱ P W a b X₀ X)
    (T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C ≥ (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ,
      let h : ℝ≥0 := T / n
      let t := fun j : ℕ ↦ j * h
      (∀ j, Measurable[ℱ (t j)] (Y j)) →
      (∀ j, Integrable (fun ω ↦ Y j ω ^ 2) P) →
      (∫ ω, (X₀ ω - Y 0 ω) ^ 2 ∂P) ≤ K * h →
      (∀ j ω, Y (j + 1) ω = Y j ω + (h : ℝ) * a (t j) (Y j ω) +
        b (t j) (Y j ω) * (W (t (j + 1)) ω - W (t j) ω)) →
      (∫ ω, (X T ω - Y n ω) ^ 2 ∂P) ≤ C * h := by
  sorry

/-- **Gap 23.12.** The scalar Milstein scheme has uniform first-order
strong error on a finite time interval. -/
theorem exists_milstein_strong_error_bound {ℱ : Filtration ℝ≥0 mΩ}
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWcont : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (a b : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hLip : ∃ L, LipschitzWith L a ∧ LipschitzWith L b ∧ LipschitzWith L (fun x ↦ deriv b x * b x))
    (hbd : ∃ M, ∀ x, |iteratedDeriv 2 a x| + |iteratedDeriv 2 b x| ≤ M)
    (x₀ : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (hX : IsScalarStrongSDESolution ℱ P W (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ x₀) X) (T : ℝ≥0) :
    ∃ C ≥ (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ≥0) 1, ∀ Y : ℕ → Ω → ℝ,
      (∀ ω, Y 0 ω = x₀) →
      (∀ n ω,
        let dW := W ((n + 1 : ℕ) * h) ω - W (n * h) ω
        Y (n + 1) ω = Y n ω + (h : ℝ) * a (Y n ω) + b (Y n ω) * dW +
          deriv b (Y n ω) * b (Y n ω) / 2 * (dW ^ 2 - h)) →
      ∀ n : ℕ, n * h ≤ T → (∫ ω, (X (n * h) ω - Y n ω) ^ 2 ∂P) ≤ C * (h : ℝ) ^ 2 := by
  sorry

/-- **Gap 23.13.** The stochastic theta method has the exact mean-square
amplification factor and the corresponding stability test. -/
theorem theta_meanSquare_stability {ℱ : Filtration ℝ≥0 mΩ}
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) {h : ℝ≥0} (hh : 0 < h)
    (r σ θ x : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (hx : x ≠ 0)
    (hden : 1 - θ * r * h ≠ 0)
    (U : ℕ → Ω → ℝ) (hU : ∀ n : ℕ, Measurable[ℱ ((n : ℝ≥0) * h)] (U n))
    (hinit : ∀ ω, U 0 ω = x)
    (hstep : ∀ n ω, (1 - θ * r * h) * U (n + 1) ω =
      (1 + (1 - θ) * r * h + σ * (W ((n + 1 : ℕ) * h) ω - W (n * h) ω)) * U n ω) :
    let R := ((1 + (1 - θ) * r * h) ^ 2 + σ ^ 2 * h) / (1 - θ * r * h) ^ 2
    (∀ n, (∫ ω, U n ω ^ 2 ∂P) = R ^ n * x ^ 2) ∧
    (Tendsto (fun n ↦ ∫ ω, U n ω ^ 2 ∂P) atTop (𝓝 0) ↔
      r + σ ^ 2 / 2 + (1 - 2 * θ) * r ^ 2 * h / 2 < 0) := by
  sorry

end ScalarSDE

/-- **Gap 23.16.** Semi-implicit spectral stepping for diagonal additive
stochastic convolution, with the mean-square error summed over all modes.
The continuous and discrete modes use the same Brownian motions. -/
theorem stochasticConvolution_spectral_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℕ → ℝ≥0 → Ω → ℝ)
    (hW : ∀ j, IsPreBrownianReal (W j) P)
    (e q : ℕ → ℝ) (he : ∀ j, 0 < e j) (hmono : Monotone e) (hq : ∀ j, 0 ≤ q j)
    {ζ : ℝ} (hζ : ζ ∈ Ioc (0 : ℝ) 2)
    (htrace : Summable fun j ↦ e j ^ (ζ - 1) * q j)
    (hkern : ∀ (j : ℕ) (t : ℝ≥0), MemLp
      (fun s : ℝ≥0 ↦ Real.exp (-e j * ((t : ℝ) - s))) 2 (timeMeasure t)) :
    ∃ C ≥ (0 : ℝ), ∀ (N n : ℕ) (h : ℝ≥0), 0 < h → 1 ≤ (h : ℝ) * e N →
      let t := (n : ℝ≥0) * h
      let X := fun (j : ℕ) (ω : Ω) ↦
        Real.sqrt (q j) * (hW j).wienerIntegral t ((hkern j t).toLp _) ω
      let U := fun (j : ℕ) (ω : Ω) ↦ if j < N then
        Real.sqrt (q j) * ∑ i ∈ Finset.range n,
          (1 + h * e j)⁻¹ ^ (n - i) * (W j ((i + 1 : ℕ) * h) ω - W j (i * h) ω)
        else 0
      (∑' j, ∫ ω, (X j ω - U j ω) ^ 2 ∂P) ≤ C * (h : ℝ) ^ ζ * ∑' j, e j ^ (ζ - 1) * q j := by
  sorry

end NASC
