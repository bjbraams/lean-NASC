module

public import NASC.FiniteElements
public import NASC.Support.BestApproximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Layer potentials and boundary elements

Single-layer jumps, the fractional trace estimate and coercivity of the Newton kernel,
and stable Galerkin approximation for compact perturbations of coercive forms.

## Notation

`ℝ³` is local notation for `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2))`, the Euclidean space in
which TauCeti's Lipschitz domains and traces are set up; its boundaries carry
`NASC.frontierMeasure`.

## Main definitions

* `NASC.circleSingleLayer`: the logarithmic single-layer potential of a circle.
* `NASC.newtonSingleLayer`: the Newton single-layer potential of a surface measure.
* `NASC.boundaryHhalfNormSq`, `NASC.boundaryHminusHalfNorm`: the boundary `H^{1/2}` norm and
  its dual norm, both extended-valued.

## Main results

* `NASC.exists_circleSingleLayer_normal_jump`: the jump relation of the normal derivative.
* `NASC.exists_newtonSingleLayer_trace_bound`: mapping property `H^{-1/2} → H^{1/2}`.
* `NASC.exists_newtonSingleLayer_elliptic_bound`: ellipticity of the single-layer form.
* `NASC.eventually_galerkin_wellPosed_compactPerturbation`: Galerkin stability for compact
  perturbations of coercive operators.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set Filter TopologicalSpace TauCeti
open scoped ENNReal NNReal Topology Interval

local notation "ℝ³" => WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2))

/-- The planar logarithmic single-layer potential on the radius-$R$ circle, with the density
`φ` given as a function of the angle. -/
def circleSingleLayer (R : ℝ) (φ : ℝ → ℝ) (z : ℂ) : ℝ :=
  -(R / (2 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖z - (R : ℂ) * Complex.exp (t * Complex.I)‖ * φ t

/-- The defining formula of `NASC.circleSingleLayer`. -/
theorem circleSingleLayer_def (R : ℝ) (φ : ℝ → ℝ) (z : ℂ) :
    circleSingleLayer R φ z = -(R / (2 * Real.pi)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖z - (R : ℂ) * Complex.exp (t * Complex.I)‖ * φ t :=
  (rfl)

/-- **Gap 21.12.** The exterior minus interior radial derivative of the circle
single layer is minus its density. -/
theorem exists_circleSingleLayer_normal_jump {R : ℝ} (hR : 0 < R) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hper : Function.Periodic φ (2 * Real.pi)) (θ : ℝ) :
    let u := fun r : ℝ ↦ circleSingleLayer R φ ((r : ℂ) * Complex.exp (θ * Complex.I))
    ∃ a b : ℝ, Tendsto (deriv u) (𝓝[<] R) (𝓝 a) ∧
      Tendsto (deriv u) (𝓝[>] R) (𝓝 b) ∧ b - a = -φ θ := by
  sorry

section NewtonKernel

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- The single-layer potential `x ↦ ∫ φ y / (4π dist x y) dσ(y)` with the Newton kernel of
three-dimensional space, defined for any measure `σ` on a pseudometric space. It is used with
surface measure on a boundary in `ℝ³`. At `y = x` the kernel takes the junk value `0`, which
does not matter when `σ` has no atoms. -/
def newtonSingleLayer (σ : Measure X) (φ : X → ℝ) (x : X) : ℝ :=
  ∫ y, φ y / (4 * Real.pi * dist x y) ∂σ

/-- The defining formula of `NASC.newtonSingleLayer`. -/
theorem newtonSingleLayer_def (σ : Measure X) (φ : X → ℝ) (x : X) :
    newtonSingleLayer σ φ x = ∫ y, φ y / (4 * Real.pi * dist x y) ∂σ :=
  (rfl)

/-- The full squared norm of a trace of order one-half on a two-dimensional surface. -/
def boundaryHhalfNormSq (σ : Measure X) (u : X → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂σ) + fractionalBoundaryEnergy σ 2 u

/-- The defining formula of `NASC.boundaryHhalfNormSq`. -/
theorem boundaryHhalfNormSq_def (σ : Measure X) (u : X → ℝ) :
    boundaryHhalfNormSq σ u =
      (∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂σ) + fractionalBoundaryEnergy σ 2 u :=
  (rfl)

/-- The dual norm determined by unit fractional boundary tests. The extended-valued
version also applies before boundedness of the functional has been checked; it is `⊤` when the
pairing is unbounded on the unit ball. -/
def boundaryHminusHalfNorm (σ : Measure X) (φ : X → ℝ) : ℝ≥0∞ :=
  ⨆ u : X → ℝ, ⨆ (_ : Continuous u ∧ boundaryHhalfNormSq σ u ≤ 1),
    ENNReal.ofReal |∫ x, φ x * u x ∂σ|

/-- The defining formula of `NASC.boundaryHminusHalfNorm`. -/
theorem boundaryHminusHalfNorm_def (σ : Measure X) (φ : X → ℝ) :
    boundaryHminusHalfNorm σ φ = ⨆ u : X → ℝ, ⨆ (_ : Continuous u ∧ boundaryHhalfNormSq σ u ≤ 1),
      ENNReal.ofReal |∫ x, φ x * u x ∂σ| :=
  (rfl)

end NewtonKernel

/-- **Gap 21.13.** The Laplace single-layer mapping at trace order one-half on
a bounded Lipschitz boundary, estimated on continuous densities. -/
theorem exists_newtonSingleLayer_trace_bound {L : ℝ≥0} {Ω : Opens ℝ³}
    (hΩ : (Ω : Set ℝ³).IsLipschitzDomainWith L) (hb : Bornology.IsBounded (Ω : Set ℝ³)) :
    ∃ C ≥ (0 : ℝ), ∀ φ : ℝ³ → ℝ, Continuous φ →
      boundaryHhalfNormSq (frontierMeasure (Ω : Set ℝ³))
          (newtonSingleLayer (frontierMeasure (Ω : Set ℝ³)) φ) ≤
        ENNReal.ofReal C * boundaryHminusHalfNorm (frontierMeasure (Ω : Set ℝ³)) φ ^ 2 := by
  sorry

/-- **Gap 21.14.** The three-dimensional Newton single-layer form is elliptic
in the dual fractional trace norm, on continuous densities. The bound is stated in `ℝ≥0∞`, so
it also gives finiteness of the dual norm. -/
theorem exists_newtonSingleLayer_elliptic_bound {L : ℝ≥0} {Ω : Opens ℝ³}
    (hΩ : (Ω : Set ℝ³).IsLipschitzDomainWith L) (hb : Bornology.IsBounded (Ω : Set ℝ³)) :
    ∃ c > (0 : ℝ), ∀ φ : ℝ³ → ℝ, Continuous φ →
      ENNReal.ofReal c * boundaryHminusHalfNorm (frontierMeasure (Ω : Set ℝ³)) φ ^ 2 ≤
        ENNReal.ofReal (∫ x, φ x * newtonSingleLayer (frontierMeasure (Ω : Set ℝ³)) φ x
          ∂frontierMeasure (Ω : Set ℝ³)) := by
  sorry

/-- **Gap 21.15.** A compact perturbation of a coercive form gives eventually
well-posed Galerkin equations and a uniform quasi-optimal error bound. -/
theorem eventually_galerkin_wellPosed_compactPerturbation {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A D : H →L[ℂ] H) (hD : IsCompactOperator D)
    {α : ℝ} (hα : 0 < α) (hA : ∀ v, α * ‖v‖ ^ 2 ≤ ‖inner ℂ v (A v)‖)
    (hinj : Function.Injective (A + D))
    (V : ℕ → Submodule ℂ H) (hV : ∀ n, FiniteDimensional ℂ (V n))
    (hdense : ∀ u, Tendsto (fun n ↦ bestApproximationError (V n : Set H) u) atTop (𝓝 0)) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ n in atTop, ∀ u : H,
      ∃! uh : V n, (∀ v : V n, inner ℂ v.val ((A + D) (u - uh.val)) = 0) ∧
        ‖u - uh.val‖ ≤ C * bestApproximationError (V n : Set H) u := by
  sorry

end NASC
