module

public import NASC.FiniteElements
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Layer potentials and boundary elements

Single-layer jumps, the fractional trace estimate and coercivity of the Newton kernel,
and stable Galerkin approximation for compact perturbations of coercive forms.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set Filter TopologicalSpace TauCeti
open scoped ENNReal NNReal Topology Interval

/-- The planar logarithmic single-layer potential on the radius-$R$ circle. -/
def circleSingleLayer (R : ℝ) (φ : ℝ → ℝ) (z : ℂ) : ℝ :=
  -(R / (2 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖z - (R : ℂ) * Complex.exp (t * Complex.I)‖ * φ t

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

/-- Newton single-layer kernel in three dimensions, integrated over surface measure. -/
def newtonSingleLayer (σ : Measure X) (φ : X → ℝ) (x : X) : ℝ :=
  ∫ y, φ y / (4 * Real.pi * dist x y) ∂σ

/-- The full squared norm of a trace of order one-half on a two-dimensional surface. -/
def boundaryHhalfNormSq (σ : Measure X) (u : X → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂σ) + fractionalBoundaryEnergy σ 2 u

/-- The dual norm determined by unit fractional boundary tests. The extended-valued
version also applies before boundedness of the functional has been checked. -/
def boundaryHminusHalfNorm (σ : Measure X) (φ : X → ℝ) : ℝ≥0∞ :=
  ⨆ u : X → ℝ, ⨆ (_ : Continuous u ∧ boundaryHhalfNormSq σ u ≤ 1),
    ENNReal.ofReal |∫ x, φ x * u x ∂σ|

end NewtonKernel

/-- **Gap 21.13.** The Laplace single-layer mapping at trace order one-half on
a bounded Lipschitz boundary, estimated on continuous densities. -/
theorem exists_newtonSingleLayer_trace_bound {L : ℝ≥0}
    {Ω : Opens (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2))))) :
    let σ := (μHE[2] : Measure (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))))
    ∃ C ≥ (0 : ℝ), ∀ φ : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)) → ℝ, Continuous φ →
      boundaryHhalfNormSq σ (newtonSingleLayer σ φ) ≤
        ENNReal.ofReal C * boundaryHminusHalfNorm σ φ ^ 2 := by
  sorry

/-- **Gap 21.14.** The three-dimensional Newton single-layer form is elliptic
in the dual fractional trace norm, on continuous densities. -/
theorem exists_newtonSingleLayer_elliptic_bound {L : ℝ≥0}
    {Ω : Opens (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2))))) :
    let σ := (μHE[2] : Measure (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)))))
    ∃ c > (0 : ℝ), ∀ φ : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2)) → ℝ, Continuous φ →
      c * (boundaryHminusHalfNorm σ φ).toReal ^ 2 ≤ ∫ x, φ x * newtonSingleLayer σ φ x ∂σ := by
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
