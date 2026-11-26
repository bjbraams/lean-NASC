module

public import NASC.Galerkin
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier

/-!
# Sobolev estimates and finite element spaces

Fractional boundary traces, convex-domain regularity, polynomial approximation, and
interpolation and divergence properties of finite elements. The Sobolev spaces, weak
Dirichlet problem and bounded boundary trace use TauCeti's corresponding APIs.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set TopologicalSpace TauCeti
open scoped ENNReal NNReal BigOperators Matrix Interval Matrix.Norms.L2Operator

/-- A fractional boundary seminorm to the power two, written as a nonnegative integral
so that the membership condition excludes divergent integrals. -/
def fractionalBoundaryEnergy {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (σ : Measure E) (d : ℕ) (g : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (∫⁻ y, ENNReal.ofReal (|g x - g y| ^ 2 / dist x y ^ (d + 1)) ∂σ) ∂σ

/-- **Gap 18.6.** The image of the first Sobolev trace is the boundary
Slobodeckij space of order one-half. -/
theorem range_frontierTrace_eq_fractionalBoundary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    let σ := (μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))
    range (TauCeti.W1p.frontierTrace (p := 2) (by norm_num) hΩ hb) =
      {g : Lp ℝ 2 σ | fractionalBoundaryEnergy σ (Module.finrank ℝ E) g < ⊤} := by
  sorry

/-- **Gap 18.6.** The bounded trace also controls the fractional boundary
seminorm with a constant depending on the Lipschitz domain. -/
theorem exists_frontierTrace_fractionalBound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    let σ := (μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))
    ∃ C ≥ (0 : ℝ), ∀ u : W1p volume Ω 2,
      fractionalBoundaryEnergy σ (Module.finrank ℝ E)
        (TauCeti.W1p.frontierTrace (p := 2) (by norm_num) hΩ hb u) ≤
          ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  sorry

/-- **Gap 18.7.** A Lipschitz uniformly elliptic coefficient on a bounded convex
domain gives global second weak derivatives for the homogeneous Dirichlet solution. -/
theorem exists_Wkp_two_of_convex_weakDirichlet {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ (Fin d))}
    (hcv : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hLip : ∃ M, LipschitzOnWith M A Ω)
    (hsym : ∀ x ∈ Ω, (A x).IsHermitian) {α : ℝ} (hα : 0 < α)
    (hell : ∀ x ∈ Ω, ∀ v : Fin d → ℝ, α * (∑ i, v i ^ 2) ≤ dotProduct v (A x *ᵥ v)) :
    ∃ C ≥ (0 : ℝ), ∀ (f : Lp ℝ 2 (μ.restrict Ω)) (u : W1p0 μ Ω 2),
      TauCeti.PDE.IsWeakSolutionDirichlet A 0 0 f u →
      ∃ v : Wkp μ Ω 2 2, Wkp.value 2 v = W1p.value (u : W1p μ Ω 2) ∧ ‖v‖ ≤ C * ‖f‖ := by
  sorry

/-- **Gap 18.9.** The Bramble--Hilbert approximation on a bounded convex
reference domain in the weak Sobolev norm. -/
theorem exists_poly_sobolev_error_le_of_convex {d k : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ (Fin d))}
    (hcv : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ C ≥ (0 : ℝ), ∀ u : Wkp μ Ω 2 (k + 1),
      ∃ (P : MvPolynomial (Fin d) ℝ) (p : Wkp μ Ω 2 (k + 1)), P.totalDegree ≤ k ∧
        (Wkp.value (k + 1) p =ᵐ[μ.restrict Ω] fun x ↦ MvPolynomial.eval x.ofLp P) ∧
        ‖u - p‖ ≤ C * ‖Wkp.iteratedGradient k u‖ := by
  sorry

/-- **Gap 18.10.** Scaled interpolation of a one-dimensional affine element,
for fixed reference nodes and derivative error measured in the supremum norm. -/
theorem exists_scaled_lagrange_derivative_bound {k r m : ℕ}
    (s : Fin (k + 1) → ℝ) (hinj : Function.Injective s) (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) (hr' : r ≤ k + 1) (hm : m ≤ r) :
    ∃ C ≥ (0 : ℝ), ∀ (a h : ℝ), 0 < h → ∀ f : ℝ → ℝ, ContDiff ℝ r f →
      let x := fun i ↦ a + h * s i
      let P := Lagrange.interpolate Finset.univ x (f ∘ x)
      ∀ y ∈ Icc a (a + h), |iteratedDeriv m (fun z ↦ f z - P.eval z) y| ≤
        C * h ^ (r - m) * intervalError a (a + h) (iteratedDeriv r f) := by
  sorry

/-- **Gap 18.11.** A uniform linear-element quasi-interpolant obtained by dual
cell moments. These moments are defined on weak Sobolev representatives. -/
theorem exists_uniform_interval_quasiInterpolator :
    let Ω : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
    ∃ C ≥ (0 : ℝ), ∀ n : ℕ, 0 < n →
      ∃ I : W1p volume Ω 2 →L[ℝ] W1p volume Ω 2,
      ∀ u : W1p volume Ω 2,
        let h := (n : ℝ)⁻¹
        let coeff := fun i : Fin (n + 1) ↦
          if i.val < n then (∫ s in (0 : ℝ)..1, (4 - 6 * s) * W1p.value u ((i.val + s) * h))
          else (∫ s in (0 : ℝ)..1, (6 * s - 2) * W1p.value u ((n - 1 + s) * h))
        (W1p.value (I u) =ᵐ[volume.restrict Ω] fun x ↦
          ∑ i : Fin (n + 1), coeff i * max 0 (1 - |(n : ℝ) * x - i.val|)) ∧
        I (I u) = I u ∧ ‖I u‖ ≤ C * ‖u‖ ∧
        ‖W1p.value (u - I u)‖ ≤ C * h * ‖W1p.gradient u‖ := by
  sorry

/-- **Gap 18.20.** The divergence of the reference Raviart--Thomas polynomial
space is the full pressure polynomial space of the corresponding degree. -/
theorem exists_raviartThomas_div_eq {d k : ℕ} (hd : 0 < d)
    (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ k) :
    ∃ (v : Fin d → MvPolynomial (Fin d) ℝ) (q : MvPolynomial (Fin d) ℝ),
      (∀ i, (v i).totalDegree ≤ k) ∧ q.totalDegree ≤ k ∧
      (∑ i, MvPolynomial.pderiv i (v i + MvPolynomial.X i * q)) = p := by
  sorry

/-- **Gap 18.21.** Continuous divergence inf-sup for the Stokes problem on a bounded,
connected Lipschitz domain. The velocity is written componentwise in the zero-trace space. -/
theorem exists_divergence_test_of_meanZero {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin (d + 1)))} [μ.IsAddHaarMeasure]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).IsLipschitzDomain
      (EuclideanSpace ℝ (Fin d)))
    (hconn : IsConnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ β > (0 : ℝ), ∀ q : Lp ℝ 2 (μ.restrict Ω), (∫ x, q x ∂μ.restrict Ω) = 0 →
      ∃ v : Fin (d + 1) → W1p0 μ Ω 2, ‖v‖ ≤ 1 ∧
        β * ‖q‖ ≤ ∫ x : EuclideanSpace ℝ (Fin (d + 1)), q x *
          (∑ i, (W1p.gradient (v i : W1p μ Ω 2) x).ofLp i) ∂μ.restrict Ω := by
  sorry

/-- **Gap 18.22.** Exactness at the first-kind polynomial edge space.
The higher-order part has zero radial component and the curl-free condition
is equality of crossed weak-coordinate derivatives on polynomials. -/
theorem exists_gradient_of_curlFree_edgePolynomial {k : ℕ}
    (u w : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hu : ∀ i, (u i).totalDegree ≤ k) (hw : ∀ i, (w i).totalDegree ≤ k + 1)
    (hr : (∑ i, MvPolynomial.X i * w i) = 0)
    (hcurl : ∀ i j, MvPolynomial.pderiv i (u j + w j) = MvPolynomial.pderiv j (u i + w i)) :
    ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ k + 1 ∧
      ∀ i, MvPolynomial.pderiv i p = u i + w i := by
  sorry

end NASC
