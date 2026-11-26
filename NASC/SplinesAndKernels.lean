module

public import NASC.Approximation
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Splines and positive definite kernels

B-spline recursion and collocation, cubic spline estimates, and radial kernel positivity
and interpolation in the native Hilbert space. See gaps 11.2–11.13.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Polynomial
open scoped Matrix BigOperators InnerProductSpace Interval

/-- A normalized B-spline with knot sequence $t$, order $m+1$ and starting index $i$. -/
def bSpline (t : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, i, x => if t i ≤ x ∧ x < t (i + 1) then 1 else 0
  | m + 1, i, x =>
    (x - t i) / (t (i + m + 1) - t i) * bSpline t m i x +
      (t (i + m + 2) - x) / (t (i + m + 2) - t (i + 1)) * bSpline t m (i + 1) x

/-- **Gap 11.2.** B-splines for nondecreasing knots are nonnegative and vanish outside
their half-open knot support. -/
theorem bSpline_nonneg_and_eq_zero (t : ℕ → ℝ) (ht : Monotone t) (m i : ℕ) (x : ℝ) :
    0 ≤ bSpline t m i x ∧ (x ∉ Ico (t i) (t (i + m + 1)) → bSpline t m i x = 0) := by
  sorry

/-- **Gap 11.3.** Curry--Schoenberg partition of unity on the interior of the active
knot interval. Here $n$ is the number of active basis functions. -/
theorem sum_bSpline_eq_one (t : ℕ → ℝ) (ht : Monotone t) {m n : ℕ} {x : ℝ}
    (hx : x ∈ Ico (t m) (t n)) :
    ∑ i ∈ Finset.range n, bSpline t m i x = 1 := by
  sorry

/-- **Gap 11.4.** Schoenberg--Whitney criterion for nonsingular spline collocation. -/
theorem det_bSpline_collocation_ne_zero_iff {n : ℕ} (m : ℕ)
    (t : ℕ → ℝ) (ht : Monotone t) (x : Fin n → ℝ) (hx : StrictMono x)
    (hsupport : ∀ i : Fin n, t i.val < t (i.val + m + 1)) :
    (Matrix.of (fun i j : Fin n ↦ bSpline t m j.val (x i))).det ≠ 0 ↔
      ∀ i : Fin n, bSpline t m i.val (x i) ≠ 0 := by
  sorry

/-- A cubic spline is twice continuously differentiable and has cubic pieces on the mesh. -/
def IsCubicSpline {n : ℕ} (t : Fin (n + 1) → ℝ) (s : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 s ∧
    ∀ i : Fin n, ∃ p : ℝ[X], p.natDegree ≤ 3 ∧ ∀ x ∈ Icc (t i.castSucc) (t i.succ), s x = p.eval x

/-- **Gap 11.6.** The natural interpolating cubic spline minimizes squared curvature.
The energy identity quantifies the difference from any twice differentiable interpolant. -/
theorem cubicSpline_curvature_identity {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    {f s : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hs : IsCubicSpline t s) (hvals : ∀ i, s (t i) = f (t i))
    (ha : iteratedDeriv 2 s (t 0) = 0) (hb : iteratedDeriv 2 s (t (Fin.last n)) = 0) :
    let a := t 0
    let b := t (Fin.last n)
    (∫ x in a..b, (iteratedDeriv 2 f x - iteratedDeriv 2 s x) ^ 2) =
      (∫ x in a..b, iteratedDeriv 2 f x ^ 2) - (∫ x in a..b, iteratedDeriv 2 s x ^ 2) := by
  sorry

/-- **Gap 11.7.** For complete cubic spline interpolation the orders for the
function, first and second derivative are respectively four, three and two. -/
theorem completeSpline_derivative_error_le {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    {f s : ℝ → ℝ} (hf : ContDiff ℝ 4 f) (hs : IsCubicSpline t s)
    (hvals : ∀ i, s (t i) = f (t i))
    (ha : deriv s (t 0) = deriv f (t 0)) (hb : deriv s (t (Fin.last n)) = deriv f (t (Fin.last n)))
    {h M : ℝ} (hh : 0 ≤ h) (hmesh : ∀ i : Fin n, t i.succ - t i.castSucc ≤ h)
    (hM : ∀ x ∈ Icc (t 0) (t (Fin.last n)), |iteratedDeriv 4 f x| ≤ M)
    (k : Fin 3) {x : ℝ} (hx : x ∈ Icc (t 0) (t (Fin.last n))) :
    |iteratedDeriv k.val f x - iteratedDeriv k.val s x| ≤ 2 * M * h ^ (4 - k.val) := by
  sorry

/-- **Gap 11.9.** An open subset of the support of the spectral measure forces strict
positivity of finite Fourier Gram forms. -/
theorem fourier_gram_pos_of_spectral_support {d n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))] [BorelSpace (EuclideanSpace ℝ (Fin d))]
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (hμ : ∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ U.Nonempty ∧
      ∀ v ∈ U, ∀ r > 0, μ (Metric.ball v r) ≠ 0)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (c : Fin n → ℂ) (hc : c ≠ 0) :
    let Φ := fun z : EuclideanSpace ℝ (Fin d) ↦
      ∫ w, Complex.exp (-Complex.I * (inner ℝ z w : ℂ)) ∂μ
    0 < (∑ i, ∑ j, c i * star (c j) * Φ (x i - x j)).re := by
  sorry

/-- Integration of a compactly supported radial profile, with support bounded by one. -/
def radialIntegral (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in Ioc r 1, t * p t

/-- **Gap 11.10.** Wendland's compactly supported radial profiles are strictly
positive definite in the specified Euclidean dimension. -/
theorem wendland_gram_pos {d n : ℕ} (hd : 0 < d) (k : ℕ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (c : Fin n → ℝ) (hc : c ≠ 0) :
    let p := radialIntegral^[k] (fun t : ℝ ↦ (max (1 - t) 0) ^ (d / 2 + k + 1))
    0 < ∑ i, ∑ j, c i * c j * p ‖x i - x j‖ := by
  sorry

/-- Conditional positive semidefiniteness for radial kernels on Euclidean space. -/
def ConditionallyPosSemidefRadial (m d : ℕ) (p : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ), Function.Injective x →
    (∀ P : MvPolynomial (Fin d) ℝ, P.totalDegree < m →
      (∑ i, c i * MvPolynomial.eval (x i).ofLp P) = 0) →
    0 ≤ ∑ i, ∑ j, c i * c j * p (‖x i - x j‖ ^ 2)

/-- **Gap 11.11.** Micchelli's criterion relates dimension-independent conditional
positive semidefiniteness to the alternating derivative signs. -/
theorem conditionallyPosSemidefRadial_iff_derivative_nonneg (p : ℝ → ℝ) (m : ℕ)
    (hc : ContinuousOn p (Ici 0)) (hs : ContDiffOn ℝ ⊤ p (Ioi 0)) :
    (∀ d, ConditionallyPosSemidefRadial m d p) ↔
      ∀ j : ℕ, ∀ r > (0 : ℝ), 0 ≤ (-1 : ℝ) ^ (m + j) * iteratedDeriv (m + j) p r := by
  sorry

/-- **Gap 11.13.** The power function is the length of the residual feature vector.
This residual controls the pointwise error of orthogonal kernel interpolation. -/
theorem abs_kernelInterpolation_error_le {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (feature : X → H) {n : ℕ} (sites : Fin n → X) (u : H) (x : X) :
    let V := Submodule.span ℝ (range (feature ∘ sites))
    let P := V.topologicalClosure.starProjection
    |inner ℝ u (feature x) - inner ℝ (P u) (feature x)| ≤ ‖feature x - P (feature x)‖ * ‖u‖ := by
  sorry

end NASC
