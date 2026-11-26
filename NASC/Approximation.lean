module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Polynomial and rational approximation

Haar spaces, alternation, interpolation estimates, Bernstein ellipses and Padé approximation.
See section 10 of the gap catalogue.
-/

public section

noncomputable section

namespace NASC

open Set Filter Polynomial MeasureTheory
open scoped BigOperators Interval

/-- A Haar space of dimension $n$ interpolates arbitrary data on $n$ distinct points. -/
def IsHaarSpace {K : Type*} [TopologicalSpace K] (V : Submodule ℝ C(K, ℝ)) (n : ℕ) : Prop :=
  ∀ (x : Fin n → K) (y : Fin n → ℝ), Function.Injective x →
    ∃! v : V, ∀ i, v.val (x i) = y i

/-- **Gap 10.2.** On a finite-dimensional space, unisolvence of interpolation is
equivalent to the zero-count property. -/
theorem isHaarSpace_iff_no_many_zeros {K : Type*} [TopologicalSpace K]
    (V : Submodule ℝ C(K, ℝ)) (n : ℕ) (hdim : Module.finrank ℝ V = n)
    [FiniteDimensional ℝ V] :
    IsHaarSpace V n ↔
      ∀ (v : V) (x : Fin n → K), Function.Injective x → (∀ i, v.val (x i) = 0) → v = 0 := by
  sorry

/-- Supremum of the absolute error over a compact interval on which the function is
continuous. Callers of the uniform approximation results supply this continuity. -/
def intervalError (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup ((fun x ↦ |f x|) '' Icc a b)

/-- **Gap 10.3.** Alternation characterizes the best polynomial, with an explicit
alternating sequence of extremal errors. -/
theorem isMinOn_polyError_iff_alternation {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) {n : ℕ} (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    (∀ q : ℝ[X], q.natDegree ≤ n →
      intervalError a b (fun x ↦ f x - p.eval x) ≤ intervalError a b (fun x ↦ f x - q.eval x)) ↔
    ∃ (x : Fin (n + 2) → ℝ) (s : ℝ),
      StrictMono x ∧ (∀ i, x i ∈ Icc a b) ∧ (s = 1 ∨ s = -1) ∧
      ∀ i, f (x i) - p.eval (x i) = s * (-1 : ℝ) ^ i.val *
        intervalError a b (fun t ↦ f t - p.eval t) := by
  sorry

/-- **Gap 10.5.** Lagrange interpolation has the classical derivative remainder at
distinct real nodes. Any compact interval containing the nodes and evaluation point suffices. -/
theorem exists_lagrange_remainder {n : ℕ} (nodes : Fin n → ℝ) (hn : Function.Injective nodes)
    {a b x : ℝ} (hx : x ∈ Icc a b) (ha : ∀ i, nodes i ∈ Icc a b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ n f) :
    ∃ z ∈ Icc a b,
      f x - (Lagrange.interpolate Finset.univ nodes (f ∘ nodes)).eval x =
        iteratedDeriv n f z / n.factorial * ∏ i, (x - nodes i) := by
  sorry

/-- **Gap 10.7.** For any triangular array of distinct nodes there is a continuous
function whose polynomial interpolants fail to converge uniformly. -/
theorem exists_not_tendsto_uniform_lagrange {a b : ℝ} (hab : a < b)
    (nodes : ∀ n, Fin (n + 1) → ℝ) (hinj : ∀ n, Function.Injective (nodes n))
    (hmem : ∀ n i, nodes n i ∈ Icc a b) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc a b) ∧
      ¬Tendsto (fun n ↦ intervalError a b (fun x ↦
        f x - (Lagrange.interpolate Finset.univ (nodes n) (f ∘ nodes n)).eval x))
          atTop (nhds 0) := by
  sorry

/-- **Gap 10.8.** Jackson's polynomial approximation bound in terms of a Hölder
seminorm of the $k$-th derivative. -/
theorem exists_polynomial_uniform_error_le_jackson {n k : ℕ} (hk : k < n)
    (f : ℝ → ℝ) (hf : ContDiff ℝ k f) {M α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) (hM : 0 ≤ M)
    (hhold : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv k f x - iteratedDeriv k f y| ≤ M * |x - y| ^ α) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |f x - p.eval x| ≤ (1 + Real.pi ^ 2 / 2) ^ (k + 1) * M /
        ((∏ j : Fin k, ((n - j.val : ℕ) : ℝ)) * ((n - k : ℕ) : ℝ) ^ α) := by
  sorry

/-- Bernstein ellipse with foci at $-1$ and $1$, parameterized by the sum of semiaxes. -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ := {z | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

/-- **Gap 10.9.** Geometrically decaying uniform polynomial errors give an analytic
extension to the open Bernstein ellipse. -/
theorem exists_analyticOnNhd_of_geometric_polyApprox (f : ℝ → ℂ) {ρ M : ℝ}
    (hρ : 1 < ρ) (hM : 0 ≤ M) (p : ℕ → ℂ[X]) (hdeg : ∀ n, (p n).natDegree ≤ n)
    (happrox : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → ‖f x - (p n).eval (x : ℂ)‖ ≤ M / ρ ^ n) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (bernsteinEllipse ρ) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, g x = f x := by
  sorry

/-- **Gap 10.11.** Chebyshev coefficients decay geometrically for holomorphic
functions bounded on the open Bernstein ellipse. -/
theorem norm_chebyshevCoeff_le_of_analyticOnEllipse (f : ℂ → ℂ) {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hM : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) (k : ℕ) :
    let c := ((if k = 0 then 1 else 2) / Real.pi : ℝ) •
      ∫ t in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * t) • f (Real.cos t)
    ‖c‖ ≤ (if k = 0 then 1 else 2) * M / ρ ^ k := by
  sorry

/-- Chebyshev--Lobatto nodes of degree $n$. Interpolation uses positive degree. -/
def chebyshevNodes (n : ℕ) (j : Fin (n + 1)) : ℝ := Real.cos (j.val * Real.pi / n)

/-- **Gap 10.12.** Explicit Chebyshev barycentric weights evaluate the interpolant
away from the nodes. -/
theorem eval_lagrange_chebyshevNodes_eq_barycentric {n : ℕ} (hn : 0 < n)
    (y : Fin (n + 1) → ℝ) (x : ℝ) (hx : ∀ j, x ≠ chebyshevNodes n j) :
    let w := fun j : Fin (n + 1) ↦
      (-1 : ℝ) ^ j.val / (if j.val = 0 ∨ j.val = n then 2 else 1)
    (Lagrange.interpolate Finset.univ (chebyshevNodes n) y).eval x =
      (∑ j, w j * y j / (x - chebyshevNodes n j)) /
        ∑ j, w j / (x - chebyshevNodes n j) := by
  sorry

/-- On an interval a rational pair is admissible when it meets the degree bounds
and has no denominator zero. Uncancelled poles are therefore excluded. -/
def IsRationalPairOn (s : Set ℝ) (m n : ℕ) (p q : ℝ[X]) : Prop :=
  p.natDegree ≤ m ∧ q.natDegree ≤ n ∧ ∀ x ∈ s, q.eval x ≠ 0

/-- **Gap 10.13.** A best real rational approximant exists and its values are unique.
Polynomial representatives need not be unique. -/
theorem exists_best_rational_uniform {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (m n : ℕ) :
    ∃ p q : ℝ[X], IsRationalPairOn (Icc a b) m n p q ∧
      ∀ P Q : ℝ[X], IsRationalPairOn (Icc a b) m n P Q →
        let e := intervalError a b (fun x ↦ f x - p.eval x / q.eval x)
        let E := intervalError a b (fun x ↦ f x - P.eval x / Q.eval x)
        e ≤ E ∧ (E = e → ∀ x ∈ Icc a b, P.eval x / Q.eval x = p.eval x / q.eval x) := by
  sorry

/-- Degree and coefficient conditions for a formal Padé pair. Coefficients of the
product are written as finite convolution to include singular entries in the table. -/
def IsPadePair (c : ℕ → ℂ) (m n : ℕ) (p q : ℂ[X]) : Prop :=
  p.natDegree ≤ m ∧ q.natDegree ≤ n ∧ q ≠ 0 ∧
    ∀ k ≤ m + n, p.coeff k = ∑ j ∈ Finset.range (k + 1), q.coeff j * c (k - j)

/-- **Gap 10.14.** Formal Padé pairs exist, and their rational functions agree by
cross-multiplication. -/
theorem exists_padePair_and_eq_cross (c : ℕ → ℂ) (m n : ℕ) :
    ∃ p q : ℂ[X], IsPadePair c m n p q ∧
      ∀ P Q : ℂ[X], IsPadePair c m n P Q → p * Q = P * q := by
  sorry

/-- **Gap 10.15.** De Montessus convergence of the fixed-denominator-degree row.
The polynomial of actual poles is given explicitly and has no cancellation. -/
theorem exists_pade_row_tendstoUniformlyOn {f H : ℂ → ℂ} (Q : ℂ[X])
    {r : ℝ} (hr : 0 < r) (hQ : Q.eval 0 ≠ 0)
    (hroot : ∀ z, Q.eval z = 0 → ‖z‖ < r ∧ H z ≠ 0)
    (hH : AnalyticOnNhd ℂ H (Metric.closedBall 0 r))
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) r, Q.eval z ≠ 0 → f z = H z / Q.eval z) :
    ∃ P D : ℕ → ℂ[X],
      (∀ᶠ m in atTop, IsPadePair (fun k ↦ iteratedDeriv k f 0 / k.factorial) m Q.natDegree
          (P m) (D m) ∧ (D m).eval 0 = 1) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.closedBall 0 r → (∀ z ∈ K, Q.eval z ≠ 0) →
        TendstoUniformlyOn (fun m z ↦ (P m).eval z / (D m).eval z) f atTop K := by
  sorry

/-- **Gap 10.16.** A Stieltjes series with a nonnegative measure of infinite support
has normalized Padé approximants in the stated half of the table. -/
theorem exists_padePair_of_stieltjes {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hinf : ∀ s : Finset ℝ, ¬(∀ᵐ x ∂μ, x ∈ s))
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ)
    (m n : ℕ) (hmn : n ≤ m + 1) :
    ∃ p q : ℂ[X], IsPadePair (fun k ↦ (-1 : ℂ) ^ k * (∫ x, x ^ k ∂μ : ℝ)) m n p q ∧
      q.eval 0 = 1 := by
  sorry

/-- Best approximation error from a nonempty family of approximants. -/
def bestApproximationError {E : Type*} [NormedAddCommGroup E] (A : Set E) (x : E) : ℝ :=
  sInf ((fun y ↦ ‖x - y‖) '' A)

end NASC
