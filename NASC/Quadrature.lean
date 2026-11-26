module

public import NASC.Approximation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.NumberTheory.Bernoulli

/-!
# Orthogonal polynomials and quadrature

Moment orthogonality, Gaussian quadrature and its spectral construction, derivative error
formulas, and the analytic trapezoidal rule. See section 12 of the gap catalogue.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Polynomial
open scoped BigOperators Matrix Interval

/-- A moment measure has all polynomial moments and has no finite set of full measure. -/
def HasInfiniteMomentSupport (μ : Measure ℝ) : Prop :=
  (∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ) ∧
    ∀ s : Finset ℝ, ¬(∀ᵐ x ∂μ, x ∈ s)

/-- Monic polynomials of successive degrees orthogonal for the given moment measure. -/
def AreMonicOrthogonal (μ : Measure ℝ) (p : ℕ → ℝ[X]) : Prop :=
  (∀ n, (p n).Monic ∧ (p n).natDegree = n) ∧
    ∀ i j, i ≠ j → (∫ x, (p i).eval x * (p j).eval x ∂μ) = 0

/-- **Gap 12.1.** The sequence of monic orthogonal polynomials exists and is unique. -/
theorem existsUnique_monicOrthogonal (μ : Measure ℝ) (hμ : HasInfiniteMomentSupport μ) :
    ∃! p : ℕ → ℝ[X], AreMonicOrthogonal μ p := by
  sorry

/-- **Gap 12.2.** Multiplication by the coordinate yields the monic three-term
recurrence with strictly positive lower recurrence coefficients. -/
theorem exists_monicOrthogonal_threeTerm (μ : Measure ℝ) (hμ : HasInfiniteMomentSupport μ)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < b (n + 1)) ∧ p 0 = 1 ∧
      p 1 = X - C (a 0) ∧
      ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n := by
  sorry

/-- **Gap 12.2.** Favard's theorem realizes positive recurrence coefficients
by orthogonality for a probability measure with infinite moment support. -/
theorem exists_measure_monicOrthogonal_of_threeTerm (a b : ℕ → ℝ) (p : ℕ → ℝ[X])
    (hb : ∀ n, 0 < b (n + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hrec : ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ HasInfiniteMomentSupport μ ∧
      AreMonicOrthogonal μ p := by
  sorry

/-- **Gap 12.3.** The real roots of successive monic orthogonal polynomials are
simple, lie in the interior of a supporting interval, and strictly interlace. -/
theorem exists_monicOrthogonal_interlacing_roots (μ : Measure ℝ)
    (hμ : HasInfiniteMomentSupport μ) (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p)
    {a b : ℝ} (hI : ∀ᵐ x ∂μ, x ∈ Icc a b) (n : ℕ) :
    ∃ (x : Fin n → ℝ) (y : Fin (n + 1) → ℝ),
      (p n).roots = Multiset.ofList (List.ofFn x) ∧
      (p (n + 1)).roots = Multiset.ofList (List.ofFn y) ∧
      (∀ i, y i ∈ Ioo a b) ∧ (∀ i, y i.castSucc < x i ∧ x i < y i.succ) := by
  sorry

/-- The symmetric Jacobi matrix associated with the monic three-term recurrence. -/
def jacobiMatrix (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then a i.val else if i.val + 1 = j.val then Real.sqrt (b j.val)
    else if j.val + 1 = i.val then Real.sqrt (b i.val) else 0

/-- **Gap 12.4.** Determinants of successive Jacobi sections satisfy the given
three-term recurrence. -/
theorem charpoly_jacobiMatrix_eq (a b : ℕ → ℝ) (p : ℕ → ℝ[X])
    (hb : ∀ i, 0 ≤ b (i + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hp : ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n)
    (n : ℕ) : (jacobiMatrix a b n).charpoly = p n := by
  sorry

/-- Exactness through degree $2n-1$ for an $n$-node formula. -/
def IsGaussRule {n : ℕ} (μ : Measure ℝ) (x w : Fin n → ℝ) : Prop :=
  Function.Injective x ∧
    ∀ p : ℝ[X], p.natDegree < 2 * n → (∫ y, p.eval y ∂μ) = ∑ i, w i * p.eval (x i)

/-- **Gap 12.6.** An exact Gauss rule has positive Christoffel weights and its
nodes are precisely the roots of the monic orthogonal polynomial. -/
theorem IsGaussRule.roots_and_weights {n : ℕ} {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {x w : Fin n → ℝ} (h : IsGaussRule μ x w)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) :
    (p n).roots = Multiset.ofList (List.ofFn x) ∧ ∀ i,
      0 < w i ∧ w i = ∫ z, (Lagrange.basis Finset.univ x i).eval z ^ 2 ∂μ := by
  sorry

/-- **Gap 12.7.** Golub--Welsch constructs an exact Gauss rule using the first
row of an orthogonal diagonalization of the Jacobi matrix. -/
theorem isGaussRule_of_jacobiDiagonalization {n : ℕ} {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p)
    (a b : ℕ → ℝ) (hb : ∀ j, 0 < b (j + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hrec : ∀ j, p (j + 2) = (X - C (a (j + 1))) * p (j + 1) - C (b (j + 1)) * p j)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ)
    (hQ : Qᵀ * Q = 1) (hx : jacobiMatrix a b (n + 1) * Q = Q * Matrix.diagonal x) :
    IsGaussRule μ x (fun i ↦ (μ Set.univ).toReal * Q 0 i ^ 2) := by
  sorry

/-- **Gap 12.8.** The Gaussian quadrature error is a derivative at an interior point
times the squared norm of the monic orthogonal polynomial. -/
theorem exists_gauss_remainder {n : ℕ} (hn : 0 < n) {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {a b : ℝ} (hab : a < b)
    (hs : ∀ᵐ t ∂μ, t ∈ Icc a b) {x w : Fin n → ℝ} (hG : IsGaussRule μ x w)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (2 * n : ℕ) f) :
    ∃ z ∈ Ioo a b, (∫ t, f t ∂μ) - (∑ i, w i * f (x i)) =
      (iteratedDeriv (2 * n) f z / (2 * n).factorial) * ∫ t, (p n).eval t ^ 2 ∂μ := by
  sorry

/-- **Gap 12.10.** Peano's integral error representation for a point-value quadrature
formula that is exact through degree $n$. -/
theorem quadrature_error_eq_peanoKernel {k n : ℕ} {a b : ℝ} (hab : a < b)
    (x w : Fin k → ℝ) (hx : ∀ i, x i ∈ Icc a b)
    (hexact : ∀ p : ℝ[X], p.natDegree ≤ n →
      (∑ i, w i * p.eval (x i)) = ∫ y in a..b, p.eval y)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    let R := fun g : ℝ → ℝ ↦ (∑ i, w i * g (x i)) - ∫ y in a..b, g y
    R f = ∫ t in a..b, (R (fun y ↦ if t ≤ y then (y - t) ^ n else 0) / n.factorial) *
      iteratedDeriv (n + 1) f t := by
  sorry

/-- **Gap 12.12.** Composite Euler--Maclaurin on a uniform mesh with the
pointwise derivative remainder. -/
theorem exists_compositeTrapezoid_eulerMaclaurin {a b : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (m N : ℕ) (hN : 0 < N) (hf : ContDiff ℝ (2 * m + 2 : ℕ) f) :
    let h := (b - a) / N
    let T := h * (f a / 2 + (∑ i ∈ Finset.Ico 1 N, f (a + i * h)) + f b / 2)
    ∃ z ∈ Ioo a b, T = (∫ x in a..b, f x) +
      (∑ j ∈ Finset.Icc 1 m, (bernoulli (2 * j) : ℝ) / (2 * j).factorial * h ^ (2 * j) *
        (iteratedDeriv (2 * j - 1) f b - iteratedDeriv (2 * j - 1) f a)) +
      (bernoulli (2 * m + 2) : ℝ) / (2 * m + 2).factorial * h ^ (2 * m + 2) *
        (b - a) * iteratedDeriv (2 * m + 2) f z := by
  sorry

/-- **Gap 12.14.** Bounded holomorphy on a strip gives the analytic periodic
trapezoidal error bound. -/
theorem norm_trapezoid_sub_integral_le_of_analyticOnStrip
    (f : ℂ → ℂ) {a M : ℝ} (ha : 0 < a)
    (hf : AnalyticOnNhd ℂ f {z | |z.im| < a}) (hM : ∀ z, |z.im| < a → ‖f z‖ ≤ M)
    (hper : Function.Periodic (fun x : ℝ ↦ f x) (2 * Real.pi))
    (N : ℕ) (hN : 0 < N) :
    let h := 2 * Real.pi / N
    ‖h • (∑ j : Fin N, f ((j.val : ℝ) * h)) -
      ∫ x in (0 : ℝ)..(2 * Real.pi), f (x : ℂ)‖ ≤ 4 * Real.pi * M / (Real.exp (a * N) - 1) := by
  sorry

end NASC
