module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Splines and positive definite kernels

B-spline recursion and collocation, cubic spline estimates, and radial kernel positivity
and interpolation in the native Hilbert space. See gaps 11.2–11.13.
The kernel interpolation error proof uses Mathlib's self-adjointness identity for
orthogonal projection.

## Main definitions

* `NASC.bSpline`: the normalized B-spline `B_{m,i}` of order `m + 1` (Cox–de Boor recursion).
* `NASC.IsCubicSpline`: a `C²` function that is cubic on every mesh interval.
* `NASC.radialIntegral`: the Wendland integration operator `p ↦ ∫_r^1 t p(t) dt`.
* `NASC.ConditionallyPosSemidefRadial`: conditional positive semidefiniteness of order `m`.

## Main results

* `NASC.bSpline_nonneg`, `NASC.bSpline_eq_zero_of_notMem`, `NASC.sum_bSpline_eq_one`.
* `NASC.det_bSpline_collocation_ne_zero_iff` (Schoenberg–Whitney).
* `NASC.cubicSpline_curvature_identity`, `NASC.completeSpline_derivative_error_le`.
* `NASC.fourier_gram_pos_of_spectral_support`, `NASC.wendland_gram_pos`,
  `NASC.conditionallyPosSemidefRadial_iff_derivative_nonneg` (Micchelli).
* `NASC.abs_kernelInterpolation_error_le`: the power-function error bound.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Polynomial
open scoped Matrix InnerProductSpace Interval ContDiff

/-- A normalized B-spline with knot sequence $t$, order $m+1$ and starting index $i$. -/
def bSpline (t : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, i, x => if t i ≤ x ∧ x < t (i + 1) then 1 else 0
  | m + 1, i, x =>
    (x - t i) / (t (i + m + 1) - t i) * bSpline t m i x +
      (t (i + m + 2) - x) / (t (i + m + 2) - t (i + 1)) * bSpline t m (i + 1) x

/-- The B-spline of order one is the indicator of the half-open knot interval. -/
theorem bSpline_zero (t : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    bSpline t 0 i x = if t i ≤ x ∧ x < t (i + 1) then 1 else 0 := by
  rfl

/-- The Cox–de Boor recursion (with Lean's convention `a / 0 = 0` at repeated knots). -/
theorem bSpline_succ (t : ℕ → ℝ) (m i : ℕ) (x : ℝ) :
    bSpline t (m + 1) i x =
      (x - t i) / (t (i + m + 1) - t i) * bSpline t m i x +
        (t (i + m + 2) - x) / (t (i + m + 2) - t (i + 1)) * bSpline t m (i + 1) x := by
  rfl

/-- **Gap 11.2.** B-splines for nondecreasing knots vanish outside their half-open knot
support. -/
theorem bSpline_eq_zero_of_notMem (t : ℕ → ℝ) (ht : Monotone t) (m i : ℕ) {x : ℝ}
    (hx : x ∉ Ico (t i) (t (i + m + 1))) : bSpline t m i x = 0 := by
  induction m generalizing i with
  | zero =>
      simp only [Nat.add_zero, mem_Ico] at hx
      rw [bSpline_zero, ite_eq_right hx]
  | succ m ih =>
      have hright : t (i + m + 1) ≤ t (i + (m + 1) + 1) := ht (by omega)
      have hnot₀ : x ∉ Ico (t i) (t (i + m + 1)) :=
        fun hi ↦ hx ⟨hi.1, hi.2.trans_le hright⟩
      have hnot₁ : x ∉ Ico (t (i + 1)) (t (i + 1 + m + 1)) := by
        rw [show i + 1 + m + 1 = i + (m + 1) + 1 by omega]
        exact fun hi ↦ hx ⟨(ht (Nat.le_succ _)).trans hi.1, hi.2⟩
      rw [bSpline_succ, ih i hnot₀, ih (i + 1) hnot₁, mul_zero, mul_zero, add_zero]

/-- **Gap 11.2.** B-splines for nondecreasing knots are nonnegative. -/
theorem bSpline_nonneg (t : ℕ → ℝ) (ht : Monotone t) (m i : ℕ) (x : ℝ) :
    0 ≤ bSpline t m i x := by
  induction m generalizing i with
  | zero =>
      rw [bSpline_zero]
      split <;> norm_num
  | succ m ih =>
      rw [bSpline_succ]
      apply add_nonneg
      · by_cases hi : x ∈ Ico (t i) (t (i + m + 1))
        · exact mul_nonneg (div_nonneg (sub_nonneg.mpr hi.1)
            (sub_nonneg.mpr (ht (by omega)))) (ih i)
        · rw [bSpline_eq_zero_of_notMem t ht m i hi, mul_zero]
      · by_cases hi : x ∈ Ico (t (i + 1)) (t (i + 1 + m + 1))
        · rw [show i + 1 + m + 1 = i + m + 2 by omega] at hi
          exact mul_nonneg (div_nonneg (sub_nonneg.mpr hi.2.le)
            (sub_nonneg.mpr (ht (by omega)))) (ih (i + 1))
        · rw [bSpline_eq_zero_of_notMem t ht m (i + 1) hi, mul_zero]

/-- The first `k` order-one B-splines telescope: their sum at `x` is
`[t 0 ≤ x] - [t k ≤ x]`. -/
theorem sum_range_bSpline_zero (t : ℕ → ℝ) (ht : Monotone t) (x : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, bSpline t 0 i x =
      (if t 0 ≤ x then (1 : ℝ) else 0) - if t k ≤ x then 1 else 0 := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, bSpline_zero]
      by_cases h₁ : t k ≤ x
      · by_cases h₂ : t (k + 1) ≤ x
        · simp only [h₁, h₂, true_and, not_lt.mpr h₂, ite_true, ite_false, add_zero]
        · simp only [h₁, h₂, true_and, lt_of_not_ge h₂, ite_true, ite_false, sub_zero]
          ring
      · have h₂ : ¬t (k + 1) ≤ x := fun h ↦ h₁ ((ht (Nat.le_succ k)).trans h)
        simp only [h₁, h₂, false_and, ite_false, add_zero]

/-- **Gap 11.3.** Curry--Schoenberg partition of unity: for `x ∈ [t m, t n)` the first `n`
B-splines of order `m + 1` (indices `0, …, n - 1`) sum to one. -/
theorem sum_bSpline_eq_one (t : ℕ → ℝ) (ht : Monotone t) {m n : ℕ} {x : ℝ}
    (hx : x ∈ Ico (t m) (t n)) :
    ∑ i ∈ Finset.range n, bSpline t m i x = 1 := by
  classical
  induction m with
  | zero =>
      simp only [sum_range_bSpline_zero t ht, hx.1, not_le.mpr hx.2, ite_true, ite_false,
        sub_zero]
  | succ m ih =>
      let F := fun i : ℕ ↦ (x - t i) / (t (i + m + 1) - t i) * bSpline t m i x
      let G := fun i : ℕ ↦ (t (i + m + 1) - x) / (t (i + m + 1) - t i) * bSpline t m i x
      have hFG (i : ℕ) : F i + G i = bSpline t m i x := by
        dsimp only [F, G]
        by_cases hi : x ∈ Ico (t i) (t (i + m + 1))
        · rw [← add_mul, ← add_div]
          have hnum : x - t i + (t (i + m + 1) - x) = t (i + m + 1) - t i := by ring
          rw [hnum, div_self (sub_ne_zero.mpr (hi.1.trans_lt hi.2).ne'), one_mul]
        · rw [bSpline_eq_zero_of_notMem t ht m i hi, mul_zero, mul_zero, add_zero]
      have hG0 : G 0 = 0 := by
        have hnot : x ∉ Ico (t 0) (t (0 + m + 1)) := by
          intro h
          exact (not_lt.mpr hx.1) (by simpa only [Nat.zero_add] using h.2)
        dsimp only [G]
        rw [bSpline_eq_zero_of_notMem t ht m 0 hnot, mul_zero]
      have hGn : G n = 0 := by
        dsimp only [G]
        rw [bSpline_eq_zero_of_notMem t ht m n (fun h ↦ (not_le.mpr hx.2) h.1), mul_zero]
      have hsum := (Finset.sum_range_succ' G n).symm.trans (Finset.sum_range_succ G n)
      rw [hG0, hGn, add_zero, add_zero] at hsum
      calc
        _ = ∑ i ∈ Finset.range n, (F i + G (i + 1)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hi : i + 1 + m + 1 = i + m + 2 := by omega
          simp only [bSpline, F, G, hi]
        _ = ∑ i ∈ Finset.range n, (F i + G i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum]
        _ = ∑ i ∈ Finset.range n, bSpline t m i x := Finset.sum_congr rfl fun i _ ↦ hFG i
        _ = 1 := ih ⟨(ht (Nat.le_succ m)).trans hx.1, hx.2⟩

/-- **Gap 11.4.** Schoenberg--Whitney criterion for nonsingular spline collocation. If a
knot interval `[t i, t (i + m + 1))` is empty, both sides fail (a zero column, and a zero
diagonal entry). -/
theorem det_bSpline_collocation_ne_zero_iff {n : ℕ} (m : ℕ)
    (t : ℕ → ℝ) (ht : Monotone t) (x : Fin n → ℝ) (hx : StrictMono x) :
    (Matrix.of (fun i j : Fin n ↦ bSpline t m j.val (x i))).det ≠ 0 ↔
      ∀ i : Fin n, bSpline t m i.val (x i) ≠ 0 := by
  sorry

/-- A cubic spline is twice continuously differentiable and has cubic pieces on the mesh. -/
def IsCubicSpline {n : ℕ} (t : Fin (n + 1) → ℝ) (s : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 s ∧
    ∀ i : Fin n, ∃ p : ℝ[X], p.natDegree ≤ 3 ∧ ∀ x ∈ Icc (t i.castSucc) (t i.succ), s x = p.eval x

/-- The defining property of `IsCubicSpline`. -/
theorem isCubicSpline_iff {n : ℕ} (t : Fin (n + 1) → ℝ) (s : ℝ → ℝ) :
    IsCubicSpline t s ↔ ContDiff ℝ 2 s ∧ ∀ i : Fin n, ∃ p : ℝ[X], p.natDegree ≤ 3 ∧
      ∀ x ∈ Icc (t i.castSucc) (t i.succ), s x = p.eval x :=
  Iff.rfl

/-- **Gap 11.6.** The natural interpolating cubic spline minimizes `∫ (s'')²`.
The energy identity quantifies the difference from any `C²` interpolant `f`. -/
theorem cubicSpline_curvature_identity {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    {f s : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hs : IsCubicSpline t s) (hvals : ∀ i, s (t i) = f (t i))
    (ha : iteratedDeriv 2 s (t 0) = 0) (hb : iteratedDeriv 2 s (t (Fin.last n)) = 0) :
    let a := t 0
    let b := t (Fin.last n)
    (∫ x in a..b, (iteratedDeriv 2 f x - iteratedDeriv 2 s x) ^ 2) =
      (∫ x in a..b, iteratedDeriv 2 f x ^ 2) - (∫ x in a..b, iteratedDeriv 2 s x ^ 2) := by
  sorry

/-- **Gap 11.7.** For complete cubic spline interpolation on at least two nodes the orders
for the function, first and second derivative are respectively four, three and two. With a
single node the end conditions fix only `s (t 0)` and `s' (t 0)`, and the bound fails. -/
theorem completeSpline_derivative_error_le {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    {f s : ℝ → ℝ} (hf : ContDiff ℝ 4 f) (hs : IsCubicSpline t s)
    (hvals : ∀ i, s (t i) = f (t i))
    (ha : deriv s (t 0) = deriv f (t 0)) (hb : deriv s (t (Fin.last n)) = deriv f (t (Fin.last n)))
    (hn : 0 < n) {h M : ℝ} (hmesh : ∀ i : Fin n, t i.succ - t i.castSucc ≤ h)
    (hM : ∀ x ∈ Icc (t 0) (t (Fin.last n)), |iteratedDeriv 4 f x| ≤ M)
    (k : Fin 3) {x : ℝ} (hx : x ∈ Icc (t 0) (t (Fin.last n))) :
    |iteratedDeriv k.val f x - iteratedDeriv k.val s x| ≤ 2 * M * h ^ (4 - k.val) := by
  sorry

/-- **Gap 11.9.** An open subset of the support of the spectral measure forces strict
positivity of finite Fourier Gram forms. -/
theorem fourier_gram_pos_of_spectral_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : ∃ U : Set E, IsOpen U ∧ U.Nonempty ∧ U ⊆ μ.support)
    (x : Fin n → E) (hx : Function.Injective x)
    (c : Fin n → ℂ) (hc : c ≠ 0) :
    let Φ := fun z : E ↦
      ∫ w, Complex.exp (-Complex.I * (inner ℝ z w : ℂ)) ∂μ
    0 < (∑ i, ∑ j, c i * star (c j) * Φ (x i - x j)).re := by
  sorry

/-- Integration of a compactly supported radial profile, with support bounded by one. -/
def radialIntegral (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in Ioc r 1, t * p t

/-- The defining formula of `radialIntegral`. -/
theorem radialIntegral_apply (p : ℝ → ℝ) (r : ℝ) :
    radialIntegral p r = ∫ t in Ioc r 1, t * p t := by
  rfl

/-- **Gap 11.10.** Wendland's compactly supported radial profiles are strictly
positive definite in the specified Euclidean dimension (at `d = 0` only `n ≤ 1` points are
distinct and `p 0 > 0`). -/
theorem wendland_gram_pos {d n : ℕ} (k : ℕ)
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

/-- The defining property of `ConditionallyPosSemidefRadial`. -/
theorem conditionallyPosSemidefRadial_iff (m d : ℕ) (p : ℝ → ℝ) :
    ConditionallyPosSemidefRadial m d p ↔
      ∀ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ), Function.Injective x →
        (∀ P : MvPolynomial (Fin d) ℝ, P.totalDegree < m →
          (∑ i, c i * MvPolynomial.eval (x i).ofLp P) = 0) →
        0 ≤ ∑ i, ∑ j, c i * c j * p (‖x i - x j‖ ^ 2) :=
  Iff.rfl

/-- **Gap 11.11.** Micchelli's criterion relates dimension-independent conditional
positive semidefiniteness to the alternating derivative signs. -/
theorem conditionallyPosSemidefRadial_iff_derivative_nonneg (p : ℝ → ℝ) (m : ℕ)
    (hc : ContinuousOn p (Ici 0)) (hs : ContDiffOn ℝ ∞ p (Ioi 0)) :
    (∀ d, ConditionallyPosSemidefRadial m d p) ↔
      ∀ j : ℕ, ∀ r > (0 : ℝ), 0 ≤ (-1 : ℝ) ^ (m + j) * iteratedDeriv (m + j) p r := by
  sorry

/-- **Gap 11.13.** The power function is the length of the residual feature vector.
This residual controls the pointwise error of orthogonal kernel interpolation. -/
theorem abs_kernelInterpolation_error_le {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (feature : X → H) {ι : Type*} (sites : ι → X) (u : H) (x : X) :
    let V := Submodule.span ℝ (range (feature ∘ sites))
    let P := V.topologicalClosure.starProjection
    |inner ℝ u (feature x) - inner ℝ (P u) (feature x)| ≤ ‖feature x - P (feature x)‖ * ‖u‖ := by
  dsimp only
  rw [Submodule.inner_starProjection_left_eq_right, ← inner_sub_right]
  exact (abs_real_inner_le_norm u _).trans_eq (mul_comm _ _)

end NASC
