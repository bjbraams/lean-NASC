module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import NASC.Support.Analysis

/-!
# Polynomial and rational approximation

Haar spaces, alternation, interpolation estimates, Faber's divergence theorem, Jackson's
bound, Bernstein ellipses and Chebyshev coefficients, Chebyshev barycentric interpolation,
best rational approximation, and Padé approximation (de Montessus and Stieltjes series). See
section 10 of the gap catalogue.

## Main definitions

* `NASC.IsHaarSpace V n`: interpolation of arbitrary data at `n` distinct points by a unique
  element of `V`.
* `NASC.intervalError a b f`: the supremum of `|f|` over `[a, b]`.
* `NASC.bernsteinEllipse ρ`, `NASC.chebyshevNodes n`, `NASC.IsRationalPairOn`,
  `NASC.IsPadePair`.

## Main results

* `NASC.isHaarSpace_iff_forall_eq_zero`: unisolvence is equivalent to the zero-count property.
* `NASC.forall_intervalError_le_iff_exists_alternation`: Chebyshev's alternation theorem.
* `NASC.exists_lagrange_remainder`: the Lagrange interpolation remainder.
* `NASC.exists_not_tendsto_uniform_lagrange`: Faber's theorem.
* `NASC.exists_polynomial_uniform_error_le_jackson`: Jackson's theorem.
* `NASC.exists_analyticOnNhd_of_geometric_polyApprox`,
  `NASC.norm_chebyshevCoeff_le_of_analyticOnEllipse`: Bernstein's theorem in both directions.
* `NASC.eval_lagrange_chebyshevNodes_eq_barycentric`: the Chebyshev barycentric formula.
* `NASC.exists_best_rational_uniform`: existence and uniqueness of best rational approximation.
* `NASC.exists_padePair_and_eq_cross`, `NASC.exists_pade_row_tendstoUniformlyOn`,
  `NASC.exists_padePair_of_stieltjes`: Padé pairs, de Montessus, Stieltjes series.

The Haar-space proof uses Mathlib's finite-dimensional injectivity-surjectivity
criterion for evaluation. The interpolation remainder uses Mathlib's nodal
polynomial and the generalized Rolle theorem `NASC.exists_iteratedDeriv_eq_zero_of_strictMono`.
-/

public section

noncomputable section

namespace NASC

open Set Filter Polynomial MeasureTheory
open scoped Interval

/-- A space `V` of continuous functions is unisolvent at every `n` distinct points: arbitrary
data at `n` distinct points are interpolated by exactly one element of `V`. The definition does
not tie `n` to the dimension of `V`. -/
def IsHaarSpace {K : Type*} [TopologicalSpace K] (V : Submodule ℝ C(K, ℝ)) (n : ℕ) : Prop :=
  ∀ (x : Fin n → K) (y : Fin n → ℝ), Function.Injective x →
    ∃! v : V, ∀ i, v.val (x i) = y i

/-- The defining property of `IsHaarSpace`. -/
theorem isHaarSpace_iff {K : Type*} [TopologicalSpace K] (V : Submodule ℝ C(K, ℝ)) (n : ℕ) :
    IsHaarSpace V n ↔ ∀ (x : Fin n → K) (y : Fin n → ℝ), Function.Injective x →
      ∃! v : V, ∀ i, v.val (x i) = y i := by
  unfold IsHaarSpace
  exact Iff.rfl

/-- **Gap 10.2.** On a finite-dimensional space, unisolvence of interpolation is
equivalent to the zero-count property. -/
theorem isHaarSpace_iff_forall_eq_zero {K : Type*} [TopologicalSpace K]
    (V : Submodule ℝ C(K, ℝ)) (n : ℕ) (hdim : Module.finrank ℝ V = n)
    [FiniteDimensional ℝ V] :
    IsHaarSpace V n ↔
      ∀ (v : V) (x : Fin n → K), Function.Injective x → (∀ i, v.val (x i) = 0) → v = 0 := by
  constructor
  · intro h v x hx hv
    obtain ⟨w, _, hw⟩ := h x (fun _ ↦ 0) hx
    have hzero : ∀ i, (0 : V).val (x i) = 0 := fun _ ↦ rfl
    exact (hw v hv).trans (hw 0 hzero).symm
  · intro h x y hx
    let E : V →ₗ[ℝ] Fin n → ℝ :=
      { toFun := fun v i ↦ v.val (x i)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hE : Function.Injective E := by
      intro u v huv
      apply sub_eq_zero.mp
      apply h (u - v) x hx
      intro i
      exact sub_eq_zero.mpr (congrFun huv i)
    have hn : Module.finrank ℝ V = Module.finrank ℝ (Fin n → ℝ) := by
      rw [hdim, Module.finrank_pi, Fintype.card_fin]
    obtain ⟨v, hv⟩ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hn).mp hE y
    exact ⟨v, congrFun hv, fun w hw ↦ hE ((funext hw).trans hv.symm)⟩

/-- Supremum of the absolute error over a compact interval on which the function is
continuous. Callers of the uniform approximation results supply this continuity. For an
empty interval, or a function unbounded on the interval, the value is the junk value `0`. -/
def intervalError (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup ((fun x ↦ |f x|) '' Icc a b)

/-- The defining formula for `intervalError`. -/
theorem intervalError_def (a b : ℝ) (f : ℝ → ℝ) :
    intervalError a b f = sSup ((fun x ↦ |f x|) '' Icc a b) := by
  unfold intervalError
  rfl

/-- **Gap 10.3.** Alternation characterizes the best polynomial, with an explicit
alternating sequence of extremal errors. -/
theorem forall_intervalError_le_iff_exists_alternation {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) {n : ℕ} (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    (∀ q : ℝ[X], q.natDegree ≤ n →
      intervalError a b (fun x ↦ f x - p.eval x) ≤ intervalError a b (fun x ↦ f x - q.eval x)) ↔
    ∃ (x : Fin (n + 2) → ℝ) (s : ℝ),
      StrictMono x ∧ (∀ i, x i ∈ Icc a b) ∧ (s = 1 ∨ s = -1) ∧
      ∀ i, f (x i) - p.eval (x i) = s * (-1 : ℝ) ^ i.val *
        intervalError a b (fun t ↦ f t - p.eval t) := by
  sorry

/-- Subtracting the interpolating polynomial and a nodal correction creates
an additional zero at the evaluation point. -/
theorem exists_iteratedDeriv_eq_zero_of_nodal_correction {n : ℕ}
    (nodes : Fin n → ℝ) (hn : Function.Injective nodes) {a b x : ℝ}
    (hx : x ∈ Icc a b) (ha : ∀ i, nodes i ∈ Icc a b) (hnode : ¬ ∃ i, nodes i = x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ n f) (p q : ℝ[X]) (c : ℝ)
    (hp : ∀ i, p.eval (nodes i) = f (nodes i)) (hq : ∀ i, q.eval (nodes i) = 0)
    (hc : f x - p.eval x = c * q.eval x) :
    ∃ t ∈ Icc a b, iteratedDeriv n (fun u ↦ f u - (p + C c * q).eval u) t = 0 := by
  classical
  let s := insert x (Finset.univ.image nodes)
  have hcard : s.card = n + 1 := by
    have hxmem : x ∉ Finset.univ.image nodes := by
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hnode
    simp only [s, Finset.card_insert_of_notMem hxmem, Finset.card_image_of_injective _ hn,
      Finset.card_univ, Fintype.card_fin]
  let r := p + C c * q
  let g := fun t ↦ f t - r.eval t
  have hrDiff := contDiff_polynomial_eval n r
  have hroots {t : ℝ} (ht : t ∈ s) : t ∈ Icc a b ∧ g t = 0 := by
    simp only [s, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at ht
    rcases ht with rfl | ⟨i, rfl⟩
    · refine ⟨hx, ?_⟩
      simp only [g, r, eval_add, eval_mul, eval_C]
      linarith only [hc]
    · refine ⟨ha i, ?_⟩
      simp only [g, r, eval_add, eval_mul, eval_C, hp i, hq i, mul_zero, add_zero, sub_self]
  let z := s.orderEmbOfFin hcard
  exact exists_iteratedDeriv_eq_zero_of_strictMono g (hf.sub hrDiff) z z.strictMono
    (fun i ↦ (hroots (s.orderEmbOfFin_mem hcard i)).1)
    (fun i ↦ (hroots (s.orderEmbOfFin_mem hcard i)).2)

/-- **Gap 10.5.** Lagrange interpolation has the classical derivative remainder at
distinct real nodes. Any compact interval containing the nodes and evaluation point suffices. -/
theorem exists_lagrange_remainder {n : ℕ} (nodes : Fin n → ℝ) (hn : Function.Injective nodes)
    {a b x : ℝ} (hx : x ∈ Icc a b) (ha : ∀ i, nodes i ∈ Icc a b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ n f) :
    ∃ z ∈ Icc a b,
      f x - (Lagrange.interpolate Finset.univ nodes (f ∘ nodes)).eval x =
        iteratedDeriv n f z / n.factorial * ∏ i, (x - nodes i) := by
  classical
  let p := Lagrange.interpolate Finset.univ nodes (f ∘ nodes)
  have hp : p.degree < n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) (f ∘ nodes) hn.injOn
  have hnodal (i : Fin n) : p.eval (nodes i) = f (nodes i) :=
    Lagrange.eval_interpolate_at_node _ hn.injOn (Finset.mem_univ _)
  by_cases hnode : ∃ i, nodes i = x
  · obtain ⟨i, rfl⟩ := hnode
    refine ⟨nodes i, ha i, ?_⟩
    have hprod : (∏ j, (nodes i - nodes j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    rw [hnodal i, sub_self, hprod, mul_zero]
  let q := Lagrange.nodal Finset.univ nodes
  have hqN : q.natDegree = n := by
    simp only [q, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hqEval : q.eval x ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun i _ h ↦ hnode ⟨i, h.symm⟩)
  let c := (f x - p.eval x) / q.eval x
  let r := p + C c * q
  have hrD : r.natDegree ≤ n := by
    simpa only [max_self] using natDegree_add_le_of_le (natDegree_le_of_degree_le hp.le)
      ((natDegree_C_mul_le c q).trans hqN.le)
  have hrC : r.coeff n = c := by
    have hqC : q.coeff n = 1 :=
      hqN ▸ (Lagrange.nodal_monic (s := Finset.univ) (v := nodes)).coeff_natDegree
    simp only [r, coeff_add, coeff_C_mul, coeff_eq_zero_of_degree_lt hp, hqC, mul_one, zero_add]
  obtain ⟨t, htab, htz⟩ := exists_iteratedDeriv_eq_zero_of_nodal_correction
    nodes hn hx ha hnode f hf p q c hnodal
    (fun i ↦ Lagrange.eval_nodal_at_node (Finset.mem_univ i)) (div_mul_cancel₀ _ hqEval).symm
  have hrDiff := contDiff_polynomial_eval n r
  have hder : iteratedDeriv n f t = (n.factorial : ℝ) * c := by
    rw [iteratedDeriv_fun_sub hf.contDiffAt hrDiff.contDiffAt,
      iteratedDeriv_polynomial_eval_of_natDegree_le r hrD, hrC] at htz
    exact sub_eq_zero.mp htz
  refine ⟨t, htab, ?_⟩
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [hder, mul_comm (n.factorial : ℝ), mul_div_cancel_right₀ _ hfac,
    ← Lagrange.eval_nodal]
  exact (div_mul_cancel₀ _ hqEval).symm

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
    (f : ℝ → ℝ) (hf : ContDiff ℝ k f) {M α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1)
    (hhold : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv k f x - iteratedDeriv k f y| ≤ M * |x - y| ^ α) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |f x - p.eval x| ≤ (1 + Real.pi ^ 2 / 2) ^ (k + 1) * M /
        ((∏ j : Fin k, ((n - j.val : ℕ) : ℝ)) * ((n - k : ℕ) : ℝ) ^ α) := by
  sorry

/-- Bernstein ellipse with foci at $-1$ and $1$, parameterized by the sum of semiaxes. -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ := {z | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

/-- Membership in the open Bernstein ellipse. -/
theorem mem_bernsteinEllipse {ρ : ℝ} {z : ℂ} :
    z ∈ bernsteinEllipse ρ ↔ ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹ := by
  unfold bernsteinEllipse
  exact Iff.rfl

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

/-- Chebyshev--Lobatto nodes of degree $n$. Interpolation uses positive degree; for `n = 0`
the single node is `Real.cos 0 = 1`, by the junk value of division by zero. -/
def chebyshevNodes (n : ℕ) (j : Fin (n + 1)) : ℝ := Real.cos (j.val * Real.pi / n)

/-- The defining formula for the Chebyshev--Lobatto nodes. -/
theorem chebyshevNodes_def (n : ℕ) (j : Fin (n + 1)) :
    chebyshevNodes n j = Real.cos (j.val * Real.pi / n) := by
  unfold chebyshevNodes
  rfl

/-- **Synopsis 10.12.** Explicit Chebyshev barycentric weights evaluate the interpolant
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

/-- The defining property of `IsRationalPairOn`. -/
theorem isRationalPairOn_iff {s : Set ℝ} {m n : ℕ} {p q : ℝ[X]} :
    IsRationalPairOn s m n p q ↔ p.natDegree ≤ m ∧ q.natDegree ≤ n ∧ ∀ x ∈ s, q.eval x ≠ 0 := by
  unfold IsRationalPairOn
  exact Iff.rfl

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
def IsPadePair {K : Type*} [Field K] (c : ℕ → K) (m n : ℕ) (p q : K[X]) : Prop :=
  p.natDegree ≤ m ∧ q.natDegree ≤ n ∧ q ≠ 0 ∧
    ∀ k ≤ m + n, p.coeff k = ∑ j ∈ Finset.range (k + 1), q.coeff j * c (k - j)

/-- The defining property of `IsPadePair`. -/
theorem isPadePair_iff {K : Type*} [Field K] {c : ℕ → K} {m n : ℕ} {p q : K[X]} :
    IsPadePair c m n p q ↔ p.natDegree ≤ m ∧ q.natDegree ≤ n ∧ q ≠ 0 ∧
      ∀ k ≤ m + n, p.coeff k = ∑ j ∈ Finset.range (k + 1), q.coeff j * c (k - j) := by
  unfold IsPadePair
  exact Iff.rfl

/-- **Gap 10.14.** Formal Padé pairs exist, and their rational functions agree by
cross-multiplication. -/
theorem exists_padePair_and_eq_cross {K : Type*} [Field K] (c : ℕ → K) (m n : ℕ) :
    ∃ p q : K[X], IsPadePair c m n p q ∧
      ∀ P Q : K[X], IsPadePair c m n P Q → p * Q = P * q := by
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
has normalized Padé approximants in the stated half of the table. Finiteness of `μ` is the
case `k = 0` of the moment hypothesis. -/
theorem exists_padePair_of_stieltjes {μ : Measure ℝ}
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hinf : ∀ s : Finset ℝ, ¬(∀ᵐ x ∂μ, x ∈ s))
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ)
    (m n : ℕ) (hmn : n ≤ m + 1) :
    ∃ p q : ℂ[X], IsPadePair (fun k ↦ (-1 : ℂ) ^ k * (∫ x, x ^ k ∂μ : ℝ)) m n p q ∧
      q.eval 0 = 1 := by
  sorry

end NASC
