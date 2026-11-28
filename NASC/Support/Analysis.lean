module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Calculus and analysis helpers

Topic-free facts from one-variable calculus used by several files of the library: a
derivative bound along a segment, derivatives along an affine path, continuity from
derivatives within a set, the generalized Rolle theorem, derivatives of polynomial
evaluation, and the injectivity of the complex exponential on a horizontal strip.

## Main results

* `NASC.norm_sub_endpoints_le_half`: `‖f 1 - f 0‖ ≤ C / 2` when `‖f' t‖ ≤ C t` on `[0, 1]`.
* `NASC.HasFDerivAt.hasDerivAt_comp_add_smul`: the derivative of `s ↦ f (x + s • d)`.
* `NASC.continuousOn_of_forall_hasDerivWithinAt`: differentiability within a set gives
  continuity on it.
* `NASC.exists_iteratedDeriv_eq_zero_of_strictMono`: the generalized Rolle theorem.
* `NASC.iteratedDeriv_polynomial_eval`, `NASC.iteratedDeriv_polynomial_eval_of_natDegree_le`,
  `NASC.contDiff_polynomial_eval`: polynomial evaluation is smooth, with its iterated
  derivatives given by formal differentiation.
* `NASC.exp_injOn_im_mem_Ico`: `Complex.exp` is injective on `-π ≤ im z < π`.
-/

public section

namespace NASC

open Set Polynomial

/-- A linear bound for the derivative along a unit-interval path integrates to half its slope. -/
theorem norm_sub_endpoints_le_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C : ℝ} (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖f' t‖ ≤ C * t) :
    ‖f 1 - f 0‖ ≤ C / 2 := by
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le (B := fun t : ℝ ↦ C * t) zero_le_one
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun t ht ↦ by
      rw [(hd t (Ioo_subset_Icc_self ht)).deriv]
      exact hC t (Ioo_subset_Icc_self ht))
    ((continuous_const.mul continuous_id).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, integral_id, one_pow, zero_pow (by decide),
    sub_zero] at h
  linarith only [h]

/-- The scalar derivative of a composition with an affine path, given its Fréchet derivative. -/
theorem HasFDerivAt.hasDerivAt_comp_add_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {D : E →L[ℝ] F} {x d : E}
    {t : ℝ} (hf : HasFDerivAt f D (x + t • d)) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • d)) (D d) t := by
  simpa only [one_smul, Function.comp_def, id_eq] using
    hf.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)

/-- A function with a derivative within `X` at every point of `X` is continuous on `X`. -/
theorem continuousOn_of_forall_hasDerivWithinAt {f : ℝ → ℝ} {X D : Set ℝ}
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d X x) : ContinuousOn f X :=
  fun x hx ↦ (hderiv x hx).choose_spec.2.continuousWithinAt

/-- A real function with $n+1$ ordered zeros on an interval has a zero of its
$n$-th derivative there. -/
theorem exists_iteratedDeriv_eq_zero_of_strictMono {n : ℕ} {a b : ℝ} (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) (x : Fin (n + 1) → ℝ) (hm : StrictMono x)
    (hx : ∀ i, x i ∈ Icc a b) (hz : ∀ i, f (x i) = 0) :
    ∃ z ∈ Icc a b, iteratedDeriv n f z = 0 := by
  induction n generalizing f with
  | zero => exact ⟨x 0, hx 0, by simpa only [iteratedDeriv_zero] using hz 0⟩
  | succ n ih =>
      have h (i : Fin (n + 1)) :
          ∃ z ∈ Ioo (x i.castSucc) (x i.succ), deriv f z = 0 :=
        exists_deriv_eq_zero (hm Fin.castSucc_lt_succ) hf.continuous.continuousOn
          ((hz i.castSucc).trans (hz i.succ).symm)
      choose z hI hzero using h
      have hmono : StrictMono z := by
        intro i j hij
        exact (hI i).2.trans_le
          ((hm.monotone (Fin.succ_le_castSucc_iff.mpr hij)).trans (hI j).1.le)
      have hmem (i) : z i ∈ Icc a b :=
        ⟨(hx i.castSucc).1.trans (hI i).1.le, (hI i).2.le.trans (hx i.succ).2⟩
      have hd : ContDiff ℝ n (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
      simpa only [iteratedDeriv_succ'] using ih (deriv f) hd z hmono hmem hzero

/-- The iterated analytic derivative of polynomial evaluation agrees with iterated
formal differentiation. -/
theorem iteratedDeriv_polynomial_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n : ℕ) (p : 𝕜[X]) :
    iteratedDeriv n (fun t ↦ p.eval t) = fun x ↦ (derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp only [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ n ih =>
      have he : deriv (fun t ↦ p.eval t) = fun x ↦ p.derivative.eval x :=
        funext fun _ ↦ Polynomial.deriv p
      rw [iteratedDeriv_succ', he, Function.iterate_succ_apply]
      exact ih _

/-- At the degree bound, the derivative is the top coefficient multiplied by the
factorial of its index. -/
theorem iteratedDeriv_polynomial_eval_of_natDegree_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (p : 𝕜[X]) {n : ℕ} (h : p.natDegree ≤ n) (x : 𝕜) :
    iteratedDeriv n (fun t ↦ p.eval t) x = (n.factorial : 𝕜) * p.coeff n := by
  have hzero : (derivative^[n] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p n).trans (by rw [Nat.sub_eq_zero_of_le h])
  have he := congrArg (Polynomial.eval x) (eq_C_of_natDegree_le_zero hzero)
  rw [iteratedDeriv_polynomial_eval]
  dsimp only
  rw [he, eval_C, coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]

/-- Polynomial evaluation is smooth, indeed analytic. -/
theorem contDiff_polynomial_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞)
    (p : 𝕜[X]) : ContDiff 𝕜 n (fun t ↦ p.eval t) := by
  have he : (fun t : 𝕜 ↦ aeval t p) = fun t ↦ p.eval t :=
    funext fun t ↦ congrFun (coe_aeval_eq_eval t) p
  rw [← he]
  exact Polynomial.contDiff_aeval p n

/-- The complex exponential is injective on the half-open strip `-π ≤ im z < π`. -/
theorem exp_injOn_im_mem_Ico :
    Set.InjOn Complex.exp {x | x.im ∈ Set.Ico (-Real.pi) Real.pi} := by
  intro x hx y hy he
  simp only [Set.mem_ofPred_eq, Set.mem_Ico] at hx hy
  have hneg : Complex.exp (-x) = Complex.exp (-y) := by
    rw [Complex.exp_neg, Complex.exp_neg, he]
  apply neg_injective
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ hneg
  · simpa only [Complex.neg_im, neg_lt_neg_iff] using hx.2
  · simpa only [Complex.neg_im, neg_neg] using neg_le_neg hx.1
  · simpa only [Complex.neg_im, neg_lt_neg_iff] using hy.2
  · simpa only [Complex.neg_im, neg_neg] using neg_le_neg hy.1

end NASC
