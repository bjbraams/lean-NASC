module

public import NASC.DirectMethods
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Nonlinear equations and algorithmic differentiation

Bisection, secant and Newton convergence, tangent predictors, and derivative propagation
through finite programs. See section 8 of the gap catalogue.
The local error estimates use Mathlib's integrated derivative bound.
-/

public section

noncomputable section

namespace NASC

open Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- One bisection step, selecting the half whose left endpoint still has negative value. -/
def bisect (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  let m := (ab.1 + ab.2) / 2
  if f m < 0 then (m, ab.2) else (ab.1, m)

/-- **Gap 8.3.** Nested bisection intervals contain a common root, with exact geometric
width and midpoint error. -/
theorem exists_bisection_root {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ z ∈ Icc a b, f z = 0 ∧ ∀ k : ℕ,
      let ab := (bisect f)^[k] (a, b)
      z ∈ Icc ab.1 ab.2 ∧ f ab.1 < 0 ∧ 0 ≤ f ab.2 ∧
        ab.2 - ab.1 = (b - a) / 2 ^ k ∧ |(ab.1 + ab.2) / 2 - z| ≤ (b - a) / 2 ^ (k + 1) := by
  let p := fun k : ℕ ↦ (bisect f)^[k] (a, b)
  let J := fun k ↦ Icc (p k).1 (p k).2
  have hp (k : ℕ) : p (k + 1) = bisect f (p k) := Function.iterate_succ_apply' ..
  have hs (k : ℕ) :
      (p k).1 ≤ (p k).2 ∧ f (p k).1 < 0 ∧ 0 ≤ f (p k).2 ∧
        (p k).2 - (p k).1 = (b - a) / 2 ^ k := by
    induction k with
    | zero => exact ⟨hab.le, ha, hb.le, by norm_num [p]⟩
    | succ k ih =>
      rw [hp k]
      rw [bisect]
      split
      · refine ⟨by linarith [ih.1], ‹_›, ih.2.2.1, ?_⟩
        rw [pow_succ, ← div_div, ← ih.2.2.2]
        ring
      · refine ⟨by linarith [ih.1], ih.2.1, le_of_not_gt ‹_›, ?_⟩
        rw [pow_succ, ← div_div, ← ih.2.2.2]
        ring
  have hJ (k : ℕ) : J (k + 1) ⊆ J k := by
    dsimp only [J]
    rw [hp k]
    rw [bisect]
    split
    · exact Icc_subset_Icc_left (by linarith [(hs k).1])
    · exact Icc_subset_Icc_right (by linarith [(hs k).1])
  have habJ (k : ℕ) : J k ⊆ Icc a b := antitone_nat_of_succ_le hJ (Nat.zero_le k)
  let R := fun k ↦ J k ∩ f ⁻¹' {0}
  have hclosed (k : ℕ) : IsClosed (R k) :=
    (hf.mono (habJ k)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hne (k : ℕ) : (R k).Nonempty := by
    obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc (hs k).1 (hf.mono (habJ k))
      (mem_Icc.mpr ⟨(hs k).2.1.le, (hs k).2.2.1⟩ : (0 : ℝ) ∈ Icc (f (p k).1) (f (p k).2))
    exact ⟨z, hz, hzero⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed R
    (fun k ↦ inter_subset_inter_left _ (hJ k)) hne
    (isCompact_Icc.of_isClosed_subset (hclosed 0) inter_subset_left) hclosed
  have hzR := mem_iInter.mp hz
  refine ⟨z, (hzR 0).1, (hzR 0).2, fun k ↦ ?_⟩
  refine ⟨(hzR k).1, (hs k).2.1, (hs k).2.2.1, (hs k).2.2.2, ?_⟩
  have hbounds : (p k).1 ≤ z ∧ z ≤ (p k).2 := (hzR k).1
  rw [pow_succ, ← div_div, ← (hs k).2.2.2]
  exact abs_le.mpr ⟨by linarith [hbounds.2], by linarith [hbounds.1]⟩

/-- One secant step, holding the current point fixed after an exact zero. -/
def secantStep (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, if f x.2 = 0 then x.2 else x.2 - f x.2 * (x.2 - x.1) / (f x.2 - f x.1))

/-- **Gap 8.4.** A nonvanishing derivative and the local curvature bound imply the
golden-ratio error estimate for the secant iteration. -/
theorem secant_error_le_rpow {f : ℝ → ℝ} {z a b r M : ℝ}
    (hf : ContDiff ℝ 2 f) (hz : f z = 0)
    (ha : a ∈ Icc (z - r) (z + r)) (hb : b ∈ Icc (z - r) (z + r)) (hab : a ≠ b)
    (hM : 0 ≤ M) (hsmall : r * M < 1)
    (hne : ∀ x ∈ Icc (z - r) (z + r), deriv f x ≠ 0)
    (hbound : ∀ s ∈ Icc (z - r) (z + r), ∀ t ∈ Icc (z - r) (z + r),
      |iteratedDeriv 2 f s / (2 * deriv f t)| ≤ M) :
    let p := (1 + Real.sqrt 5) / 2
    let E := max (M * |a - z|) ((M * |b - z|) ^ (1 / p))
    let x := fun k ↦ ((secantStep f)^[k] (a, b)).1
    (∀ k : ℕ, x k ∈ Icc (z - r) (z + r) ∧ M * |x k - z| ≤ E ^ (p ^ k)) ∧
      Tendsto x atTop (nhds z) := by
  sorry

section Newton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Newton step at a point where the derivative is bijective. Theorems using it give
the bijectivity needed for the inverse function to be the linear inverse. -/
def newtonStep {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : E :=
  x - Function.invFun (fderiv ℝ f x) (f x)

/-- **Gap 8.5.** Local quadratic Newton convergence on the guaranteed ball around a
nondegenerate root, with uniform Lipschitz control of the derivative. -/
theorem newtonStep_iterate_quadratic {f : E → E} {z x₀ : E} {C L R : ℝ}
    (D : E ≃L[ℝ] E) (hD : HasFDerivAt f (D : E →L[ℝ] E) z)
    (hC : 0 < C) (hCi : ‖(D.symm : E →L[ℝ] E)‖ ≤ C)
    (hL : 0 < L) (hR : 0 < R) (hz : f z = 0)
    (hf : ∀ x ∈ Metric.ball z R, DifferentiableAt ℝ f x)
    (hLip : ∀ x ∈ Metric.ball z R, ∀ y ∈ Metric.ball z R,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖)
    (hx : x₀ ∈ Metric.ball z (min R (1 / (2 * C * L)))) :
    let x := fun k ↦ (newtonStep f)^[k] x₀
    Tendsto x atTop (nhds z) ∧ ∀ k : ℕ, x k ∈ Metric.ball z (min R (1 / (2 * C * L))) ∧
      Function.Bijective (fderiv ℝ f (x k)) ∧ ‖x (k + 1) - z‖ ≤ C * L * ‖x k - z‖ ^ 2 := by
  sorry

/-- **Gap 8.6.** The Newton--Kantorovich majorant gives a root and a quantitative
iteration bound. Continuity holds on the closed majorant ball, including in the critical case. -/
theorem exists_newtonKantorovich_root {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x₀ : E} (D : E ≃L[ℝ] F)
    (hD : HasFDerivAt f (D : E →L[ℝ] F) x₀) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsmall : a * b * c ≤ 1 / 2)
    (hinit : ‖D.symm (f x₀)‖ ≤ a) (hinv : ‖(D.symm : F →L[ℝ] E)‖ ≤ b)
    (hf : ∀ x ∈ Metric.ball x₀ (1 / (b * c)), DifferentiableAt ℝ f x)
    (hcont : ContinuousOn f
      (Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * a * b * c)) / (b * c))))
    (hLip : ∀ x ∈ Metric.ball x₀ (1 / (b * c)),
      ∀ y ∈ Metric.ball x₀ (1 / (b * c)), ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ c * ‖x - y‖) :
    let r := 1 / (b * c)
    let r₀ := (1 - Real.sqrt (1 - 2 * a * b * c)) * r
    let r₁ := (1 + Real.sqrt (1 - 2 * a * b * c)) * r
    (∀ y ∈ Metric.ball x₀ r, Function.Bijective (fderiv ℝ f y)) ∧
    ∃ z ∈ Metric.closedBall x₀ r₀, f z = 0 ∧
      (∀ k : ℕ, let x := (newtonStep f)^[k] x₀
        x ∈ Metric.ball x₀ r₀ ∧ ‖x - z‖ ≤ r / 2 ^ k * (r₀ / r) ^ (2 ^ k)) ∧
      Tendsto (fun k : ℕ ↦ (newtonStep f)^[k] x₀) atTop (nhds z) ∧
      (a * b * c = 1 / 2 → ∀ y ∈ Metric.closedBall x₀ r, f y = 0 → y = z) ∧
      (a * b * c < 1 / 2 →
        (∀ x ∈ Metric.ball x₀ r₁, DifferentiableAt ℝ f x) →
        (∀ x ∈ Metric.ball x₀ r₁, ∀ y ∈ Metric.ball x₀ r₁,
          ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ c * ‖x - y‖) →
        ∀ y ∈ Metric.ball x₀ r₁, f y = 0 → y = z) := by
  sorry

/-- **Gap 8.8.** Any damped Newton sequence with Armijo backtracking on the squared
residual has only zeros as cluster points under the compact-level-set hypotheses. -/
theorem eq_zero_of_mapClusterPt_dampedNewton {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) {z : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1) (hf : ContDiff ℝ 1 f)
    (hK : IsCompact {y | ‖f y‖ ≤ ‖f (x 0)‖})
    (hD : ∀ y, ‖f y‖ ≤ ‖f (x 0)‖ → Function.Bijective (fderiv ℝ f y))
    (hstep : ∀ k, ∃ j : ℕ,
      let d := Function.invFun (fderiv ℝ f (x k)) (f (x k))
      let y := fun i : ℕ ↦ x k - ((2 : ℝ)⁻¹ ^ i) • d
      x (k + 1) = y j ∧
        ‖f (y j)‖ ^ 2 ≤ (1 - σ * (2 : ℝ)⁻¹ ^ j) * ‖f (x k)‖ ^ 2 ∧
        ∀ i < j, (1 - σ * (2 : ℝ)⁻¹ ^ i) * ‖f (x k)‖ ^ 2 < ‖f (y i)‖ ^ 2)
    (hz : MapClusterPt z atTop x) : f z = 0 := by
  sorry

/-- **Gap 8.9.** Inexact Newton iterates close to a nondegenerate zero converge with
a uniform linear factor when their forcing terms are sufficiently small. -/
theorem exists_inexactNewton_linear_bound {f : E → E} {z : E} (hf : ContDiff ℝ 1 f)
    (hz : f z = 0) (hD : Function.Bijective (fderiv ℝ f z)) :
    ∃ δ > (0 : ℝ), ∃ η > (0 : ℝ), ∃ q ∈ Ioo (0 : ℝ) 1,
      ∀ x p : ℕ → E, x 0 ∈ Metric.ball z δ →
      (∀ k, x (k + 1) = x k + p k ∧
        ‖f (x k) + fderiv ℝ f (x k) (p k)‖ ≤ η * ‖f (x k)‖) →
      ∀ k, ‖x (k + 1) - z‖ ≤ q * ‖x k - z‖ := by
  sorry

end Newton

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
theorem hasDerivAt_along_add_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {D : E →L[ℝ] F} {x d : E}
    {t : ℝ} (hf : HasFDerivAt f D (x + t • d)) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • d)) (D d) t := by
  simpa only [one_smul, Function.comp_def, id_eq] using
    hf.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)

/-- **Gap 8.11.** The local Gauss--Newton error follows from the scaled Jacobian
variation bound and the small stationary-residual term. -/
theorem norm_gaussNewtonStep_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x z : E} (P : F →L[ℝ] E) {ω κ : ℝ}
    (hf : ContDiff ℝ 1 f) (hP : ∀ v, P (fderiv ℝ f x v) = v)
    (hres : ‖P (f z)‖ ≤ κ * ‖x - z‖)
    (hvar : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖P ((fderiv ℝ f (x + s • (z - x)) - fderiv ℝ f x) (z - x))‖ ≤
        s * ω * ‖z - x‖ ^ 2) :
    ‖x - P (f x) - z‖ ≤ (ω / 2) * ‖x - z‖ ^ 2 + κ * ‖x - z‖ := by
  let d := z - x
  let e := fun t : ℝ ↦ P (f (x + t • d) - f x - t • fderiv ℝ f x d)
  have hde (t : ℝ) : HasDerivAt e
      (P ((fderiv ℝ f (x + t • d) - fderiv ℝ f x) d)) t := by
    have h := hasDerivAt_along_add_smul (hf.differentiable one_ne_zero (x + t • d)).hasFDerivAt
    simpa only [e, sub_apply, one_smul, Function.comp_def, Pi.sub_apply, id_eq] using
      P.hasFDerivAt.comp_hasDerivAt t
        ((h.sub_const (f x)).sub ((hasDerivAt_id t).smul_const (fderiv ℝ f x d)))
  have hnorm : ‖e 1 - e 0‖ ≤ (ω * ‖d‖ ^ 2) / 2 :=
    norm_sub_endpoints_le_half (fun t _ ↦ hde t) (fun t ht ↦ by
      simpa only [mul_assoc, mul_comm t] using hvar t ht)
  have heq : e 1 - e 0 = (x - P (f x) - z) + P (f z) := by
    simp only [e, d, one_smul, zero_smul, add_sub_cancel, add_zero, sub_self, sub_zero,
      map_zero, map_sub, hP]
    abel
  rw [heq] at hnorm
  have hsplit : x - P (f x) - z =
      ((x - P (f x) - z) + P (f z)) + (-P (f z)) := by abel
  calc
    _ ≤ ‖(x - P (f x) - z) + P (f z)‖ + ‖P (f z)‖ := by
      conv_lhs => rw [hsplit]
      simpa only [norm_neg] using norm_add_le ((x - P (f x) - z) + P (f z)) (-P (f z))
    _ ≤ (ω * ‖d‖ ^ 2) / 2 + κ * ‖x - z‖ := add_le_add hnorm hres
    _ = _ := by rw [norm_sub_rev z x]; ring

/-- **Gap 8.13.** The tangent predictor has a quadratic error with the half-curvature
constant. -/
theorem norm_sub_tangentPredictor_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {r C t : ℝ} (hf : ContDiff ℝ 2 f) (ht : |t| ≤ r)
    (hC : ∀ s ∈ Icc (-r) r, ‖iteratedDeriv 2 f s‖ ≤ C) :
    ‖f t - (f 0 + t • deriv f 0)‖ ≤ C / 2 * |t| ^ 2 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv' 1
  have hdd (y : ℝ) : deriv (deriv f) y = iteratedDeriv 2 f y := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h0 : (0 : ℝ) ∈ Icc (-r) r := by
    have hr := (abs_nonneg t).trans ht
    exact ⟨neg_nonpos_of_nonneg hr, hr⟩
  let e := fun s : ℝ ↦ f (s * t) - f 0 - (s * t) • deriv f 0
  have hde (s : ℝ) : HasDerivAt e (t • (deriv f (s * t) - deriv f 0)) s := by
    have hp : HasDerivAt (fun u : ℝ ↦ u * t) t s := by
      simpa only [one_mul, id_eq] using (hasDerivAt_id s).mul_const t
    simpa only [e, smul_sub, Function.comp_def] using
      (((hfd (s * t)).hasDerivAt.scomp s hp).sub_const (f 0)).fun_sub
        (hp.smul_const (deriv f 0))
  have hn : ‖e 1 - e 0‖ ≤ (C * |t| ^ 2) / 2 := by
    apply norm_sub_endpoints_le_half (fun s _ ↦ hde s)
    intro s hs
    have hsabs : |s| = s := abs_of_nonneg hs.1
    have htmem : s * t ∈ Icc (-r) r := abs_le.mp <| calc
      |s * t| = s * |t| := by rw [abs_mul, hsabs]
      _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg t)
      _ ≤ r := by simpa only [one_mul] using ht
    have hsub := (convex_Icc (-r) r).norm_image_sub_le_of_norm_deriv_le
      (fun y _ ↦ hg y) (fun y hy ↦ by rw [hdd]; exact hC y hy) h0 htmem
    rw [sub_zero, Real.norm_eq_abs, abs_mul, hsabs] at hsub
    calc
      _ = |t| * ‖deriv f (s * t) - deriv f 0‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * (C * (s * |t|)) := mul_le_mul_of_nonneg_left hsub (abs_nonneg t)
      _ = _ := by ring
  simp only [e, one_mul, zero_mul, sub_self, zero_smul, sub_zero] at hn
  rw [sub_sub] at hn
  linarith only [hn]

/-- One scalar instruction of an arithmetic program. Register indices appear as operands. -/
inductive ScalarInstruction (ι : Type*)
  | constant (x : ℝ)
  | add (left right : ι)
  | mul (left right : ι)
  | unary (f : ℝ → ℝ) (input : ι)

namespace ScalarInstruction

variable {ι : Type*}

/-- Evaluate an instruction using the current register state. -/
def eval (x : ι → ℝ) : ScalarInstruction ι → ℝ
  | .constant a => a
  | .add i j => x i + x j
  | .mul i j => x i * x j
  | .unary f i => f (x i)

/-- Propagate a tangent through one instruction. -/
def tangent (x dx : ι → ℝ) : ScalarInstruction ι → ℝ
  | .constant _ => 0
  | .add i j => dx i + dx j
  | .mul i j => dx i * x j + x i * dx j
  | .unary f i => deriv f (x i) * dx i

/-- The unary operations have differentiable primitives. -/
def DifferentiablePrimitive : ScalarInstruction ι → Prop
  | .unary f _ => Differentiable ℝ f
  | _ => True

/-- The tangent of a scalar instruction as a continuous linear map of register increments. -/
def tangentMap [Fintype ι] (x : ι → ℝ) : ScalarInstruction ι → (ι → ℝ) →L[ℝ] ℝ
  | .constant _ => 0
  | .add i j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i +
    ContinuousLinearMap.proj j
  | .mul i j => x j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i +
    x i • ContinuousLinearMap.proj j
  | .unary f i => deriv f (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i

/-- The continuous linear tangent map applies the instruction's tangent rule. -/
theorem tangentMap_apply [Fintype ι] (a : ScalarInstruction ι) (x dx : ι → ℝ) :
    a.tangentMap x dx = a.tangent x dx := by
  cases a <;> simp [tangentMap, tangent, mul_comm]

/-- Differentiating the scalar evaluation gives the instruction's tangent map. -/
theorem hasFDerivAt_eval [Fintype ι] (a : ScalarInstruction ι)
    (ha : a.DifferentiablePrimitive) (x : ι → ℝ) :
    HasFDerivAt (fun v ↦ a.eval v) (a.tangentMap x) x := by
  cases a with
  | constant c => simpa only [eval, tangentMap] using hasFDerivAt_const (𝕜 := ℝ) c x
  | add i j => exact (hasFDerivAt_apply (𝕜 := ℝ) i x).add (hasFDerivAt_apply j x)
  | mul i j =>
    simpa only [eval, tangentMap, add_comm] using
      (hasFDerivAt_apply (𝕜 := ℝ) i x).fun_mul (hasFDerivAt_apply j x)
  | unary f i =>
    exact ((ha (x i)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x))

/-- The tangent map for an instruction writing to one register. -/
def updateTangentMap [Fintype ι] [DecidableEq ι] (a : ι × ScalarInstruction ι) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (Function.update ContinuousLinearMap.proj a.1 (a.2.tangentMap x))

/-- The derivative of a single register write updates the same coordinate of the tangent. -/
theorem updateTangentMap_apply [Fintype ι] [DecidableEq ι] (a : ι × ScalarInstruction ι)
    (x dx : ι → ℝ) :
    updateTangentMap a x dx = Function.update dx a.1 (a.2.tangent x dx) := by
  funext i
  simp only [updateTangentMap, ContinuousLinearMap.pi_apply]
  by_cases hi : i = a.1
  · subst i
    simp only [Function.update_self, tangentMap_apply]
  · simp only [Function.update_of_ne hi, ContinuousLinearMap.proj_apply]

/-- The derivative of a register write retains all untouched register coordinates. -/
theorem hasFDerivAt_update_eval [Fintype ι] [DecidableEq ι] (a : ι × ScalarInstruction ι)
    (ha : a.2.DifferentiablePrimitive) (x : ι → ℝ) :
    HasFDerivAt (fun v ↦ Function.update v a.1 (a.2.eval v)) (updateTangentMap a x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = a.1
  · subst i
    simpa only [Function.update_self] using a.2.hasFDerivAt_eval ha x
  · simpa only [Function.update_of_ne hi] using hasFDerivAt_apply i x

/-- **Gap 8.14.** Forward propagation through an ordered register program computes the
Fréchet derivative applied to the input tangent. Overwriting is allowed here. -/
theorem evalProgram_fderiv_apply [Fintype ι] [DecidableEq ι]
    (program : List (ι × ScalarInstruction ι))
    (h : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx : ι → ℝ) :
    let run := fun input : ι → ℝ ↦ program.foldl
      (fun v a ↦ Function.update v a.1 (a.2.eval v)) input
    let forward := program.foldl (fun (v, dv) a ↦
      (Function.update v a.1 (a.2.eval v), Function.update dv a.1 (a.2.tangent v dv))) (x, dx)
    fderiv ℝ run x dx = forward.2 := by
  induction program generalizing x dx with
  | nil =>
    exact congrFun (congrArg DFunLike.coe (fderiv_id (𝕜 := ℝ) (x := x))) dx
  | cons a rest ih =>
    dsimp only [List.foldl_cons]
    let step := fun v : ι → ℝ ↦ Function.update v a.1 (a.2.eval v)
    let runRest := fun v : ι → ℝ ↦ rest.foldl
      (fun v b ↦ Function.update v b.1 (b.2.eval v)) v
    have ha : a.2.DifferentiablePrimitive := h a List.mem_cons_self
    have hrest : ∀ b ∈ rest, (b : ι × ScalarInstruction ι).2.DifferentiablePrimitive :=
      fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have hdiff : DifferentiableAt ℝ runRest (step x) := by
      have haux (p : List (ι × ScalarInstruction ι))
          (hp : ∀ b ∈ p, b.2.DifferentiablePrimitive) (v : ι → ℝ) :
          DifferentiableAt ℝ (fun y ↦ p.foldl
            (fun v b ↦ Function.update v b.1 (b.2.eval v)) y) v := by
        induction p generalizing v with
        | nil => exact differentiableAt_id
        | cons c s ihs =>
          have hc := hasFDerivAt_update_eval c (hp c List.mem_cons_self) v
          exact (ihs (fun b hb ↦ hp b (List.mem_cons_of_mem _ hb)) _).comp v hc.differentiableAt
      exact haux rest hrest _
    have hstep := hasFDerivAt_update_eval a ha x
    have heq := congrFun (congrArg DFunLike.coe (hdiff.hasFDerivAt.comp x hstep).fderiv) dx
    rw [ContinuousLinearMap.comp_apply, updateTangentMap_apply] at heq
    exact heq.trans (ih hrest (step x) _)

/-- Pullback through one register write preserves the pairing with the updated tangent. -/
theorem updateTangent_dot_eq [Fintype ι] [DecidableEq ι] (a : ι × ScalarInstruction ι)
    (x dx c : ι → ℝ) :
    (∑ j, ((if j = a.1 then 0 else c j) +
      c a.1 * a.2.tangent x (Pi.single j 1)) * dx j) =
      ∑ j, c j * Function.update dx a.1 (a.2.tangent x dx) j := by
  have hsingle : (∑ j : ι, dx j • Pi.single j (1 : ℝ)) = dx := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_zero, mul_one]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hlin : (∑ j, a.2.tangent x (Pi.single j 1) * dx j) = a.2.tangent x dx := by
    simp_rw [← tangentMap_apply, mul_comm ((a.2.tangentMap x) _), ← smul_eq_mul, ← map_smul]
    rw [← map_sum, hsingle]
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, hlin]
  have hone : c a.1 * a.2.tangent x dx =
      ∑ j : ι, if j = a.1 then c j * a.2.tangent x dx else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hone, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j = a.1
  · subst j
    simp only [ite_true, zero_mul, zero_add, Function.update_self]
  · simp only [hj, ite_false, add_zero, Function.update_of_ne hj]

/-- Pullback through the whole program pairs with forward propagation through the same writes. -/
theorem reverseProgram_dot_eq [Fintype ι] [DecidableEq ι]
    (program : List (ι × ScalarInstruction ι)) (x dx seed : ι → ℝ) :
    let step := fun (v : ι → ℝ) (a : ι × ScalarInstruction ι) ↦
      Function.update v a.1 (a.2.eval v)
    let back := (List.range program.length).reverse.foldl
      (fun c k ↦
        match program[k]? with
        | none => c
        | some a => fun j ↦ (if j = a.1 then 0 else c j) +
          c a.1 * a.2.tangent ((program.take k).foldl step x) (Pi.single j 1)) seed
    let forward := program.foldl (fun (v, dv) a ↦
      (step v a, Function.update dv a.1 (a.2.tangent v dv))) (x, dx)
    (∑ j, back j * dx j) = ∑ j, seed j * forward.2 j := by
  induction program generalizing x dx with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [List.length_cons]
    rw [List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse, List.foldl_append,
      List.foldl_map, List.foldl_cons, List.foldl_nil]
    simp only [List.getElem?_cons_succ, List.take_succ_cons, List.foldl_cons,
      List.getElem?_cons_zero, List.take_zero, List.foldl_nil]
    rw [updateTangent_dot_eq]
    exact ih _ _

/-- **Gap 8.14.** Reverse accumulation computes the transposed derivative of a
register program. Retaining the old register state handles overwrites and repeated operands. -/
theorem evalProgram_reverse_dot_eq [Fintype ι] [DecidableEq ι]
    (program : List (ι × ScalarInstruction ι))
    (hp : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx seed : ι → ℝ) :
    let step := fun (v : ι → ℝ) (a : ι × ScalarInstruction ι) ↦
      Function.update v a.1 (a.2.eval v)
    let run := fun input ↦ program.foldl step input
    let back := (List.range program.length).reverse.foldl
      (fun c k ↦
        match program[k]? with
        | none => c
        | some a => fun j ↦ (if j = a.1 then 0 else c j) +
          c a.1 * a.2.tangent ((program.take k).foldl step x) (Pi.single j 1)) seed
    (∑ j, back j * dx j) = ∑ j, seed j * fderiv ℝ run x dx j := by
  have hfor := evalProgram_fderiv_apply program hp x dx
  have hrev := reverseProgram_dot_eq program x dx seed
  dsimp only at hfor hrev ⊢
  rw [hfor]
  exact hrev

/-- Primal and reverse work in the unit-cost scalar arithmetic model.
One derivative evaluation of a unary primitive is one operation. -/
def reverseWork : ScalarInstruction ι → ℕ × ℕ
  | .constant _ => (0, 0)
  | .add _ _ => (1, 2)
  | .mul _ _ => (1, 4)
  | .unary _ _ => (1, 3)

/-- **Gap 8.15.** Reverse accumulation costs at most four times the primal operation
count in the unit-cost scalar model, in addition to the primal pass. -/
theorem sum_reverseWork_le (program : List (ScalarInstruction ι)) :
    (program.map fun a ↦ a.reverseWork.2).sum ≤ 4 * (program.map fun a ↦ a.reverseWork.1).sum := by
  induction program with
  | nil => simp
  | cons a rest ih =>
    cases a <;> simp_all [reverseWork, Nat.mul_add] <;> omega

end ScalarInstruction

end NASC
