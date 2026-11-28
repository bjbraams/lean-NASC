module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NASC.Support.Analysis

/-!
# Nonlinear equations and algorithmic differentiation

Bisection, secant and Newton convergence (local quadratic convergence, Newton--Kantorovich,
damped and inexact Newton), Gauss--Newton, tangent predictors, and forward and reverse mode
algorithmic differentiation of register programs. See section 8 of the gap catalogue.
The local error estimates use Mathlib's integrated derivative bound.

## Main definitions

* `NASC.bisect`, `NASC.secantStep`, `NASC.newtonStep`: one step of each method.
* `NASC.ScalarInstruction 𝕜 ι`: one instruction of a register program, with its value
  `ScalarInstruction.eval` and tangent rule `ScalarInstruction.tangent`.
* `NASC.ScalarInstruction.evalProgram`, `forwardProgram`, `reverseProgram`: the run of a
  program, its forward (tangent) sweep and its reverse (adjoint) sweep.

## Main results

* `NASC.exists_bisection_root`: nested bisection intervals and the midpoint error.
* `NASC.secant_error_le_rpow`: the golden-ratio order of the secant method.
* `NASC.newtonStep_iterate_quadratic`: local quadratic convergence of Newton's method.
* `NASC.exists_newtonKantorovich_root`: the Newton--Kantorovich theorem.
* `NASC.eq_zero_of_mapClusterPt_dampedNewton`, `NASC.exists_inexactNewton_linear_bound`:
  damped and inexact Newton methods.
* `NASC.norm_gaussNewtonStep_sub_le`: the local Gauss--Newton error.
* `NASC.norm_sub_tangentPredictor_le`: the tangent predictor error.
* `NASC.ScalarInstruction.fderiv_evalProgram_apply`,
  `NASC.ScalarInstruction.sum_reverseProgram_mul_eq_sum_mul_fderiv`: forward and reverse mode.
* `NASC.ScalarInstruction.sum_reverseWork_le`: the reverse-mode cost bound in the unit-cost
  model.
-/

public section

noncomputable section

namespace NASC

open Filter Set

/-- One bisection step, selecting the half whose left endpoint still has negative value. -/
def bisect (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  let m := (ab.1 + ab.2) / 2
  if f m < 0 then (m, ab.2) else (ab.1, m)

/-- The defining formula for one bisection step. -/
theorem bisect_def (f : ℝ → ℝ) (ab : ℝ × ℝ) :
    bisect f ab = if f ((ab.1 + ab.2) / 2) < 0 then ((ab.1 + ab.2) / 2, ab.2)
      else (ab.1, (ab.1 + ab.2) / 2) := by
  unfold bisect
  rfl

/-- One bisection step keeps the sign conditions, halves the width and nests the interval. -/
theorem bisect_spec {f : ℝ → ℝ} {ab : ℝ × ℝ} (h : ab.1 ≤ ab.2) (h₁ : f ab.1 < 0)
    (h₂ : 0 ≤ f ab.2) :
    (bisect f ab).1 ≤ (bisect f ab).2 ∧ f (bisect f ab).1 < 0 ∧ 0 ≤ f (bisect f ab).2 ∧
      (bisect f ab).2 - (bisect f ab).1 = (ab.2 - ab.1) / 2 ∧
      Icc (bisect f ab).1 (bisect f ab).2 ⊆ Icc ab.1 ab.2 := by
  rw [bisect_def]
  split
  · exact ⟨by linarith only [h], ‹_›, h₂, by ring, Icc_subset_Icc_left (by linarith only [h])⟩
  · exact ⟨by linarith only [h], h₁, le_of_not_gt ‹_›, by ring,
      Icc_subset_Icc_right (by linarith only [h])⟩

/-- The bisection iterates keep the sign conditions and have geometric width. -/
theorem bisect_iterate_spec {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : f a < 0) (hb : 0 ≤ f b)
    (k : ℕ) :
    ((bisect f)^[k] (a, b)).1 ≤ ((bisect f)^[k] (a, b)).2 ∧ f ((bisect f)^[k] (a, b)).1 < 0 ∧
      0 ≤ f ((bisect f)^[k] (a, b)).2 ∧
      ((bisect f)^[k] (a, b)).2 - ((bisect f)^[k] (a, b)).1 = (b - a) / 2 ^ k := by
  induction k with
  | zero => exact ⟨hab, ha, hb, by norm_num⟩
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih
    obtain ⟨g₁, g₂, g₃, g₄, -⟩ := bisect_spec h₁ h₂ h₃
    rw [Function.iterate_succ_apply']
    exact ⟨g₁, g₂, g₃, by rw [g₄, h₄, pow_succ, div_div]⟩

/-- **Gap 8.3.** Nested bisection intervals contain a common root, with exact geometric
width and midpoint error. -/
theorem exists_bisection_root {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ z ∈ Icc a b, f z = 0 ∧ ∀ k : ℕ,
      let ab := (bisect f)^[k] (a, b)
      z ∈ Icc ab.1 ab.2 ∧ f ab.1 < 0 ∧ 0 ≤ f ab.2 ∧
        ab.2 - ab.1 = (b - a) / 2 ^ k ∧ |(ab.1 + ab.2) / 2 - z| ≤ (b - a) / 2 ^ (k + 1) := by
  let p := fun k : ℕ ↦ (bisect f)^[k] (a, b)
  let J := fun k ↦ Icc (p k).1 (p k).2
  have hs := bisect_iterate_spec hab ha hb.le
  have hJ (k : ℕ) : J (k + 1) ⊆ J k := by
    dsimp only [J, p]
    rw [Function.iterate_succ_apply']
    exact (bisect_spec (hs k).1 (hs k).2.1 (hs k).2.2.1).2.2.2.2
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

/-- The defining formula for one secant step. -/
theorem secantStep_def (f : ℝ → ℝ) (x : ℝ × ℝ) :
    secantStep f x =
      (x.2, if f x.2 = 0 then x.2 else x.2 - f x.2 * (x.2 - x.1) / (f x.2 - f x.1)) := by
  unfold secantStep
  rfl

/-- **Gap 8.4.** A nonvanishing derivative and the local curvature bound imply the
golden-ratio error estimate for the secant iteration. The constant `M` is nonnegative by
`hbound` at `s = t = a`. -/
theorem secant_error_le_rpow {f : ℝ → ℝ} {z a b r M : ℝ}
    (hf : ∀ x ∈ Icc (z - r) (z + r), ContDiffAt ℝ 2 f x) (hz : f z = 0)
    (ha : a ∈ Icc (z - r) (z + r)) (hb : b ∈ Icc (z - r) (z + r)) (hab : a ≠ b)
    (hsmall : r * M < 1)
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Newton step at a point where the derivative is bijective. Theorems using it give
the bijectivity needed for the inverse function to be the linear inverse. -/
def newtonStep {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : E :=
  x - Function.invFun (fderiv ℝ f x) (f x)

/-- The defining formula for one Newton step. -/
theorem newtonStep_def {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (x : E) : newtonStep f x = x - Function.invFun (fderiv ℝ f x) (f x) := by
  unfold newtonStep
  rfl

/-- When the derivative is surjective, the Newton correction solves the linearized equation. -/
theorem fderiv_sub_newtonStep {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {x : E} (h : Function.Surjective (fderiv ℝ f x)) :
    fderiv ℝ f x (x - newtonStep f x) = f x := by
  rw [newtonStep_def, sub_sub_cancel]
  exact Function.invFun_eq (h (f x))

/-- When the derivative is bijective, the Newton step is `x - d` for the unique solution `d`
of the linearized equation. -/
theorem newtonStep_eq_sub_of_bijective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x d : E} (h : Function.Bijective (fderiv ℝ f x))
    (hd : fderiv ℝ f x d = f x) : newtonStep f x = x - d := by
  have he := h.1 ((fderiv_sub_newtonStep h.2).trans hd.symm)
  rw [← he, sub_sub_cancel]

/-- **Gap 8.5.** Local quadratic Newton convergence on the guaranteed ball around a
nondegenerate root, with uniform Lipschitz control of the derivative. -/
theorem newtonStep_iterate_quadratic [CompleteSpace E] {f : E → E} {z x₀ : E} {C L R : ℝ}
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
theorem exists_newtonKantorovich_root [CompleteSpace E] {F : Type*}
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
a uniform linear factor when their forcing terms are sufficiently small. The map is `C¹` on a
neighbourhood of the zero. -/
theorem exists_inexactNewton_linear_bound [CompleteSpace E] {f : E → E} {z : E}
    (hf : ContDiffAt ℝ 1 f z)
    (hz : f z = 0) (hD : Function.Bijective (fderiv ℝ f z)) :
    ∃ δ > (0 : ℝ), ∃ η > (0 : ℝ), ∃ q ∈ Ioo (0 : ℝ) 1,
      ∀ x p : ℕ → E, x 0 ∈ Metric.ball z δ →
      (∀ k, x (k + 1) = x k + p k ∧
        ‖f (x k) + fderiv ℝ f (x k) (p k)‖ ≤ η * ‖f (x k)‖) →
      ∀ k, ‖x (k + 1) - z‖ ≤ q * ‖x k - z‖ := by
  sorry

end Newton

/-- **Gap 8.11.** The local Gauss--Newton error follows from the scaled Jacobian
variation bound and the small stationary-residual term. -/
theorem norm_gaussNewtonStep_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x z : E} (P : F →L[ℝ] E) {ω κ : ℝ}
    (hf : Differentiable ℝ f) (hP : ∀ v, P (fderiv ℝ f x v) = v)
    (hres : ‖P (f z)‖ ≤ κ * ‖x - z‖)
    (hvar : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖P ((fderiv ℝ f (x + s • (z - x)) - fderiv ℝ f x) (z - x))‖ ≤
        s * ω * ‖z - x‖ ^ 2) :
    ‖x - P (f x) - z‖ ≤ (ω / 2) * ‖x - z‖ ^ 2 + κ * ‖x - z‖ := by
  let d := z - x
  let e := fun t : ℝ ↦ P (f (x + t • d) - f x - t • fderiv ℝ f x d)
  have hde (t : ℝ) : HasDerivAt e
      (P ((fderiv ℝ f (x + t • d) - fderiv ℝ f x) d)) t := by
    have h := HasFDerivAt.hasDerivAt_comp_add_smul (hf (x + t • d)).hasFDerivAt
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
    [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- One scalar instruction of an arithmetic program over a field `𝕜`. Register indices of type
`ι` appear as operands. -/
inductive ScalarInstruction (𝕜 : Type*) (ι : Type*)
  /-- A constant. -/
  | constant (x : 𝕜)
  /-- The sum of two registers. -/
  | add (left right : ι)
  /-- The product of two registers. -/
  | mul (left right : ι)
  /-- A unary primitive applied to one register. -/
  | unary (f : 𝕜 → 𝕜) (input : ι)

namespace ScalarInstruction

variable {𝕜 : Type*} {ι : Type*}

/-- Primal and reverse work of one instruction in the unit-cost scalar arithmetic model, as
counted for `adjointStep`: an addition costs two additions, a product two multiplications and
two additions, and a unary primitive one derivative evaluation, one multiplication and one
addition. -/
def reverseWork : ScalarInstruction 𝕜 ι → ℕ × ℕ
  | .constant _ => (0, 0)
  | .add _ _ => (1, 2)
  | .mul _ _ => (1, 4)
  | .unary _ _ => (1, 3)

/-- A constant costs no work. -/
@[simp] theorem reverseWork_constant (a : 𝕜) :
    (constant a : ScalarInstruction 𝕜 ι).reverseWork = (0, 0) := by
  unfold reverseWork
  rfl

/-- The work of an addition. -/
@[simp] theorem reverseWork_add (i j : ι) :
    (add i j : ScalarInstruction 𝕜 ι).reverseWork = (1, 2) := by
  unfold reverseWork
  rfl

/-- The work of a product. -/
@[simp] theorem reverseWork_mul (i j : ι) :
    (mul i j : ScalarInstruction 𝕜 ι).reverseWork = (1, 4) := by
  unfold reverseWork
  rfl

/-- The work of a unary primitive. -/
@[simp] theorem reverseWork_unary (f : 𝕜 → 𝕜) (i : ι) :
    (unary f i : ScalarInstruction 𝕜 ι).reverseWork = (1, 3) := by
  unfold reverseWork
  rfl

/-- **Gap 8.15.** In the unit-cost model `reverseWork`, the reverse sweep of a program costs
at most four times the primal operation count, in addition to the primal pass. This is a
property of the cost table; it does not count the operations of `reverseProgram` itself. -/
theorem sum_reverseWork_le (program : List (ScalarInstruction 𝕜 ι)) :
    (program.map fun a ↦ a.reverseWork.2).sum ≤ 4 * (program.map fun a ↦ a.reverseWork.1).sum := by
  induction program with
  | nil => simp
  | cons a rest ih =>
    cases a <;> simp_all [reverseWork, Nat.mul_add] <;> omega

variable [NontriviallyNormedField 𝕜]

/-- Evaluate an instruction using the current register state. -/
def eval (x : ι → 𝕜) : ScalarInstruction 𝕜 ι → 𝕜
  | .constant a => a
  | .add i j => x i + x j
  | .mul i j => x i * x j
  | .unary f i => f (x i)

/-- A constant instruction evaluates to its constant. -/
@[simp] theorem eval_constant (x : ι → 𝕜) (a : 𝕜) :
    (constant a : ScalarInstruction 𝕜 ι).eval x = a := by
  unfold eval
  rfl

/-- An addition instruction adds its two registers. -/
@[simp] theorem eval_add (x : ι → 𝕜) (i j : ι) :
    (add i j : ScalarInstruction 𝕜 ι).eval x = x i + x j := by
  unfold eval
  rfl

/-- A multiplication instruction multiplies its two registers. -/
@[simp] theorem eval_mul (x : ι → 𝕜) (i j : ι) :
    (mul i j : ScalarInstruction 𝕜 ι).eval x = x i * x j := by
  unfold eval
  rfl

/-- A unary instruction applies its primitive to its register. -/
@[simp] theorem eval_unary (x : ι → 𝕜) (f : 𝕜 → 𝕜) (i : ι) :
    (unary f i : ScalarInstruction 𝕜 ι).eval x = f (x i) := by
  unfold eval
  rfl

/-- Propagate a tangent through one instruction. -/
def tangent (x dx : ι → 𝕜) : ScalarInstruction 𝕜 ι → 𝕜
  | .constant _ => 0
  | .add i j => dx i + dx j
  | .mul i j => dx i * x j + x i * dx j
  | .unary f i => deriv f (x i) * dx i

/-- A constant instruction has zero tangent. -/
@[simp] theorem tangent_constant (x dx : ι → 𝕜) (a : 𝕜) :
    (constant a : ScalarInstruction 𝕜 ι).tangent x dx = 0 := by
  unfold tangent
  rfl

/-- The tangent of an addition is the sum of the tangents. -/
@[simp] theorem tangent_add (x dx : ι → 𝕜) (i j : ι) :
    (add i j : ScalarInstruction 𝕜 ι).tangent x dx = dx i + dx j := by
  unfold tangent
  rfl

/-- The tangent of a product follows the Leibniz rule. -/
@[simp] theorem tangent_mul (x dx : ι → 𝕜) (i j : ι) :
    (mul i j : ScalarInstruction 𝕜 ι).tangent x dx = dx i * x j + x i * dx j := by
  unfold tangent
  rfl

/-- The tangent of a unary primitive follows the chain rule. -/
@[simp] theorem tangent_unary (x dx : ι → 𝕜) (f : 𝕜 → 𝕜) (i : ι) :
    (unary f i : ScalarInstruction 𝕜 ι).tangent x dx = deriv f (x i) * dx i := by
  unfold tangent
  rfl

/-- The unary operations have differentiable primitives. -/
def DifferentiablePrimitive : ScalarInstruction 𝕜 ι → Prop
  | .unary f _ => Differentiable 𝕜 f
  | _ => True

/-- The defining property of `DifferentiablePrimitive`: only unary primitives are
constrained. -/
theorem differentiablePrimitive_iff (a : ScalarInstruction 𝕜 ι) :
    a.DifferentiablePrimitive ↔ ∀ f i, a = unary f i → Differentiable 𝕜 f := by
  cases a <;> simp [DifferentiablePrimitive]

/-- The tangent of a scalar instruction as a continuous linear map of register increments. -/
def tangentMap (x : ι → 𝕜) : ScalarInstruction 𝕜 ι → (ι → 𝕜) →L[𝕜] 𝕜
  | .constant _ => 0
  | .add i j => ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i +
    ContinuousLinearMap.proj j
  | .mul i j => x j • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i +
    x i • ContinuousLinearMap.proj j
  | .unary f i => deriv f (x i) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i

/-- The continuous linear tangent map applies the instruction's tangent rule. -/
theorem tangentMap_apply (a : ScalarInstruction 𝕜 ι) (x dx : ι → 𝕜) :
    a.tangentMap x dx = a.tangent x dx := by
  cases a <;> simp [tangentMap, tangent, mul_comm]

/-- Differentiating the scalar evaluation gives the instruction's tangent map. -/
theorem hasFDerivAt_eval [Fintype ι] (a : ScalarInstruction 𝕜 ι)
    (ha : a.DifferentiablePrimitive) (x : ι → 𝕜) :
    HasFDerivAt (fun v ↦ a.eval v) (a.tangentMap x) x := by
  cases a with
  | constant c => simpa only [eval, tangentMap] using hasFDerivAt_const (𝕜 := 𝕜) c x
  | add i j => exact (hasFDerivAt_apply (𝕜 := 𝕜) i x).add (hasFDerivAt_apply j x)
  | mul i j =>
    simpa only [eval, tangentMap, add_comm] using
      (hasFDerivAt_apply (𝕜 := 𝕜) i x).fun_mul (hasFDerivAt_apply j x)
  | unary f i =>
    exact ((ha (x i)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x))

section Program

variable [DecidableEq ι]

/-- One register write: the instruction `a.2` stores its value in register `a.1`. -/
def evalStep (x : ι → 𝕜) (a : ι × ScalarInstruction 𝕜 ι) : ι → 𝕜 :=
  Function.update x a.1 (a.2.eval x)

/-- The defining formula for one register write. -/
theorem evalStep_def (x : ι → 𝕜) (a : ι × ScalarInstruction 𝕜 ι) :
    evalStep x a = Function.update x a.1 (a.2.eval x) := by
  unfold evalStep
  rfl

/-- The run of an ordered register program; registers may be overwritten. -/
def evalProgram (program : List (ι × ScalarInstruction 𝕜 ι)) (x : ι → 𝕜) : ι → 𝕜 :=
  program.foldl evalStep x

/-- The empty program is the identity. -/
@[simp] theorem evalProgram_nil (x : ι → 𝕜) : evalProgram [] x = x := by
  unfold evalProgram
  rfl

/-- A program runs its first instruction, then the rest. -/
@[simp] theorem evalProgram_cons (a : ι × ScalarInstruction 𝕜 ι)
    (program : List (ι × ScalarInstruction 𝕜 ι)) (x : ι → 𝕜) :
    evalProgram (a :: program) x = evalProgram program (evalStep x a) := by
  unfold evalProgram
  rfl

/-- The forward (tangent) sweep: each register write also updates the tangent register. -/
def forwardProgram : List (ι × ScalarInstruction 𝕜 ι) → (ι → 𝕜) → (ι → 𝕜) → ι → 𝕜
  | [], _, dx => dx
  | a :: rest, x, dx =>
    forwardProgram rest (evalStep x a) (Function.update dx a.1 (a.2.tangent x dx))

/-- The forward sweep of the empty program returns the input tangent. -/
@[simp] theorem forwardProgram_nil (x dx : ι → 𝕜) : forwardProgram [] x dx = dx := by
  rw [forwardProgram]

/-- The forward sweep processes the first instruction, then the rest. -/
@[simp] theorem forwardProgram_cons (a : ι × ScalarInstruction 𝕜 ι)
    (program : List (ι × ScalarInstruction 𝕜 ι)) (x dx : ι → 𝕜) :
    forwardProgram (a :: program) x dx =
      forwardProgram program (evalStep x a) (Function.update dx a.1 (a.2.tangent x dx)) := by
  rw [forwardProgram]

/-- Pullback of an adjoint vector `c` through one register write at state `x`: the written
register is cleared and its adjoint is distributed through the instruction's partial
derivatives. -/
def adjointStep (a : ι × ScalarInstruction 𝕜 ι) (x c : ι → 𝕜) : ι → 𝕜 :=
  fun j ↦ (if j = a.1 then 0 else c j) + c a.1 * a.2.tangent x (Pi.single j 1)

/-- The entries of the pulled-back adjoint. -/
theorem adjointStep_apply (a : ι × ScalarInstruction 𝕜 ι) (x c : ι → 𝕜) (j : ι) :
    adjointStep a x c j = (if j = a.1 then 0 else c j) + c a.1 * a.2.tangent x (Pi.single j 1) := by
  unfold adjointStep
  rfl

/-- The reverse (adjoint) sweep: the seed is pulled back through the last instruction first,
at the register states of the forward run. -/
def reverseProgram : List (ι × ScalarInstruction 𝕜 ι) → (ι → 𝕜) → (ι → 𝕜) → ι → 𝕜
  | [], _, c => c
  | a :: rest, x, c => adjointStep a x (reverseProgram rest (evalStep x a) c)

/-- The reverse sweep of the empty program returns the seed. -/
@[simp] theorem reverseProgram_nil (x c : ι → 𝕜) : reverseProgram [] x c = c := by
  rw [reverseProgram]

/-- The reverse sweep pulls back through the rest of the program, then the first
instruction. -/
@[simp] theorem reverseProgram_cons (a : ι × ScalarInstruction 𝕜 ι)
    (program : List (ι × ScalarInstruction 𝕜 ι)) (x c : ι → 𝕜) :
    reverseProgram (a :: program) x c =
      adjointStep a x (reverseProgram program (evalStep x a) c) := by
  rw [reverseProgram]

/-- The tangent map for an instruction writing to one register. -/
def updateTangentMap (a : ι × ScalarInstruction 𝕜 ι) (x : ι → 𝕜) :
    (ι → 𝕜) →L[𝕜] (ι → 𝕜) :=
  ContinuousLinearMap.pi (Function.update ContinuousLinearMap.proj a.1 (a.2.tangentMap x))

/-- The derivative of a single register write updates the same coordinate of the tangent. -/
theorem updateTangentMap_apply (a : ι × ScalarInstruction 𝕜 ι) (x dx : ι → 𝕜) :
    updateTangentMap a x dx = Function.update dx a.1 (a.2.tangent x dx) := by
  funext i
  simp only [updateTangentMap, ContinuousLinearMap.pi_apply]
  by_cases hi : i = a.1
  · subst i
    simp only [Function.update_self, tangentMap_apply]
  · simp only [Function.update_of_ne hi, ContinuousLinearMap.proj_apply]

/-- The derivative of a register write retains all untouched register coordinates. -/
theorem hasFDerivAt_evalStep [Fintype ι] (a : ι × ScalarInstruction 𝕜 ι)
    (ha : a.2.DifferentiablePrimitive) (x : ι → 𝕜) :
    HasFDerivAt (evalStep · a) (updateTangentMap a x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = a.1
  · subst i
    simpa only [evalStep, Function.update_self] using a.2.hasFDerivAt_eval ha x
  · simpa only [evalStep, Function.update_of_ne hi] using hasFDerivAt_apply i x

/-- A program of instructions with differentiable primitives is differentiable. -/
theorem differentiable_evalProgram [Fintype ι] (program : List (ι × ScalarInstruction 𝕜 ι))
    (h : ∀ a ∈ program, a.2.DifferentiablePrimitive) :
    Differentiable 𝕜 (evalProgram program) := by
  induction program with
  | nil => exact differentiable_id
  | cons a rest ih =>
    intro v
    exact (ih (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) _).comp v
      (hasFDerivAt_evalStep a (h a List.mem_cons_self) v).differentiableAt

/-- **Gap 8.14.** Forward propagation through an ordered register program computes the
Fréchet derivative applied to the input tangent. Overwriting is allowed here. -/
theorem fderiv_evalProgram_apply [Fintype ι] (program : List (ι × ScalarInstruction 𝕜 ι))
    (h : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx : ι → 𝕜) :
    fderiv 𝕜 (evalProgram program) x dx = forwardProgram program x dx := by
  induction program generalizing x dx with
  | nil => exact congrFun (congrArg DFunLike.coe (fderiv_id (𝕜 := 𝕜) (x := x))) dx
  | cons a rest ih =>
    have hrest : ∀ b ∈ rest, (b : ι × ScalarInstruction 𝕜 ι).2.DifferentiablePrimitive :=
      fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have hcomp := ((differentiable_evalProgram rest hrest) (evalStep x a)).hasFDerivAt.comp x
      (hasFDerivAt_evalStep a (h a List.mem_cons_self) x)
    have heq := congrFun (congrArg DFunLike.coe hcomp.fderiv) dx
    rw [ContinuousLinearMap.comp_apply, updateTangentMap_apply] at heq
    exact heq.trans (ih hrest (evalStep x a) _)

/-- Pullback through one register write preserves the pairing with the updated tangent. -/
theorem sum_adjointStep_mul [Fintype ι] (a : ι × ScalarInstruction 𝕜 ι) (x dx c : ι → 𝕜) :
    ∑ j, adjointStep a x c j * dx j = ∑ j, c j * Function.update dx a.1 (a.2.tangent x dx) j := by
  have hsingle : (∑ j : ι, dx j • Pi.single j (1 : 𝕜)) = dx := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_zero, mul_one]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hlin : (∑ j, a.2.tangent x (Pi.single j 1) * dx j) = a.2.tangent x dx := by
    simp_rw [← tangentMap_apply, mul_comm ((a.2.tangentMap x) _), ← smul_eq_mul, ← map_smul]
    rw [← map_sum, hsingle]
  simp_rw [adjointStep_apply, add_mul, Finset.sum_add_distrib, mul_assoc]
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
theorem sum_reverseProgram_mul_eq_sum_mul_forwardProgram [Fintype ι]
    (program : List (ι × ScalarInstruction 𝕜 ι)) (x dx seed : ι → 𝕜) :
    ∑ j, reverseProgram program x seed j * dx j = ∑ j, seed j * forwardProgram program x dx j := by
  induction program generalizing x dx with
  | nil => rfl
  | cons a rest ih =>
    rw [reverseProgram_cons, sum_adjointStep_mul, forwardProgram_cons]
    exact ih _ _

/-- **Gap 8.14.** Reverse accumulation computes the transposed derivative of a
register program. Retaining the old register state handles overwrites and repeated operands. -/
theorem sum_reverseProgram_mul_eq_sum_mul_fderiv [Fintype ι]
    (program : List (ι × ScalarInstruction 𝕜 ι))
    (hp : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx seed : ι → 𝕜) :
    ∑ j, reverseProgram program x seed j * dx j =
      ∑ j, seed j * fderiv 𝕜 (evalProgram program) x dx j := by
  rw [fderiv_evalProgram_apply program hp]
  exact sum_reverseProgram_mul_eq_sum_mul_forwardProgram program x dx seed

end Program

end ScalarInstruction

end NASC
