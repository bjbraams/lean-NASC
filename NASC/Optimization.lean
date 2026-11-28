module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import NASC.Support.Analysis
import TauCeti.Analysis.Convex.Differentiability
import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality

/-!
# Numerical optimization

Constrained optimality, Wolfe and Dennis--Moré conditions, gradient descent and the
first-order lower bound, proximal and accelerated proximal gradient methods,
Krasnosel'skiĭ--Mann iteration, primal-dual splitting, self-concordance, and finite transport
duality. See section 9 of the gap catalogue.

## Main definitions

* `NASC.IsWolfeStep`, `NASC.IsSpanFirstOrder`, `NASC.HasConvexEpigraph` and
  `NASC.IsProximalPoint`.

## Main results

* `NASC.exists_kkt_multipliers`, `NASC.kkt_strict_local_min_of_hessian`: first- and
  second-order optimality conditions.
* `NASC.summable_wolfe_gradient_sq`: Zoutendijk's theorem.
* `NASC.tendsto_error_ratio_iff_dennisMore`: the Dennis--Moré characterization.
* `NASC.abs_gradientModel_error_le`, `NASC.gradientDescent_objective_error_le`: the descent
  lemma and the `O(1/k)` rate of gradient descent.
* `NASC.exists_firstOrder_lowerBound`: the first-order lower complexity bound.
* `NASC.exists_weakLimit_krasnoselskiiMann`: Krasnosel'skiĭ--Mann convergence.
* `NASC.fista_objective_le`: the `O(1/k²)` rate of FISTA.
* `NASC.primalDualHybridGradient_gap_le`: the ergodic primal-dual gap.
* `NASC.newton_mem_and_decrement_le_of_selfConcordance`: the self-concordant Newton step.
* `NASC.exists_optimal_transport_and_potentials`: finite Kantorovich duality for real
  marginals of equal mass, derived from TauCeti's `TauCeti.exists_cost_eq_finiteDualValue`.

The gradient descent estimate uses TauCeti's supporting-plane bound for a convex function.
-/

public section

noncomputable section

namespace NASC

open Filter Set
open scoped InnerProductSpace Matrix NNReal ContDiff

/-- **Gap 9.2.** First-order multiplier existence under linear independence of the
equality and active inequality gradients. Inequalities use the convention $c_i(x)\ge 0$.
The objective and the constraints are `C¹` near `x`. -/
theorem exists_kkt_multipliers {E ιe ιi : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ιe] [Fintype ιi]
    (f : E → ℝ) (c : ιe ⊕ ιi → E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 1 f x) (hc : ∀ i, ContDiffAt ℝ 1 (c i) x)
    (hx : (∀ i, c (.inl i) x = 0) ∧ ∀ j, 0 ≤ c (.inr j) x)
    (hmin : IsLocalMinOn f {y | (∀ i, c (.inl i) y = 0) ∧ ∀ j, 0 ≤ c (.inr j) y} x)
    (hind : LinearIndependent ℝ
      (fun i : {i : ιe ⊕ ιi // c i x = 0} ↦ gradient (c i.val) x)) :
    ∃ η : ιe ⊕ ιi → ℝ,
      gradient f x = ∑ i, η i • gradient (c i) x ∧
      (∀ i : ιi, 0 ≤ η (.inr i)) ∧ ∀ i, η i * c i x = 0 := by
  sorry

/-- **Gap 9.2.** Positivity of the Lagrangian Hessian on the critical cone
suffices for strict constrained local optimality. The objective and the constraints are
`C²` near `x`. -/
theorem kkt_strict_local_min_of_hessian {E ιe ιi : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ιe] [Fintype ιi]
    (f : E → ℝ) (c : ιe ⊕ ιi → E → ℝ) (x : E) (η : ιe ⊕ ιi → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hc : ∀ i, ContDiffAt ℝ 2 (c i) x)
    (hx : (∀ i, c (.inl i) x = 0) ∧ (∀ j, 0 ≤ c (.inr j) x))
    (hstat : gradient f x = ∑ i, η i • gradient (c i) x)
    (hmul : ∀ i : ιi, 0 ≤ η (.inr i) ∧ η (.inr i) * c (.inr i) x = 0)
    (h₂ : ∀ w : E, w ≠ 0 →
      (∀ i, fderiv ℝ (c (.inl i)) x w = 0) →
      (∀ i : ιi, c (.inr i) x = 0 →
        0 ≤ fderiv ℝ (c (.inr i)) x w ∧
          (0 < η (.inr i) → fderiv ℝ (c (.inr i)) x w = 0)) →
      0 < iteratedFDeriv ℝ 2 (fun y ↦ f y - ∑ i, η i * c i y) x (fun _ ↦ w)) :
    ∀ᶠ y in nhdsWithin x {y | (∀ i, c (.inl i) y = 0) ∧ ∀ j, 0 ≤ c (.inr j) y},
      y ≠ x → f x < f y := by
  sorry

section Proximal

variable {H : Type*} [NormedAddCommGroup H]

/-- An extended-valued objective has a convex epigraph over real heights. -/
def HasConvexEpigraph [Module ℝ H] (f : H → EReal) : Prop :=
  Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The defining property of `HasConvexEpigraph`. -/
theorem hasConvexEpigraph_iff [Module ℝ H] {f : H → EReal} :
    HasConvexEpigraph f ↔ Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  unfold HasConvexEpigraph
  exact Iff.rfl

/-- Proximity step of an extended-valued objective. The input step size is positive. -/
def IsProximalPoint (f : H → EReal) (t : ℝ) (x z : H) : Prop :=
  0 < t ∧
    ∀ y, f z + (‖z - x‖ ^ 2 / (2 * t) : ℝ) ≤ f y + (‖y - x‖ ^ 2 / (2 * t) : ℝ)

/-- The defining property of `IsProximalPoint`. -/
theorem isProximalPoint_iff {f : H → EReal} {t : ℝ} {x z : H} :
    IsProximalPoint f t x z ↔ 0 < t ∧
      ∀ y, f z + (‖z - x‖ ^ 2 / (2 * t) : ℝ) ≤ f y + (‖y - x‖ ^ 2 / (2 * t) : ℝ) := by
  unfold IsProximalPoint
  exact Iff.rfl

end Proximal

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Wolfe conditions along a descent direction. -/
def IsWolfeStep (f : H → ℝ) (x p : H) (c₁ c₂ a : ℝ) : Prop :=
  0 < a ∧ f (x + a • p) ≤ f x + c₁ * a * inner ℝ (gradient f x) p ∧
    c₂ * inner ℝ (gradient f x) p ≤ inner ℝ (gradient f (x + a • p)) p

/-- The defining property of `IsWolfeStep`. -/
theorem isWolfeStep_iff {f : H → ℝ} {x p : H} {c₁ c₂ a : ℝ} :
    IsWolfeStep f x p c₁ c₂ a ↔ 0 < a ∧
      f (x + a • p) ≤ f x + c₁ * a * inner ℝ (gradient f x) p ∧
      c₂ * inner ℝ (gradient f x) p ≤ inner ℝ (gradient f (x + a • p)) p := by
  unfold IsWolfeStep
  exact Iff.rfl

/-- **Gap 9.3.** Zoutendijk's summability bound for a sequence of Wolfe steps. -/
theorem summable_wolfe_gradient_sq {f : H → ℝ} (x p : ℕ → H) (a : ℕ → ℝ)
    {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₁₂ : c₁ < c₂) (h₂ : c₂ < 1)
    (hf : Differentiable ℝ f) (hbd : BddBelow (range f))
    (hLip : ∃ L, LipschitzWith L (gradient f))
    (hdescent : ∀ k, inner ℝ (gradient f (x k)) (p k) < 0)
    (hstep : ∀ k, x (k + 1) = x k + a k • p k ∧ IsWolfeStep f (x k) (p k) c₁ c₂ (a k)) :
    Summable (fun k ↦ (inner ℝ (gradient f (x k)) (p k) / ‖p k‖) ^ 2) := by
  sorry

/-- **Gap 9.5.** Dennis--Moré characterization of superlinear convergence for a
quasi-Newton recurrence near a zero of the gradient. The model operators `B k` need not be
invertible. -/
theorem tendsto_error_ratio_iff_dennisMore {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    (x p : ℕ → H) (B : ℕ → H →L[ℝ] H) (z : H) (hz : gradient f z = 0)
    (hH : Function.Bijective (fderiv ℝ (gradient f) z))
    (hlim : Tendsto x atTop (nhds z)) (hne : ∀ k, x k ≠ z ∧ p k ≠ 0)
    (hstep : ∀ k, x (k + 1) = x k + p k ∧ B k (p k) = -gradient f (x k)) :
    Tendsto (fun k ↦ ‖x (k + 1) - z‖ / ‖x k - z‖) atTop (nhds 0) ↔
      Tendsto (fun k ↦ ‖B k (p k) - fderiv ℝ (gradient f) z (p k)‖ / ‖p k‖)
        atTop (nhds 0) := by
  sorry

/-- A Lipschitz gradient gives a quadratic bound on the affine model error. -/
theorem abs_gradientModel_error_le {f : H → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hLip : LipschitzWith L (gradient f)) (x y : H) :
    |f y - f x - inner ℝ (gradient f x) (y - x)| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let e := fun s : ℝ ↦ f (x + s • d) - f x - s * inner ℝ (gradient f x) d
  have hd (s : ℝ) :
      HasDerivAt e (inner ℝ (gradient f (x + s • d) - gradient f x) d) s := by
    have hp := HasFDerivAt.hasDerivAt_comp_add_smul (hf (x + s • d)).hasFDerivAt
    simp only [← inner_gradient_left] at hp
    simpa only [e, inner_sub_left, one_mul, id_eq] using
      (hp.sub_const (f x)).fun_sub ((hasDerivAt_id s).mul_const (inner ℝ (gradient f x) d))
  have hnorm : ‖e 1 - e 0‖ ≤ ((L : ℝ) * ‖d‖ ^ 2) / 2 := by
    apply norm_sub_endpoints_le_half (fun s _ ↦ hd s)
    intro s hs
    have h := hLip.dist_le_mul (x + s • d) x
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1] at h
    calc
      _ ≤ ‖gradient f (x + s • d) - gradient f x‖ * ‖d‖ := norm_inner_le_norm _ _
      _ ≤ (L : ℝ) * (s * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = _ := by ring
  simp only [Real.norm_eq_abs, e, d, one_smul, one_mul, add_sub_cancel, zero_smul,
    add_zero, sub_self, zero_mul, sub_zero] at hnorm
  linarith only [hnorm]

/-- A gradient step with reciprocal smoothness trades objective error for squared distance. -/
theorem gradient_step_sub_le {f : H → ℝ} (hf : Differentiable ℝ f)
    (hcv : ConvexOn ℝ univ f) {L : ℝ≥0} (hL : 0 < L)
    (hLip : LipschitzWith L (gradient f)) (x y : H) :
    let p := x - ((L : ℝ)⁻¹) • gradient f x
    f p - f y ≤ (L : ℝ) / 2 * (‖x - y‖ ^ 2 - ‖p - y‖ ^ 2) := by
  let g := gradient f x
  let p := x - ((L : ℝ)⁻¹) • g
  have hl : (L : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hL.ne'
  have hmod := le_of_abs_le (abs_gradientModel_error_le hf hLip x p)
  have hcv' := hcv.inner_gradient_sub_le (hf x) y
  have hs : inner ℝ g (p - y) = inner ℝ g (p - x) - inner ℝ g (y - x) := by
    simp only [inner_sub_right]
    ring
  have hp₁ : x - y = (p - y) + (L : ℝ)⁻¹ • g := by
    dsimp only [p]
    abel
  have hp₂ : p - x = -((L : ℝ)⁻¹ • g) := by
    dsimp only [p]
    abel
  have he : (L : ℝ) / 2 * (‖x - y‖ ^ 2 - ‖p - y‖ ^ 2) =
      inner ℝ g (p - y) + (L : ℝ) / 2 * ‖p - x‖ ^ 2 := by
    rw [hp₁, hp₂, norm_add_sq_real, norm_neg, real_inner_smul_right,
      real_inner_comm g (p - y)]
    field_simp [hl]
    ring
  exact le_trans (by linarith only [hmod, hcv', hs]) he.ge

/-- **Gap 9.7.** The objective error of gradient descent at step $1/L$ is bounded
by the initial squared distance divided by the number of steps. -/
theorem gradientDescent_objective_error_le {f : H → ℝ} (hf : Differentiable ℝ f)
    (hcv : ConvexOn ℝ univ f) {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (gradient f))
    {x₀ z : H} (hz : ∀ y, f z ≤ f y) {k : ℕ} (hk : 0 < k) :
    let step := fun y ↦ y - ((L : ℝ)⁻¹) • gradient f y
    f (step^[k] x₀) - f z ≤ (L : ℝ) * ‖x₀ - z‖ ^ 2 / (2 * k) := by
  let step := fun y : H ↦ y - ((L : ℝ)⁻¹) • gradient f y
  let u := fun j : ℕ ↦ step^[j] x₀
  let q := fun j : ℕ ↦ f (u j) - f z
  let E := fun j : ℕ ↦ (L : ℝ) / 2 * ‖u j - z‖ ^ 2
  have hu (j : ℕ) : u (j + 1) = step (u j) := Function.iterate_succ_apply' ..
  have hw (j : ℕ) : q (j + 1) ≤ E j - E (j + 1) := by
    dsimp only [q, E]
    rw [hu j]
    have h := gradient_step_sub_le hf hcv hL hLip (u j) z
    linarith only [h]
  have hmono (j : ℕ) : q (j + 1) ≤ q j := by
    dsimp only [q]
    rw [hu j]
    have h := gradient_step_sub_le hf hcv hL hLip (u j) (u j)
    simp only [sub_self, norm_zero, zero_pow (n := 2) (by decide), zero_sub] at h
    have hnon := mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2)
      (sq_nonneg ‖step (u j) - u j‖)
    linarith only [h, hnon]
  have hq (j : ℕ) : |q j| = q j := abs_of_nonneg (sub_nonneg.mpr (hz _))
  have htel (j : ℕ) : (j : ℝ) * |q j| ≤ E 0 - E j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hq j] at ih
      rw [Nat.cast_succ, hq (j + 1)]
      have hm := mul_le_mul_of_nonneg_left (hmono j) (Nat.cast_nonneg j : 0 ≤ (j : ℝ))
      linarith only [hm, ih, hw j]
  have hE : 0 ≤ E k := by
    dsimp only [E]
    positivity
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h := htel k
  rw [hq k] at h
  apply (le_div_iff₀ (mul_pos two_pos hk')).mpr
  have h0 : E 0 = (L : ℝ) / 2 * ‖x₀ - z‖ ^ 2 := rfl
  rw [h0] at h
  linarith only [h, hE]

/-- Membership in the affine span model for first-order methods. -/
def IsSpanFirstOrder (f : H → ℝ) (x : ℕ → H) : Prop :=
  ∀ k, x k - x 0 ∈ Submodule.span ℝ (range (fun j : Fin k ↦ gradient f (x j.val)))

/-- The defining property of `IsSpanFirstOrder`. -/
theorem isSpanFirstOrder_iff {f : H → ℝ} {x : ℕ → H} :
    IsSpanFirstOrder f x ↔
      ∀ k, x k - x 0 ∈ Submodule.span ℝ (range (fun j : Fin k ↦ gradient f (x j.val))) := by
  unfold IsSpanFirstOrder
  exact Iff.rfl

/-- **Gap 9.12.** Krasnosel'skiĭ--Mann convergence for a closed convex invariant
set and a divergent relaxation budget. The limit is characterized by scalar products. -/
theorem exists_weakLimit_krasnoselskiiMann (T : H → H) (D : Set H) (s : ℕ → ℝ) (x : ℕ → H)
    (hD : IsClosed D) (hcv : Convex ℝ D) (hT : MapsTo T D D)
    (hLip : LipschitzOnWith 1 T D) (hfix : ∃ z ∈ D, T z = z) (hx : x 0 ∈ D)
    (hs : ∀ k, s k ∈ Icc (0 : ℝ) 1) (hsum : ¬ Summable fun k ↦ s k * (1 - s k))
    (hstep : ∀ k, x (k + 1) = x k + s k • (T (x k) - x k)) :
    ∃ z ∈ D, T z = z ∧
      Tendsto (fun k ↦ T (x k) - x k) atTop (nhds 0) ∧
      ∀ y, Tendsto (fun k ↦ inner ℝ y (x k)) atTop (nhds (inner ℝ y z)) := by
  sorry

/-- **Gap 9.9.** Accelerated proximal gradient converges at the inverse-square
objective rate. The proximal objective retains its extended-valued domain. -/
theorem fista_objective_le {f : H → ℝ} {g : H → EReal}
    (hf : Differentiable ℝ f) (hcv : ConvexOn ℝ univ f) (hg : HasConvexEpigraph g)
    (hclosed : IsClosed {p : H × ℝ | g p.1 ≤ (p.2 : EReal)})
    (hproper : ∀ y, g y ≠ ⊥)
    {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (gradient f))
    (x y : ℕ → H) (t : ℕ → ℝ) (z : H) (hfinite : g z ≠ ⊤)
    (hz : ∀ v, (f z : EReal) + g z ≤ (f v : EReal) + g v)
    (hy : y 0 = x 0) (ht : t 0 = 1)
    (h : ∀ k,
      IsProximalPoint g (L : ℝ)⁻¹ (y k - (L : ℝ)⁻¹ • gradient f (y k)) (x (k + 1)) ∧
      t (k + 1) = (1 + Real.sqrt (1 + 4 * t k ^ 2)) / 2 ∧
      y (k + 1) = x (k + 1) + ((t k - 1) / t (k + 1)) • (x (k + 1) - x k)) :
    ∀ k : ℕ, 0 < k → (f (x k) : EReal) + g (x k) ≤
      ((f z : EReal) + g z) + (2 * (L : ℝ) * ‖x 0 - z‖ ^ 2 / ((k : ℝ) + 1) ^ 2 : ℝ) := by
  sorry

/-- **Gap 9.14.** A full Newton step lies in the domain of a closed self-concordant
function when its decrement is less than the reciprocal self-concordance constant. -/
theorem newton_mem_and_decrement_le_of_selfConcordance
    {f : H → ℝ} {U : Set H} (hU : IsOpen U) (hcv : ConvexOn ℝ U f)
    (hclosed : IsClosed {p : H × ℝ | p.1 ∈ U ∧ f p.1 ≤ p.2})
    (hf : ContDiffOn ℝ 3 f U) {M : ℝ} (hM : 0 < M)
    (Hess : H → H ≃L[ℝ] H)
    (hHess : ∀ x ∈ U, HasFDerivAt (gradient f) (Hess x : H →L[ℝ] H) x)
    (hpos : ∀ x ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (Hess x v))
    (hsc : ∀ x ∈ U, ∀ v,
      |iteratedFDeriv ℝ 3 f x (fun _ ↦ v)| ≤ 2 * M * (inner ℝ v (Hess x v)) ^ (3 / 2 : ℝ))
    {x : H} (hx : x ∈ U) :
    let dec := fun x ↦ Real.sqrt (inner ℝ (gradient f x) ((Hess x).symm (gradient f x)))
    let next := x - (Hess x).symm (gradient f x)
    M * dec x < 1 → next ∈ U ∧ dec next ≤ M * dec x ^ 2 / (1 - M * dec x) ^ 2 := by
  sorry

end Hilbert

/-- **Gap 9.8.** A smooth convex quadratic witness for the first-order span lower
bound in dimension at least $2k+1$. -/
theorem exists_firstOrder_lowerBound {n k : ℕ} (hk : 0 < k) (hn : 2 * k + 1 ≤ n)
    (x₀ : EuclideanSpace ℝ (Fin n)) {L : ℝ≥0} (hL : 0 < L) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)),
      z ≠ x₀ ∧ ConvexOn ℝ univ f ∧ ContDiff ℝ ∞ f ∧ LipschitzWith L (gradient f) ∧
      (∀ y, f z ≤ f y) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x₀ → IsSpanFirstOrder f x →
        3 * (L : ℝ) * ‖x₀ - z‖ ^ 2 / (32 * ((k : ℝ) + 1) ^ 2) ≤ f (x k) - f z ∧
        ‖x₀ - z‖ ^ 2 / 8 ≤ ‖x k - z‖ ^ 2 := by
  sorry

/-- **Gap 9.13.** Ergodic primal-dual gap for the extrapolated primal-dual
hybrid gradient scheme. The objective functions in this version are finite-valued. -/
theorem primalDualHybridGradient_gap_le {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    (K : H →L[ℝ] J) (g : H → ℝ) (fstar : J → ℝ)
    (hg : ConvexOn ℝ univ g) (hf : ConvexOn ℝ univ fstar)
    (x : ℕ → H) (y : ℕ → J) {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hbound : τ * σ * ‖K‖ ^ 2 ≤ 1)
    (hstep : ∀ k,
      IsProximalPoint (fun v ↦ (g v : EReal)) τ (x k - τ • K.adjoint (y k)) (x (k + 1)) ∧
      IsProximalPoint (fun v ↦ (fstar v : EReal)) σ
        (y k + σ • K ((2 : ℝ) • x (k + 1) - x k)) (y (k + 1)))
    {k : ℕ} (hk : 0 < k) (v : H) (w : J) :
    let X := (k : ℝ)⁻¹ • ∑ j ∈ Finset.range k, x (j + 1)
    let Y := (k : ℝ)⁻¹ • ∑ j ∈ Finset.range k, y (j + 1)
    let L := fun x y ↦ inner ℝ y (K x) - fstar y + g x
    L X w - L v Y ≤ (‖v - x 0‖ ^ 2 / τ + ‖w - y 0‖ ^ 2 / σ) / k := by
  sorry

/-- Finite Kantorovich duality with primal and dual attainment for probability vectors.
Nonnegative marginals may have zero coordinates. This is the real-vector form of TauCeti's
`TauCeti.exists_cost_eq_finiteDualValue`. -/
theorem exists_optimal_transport_and_potentials_of_sum_eq_one {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (C : Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (ha₁ : ∑ i, a i = 1) (hb₁ : ∑ j, b j = 1) :
    ∃ (P : Matrix (Fin m) (Fin n) ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j) ∧
      (∀ i j, f i + g j ≤ C i j) ∧
      (∑ i, ∑ j, C i j * P i j) = (∑ i, f i * a i) + (∑ j, g j * b j) := by
  let μ : PMF (Fin m) := PMF.ofFintype (fun i ↦ ENNReal.ofReal (a i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ ha i, ha₁, ENNReal.ofReal_one])
  let ν : PMF (Fin n) := PMF.ofFintype (fun j ↦ ENNReal.ofReal (b j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hb j, hb₁, ENNReal.ofReal_one])
  have hμ (i : Fin m) : (μ i).toReal = a i := ENNReal.toReal_ofReal (ha i)
  have hν (j : Fin n) : (ν j).toReal = b j := ENNReal.toReal_ofReal (hb j)
  obtain ⟨A, φ, ψ, -, hfeas, hcost⟩ :=
    TauCeti.exists_cost_eq_finiteDualValue (fun q ↦ C q.1 q.2) μ ν
  refine ⟨fun i j ↦ A.toRealFun (i, j), φ, ψ, fun i j ↦ A.toRealFun_nonneg _,
    fun i ↦ (A.sum_toRealFun_row i).trans (hμ i), fun j ↦ (A.sum_toRealFun_col j).trans (hν j),
    hfeas, ?_⟩
  rw [TauCeti.TransportMatrix.cost_def, TauCeti.finiteDualValue_def, Fintype.sum_prod_type]
    at hcost
  simpa only [hμ, hν, mul_comm (a _), mul_comm (b _)] using hcost

/-- Finite Kantorovich duality with primal and dual attainment (synopsis 9.16) for nonnegative
real marginals of equal total mass. Nonnegative marginals may have zero coordinates. For total
mass zero the plan is zero. -/
theorem exists_optimal_transport_and_potentials {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (C : Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (hab : ∑ i, a i = ∑ j, b j) :
    ∃ (P : Matrix (Fin m) (Fin n) ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j) ∧
      (∀ i j, f i + g j ≤ C i j) ∧
      (∑ i, ∑ j, C i j * P i j) = (∑ i, f i * a i) + (∑ j, g j * b j) := by
  set s := ∑ i, a i with hs
  rcases (Finset.sum_nonneg fun i _ ↦ ha i : 0 ≤ s).eq_or_lt with h0 | hpos
  · have ha0 (i : Fin m) : a i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ ha i).mp h0.symm i (Finset.mem_univ i)
    have hb0 (j : Fin n) : b j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hb j).mp (hab ▸ h0.symm) j (Finset.mem_univ j)
    refine ⟨0, fun i ↦ -∑ j, |C i j|, 0, fun _ _ ↦ le_rfl, fun i ↦ by simp [ha0],
      fun j ↦ by simp [hb0], fun i j ↦ ?_, by simp [ha0, hb0]⟩
    have hle := Finset.single_le_sum (fun j _ ↦ abs_nonneg (C i j)) (Finset.mem_univ j)
    simp only [Pi.zero_apply, add_zero]
    linarith only [hle, neg_abs_le (C i j)]
  · have hs0 : s ≠ 0 := hpos.ne'
    obtain ⟨P, f, g, hP, hrow, hcol, hfg, hcost⟩ :=
      exists_optimal_transport_and_potentials_of_sum_eq_one (fun i ↦ a i / s) (fun j ↦ b j / s)
        C (fun i ↦ div_nonneg (ha i) hpos.le) (fun j ↦ div_nonneg (hb j) hpos.le)
        (by rw [← Finset.sum_div]; exact div_self hs0)
        (by rw [← Finset.sum_div, ← hab]; exact div_self hs0)
    refine ⟨s • P, f, g, fun i j ↦ mul_nonneg hpos.le (hP i j), fun i ↦ ?_, fun j ↦ ?_, hfg, ?_⟩
    · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow i]
      field_simp
    · simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hcol j]
      field_simp
    · have he : (∑ i, ∑ j, C i j * (s • P) i j) = s * ∑ i, ∑ j, C i j * P i j := by
        simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      rw [he, hcost, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by field_simp

end NASC
