module

public import NASC.NonlinearEquations
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Numerical optimization

Constrained optimality, Wolfe and Dennis--Moré conditions, gradient and proximal methods,
primal-dual splitting, self-concordance, and finite transport duality.
-/

public section

noncomputable section

namespace NASC

open Filter Set
open scoped BigOperators InnerProductSpace Matrix NNReal

/-- **Gap 9.2.** First-order multiplier existence under linear independence of the
equality and active inequality gradients. Inequalities use the convention $c_i(x)\ge 0$. -/
theorem exists_kkt_multipliers {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin p ⊕ Fin q → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ 1 f) (hc : ∀ i, ContDiff ℝ 1 (c i))
    (hx : (∀ i, c (.inl i) x = 0) ∧ ∀ j, 0 ≤ c (.inr j) x)
    (hmin : IsLocalMinOn f {y | (∀ i, c (.inl i) y = 0) ∧ ∀ j, 0 ≤ c (.inr j) y} x)
    (hind : LinearIndependent ℝ
      (fun i : {i : Fin p ⊕ Fin q // c i x = 0} ↦ gradient (c i.val) x)) :
    ∃ η : Fin p ⊕ Fin q → ℝ,
      gradient f x = ∑ i, η i • gradient (c i) x ∧
      (∀ i : Fin q, 0 ≤ η (.inr i)) ∧ ∀ i, η i * c i x = 0 := by
  sorry

/-- **Gap 9.2.** Positivity of the Lagrangian Hessian on the critical cone
suffices for strict constrained local optimality. -/
theorem kkt_strict_local_min_of_hessian {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin p ⊕ Fin q → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (η : Fin p ⊕ Fin q → ℝ)
    (hf : ContDiff ℝ 2 f) (hc : ∀ i, ContDiff ℝ 2 (c i))
    (hx : (∀ i, c (.inl i) x = 0) ∧ (∀ j, 0 ≤ c (.inr j) x))
    (hstat : gradient f x = ∑ i, η i • gradient (c i) x)
    (hmul : ∀ i : Fin q, 0 ≤ η (.inr i) ∧ η (.inr i) * c (.inr i) x = 0)
    (h₂ : ∀ w : EuclideanSpace ℝ (Fin n), w ≠ 0 →
      (∀ i, fderiv ℝ (c (.inl i)) x w = 0) →
      (∀ i : Fin q, c (.inr i) x = 0 →
        0 ≤ fderiv ℝ (c (.inr i)) x w ∧
          (0 < η (.inr i) → fderiv ℝ (c (.inr i)) x w = 0)) →
      0 < iteratedFDeriv ℝ 2 (fun y ↦ f y - ∑ i, η i * c i y) x (fun _ ↦ w)) :
    ∀ᶠ y in nhdsWithin x {y | (∀ i, c (.inl i) y = 0) ∧ ∀ j, 0 ≤ c (.inr j) y},
      y ≠ x → f x < f y := by
  sorry

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Wolfe conditions along a descent direction. -/
def IsWolfeStep (f : H → ℝ) (x p : H) (c₁ c₂ a : ℝ) : Prop :=
  0 < a ∧ f (x + a • p) ≤ f x + c₁ * a * inner ℝ (gradient f x) p ∧
    c₂ * inner ℝ (gradient f x) p ≤ inner ℝ (gradient f (x + a • p)) p

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
quasi-Newton recurrence near a zero of the gradient. -/
theorem tendsto_error_ratio_iff_dennisMore {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    (x p : ℕ → H) (B : ℕ → H ≃L[ℝ] H) (z : H) (hz : gradient f z = 0)
    (hH : Function.Bijective (fderiv ℝ (gradient f) z))
    (hlim : Tendsto x atTop (nhds z)) (hne : ∀ k, x k ≠ z ∧ p k ≠ 0)
    (hstep : ∀ k, x (k + 1) = x k + p k ∧ B k (p k) = -gradient f (x k)) :
    Tendsto (fun k ↦ ‖x (k + 1) - z‖ / ‖x k - z‖) atTop (nhds 0) ↔
      Tendsto (fun k ↦ ‖B k (p k) - fderiv ℝ (gradient f) z (p k)‖ / ‖p k‖)
        atTop (nhds 0) := by
  sorry

/-- **Gap 9.7.** The objective error of gradient descent at step $1/L$ is bounded
by the initial squared distance divided by the number of steps. -/
theorem gradientDescent_objective_error_le {f : H → ℝ} (hf : Differentiable ℝ f)
    (hcv : ConvexOn ℝ univ f) {L : ℝ≥0} (hL : 0 < L) (hLip : LipschitzWith L (gradient f))
    {x₀ z : H} (hz : ∀ y, f z ≤ f y) {k : ℕ} (hk : 0 < k) :
    let step := fun y ↦ y - ((L : ℝ)⁻¹) • gradient f y
    f (step^[k] x₀) - f z ≤ (L : ℝ) * ‖x₀ - z‖ ^ 2 / (2 * k) := by
  sorry

/-- Membership in the affine span model for first-order methods. -/
def IsSpanFirstOrder (f : H → ℝ) (x : ℕ → H) : Prop :=
  ∀ k, x k - x 0 ∈ Submodule.span ℝ (range (fun j : Fin k ↦ gradient f (x j.val)))

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

/-- An extended-valued objective has a convex epigraph over real heights. -/
def HasConvexEpigraph (f : H → EReal) : Prop :=
  Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- Proximity step of an extended-valued objective. The input step size is positive. -/
def IsProximalPoint (f : H → EReal) (t : ℝ) (x z : H) : Prop :=
  0 < t ∧
    ∀ y, f z + (‖z - x‖ ^ 2 / (2 * t) : ℝ) ≤ f y + (‖y - x‖ ^ 2 / (2 * t) : ℝ)

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
      z ≠ x₀ ∧ ConvexOn ℝ univ f ∧ ContDiff ℝ ⊤ f ∧ LipschitzWith L (gradient f) ∧
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

/-- **Gap 9.16.** Finite Kantorovich duality with primal and dual attainment.
Nonnegative marginals may have zero coordinates. -/
theorem exists_optimal_transport_and_potentials {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (C : Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (ha₁ : ∑ i, a i = 1) (hb₁ : ∑ j, b j = 1) :
    ∃ (P : Matrix (Fin m) (Fin n) ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j) ∧
      (∀ i j, f i + g j ≤ C i j) ∧
      (∑ i, ∑ j, C i j * P i j) = (∑ i, f i * a i) + (∑ j, g j * b j) := by
  sorry

end NASC
