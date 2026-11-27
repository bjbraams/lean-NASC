module

public import NASC.Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integral equations

Fredholm compatibility and approximation, Nyström nodal equations, and collocation
for Volterra equations on uniform and graded meshes. The compact-operator obstruction uses
Mathlib's finite-dimensionality criterion from a totally bounded neighborhood.
-/

public section

noncomputable section

namespace NASC

open Set Filter MeasureTheory Polynomial
open scoped BigOperators Topology Interval Matrix NNReal

/-- **Gap 21.1.** A continuous-kernel operator on continuous functions over a compact
space is compact for any finite integration measure. -/
theorem isCompactOperator_of_continuousKernel {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : C(X × X, ℂ)) (A : C(X, ℂ) →L[ℂ] C(X, ℂ))
    (hA : ∀ f x, A f x = ∫ y, K (x, y) * f y ∂μ) :
    IsCompactOperator A := by
  sorry

/-- **Gap 21.1.** Compactness also follows for a kernel continuous off the
diagonal when its integrable diagonal tails vanish uniformly. -/
theorem isCompactOperator_of_small_diagonal_tails {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : X → X → ℂ) (A : C(X, ℂ) →L[ℂ] C(X, ℂ))
    (hK : ContinuousOn (Function.uncurry K) {p : X × X | p.1 ≠ p.2})
    (hI : ∀ x, Integrable (K x) μ)
    (hsmall : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ x, (∫ y in Metric.ball x δ, ‖K x y‖ ∂μ) ≤ ε)
    (hA : ∀ f x, A f x = ∫ y, K x y * f y ∂μ) :
    IsCompactOperator A := by
  sorry

/-- **Gap 21.2.** The normed dual-pair Fredholm compatibility condition for
two compact operators adjoint with respect to a nondegenerate pairing. -/
theorem exists_fredholm_solution_iff_pairing {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (P : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (A : X →L[ℂ] X) (B : Y →L[ℂ] Y)
    (hPX : ∀ x, (∀ y, P x y = 0) → x = 0) (hPY : ∀ y, (∀ x, P x y = 0) → y = 0)
    (hA : IsCompactOperator A) (hB : IsCompactOperator B)
    (hAB : ∀ x y, P (A x) y = P x (B y)) (f : X) :
    (∃ x, x - A x = f) ↔ ∀ y, B y = y → P f y = 0 := by
  sorry

/-- **Gap 21.5.** The projection method for a second-kind equation, with the
discrete error bounded above and below by the original projection defect. -/
theorem exists_projection_secondKind_bounds {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (K : X →L[ℂ] X) (P : ℕ → X →L[ℂ] X)
    (hproj : ∀ n x, P n (P n x) = P n x)
    (hconv : Tendsto (fun n ↦ (P n).comp K) atTop (𝓝 K))
    {z : ℂ} (hz : z ≠ 0) (hres : Function.Bijective fun x ↦ z • x - K x) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ n in atTop, ∀ x : X,
      ∃! y : X, P n y = y ∧ z • y - P n (K y) = P n (z • x - K x) ∧
        a * ‖x - P n x‖ ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ b * ‖x - P n x‖ := by
  sorry

/-- **Gap 21.7.** Collectively compact strong approximations have eventually
invertible second-kind operators with uniformly bounded inverses. -/
theorem eventually_secondKind_boundedInverse {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (A : X →L[𝕜] X) (B : ℕ → X →L[𝕜] X)
    (hA : IsCompactOperator A) (hinj : Function.Injective fun x ↦ x - A x)
    (hcollect : ∃ K : Set X, IsCompact K ∧
      ∀ n, B n '' Metric.closedBall (0 : X) 1 ⊆ K)
    (hstrong : ∀ x, Tendsto (fun n ↦ B n x) atTop (𝓝 (A x))) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ n in atTop, ∃ U : X ≃L[𝕜] X,
      (U : X →L[𝕜] X) = 1 - B n ∧ ‖(U.symm : X →L[𝕜] X)‖ ≤ C := by
  sorry

/-- **Gap 21.8.** The Nyström nodal solves reconstruct continuous solutions and
converge uniformly when the quadratures converge on continuous test functions. -/
theorem exists_nystrom_convergence {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : C(X × X, ℂ)) (f φ : C(X, ℂ))
    (hφ : ∀ x, φ x = f x + ∫ y, K (x, y) * φ y ∂μ)
    (huniq : ∀ ψ : C(X, ℂ), (∀ x, ψ x = ∫ y, K (x, y) * ψ y ∂μ) → ψ = 0)
    (x : ∀ n, Fin n → X) (w : ∀ n, Fin n → ℝ)
    (hq : ∀ g : C(X, ℂ), Tendsto (fun n ↦ ∑ i : Fin n, (w n i : ℂ) * g (x n i))
      atTop (𝓝 (∫ y, g y ∂μ))) :
    ∃ φₕ : ℕ → C(X, ℂ), Tendsto φₕ atTop (𝓝 φ) ∧ ∀ᶠ n in atTop,
      ∃! c : Fin n → ℂ, (∀ i, c i = f (x n i) +
        ∑ j, (w n j : ℂ) * K (x n i, x n j) * c j) ∧
        ∀ y, φₕ n y = f y + ∑ j, (w n j : ℂ) * K (y, x n j) * c j := by
  sorry

/-- **Gap 21.9.** Continuous Volterra kernels have resolvents and give unique
continuous second-kind solutions on the time interval. -/
theorem exists_volterra_resolvent (K : ℝ → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) :
    ∃ R : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry R) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) t,
        R t s = K t s + ∫ v in s..t, K t v * R v s) ∧
      ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 T) →
        let y := fun t ↦ g t + ∫ s in (0 : ℝ)..t, R t s * g s
        ContinuousOn y (Icc 0 T) ∧
        (∀ t ∈ Icc (0 : ℝ) T, y t = g t + ∫ s in (0 : ℝ)..t, K t s * y s) ∧
        ∀ u : ℝ → ℝ, ContinuousOn u (Icc 0 T) →
          (∀ t ∈ Icc (0 : ℝ) T, u t = g t + ∫ s in (0 : ℝ)..t, K t s * u s) →
          EqOn u y (Icc 0 T) := by
  sorry

/-- The piecewise polynomial Volterra collocation equations. Earlier cells enter
as full integrals. At a collocation node the current polynomial enters on its
partial cell, so the equations also cover endpoint collocation. -/
def IsVolterraCollocation {n m : ℕ} (t : Fin (n + 1) → ℝ) (c : Fin m → ℝ)
    (K : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (p : Fin n → ℝ[X]) : Prop :=
  (∀ i, (p i).natDegree < m) ∧ ∀ (i : Fin n) (j : Fin m),
    let τ := t i.castSucc + c j * (t i.succ - t i.castSucc)
    (p i).eval τ = g τ + (∑ k ∈ Finset.univ.filter (· < i),
      ∫ s in t k.castSucc..t k.succ, K τ s * (p k).eval s) +
      ∫ s in t i.castSucc..τ, K τ s * (p i).eval s

/-- **Gap 21.10.** Smooth Volterra collocation on sufficiently fine meshes
has a uniform error of order the number of collocation nodes. -/
theorem exists_volterraCollocation_error_le {m : ℕ} (hm : 0 < m) {T : ℝ} (hT : 0 < T)
    (c : Fin m → ℝ) (hc : StrictMono c) (hc' : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (K : ℝ → ℝ → ℝ) (g y : ℝ → ℝ)
    (hK : ContDiff ℝ m (Function.uncurry K)) (hg : ContDiff ℝ m g)
    (hy : ContinuousOn y (Icc 0 T))
    (heq : ∀ t ∈ Icc (0 : ℝ) T, y t = g t + ∫ s in (0 : ℝ)..t, K t s * y s) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (n : ℕ) (t : Fin (n + 1) → ℝ),
      StrictMono t → t 0 = 0 → t (Fin.last n) = T →
      ∀ h > (0 : ℝ), h < δ → (∀ i : Fin n, t i.succ - t i.castSucc ≤ h) →
      ∃! p : Fin n → ℝ[X], IsVolterraCollocation t c K g p ∧
        ∀ i : Fin n, ∀ s ∈ Icc (t i.castSucc) (t i.succ), |y s - (p i).eval s| ≤ C * h ^ m := by
  sorry

/-- **Gap 21.11.** The graded collocation mesh resolves the initial singularity
of the Volterra equation, with order capped by the degree of collocation. -/
theorem exists_graded_volterraCollocation_error_le {m : ℕ} (hm : 0 < m) {T α r : ℝ}
    (hT : 0 < T) (hα : α ∈ Ioo (0 : ℝ) 1) (hr : 1 ≤ r)
    (c : Fin m → ℝ) (hc : StrictMono c) (hc' : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (K : ℝ → ℝ → ℝ) (g y : ℝ → ℝ)
    (hK : ContDiff ℝ m (Function.uncurry K)) (hg : ContDiff ℝ m g)
    (hy : ContinuousOn y (Icc 0 T))
    (heq : ∀ t ∈ Icc (0 : ℝ) T, y t = g t + ∫ s in (0 : ℝ)..t, (t - s) ^ (-α) * K t s * y s) :
    ∃ N₀ : ℕ, ∃ C ≥ (0 : ℝ), ∀ n : ℕ, N₀ < n →
      let t := fun j : Fin (n + 1) ↦ T * ((j.val : ℝ) / n) ^ r
      let W := fun t s ↦ (t - s) ^ (-α) * K t s
      ∃ p : Fin n → ℝ[X], IsVolterraCollocation t c W g p ∧
        ∀ i : Fin n, ∀ s ∈ Icc (t i.castSucc) (t i.succ),
          |y s - (p i).eval s| ≤ C * (T / n) ^ min (m : ℝ) (r * (1 - α)) := by
  sorry

/-- **Gap 21.16.** A compact operator with infinite-dimensional domain cannot
have a bounded inverse on its range. -/
theorem not_exists_lowerBound_of_isCompactOperator {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →L[ℝ] Y) (hA : IsCompactOperator A) (hX : ¬FiniteDimensional ℝ X) :
    ¬∃ C : ℝ, ∀ x, ‖x‖ ≤ C * ‖A x‖ := by
  rintro ⟨C, hC⟩
  let K : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  have hanti : AntilipschitzWith K A := AntilipschitzWith.of_le_mul_dist fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (hC (x - y)).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  have hU := hanti.isUniformInducing A.uniformContinuous
  have hball := (hA.isCompact_closure_image_closedBall 1).totallyBounded
  exact hX (FiniteDimensional.of_totallyBounded_nhds_zero ℝ
    (Metric.closedBall_mem_nhds 0 zero_lt_one)
    ((totallyBounded_image_iff hU).mp (hball.subset subset_closure)))

end NASC
