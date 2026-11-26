module

public import NASC.IntegralEquations
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Linear inverse problems and regularization

Picard's range criterion, the generalized inverse, convergence under parameter selection,
Tikhonov and discrepancy methods, and Landweber iteration.
-/

public section

noncomputable section

namespace NASC

open Set Filter
open scoped BigOperators Topology

section Hilbert

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Gap 22.3.** Picard's criterion and its reconstruction from a complete
positive singular system, with finite and countable index sets allowed. -/
theorem exists_eq_image_iff_picard {ι : Type*} [Countable ι]
    (K : X →L[ℝ] Y) (e : ι → X) (g : ι → Y) (σ : ι → ℝ)
    (he : Orthonormal ℝ e) (hg : Orthonormal ℝ g) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ i, K (e i) = σ i • g i ∧ K.adjoint (g i) = σ i • e i)
    (hcomplete : ∀ v, (∀ i, inner ℝ v (g i) = 0) ↔ K.adjoint v = 0) (y : Y) :
    let coeff := fun i ↦ inner ℝ y (g i) / σ i
    (∃ x, K x = y) ↔
      ((∀ v, K.adjoint v = 0 → inner ℝ y v = 0) ∧ Summable (fun i ↦ coeff i ^ 2) ∧
        K (∑' i, coeff i • e i) = y) := by
  sorry

/-- The natural domain of the generalized inverse, allowing nonclosed range. -/
def generalizedInverseDomain (K : X →L[ℝ] Y) : Submodule ℝ Y :=
  K.toLinearMap.range ⊔ K.toLinearMap.rangeᗮ

/-- **Gap 22.4.** The generalized inverse is a closed, densely defined map
returning the minimum-norm least-squares solution. Boundedness is equivalent
to closed range. -/
theorem exists_generalizedInverse_closedGraph (K : X →L[ℝ] Y) :
    let D := generalizedInverseDomain K
    Dense (D : Set Y) ∧
      ∃ P : D →ₗ[ℝ] X,
        IsClosed {p : Y × X | ∃ y : D, p = (y.val, P y)} ∧
        (∀ y : D, K.adjoint (K (P y) - y.val) = 0 ∧
          ∀ x, K.adjoint (K x - y.val) = 0 → ‖P y‖ ≤ ‖x‖) ∧
        (Continuous P ↔ IsClosed (range K)) := by
  sorry

/-- **Gap 22.5.** Noise amplification and exact-data consistency give regularization
convergence for an a priori parameter choice. -/
theorem regularization_tendsto_of_noise_control (K : X →L[ℝ] Y)
    (R : ℝ → Y →L[ℝ] X) (α : ℝ → ℝ) (data : ℝ → Y) (x : X)
    (hα : Tendsto α (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (hR : Tendsto (fun a ↦ R a (K x)) (𝓝[>] (0 : ℝ)) (𝓝 x))
    (hnoise : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖data δ - K x‖ ≤ δ)
    (hsmall : Tendsto (fun δ ↦ δ * ‖R (α δ)‖) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun δ ↦ R (α δ) (data δ)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  sorry

/-- **Gap 22.6.** Tikhonov regularization is the unique quadratic minimizer.
The regularized inverse has the bound $1/(2\sqrt{\alpha})$. -/
theorem exists_tikhonov_normalSolve (K : X →L[ℝ] Y) {α : ℝ} (hα : 0 < α) :
    ∃ R : Y →L[ℝ] X, ‖R‖ ≤ (2 * Real.sqrt α)⁻¹ ∧ ∀ y : Y,
      α • R y + K.adjoint (K (R y)) = K.adjoint y ∧
      ∀ x : X, x ≠ R y →
        ‖K (R y) - y‖ ^ 2 + α * ‖R y‖ ^ 2 < ‖K x - y‖ ^ 2 + α * ‖x‖ ^ 2 := by
  sorry

/-- **Gap 22.7.** Tikhonov error under the order-one source condition.
The inequality separates data noise from approximation bias. -/
theorem tikhonov_error_le_of_adjoint_source (K : X →L[ℝ] Y) (w : X) (y : Y)
    {α δ : ℝ} (hα : 0 < α) (R : Y →L[ℝ] X)
    (hR : ∀ d, α • R d + K.adjoint (K (R d)) = K.adjoint d)
    (hnoise : ‖y - K (K.adjoint (K w))‖ ≤ δ) :
    ‖R y - K.adjoint (K w)‖ ≤ δ / (2 * Real.sqrt α) + α * ‖w‖ := by
  sorry

/-- **Gap 22.8.** The minimum-norm solution in a discrepancy ball is a
Tikhonov solution at positive discrepancy parameter when zero is infeasible. -/
theorem exists_morozov_parameter (K : X →L[ℝ] Y) (hK : DenseRange K)
    {y : Y} {δ : ℝ} (hδ : 0 < δ) (hy : δ < ‖y‖) :
    ∃ (x : X) (α : ℝ), 0 < α ∧ ‖K x - y‖ = δ ∧
      α • x + K.adjoint (K x) = K.adjoint y ∧
      α * (‖y‖ - δ) ≤ ‖K‖ ^ 2 * δ ∧
      ∀ z : X, ‖K z - y‖ ≤ δ → (‖x‖ ≤ ‖z‖ ∧ (‖x‖ = ‖z‖ → x = z)) := by
  sorry

/-- Landweber filter with an initial gradient step, so index $m$ includes $m+1$ terms. -/
def landweberFilter (K : X →L[ℝ] Y) (a : ℝ) (m : ℕ) : Y →L[ℝ] X :=
  a • ∑ j ∈ Finset.range (m + 1), ((1 - a • K.adjoint.comp K) ^ j).comp K.adjoint

/-- **Gap 22.9.** The Landweber filter converges on exact data and has the
square-root amplification bound for perturbed data. -/
theorem landweberFilter_norm_le_and_tendsto (K : X →L[ℝ] Y)
    (hK : Function.Injective K) {a : ℝ} (ha : 0 < a) (hstep : a * ‖K‖ ^ 2 < 1) :
    (∀ m, ‖landweberFilter K a m‖ ≤ Real.sqrt (a * ((m : ℝ) + 1))) ∧
      ∀ x : X, Tendsto (fun m ↦ landweberFilter K a m (K x)) atTop (𝓝 x) := by
  sorry

/-- **Gap 22.9.** The first discrepancy crossing exists for dense-range data
and yields a regular parameter choice for the Landweber iteration. -/
theorem exists_landweber_discrepancy_tendsto (K : X →L[ℝ] Y)
    (hK : Function.Injective K) (hKd : DenseRange K) {a γ : ℝ}
    (ha : 0 < a) (hstep : a * ‖K‖ ^ 2 < 1) (hγ : 1 < γ)
    (x : X) (d : ℝ → Y) (hnoise : ∀ δ > (0 : ℝ), ‖d δ - K x‖ ≤ δ) :
    ∃ m : ℝ → ℕ, (∀ δ > (0 : ℝ),
      ‖K (landweberFilter K a (m δ) (d δ)) - d δ‖ ≤ γ * δ ∧
        ∀ j < m δ, γ * δ < ‖K (landweberFilter K a j (d δ)) - d δ‖) ∧
      Tendsto (fun δ ↦ landweberFilter K a (m δ) (d δ)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  sorry

end Hilbert

end NASC
