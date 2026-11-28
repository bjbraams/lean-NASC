module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Linear inverse problems and regularization

Picard's range criterion, the generalized inverse, convergence under parameter selection,
Tikhonov and discrepancy methods, and Landweber iteration. Tikhonov existence uses
Mathlib's Lax--Milgram equivalence in the pivot Hilbert space. `K†` below denotes the
Hilbert adjoint `K.adjoint`.

## Main definitions

* `NASC.generalizedInverseDomain`: the domain `range K ⊕ (range K)ᗮ` of the generalized
  inverse.
* `NASC.tikhonovNormalOp`: the Tikhonov normal operator `α • 1 + K† K`.
* `NASC.landweberFilter`: the Landweber iteration as a filter of the normal operator.

## Main results

* `NASC.exists_eq_image_iff_picard`: Picard's criterion.
* `NASC.exists_generalizedInverse_closedGraph`: the Moore--Penrose generalized inverse.
* `NASC.regularization_tendsto_of_noise_control`: convergence of a priori parameter choices.
* `NASC.exists_tikhonov_normal_solve`: Tikhonov regularization and its noise amplification.
* `NASC.tikhonov_error_le_of_adjoint_source`: the Tikhonov error under a source condition.
* `NASC.exists_morozov_parameter`: Morozov's discrepancy principle.
* `NASC.landweberFilter_norm_le_and_tendsto`, `NASC.exists_landweber_discrepancy_tendsto`:
  Landweber iteration with a priori and discrepancy stopping.
-/

public section

noncomputable section

namespace NASC

open Set Filter
open scoped Topology

/-- **Gap 22.5.** Noise amplification and exact-data consistency give regularization
convergence for an a priori parameter choice. The noise level `δ` tends to its limit along
any filter `l` (typically `𝓝[>] 0`), the parameter choice `α` maps `l` to the filter `l'` along
which the regularization `R` is consistent on the exact data `y₀`, and `δ ‖R (α δ)‖ → 0`. -/
theorem regularization_tendsto_of_noise_control {X Y β : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter ℝ} {l' : Filter β} (R : β → Y →L[ℝ] X) (α : ℝ → β) (data : ℝ → Y)
    (y₀ : Y) (x : X) (hα : Tendsto α l l') (hR : Tendsto (fun a ↦ R a y₀) l' (𝓝 x))
    (hnoise : ∀ᶠ δ in l, ‖data δ - y₀‖ ≤ δ)
    (hsmall : Tendsto (fun δ ↦ δ * ‖R (α δ)‖) l (𝓝 0)) :
    Tendsto (fun δ ↦ R (α δ) (data δ)) l (𝓝 x) := by
  have hbase := hR.comp hα
  have herror : Tendsto (fun δ ↦ R (α δ) (data δ - y₀)) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hsmall
    filter_upwards [hnoise] with δ hd
    calc
      _ ≤ ‖R (α δ)‖ * ‖data δ - y₀‖ := (R (α δ)).le_opNorm _
      _ ≤ ‖R (α δ)‖ * δ := mul_le_mul_of_nonneg_left hd (R (α δ)).opNorm_nonneg
      _ = _ := mul_comm _ _
  simpa only [map_sub, Function.comp_apply, sub_add_cancel, zero_add] using herror.add hbase

section Hilbert

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Gap 22.3.** Picard's criterion and its reconstruction from a complete
positive singular system, with arbitrary index sets allowed. -/
theorem exists_eq_image_iff_picard {ι : Type*}
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

omit [CompleteSpace X] [CompleteSpace Y] in
/-- The defining formula of `NASC.generalizedInverseDomain`. -/
theorem generalizedInverseDomain_def (K : X →L[ℝ] Y) :
    generalizedInverseDomain K = K.toLinearMap.range ⊔ K.toLinearMap.rangeᗮ :=
  (rfl)

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

/-- The Tikhonov normal operator `α • 1 + K† K`. -/
def tikhonovNormalOp (K : X →L[ℝ] Y) (α : ℝ) : X →L[ℝ] X :=
  α • (1 : X →L[ℝ] X) + K.adjoint.comp K

/-- The defining formula of `NASC.tikhonovNormalOp`. -/
theorem tikhonovNormalOp_apply (K : X →L[ℝ] Y) (α : ℝ) (v : X) :
    tikhonovNormalOp K α v = α • v + K.adjoint (K v) := by
  simp only [tikhonovNormalOp, add_apply, smul_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]

/-- Testing the normal operator against a vector gives its coercive bilinear form. -/
theorem tikhonov_normal_inner (K : X →L[ℝ] Y) (α : ℝ) (v w : X) :
    inner ℝ (α • v + K.adjoint (K v)) w = α * inner ℝ v w + inner ℝ (K v) (K w) := by
  rw [inner_add_left, real_inner_smul_left, K.adjoint_inner_left]

/-- Testing the normal equation against the solution gives the Tikhonov noise budget. -/
theorem norm_le_of_tikhonov_normal (K : X →L[ℝ] Y) {α : ℝ} (hα : 0 < α)
    {x : X} {y : Y} (h : α • x + K.adjoint (K x) = K.adjoint y) :
    ‖x‖ ≤ ‖y‖ / (2 * Real.sqrt α) := by
  have heq := congrArg (fun v : X ↦ inner ℝ v x) h
  simp only [tikhonov_normal_inner, K.adjoint_inner_left, real_inner_self_eq_norm_sq] at heq
  have hbound := heq.le.trans (real_inner_le_norm y (K x))
  have hsq : 4 * α * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith only [hbound, sq_nonneg (‖K x‖ - ‖y‖ / 2)]
  apply (le_div_iff₀ (mul_pos two_pos (Real.sqrt_pos.mpr hα))).mpr
  apply (sq_le_sq₀ (by positivity) (norm_nonneg y)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hα.le]
  nlinarith only [hsq]

/-- The normal equation gives the exact Tikhonov objective difference. -/
theorem tikhonov_objective_eq_add_error (K : X →L[ℝ] Y) (α : ℝ) (y : Y) (x v : X)
    (h : α • x + K.adjoint (K x) = K.adjoint y) :
    ‖K v - y‖ ^ 2 + α * ‖v‖ ^ 2 =
      (‖K x - y‖ ^ 2 + α * ‖x‖ ^ 2) + (‖K (v - x)‖ ^ 2 + α * ‖v - x‖ ^ 2) := by
  have heq := congrArg (fun z : X ↦ inner ℝ z (v - x)) h
  simp only [tikhonov_normal_inner, K.adjoint_inner_left] at heq
  have hcancel : inner ℝ (K x - y) (K (v - x)) + α * inner ℝ x (v - x) = 0 := by
    rw [inner_sub_left]
    linarith only [heq]
  have hs : x + (v - x) = v := by abel
  have hKs : (K x - y) + K (v - x) = K v - y := by rw [map_sub]; abel
  have hn := norm_add_sq_real x (v - x)
  have hKn := norm_add_sq_real (K x - y) (K (v - x))
  rw [hs] at hn
  rw [hKs] at hKn
  rw [hn, hKn]
  nlinarith only [hcancel]

/-- **Gap 22.6.** Tikhonov regularization is the unique quadratic minimizer.
The regularized inverse has the bound $1/(2\sqrt{\alpha})$. -/
theorem exists_tikhonov_normal_solve (K : X →L[ℝ] Y) {α : ℝ} (hα : 0 < α) :
    ∃ R : Y →L[ℝ] X, ‖R‖ ≤ (2 * Real.sqrt α)⁻¹ ∧ ∀ y : Y,
      α • R y + K.adjoint (K (R y)) = K.adjoint y ∧
      ∀ x : X, x ≠ R y →
        ‖K (R y) - y‖ ^ 2 + α * ‖R y‖ ^ 2 < ‖K x - y‖ ^ 2 + α * ‖x‖ ^ 2 := by
  let N := tikhonovNormalOp K α
  have hN (v : X) : N v = α • v + K.adjoint (K v) := tikhonovNormalOp_apply K α v
  let B : X →L[ℝ] StrongDual ℝ X := (innerSL ℝ).comp N
  have hB (v w : X) : B v w = inner ℝ (N v) w := by
    simp only [B, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  have hco : IsCoercive B := by
    refine ⟨α, hα, fun v ↦ ?_⟩
    rw [hB, hN, tikhonov_normal_inner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith only [sq_nonneg ‖K v‖]
  let A := hco.continuousLinearEquivOfBilin
  have hA (v : X) : A v = N v :=
    (hco.unique_continuousLinearEquivOfBilin (fun w ↦ (hB v w).symm)).symm
  let R := (A.symm : X →L[ℝ] X).comp K.adjoint
  have hR (y : Y) : α • R y + K.adjoint (K (R y)) = K.adjoint y := by
    rw [← hN, ← hA]
    exact A.apply_symm_apply (K.adjoint y)
  refine ⟨R, R.opNorm_le_bound (by positivity) ?_, fun y ↦ ⟨hR y, ?_⟩⟩
  · intro y
    simpa only [div_eq_mul_inv, mul_comm ‖y‖] using norm_le_of_tikhonov_normal K hα (hR y)
  · intro v hv
    rw [tikhonov_objective_eq_add_error K α y (R y) v (hR y)]
    exact lt_add_of_pos_right _ (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos hα (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)))))

/-- Applying a Tikhonov solver to exact data is a contraction on the source space. -/
theorem norm_tikhonov_exactData_le (K : X →L[ℝ] Y) {α : ℝ} (hα : 0 < α)
    {z w : X} (h : α • z + K.adjoint (K z) = K.adjoint (K w)) : ‖z‖ ≤ ‖w‖ := by
  by_cases hz : z = 0
  · simpa only [hz, norm_zero] using norm_nonneg w
  have htest := congrArg (fun x : X ↦ inner ℝ x (w - z)) h
  simp only [tikhonov_normal_inner, K.adjoint_inner_left] at htest
  have hprod : α * inner ℝ z (w - z) = ‖K (w - z)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, map_sub K w z, inner_sub_left]
    rw [map_sub] at htest
    linarith only [htest]
  have hnn : 0 ≤ inner ℝ z (w - z) :=
    nonneg_of_mul_nonneg_right (hprod.symm ▸ sq_nonneg _) hα
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hnn
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
  rw [← pow_two]
  exact (sub_nonneg.mp hnn).trans (real_inner_le_norm z w)

/-- **Gap 22.7.** Tikhonov error under the order-one source condition.
The inequality separates data noise from approximation bias. -/
theorem tikhonov_error_le_of_adjoint_source (K : X →L[ℝ] Y) (w : X) (y : Y)
    {α δ : ℝ} (hα : 0 < α) (R : Y →L[ℝ] X)
    (hR : ∀ d, α • R d + K.adjoint (K (R d)) = K.adjoint d)
    (hnoise : ‖y - K (K.adjoint (K w))‖ ≤ δ) :
    ‖R y - K.adjoint (K w)‖ ≤ δ / (2 * Real.sqrt α) + α * ‖w‖ := by
  let x := K.adjoint (K w)
  let z := R (K w)
  let N := tikhonovNormalOp K α
  have hN (v : X) : N v = α • v + K.adjoint (K v) := tikhonovNormalOp_apply K α v
  have hR' (d : Y) : N (R d) = K.adjoint d := (hN _).trans (hR d)
  have hinj : Function.Injective N := by
    intro a b hab
    have he : α • (a - b) + K.adjoint (K (a - b)) = K.adjoint 0 := by
      rw [← hN, map_sub, hab, sub_self, map_zero]
    have hnorm := norm_le_of_tikhonov_normal K hα he
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [norm_zero, zero_div] using hnorm))
  have hbias : x - R (K x) = α • z := by
    apply hinj
    rw [map_sub, hR', map_smul, hR', hN]
    exact add_sub_cancel_right _ _
  have hsplit : R y - x = R (y - K x) - α • z := by rw [← hbias, map_sub]; abel
  have hnoise' : ‖R (y - K x)‖ ≤ δ / (2 * Real.sqrt α) :=
    (norm_le_of_tikhonov_normal K hα (hR (y - K x))).trans
      (div_le_div_of_nonneg_right hnoise (by positivity))
  have hb : ‖α • z‖ ≤ α * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg hα.le]
    exact mul_le_mul_of_nonneg_left (norm_tikhonov_exactData_le K hα (hR (K w))) hα.le
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add hnoise' hb)

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

/-- The defining formula of `NASC.landweberFilter`. -/
theorem landweberFilter_def (K : X →L[ℝ] Y) (a : ℝ) (m : ℕ) :
    landweberFilter K a m =
      a • ∑ j ∈ Finset.range (m + 1), ((1 - a • K.adjoint.comp K) ^ j).comp K.adjoint :=
  (rfl)

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
