module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multilevel and Schwarz methods

Two-grid smoothing, cycle estimates, optimal decompositions, successive correction,
and spectral bounds for additive Schwarz and BDDC lifts. Subspace corrections use the
orthogonal projections `Submodule.starProjection`, with the Hilbert inner product playing the
role of the energy inner product.

## Main definitions

* `NASC.projectionSweep`: the error propagation operator of successive subspace correction.

## Main results

* `NASC.norm_twoGrid_le`: the two-grid bound from smoothing and approximation properties.
* `NASC.norm_symmetricTwoGrid_le`: the symmetric two-grid estimate.
* `NASC.norm_projectionSweep_sq_eq_xuZikatanov`: the Xu--Zikatanov identity.
* `NASC.norm_twoLevel_sq_eq_coarseOptimization`: the two-level convergence identity.
* `NASC.schwarz_rayleigh_bounds`: spectral bounds for additive Schwarz, and
  `NASC.schwarz_condition_bound_of_overlap_decomposition` the resulting condition bound.
* `NASC.exists_additiveInverse_isLeast_energy`: Lions' lemma.
* `NASC.exists_wCycle_uniform_bound`, `NASC.fullMultigrid_dyadic_error_le`: cycle recurrences.
* `NASC.bddc_averaging_spectral_bounds`: the BDDC spectral estimate.
-/

public section

noncomputable section

namespace NASC

open Set

/-- **Gap 20.1.** The two-grid error operator `(1 - B A) S^ν` is bounded by the smoothing
budget times the relative inverse approximation constant. It is an identity in any normed
ring, applied to the unit `A` (for example a continuous linear equivalence). On the zero ring
the hypotheses carry no information and `0 ≤ η` is needed. -/
theorem norm_twoGrid_le {R : Type*} [SeminormedRing R] (A : Rˣ) (B S : R)
    (ν : ℕ) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (happrox : ‖(↑A⁻¹ : R) - B‖ ≤ C / ‖(A : R)‖)
    (hsmooth : ‖(A : R) * S ^ ν‖ ≤ η * ‖(A : R)‖) :
    ‖(1 - B * A) * S ^ ν‖ ≤ C * η := by
  rw [← A.inv_mul, ← sub_mul, mul_assoc]
  calc
    _ ≤ ‖(↑A⁻¹ : R) - B‖ * ‖(A : R) * S ^ ν‖ := norm_mul_le _ _
    _ ≤ (C / ‖(A : R)‖) * (η * ‖(A : R)‖) :=
      mul_le_mul happrox hsmooth (norm_nonneg _) (div_nonneg hC (norm_nonneg _))
    _ = C * η * (‖(A : R)‖ / ‖(A : R)‖) := by ring
    _ ≤ C * η := mul_le_of_le_one_right (mul_nonneg hC hη) (div_self_le_one _)

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Gap 20.3.** Symmetric smoothing bounds the two-grid energy norm by the
Richardson smoothing constant. The Hilbert norm here is the energy norm. -/
theorem norm_symmetricTwoGrid_le [CompleteSpace H]
    (S : H →L[ℝ] H) (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (hS : S.IsPositive) (hS₁ : ‖S‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (happrox : ∀ v, ‖v - V.starProjection v‖ ^ 2 ≤ C * inner ℝ ((1 - S) v) v)
    (m : ℕ) :
    ‖S ^ m * (1 - V.starProjection) * S ^ m‖ ≤
      C * ((2 * m : ℕ) : ℝ) ^ (2 * m) / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * m + 1) := by
  sorry

/-- The consecutive exact subspace corrections `(1 - P_{n-1}) ⋯ (1 - P_0)`, in increasing
index order. -/
def projectionSweep {n : ℕ} (P : Fin n → H →L[ℝ] H) : H →L[ℝ] H :=
  (List.finRange n).foldl (fun E i ↦ (1 - P i) * E) 1

/-- The defining formula of `NASC.projectionSweep`. -/
theorem projectionSweep_def {n : ℕ} (P : Fin n → H →L[ℝ] H) :
    projectionSweep P = (List.finRange n).foldl (fun E i ↦ (1 - P i) * E) 1 :=
  (rfl)

/-- **Gap 20.6.** Xu--Zikatanov identity for exact subspace correction, with
orthogonal projections taken in the energy inner product. -/
theorem norm_projectionSweep_sq_eq_xuZikatanov [FiniteDimensional ℝ H] {n : ℕ}
    (V : Fin n → Submodule ℝ H) [∀ i, (V i).HasOrthogonalProjection]
    (hspan : ∀ v : H, ∃ w : ∀ i, V i, v = ∑ i, (w i).val) :
    let P := fun i ↦ (V i).starProjection
    let c := sSup {t : ℝ | ∃ v : H, ‖v‖ = 1 ∧
      t = sInf {s : ℝ | ∃ w : ∀ i, V i, v = (∑ i, (w i).val) ∧
        s = ∑ i, ‖P i (∑ j ∈ Finset.univ.filter (i < ·), (w j).val)‖ ^ 2}}
    ‖projectionSweep P‖ ^ 2 = 1 - (1 + c)⁻¹ := by
  sorry

/-- **Gap 20.7.** The two-level convergence identity after transforming the energy
operator to the identity. The inverse symmetrized smoother supplies the coarse norm. The
coarse space must be proper: for `V = ⊤` the left side is `0`, while `K = 0` and the junk value
`0⁻¹ = 0` make the right side `1`. -/
theorem norm_twoLevel_sq_eq_coarseOptimization [FiniteDimensional ℝ H] [Nontrivial H]
    (S : H →L[ℝ] H) (hS : ‖S‖ < 1) (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (hV : V ≠ ⊤)
    (R : H ≃L[ℝ] H) (hR : (R : H →L[ℝ] H) = 1 - S.adjoint * S) :
    let K := sSup {t : ℝ | ∃ v : H, ‖v‖ = 1 ∧ t =
      sInf (range (fun w : V ↦ inner ℝ (R.symm (v - w.val)) (v - w.val)))}
    ‖S * (1 - V.starProjection)‖ ^ 2 = 1 - K⁻¹ := by
  sorry

/-- **Gap 20.8.** Stable decompositions and bounded overlap in the synthesis norm
give both spectral bounds for additive Schwarz with exact local solves. -/
theorem schwarz_rayleigh_bounds {n : ℕ}
    (V : Fin n → Submodule ℝ H) [∀ i, (V i).HasOrthogonalProjection]
    {C D : ℝ} (hC : 0 < C)
    (hdecomp : ∀ u : H, ∃ v : ∀ i, V i, u = (∑ i, (v i).val) ∧
      (∑ i, ‖v i‖ ^ 2) ≤ C * ‖u‖ ^ 2)
    (hoverlap : ∀ v : ∀ i, V i, ‖∑ i, (v i).val‖ ^ 2 ≤ D * ∑ i, ‖v i‖ ^ 2) :
    ∀ u : H, ‖u‖ ^ 2 / C ≤ inner ℝ ((∑ i, (V i).starProjection) u) u ∧
      inner ℝ ((∑ i, (V i).starProjection) u) u ≤ D * ‖u‖ ^ 2 := by
  intro u
  -- `⟪v, u⟫ = ⟪v, P i u⟫` for `v ∈ V i`
  have hproj (i : Fin n) (v : H) (hv : v ∈ V i) :
      inner ℝ v u = inner ℝ v ((V i).starProjection u) := by
    have h := (V i).starProjection_inner_eq_zero u v hv
    rw [inner_sub_left, real_inner_comm, real_inner_comm v] at h
    linarith only [h]
  have hmem (i : Fin n) := (V i).starProjection_apply_mem u
  set p := inner ℝ ((∑ i, (V i).starProjection) u) u
  have hp : p = ∑ i, ‖(V i).starProjection u‖ ^ 2 := by
    simp only [p, FunLike.coe_sum, Finset.sum_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hproj i _ (hmem i), real_inner_self_eq_norm_sq]
  have hp₀ : 0 ≤ p := hp ▸ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  -- lower bound: test the decomposition of `u` against the projections
  obtain ⟨v, hu, hv⟩ := hdecomp u
  have hsq : (‖u‖ ^ 2) ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) * p := by
    have heq : ‖u‖ ^ 2 = ∑ i, inner ℝ (v i : H) ((V i).starProjection u) := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => arg 2; rw [hu]
      rw [sum_inner]
      exact Finset.sum_congr rfl fun i _ ↦ hproj i _ (v i).2
    rw [heq, hp]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ ↦ sq_nonneg _)
      (fun i _ ↦ sq_nonneg _) fun i _ ↦ ?_
    rw [← Submodule.norm_coe, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  have hlow : ‖u‖ ^ 2 ≤ C * p := by
    have h := hsq.trans (mul_le_mul_of_nonneg_right hv hp₀)
    rcases (sq_nonneg ‖u‖).eq_or_lt with h' | h'
    · rw [← h']
      exact mul_nonneg hC.le hp₀
    · nlinarith only [h, h']
  refine ⟨(div_le_iff₀ hC).mpr (by linarith only [hlow]), ?_⟩
  -- upper bound: Cauchy--Schwarz and the overlap bound for the projections
  have hup : p ^ 2 ≤ D * p * ‖u‖ ^ 2 := by
    have h₁ : p ≤ ‖∑ i, (V i).starProjection u‖ * ‖u‖ := by
      simpa only [p, FunLike.coe_sum, Finset.sum_apply] using
        real_inner_le_norm ((∑ i, (V i).starProjection) u) u
    have h₂ : ‖∑ i, (V i).starProjection u‖ ^ 2 ≤ D * p := by
      rw [hp]
      exact hoverlap fun i ↦ ⟨(V i).starProjection u, hmem i⟩
    calc
      p ^ 2 ≤ (‖∑ i, (V i).starProjection u‖ * ‖u‖) ^ 2 := pow_le_pow_left₀ hp₀ h₁ 2
      _ = ‖∑ i, (V i).starProjection u‖ ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
      _ ≤ D * p * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right h₂ (sq_nonneg _)
  rcases hp₀.eq_or_lt with h | h
  · have hu0 : ‖u‖ ^ 2 = 0 := le_antisymm (by simpa only [← h, mul_zero] using hlow)
      (sq_nonneg _)
    rw [← h, hu0, mul_zero]
  · nlinarith only [hup, h]

/-- **Gap 20.9.** Overlap and the stable decomposition estimate with a coarse
component give the two-level Schwarz condition bound. The decomposition budget
contains the ratio of subdomain diameter to overlap. This is `NASC.schwarz_rayleigh_bounds`
with the decomposition constant `C (1 + Hdiam / δ)`; the geometric construction of such a
decomposition is not part of the statement. The hypothesis `0 ≤ Hdiam` keeps the budget
positive, which the conclusion `0 ≤ b / a` needs on the zero space. -/
theorem schwarz_condition_bound_of_overlap_decomposition {n : ℕ}
    (V : Fin n → Submodule ℝ H) [∀ i, (V i).HasOrthogonalProjection]
    {C L Hdiam δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hH : 0 ≤ Hdiam) (hδ : 0 < δ)
    (hdecomp : ∀ u : H, ∃ v : ∀ i, V i, u = (∑ i, (v i).val) ∧
      (∑ i, ‖v i‖ ^ 2) ≤ C * (1 + Hdiam / δ) * ‖u‖ ^ 2)
    (hcolor : ∀ v : ∀ i, V i, ‖∑ i, (v i).val‖ ^ 2 ≤ L * ∑ i, ‖v i‖ ^ 2) :
    ∃ a > (0 : ℝ), ∃ b ≥ (0 : ℝ), b / a ≤ C * L * (1 + Hdiam / δ) ∧
      ∀ u : H, a * ‖u‖ ^ 2 ≤ inner ℝ ((∑ i, (V i).starProjection) u) u ∧
        inner ℝ ((∑ i, (V i).starProjection) u) u ≤ b * ‖u‖ ^ 2 := by
  have hK : 0 < C * (1 + Hdiam / δ) := mul_pos hC (by positivity)
  have hb := schwarz_rayleigh_bounds V hK hdecomp hcolor
  refine ⟨(C * (1 + Hdiam / δ))⁻¹, inv_pos.mpr hK, L, hL, ?_, fun u ↦ ⟨?_, (hb u).2⟩⟩
  · rw [div_inv_eq_mul]
    exact le_of_eq (by ring)
  · simpa only [div_eq_inv_mul] using (hb u).1

/-- **Gap 20.5.** Lions' minimum energy characterization of the additive
subspace preconditioner, with heterogeneous local Hilbert spaces. -/
theorem exists_additiveInverse_isLeast_energy [FiniteDimensional ℝ H] {n : ℕ}
    {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (I : ∀ i, E i →L[ℝ] H) (B : ∀ i, E i ≃L[ℝ] E i)
    (hB : ∀ i, IsSelfAdjoint (B i : E i →L[ℝ] E i))
    (hBpos : ∀ i x, x ≠ 0 → 0 < inner ℝ (B i x) x)
    (hs : ∀ u : H, ∃ v : ∀ i, E i, u = ∑ i, I i (v i)) :
    ∃ P : H ≃L[ℝ] H, (P : H →L[ℝ] H) =
      (∑ i, (I i).comp (((B i).symm : E i →L[ℝ] E i).comp (I i).adjoint)) ∧
      ∀ u : H, IsLeast {t : ℝ | ∃ v : ∀ i, E i, u = (∑ i, I i (v i)) ∧
        t = ∑ i, inner ℝ (B i (v i)) (v i)} (inner ℝ (P.symm u) u) := by
  sorry

end Hilbert

/-- **Gap 20.2.** A W-cycle error recurrence with at least two inner
iterations preserves a uniform target contraction for a sufficiently small
two-grid factor. -/
theorem exists_wCycle_uniform_bound {γ : ℕ} (hγ : 2 ≤ γ)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ δ ∈ Ioc (0 : ℝ) ε, ∃ η > (0 : ℝ), ∀ M : ℕ → ℝ,
      (∀ k, 0 ≤ M k) → M 0 = 0 → (∀ k, M (k + 1) ≤ η + C * M k ^ γ) →
      ∀ k, M k ≤ δ := by
  let δ := min ε (1 / (2 * (C + 1)))
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := lt_min hε (one_div_pos.mpr hden)
  have hδε : δ ≤ ε := min_le_left ..
  have hδone : δ ≤ 1 := hδε.trans hε'.le
  have hsmall : δ * (2 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right ..)
  have hCδ : C * δ ≤ 1 / 2 := by nlinarith only [hsmall, hδ.le]
  refine ⟨δ, ⟨hδ, hδε⟩, δ / 2, by positivity, fun M hM hzero hstep k ↦ ?_⟩
  induction k with
  | zero => rw [hzero]; exact hδ.le
  | succ k ih =>
    calc
      M (k + 1) ≤ δ / 2 + C * M k ^ γ := hstep k
      _ ≤ δ / 2 + C * δ ^ 2 := add_le_add_right
        (mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (hM k) ih γ).trans (pow_le_pow_of_le_one hδ.le hδone hγ)) hC) _
      _ ≤ δ := by
        have h := mul_le_mul_of_nonneg_right hCδ hδ.le
        nlinarith only [h]

/-- **Gap 20.4.** Full multigrid preserves first-order energy accuracy on a
dyadic hierarchy when each cycle contracts more strongly than the mesh ratio. -/
theorem fullMultigrid_dyadic_error_le (e : ℕ → ℝ) {γ C h : ℝ}
    (hγ : 0 ≤ γ) (hcontract : 2 * γ < 1) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (h₀ : e 0 ≤ C * h)
    (hstep : ∀ k, e (k + 1) ≤ γ * (e k + C * h / (2 : ℝ) ^ k)) :
    ∀ k, e k ≤ (C / (1 - 2 * γ)) * h / (2 : ℝ) ^ k := by
  let K := (C / (1 - 2 * γ)) * h
  have hden : 0 < 1 - 2 * γ := sub_pos.mpr hcontract
  have hK : 0 ≤ K := mul_nonneg (div_nonneg hC hden.le) hh
  have heq : (1 - 2 * γ) * K = C * h := by
    dsimp only [K]
    field_simp
  have hK₀ : C * h ≤ K := by nlinarith only [heq, mul_nonneg hγ hK]
  have hK₁ : 2 * γ * (K + C * h) ≤ K := by
    nlinarith only [heq, mul_nonneg hden.le (mul_nonneg hC hh)]
  intro k
  induction k with
  | zero => simpa only [pow_zero, div_one] using h₀.trans hK₀
  | succ k ih =>
    calc
      e (k + 1) ≤ γ * (e k + C * h / (2 : ℝ) ^ k) := hstep k
      _ ≤ γ * (K / (2 : ℝ) ^ k + C * h / (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add_left ih _) hγ
      _ = (2 * γ * (K + C * h)) / (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hK₁ (by positivity)

/-- **Gap 20.11.** The discrete trace bound on BDDC averaging yields the
polylogarithmic spectral estimate in the interface energy inner product. -/
theorem bddc_averaging_spectral_bounds {H W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (E : W →L[ℝ] H) (J : H →ₗᵢ[ℝ] W) (hJ : ∀ u, E (J u) = u)
    {C Hdiam h : ℝ} (hC : 0 ≤ C) (hh : 0 < h) (hH : h ≤ Hdiam)
    (htrace : ∀ w, ‖E w‖ ≤ C * (1 + Real.log (Hdiam / h)) * ‖w‖) :
    ∀ u : H, ‖u‖ ^ 2 ≤ inner ℝ (E (E.adjoint u)) u ∧
      inner ℝ (E (E.adjoint u)) u ≤ C ^ 2 * (1 + Real.log (Hdiam / h)) ^ 2 * ‖u‖ ^ 2 := by
  intro u
  have hid : inner ℝ (E (E.adjoint u)) u = ‖E.adjoint u‖ ^ 2 := by
    rw [← E.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hid]
  have hlower : ‖u‖ ≤ ‖E.adjoint u‖ := by
    by_cases hu : u = 0
    · rw [hu, norm_zero]
      exact norm_nonneg _
    have hpair : inner ℝ (J u) (E.adjoint u) = ‖u‖ ^ 2 := by
      rw [E.adjoint_inner_right, hJ, real_inner_self_eq_norm_sq]
    have hs := abs_real_inner_le_norm (J u) (E.adjoint u)
    rw [hpair, abs_of_nonneg (sq_nonneg _), J.norm_map] at hs
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hu)).mp (by rw [← pow_two]; exact hs)
  have hlog : 0 ≤ Real.log (Hdiam / h) := Real.log_nonneg ((le_div_iff₀ hh).mpr (by simpa using hH))
  have hE : ‖E‖ ≤ C * (1 + Real.log (Hdiam / h)) :=
    E.opNorm_le_bound (mul_nonneg hC (by positivity)) htrace
  have hu : ‖E.adjoint u‖ ≤ C * (1 + Real.log (Hdiam / h)) * ‖u‖ := by
    refine (E.adjoint.le_opNorm u).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  refine ⟨pow_le_pow_left₀ (norm_nonneg _) hlower 2, ?_⟩
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hu 2

end NASC
