module

public import NASC.Approximation
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Variational and mixed Galerkin methods

Banach inf-sup solvability, Fortin's criterion, quasi-optimality, Strang consistency,
duality, and saddle point problems. Bilinear forms are bundled into maps to the dual.
-/

public section

noncomputable section

namespace NASC

open Set
open scoped BigOperators InnerProductSpace

section Banach

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Gap 18.1.** The Banach--Nečas--Babuška theorem. The inf-sup condition
is written as a uniform lower bound for the map to the test-space dual. -/
theorem bijective_iff_infSup_of_reflexive [CompleteSpace V] [CompleteSpace W]
    (A : V →L[ℝ] StrongDual ℝ W)
    (hW : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ W)) :
    Function.Bijective A ↔
      (∃ α > (0 : ℝ), ∀ v, α * ‖v‖ ≤ ‖A v‖) ∧ (∀ w, (∀ v, A v w = 0) → w = 0) := by
  sorry

/-- **Gap 18.2.** A Fortin map that preserves the pairing transfers the
continuous inf-sup lower bound to the discrete trial space. -/
theorem norm_restrict_ge_of_fortin (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) (P : W →L[ℝ] Y)
    {α γ : ℝ} (_hα : 0 < α) (hγ : 0 < γ) (hA : ∀ v, α * ‖v‖ ≤ ‖A v‖)
    (hP : ∀ w, γ * ‖P w‖ ≤ ‖w‖)
    (hfortin : ∀ (v : X) (w : W), A v.val (P w).val = A v.val w) :
    ∀ v : X, γ * α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖ := by
  intro v
  let R := (A v.val).comp Y.subtypeL
  have hbound : ‖A v.val‖ ≤ ‖R‖ / γ := by
    refine (A v.val).opNorm_le_bound (div_nonneg R.opNorm_nonneg hγ.le) fun w ↦ ?_
    have hpair : R (P w) = A v.val w := hfortin v w
    rw [← hpair]
    have hw : ‖P w‖ ≤ ‖w‖ / γ := (le_div_iff₀ hγ).mpr (by simpa [mul_comm] using hP w)
    calc
      _ ≤ ‖R‖ * ‖P w‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (‖w‖ / γ) := mul_le_mul_of_nonneg_left hw R.opNorm_nonneg
      _ = _ := by ring
  have h := (hA v.val).trans hbound
  have hmul := (le_div_iff₀ hγ).mp h
  simpa only [R, Submodule.norm_coe, mul_left_comm, mul_comm, mul_assoc] using hmul

/-- Restriction to the discrete test space preserves the bilinear operator bound. -/
theorem norm_bilinear_restrict_le (A : V →L[ℝ] StrongDual ℝ W) (v : V) (Y : Submodule ℝ W) :
    ‖(A v).comp Y.subtypeL‖ ≤ ‖A‖ * ‖v‖ := by
  calc
    _ ≤ ‖A v‖ * ‖Y.subtypeL‖ := (A v).opNorm_comp_le _
    _ ≤ ‖A v‖ * 1 := mul_le_mul_of_nonneg_left Y.norm_subtypeL_le (A v).opNorm_nonneg
    _ = ‖A v‖ := mul_one _
    _ ≤ _ := A.le_opNorm v

/-- **Gap 18.3.** Babuška quasi-optimality for a discrete solution
satisfying Galerkin orthogonality. -/
theorem norm_galerkinError_le_of_infSup (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) {α : ℝ} (hα : 0 < α)
    (hstab : ∀ v : X, α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖)
    (u : V) (uh : X) (horth : ∀ w : Y, A (u - uh.val) w.val = 0) :
    ‖u - uh.val‖ ≤ (1 + ‖A‖ / α) * bestApproximationError (X : Set V) u := by
  let c : ℝ := 1 + ‖A‖ / α
  have hc : 0 < c := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg A.opNorm_nonneg hα.le)
  have hpoint (v : X) : ‖u - uh.val‖ ≤ c * ‖u - v.val‖ := by
    have hr : (A (v - uh).val).comp Y.subtypeL = -((A (u - v.val)).comp Y.subtypeL) := by
      ext w
      have hz := horth w
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.coe_sub,
        map_sub, sub_apply, neg_apply] at hz ⊢
      linarith only [hz]
    have hstab' := hstab (v - uh)
    have hrnorm : ‖(A (v - uh).val).comp Y.subtypeL‖ =
        ‖(A (u - v.val)).comp Y.subtypeL‖ := by
      rw [hr]
      exact norm_neg ((A (u - v.val)).comp Y.subtypeL)
    rw [hrnorm, ← Submodule.norm_coe, Submodule.coe_sub] at hstab'
    have hv : ‖v.val - uh.val‖ ≤ ‖A‖ / α * ‖u - v.val‖ := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hα).mpr (by
        simpa only [mul_comm ‖v.val - uh.val‖] using
          hstab'.trans (norm_bilinear_restrict_le A (u - v.val) Y))
    calc
      _ ≤ ‖u - v.val‖ + ‖v.val - uh.val‖ := by
        simpa only [dist_eq_norm] using dist_triangle u v.val uh.val
      _ ≤ ‖u - v.val‖ + (‖A‖ / α) * ‖u - v.val‖ := add_le_add_right hv _
      _ = _ := by dsimp only [c]; ring
  rw [bestApproximationError_def, mul_comm (1 + ‖A‖ / α)]
  apply (div_le_iff₀ hc).mp
  refine le_csInf ⟨‖u - 0‖, ⟨0, X.zero_mem, rfl⟩⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact (div_le_iff₀ hc).mpr (by
    simpa only [mul_comm ‖u - v‖] using hpoint ⟨v, hv⟩)

/-- **Gap 18.3.** The Hilbert trial-space improvement of the inf-sup
quasi-optimality factor. -/
theorem norm_galerkinError_le_of_infSup_hilbert {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ H) [X.HasOrthogonalProjection] (Y : Submodule ℝ W)
    (hn : X ≠ ⊥) {α : ℝ} (hα : 0 < α)
    (hstab : ∀ v : X, α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖)
    (u : H) (uh : X) (horth : ∀ w : Y, A (u - uh.val) w.val = 0) :
    ‖u - uh.val‖ ≤ ‖A‖ / α * bestApproximationError (X : Set H) u := by
  sorry

/-- **Gap 18.4.** An inconsistent discrete form is controlled by the
approximation error and the dual norm of its consistency defect. -/
theorem norm_galerkinError_le_strang (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) (Ah : X →L[ℝ] StrongDual ℝ Y)
    {α : ℝ} (hα : 0 < α) (hstab : ∀ v : X, α * ‖v‖ ≤ ‖Ah v‖)
    (u : V) (uh : X) (f : StrongDual ℝ W) (fh : StrongDual ℝ Y)
    (hsol : A u = f) (hsh : Ah uh = fh) (v : X) :
    ‖u - uh.val‖ ≤ (1 + ‖A‖ / α) * ‖u - v.val‖ +
      ‖fh - f.comp Y.subtypeL + (A v.val).comp Y.subtypeL - Ah v‖ / α := by
  let D := fh - f.comp Y.subtypeL + (A v.val).comp Y.subtypeL - Ah v
  have hsplit : Ah (uh - v) = (A (u - v.val)).comp Y.subtypeL + D := by
    ext w
    simp only [D, ← hsol, ← hsh, ContinuousLinearMap.comp_apply, map_sub, sub_apply, add_apply]
    abel
  have hstab' : α * ‖uh.val - v.val‖ ≤ ‖A‖ * ‖u - v.val‖ + ‖D‖ := by
    have hs := hstab (uh - v)
    rw [hsplit, ← Submodule.norm_coe, Submodule.coe_sub] at hs
    exact hs.trans ((norm_add_le ((A (u - v.val)).comp Y.subtypeL) D).trans
      (add_le_add_left (norm_bilinear_restrict_le A (u - v.val) Y) _))
  have hv : ‖uh.val - v.val‖ ≤ (‖A‖ * ‖u - v.val‖ + ‖D‖) / α :=
    (le_div_iff₀ hα).mpr (by simpa only [mul_comm ‖uh.val - v.val‖] using hstab')
  calc
    ‖u - uh.val‖ ≤ ‖u - v.val‖ + ‖v.val - uh.val‖ := by
      simpa only [dist_eq_norm] using dist_triangle u v.val uh.val
    _ = ‖u - v.val‖ + ‖uh.val - v.val‖ := by rw [norm_sub_rev v.val uh.val]
    _ ≤ ‖u - v.val‖ + (‖A‖ * ‖u - v.val‖ + ‖D‖) / α := add_le_add_right hv _
    _ = _ := by rw [add_div]; ring

/-- **Gap 18.13.** Energy quasi-optimality for a conforming Galerkin approximation.
The energy norm is written as the square root of the positive symmetric form. -/
theorem galerkin_energy_error_le (A : V →L[ℝ] StrongDual ℝ V)
    (hA : ∀ v w, A v w = A w v) (hpos : ∀ v, 0 ≤ A v v)
    (X : Submodule ℝ V) (u : V) (uh : X) (horth : ∀ w : X, A (u - uh.val) w.val = 0)
    (v : X) :
    Real.sqrt (A (u - uh.val) (u - uh.val)) ≤ Real.sqrt (A (u - v.val) (u - v.val)) := by
  let e := u - uh.val
  let w := uh - v
  have hsplit : u - v.val = e + w.val := by
    simp only [e, w, Submodule.coe_sub]
    abel
  have hew : A e w.val = 0 := horth w
  have hwe : A w.val e = 0 := (hA _ _).trans hew
  apply Real.sqrt_le_sqrt
  rw [hsplit]
  simp only [map_add, add_apply, hew, hwe, add_zero, zero_add]
  exact le_add_of_nonneg_right (hpos w.val)

/-- **Gap 18.14.** Aubin--Nitsche improvement from approximation of all dual
solutions for the weaker Hilbert-space norm. -/
theorem norm_weak_galerkinError_le_of_dualApproximation {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : V →L[ℝ] StrongDual ℝ V) (J : V →L[ℝ] H) (X : Submodule ℝ V)
    (e : V) (horth : ∀ v : X, A e v.val = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdual : ∀ g : H, ∃ z : V, (∀ v, A v z = inner ℝ (J v) g) ∧
      ∃ w : X, ‖z - w.val‖ ≤ δ * ‖g‖) :
    ‖J e‖ ≤ ‖A‖ * δ * ‖e‖ := by
  by_cases he : ‖J e‖ = 0
  · rw [he]
    positivity
  have hp : 0 < ‖J e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
  obtain ⟨z, hz, w, hw⟩ := hdual (J e)
  have hpair : A e (z - w.val) = ‖J e‖ ^ 2 := by
    rw [map_sub, horth, sub_zero, hz, real_inner_self_eq_norm_sq]
  have hbound : ‖J e‖ ^ 2 ≤ (‖A‖ * δ * ‖e‖) * ‖J e‖ :=
    calc
      _ = ‖A e (z - w.val)‖ := by rw [hpair, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖A e‖ * ‖z - w.val‖ := (A e).le_opNorm _
      _ ≤ (‖A‖ * ‖e‖) * (δ * ‖J e‖) :=
        mul_le_mul (A.le_opNorm e) hw (norm_nonneg _) (mul_nonneg A.opNorm_nonneg (norm_nonneg _))
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hp).mp (by
    simpa only [← pow_two, mul_comm ‖J e‖ (‖A‖ * δ * ‖e‖)] using hbound)

/-- Equations for a mixed problem in the ambient spaces. -/
def IsMixedSolution (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W)
    (f : StrongDual ℝ V) (g : StrongDual ℝ W) (u : V) (p : W) : Prop :=
  (∀ v, A u v + B v p = f v) ∧ ∀ q, B u q = g q

/-- **Gap 18.18.** Coercivity on the kernel and the constraint inf-sup condition
give unique saddle point solvability in real reflexive Banach spaces. -/
theorem existsUnique_mixedSolution_of_infSup [CompleteSpace V] [CompleteSpace W]
    (hV : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V))
    (hW : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ W))
    (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ v, B v = 0 → α * ‖v‖ ^ 2 ≤ A v v)
    (hB : ∀ q : W, β * ‖q‖ ≤ ‖(NormedSpace.inclusionInDoubleDual ℝ W q).comp B‖)
    (f : StrongDual ℝ V) (g : StrongDual ℝ W) :
    ∃! up : V × W, IsMixedSolution A B f g up.1 up.2 := by
  sorry

/-- **Gap 18.19.** Uniform discrete saddle stability yields quasi-optimality with
constants independent of the discrete subspaces. -/
theorem exists_mixed_quasiOptimal_constant
    (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ C ≥ (0 : ℝ), ∀ (X : Submodule ℝ V) (Y : Submodule ℝ W)
      (_ : FiniteDimensional ℝ X) (_ : FiniteDimensional ℝ Y),
      (∀ v : X, (∀ q : Y, B v.val q.val = 0) → α * ‖v‖ ^ 2 ≤ A v.val v.val) →
      (∀ q : Y, β * ‖q‖ ≤ ‖(NormedSpace.inclusionInDoubleDual ℝ W q.val).comp
        (B.comp X.subtypeL)‖) →
      ∀ (u : V) (p : W) (uh : X) (ph : Y),
        (∀ v : X, A (u - uh.val) v.val + B v.val (p - ph.val) = 0) →
        (∀ q : Y, B (u - uh.val) q.val = 0) →
        ‖u - uh.val‖ + ‖p - ph.val‖ ≤ C *
          (bestApproximationError (X : Set V) u + bestApproximationError (Y : Set W) p) := by
  sorry

end Banach

/-- **Gap 18.17.** The symmetric interior penalty quadratic form controls the
broken gradient and weighted jump norm under the inverse trace bound. -/
theorem sipg_coercivity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (h : Fin n → ℝ) (hpos : ∀ i, 0 < h i) (j a : Fin n → H)
    {c G η : ℝ} (hG : 0 ≤ G) (htrace : (∑ i, h i * ‖a i‖ ^ 2) ≤ c ^ 2 * G)
    (hpen : 2 * c ^ 2 + 1 / 2 ≤ η) :
    (G + ∑ i, ‖j i‖ ^ 2 / h i) / 2 ≤
      G - 2 * (∑ i, inner ℝ (a i) (j i)) + η * ∑ i, ‖j i‖ ^ 2 / h i := by
  let T := ∑ i, ‖j i‖ ^ 2 / h i
  let S := ∑ i, inner ℝ (a i) (j i)
  let u := fun i ↦ Real.sqrt (h i) * ‖a i‖
  let v := fun i ↦ ‖j i‖ / Real.sqrt (h i)
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ ↦ div_nonneg (sq_nonneg _) (hpos i).le
  have hu : (∑ i, u i ^ 2) = ∑ i, h i * ‖a i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [u, mul_pow, Real.sq_sqrt (hpos i).le]
  have hv : (∑ i, v i ^ 2) = T := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [v, div_pow, Real.sq_sqrt (hpos i).le]
  have hp : |S| ≤ ∑ i, u i * v i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    have hh : Real.sqrt (h i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    have heq : u i * v i = ‖a i‖ * ‖j i‖ := by
      dsimp only [u, v]
      field_simp
    rw [heq]
    exact abs_real_inner_le_norm _ _
  have hs : S ^ 2 ≤ c ^ 2 * G * T := calc
    _ = |S| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i, u i * v i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
    _ ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by rw [hu, hv]; exact mul_le_mul_of_nonneg_right htrace hT
  have hm : 0 ≤ G / 2 + 2 * c ^ 2 * T := by positivity
  have hc : 2 * S ≤ G / 2 + 2 * c ^ 2 * T := by
    by_cases hS : S ≤ 0
    · linarith only [hS, hm]
    apply (sq_le_sq₀ (by linarith only [hS]) hm).mp
    nlinarith only [hs, sq_nonneg (G / 2 - 2 * c ^ 2 * T)]
  have hη := mul_le_mul_of_nonneg_right hpen hT
  linarith only [hc, hη]

end NASC
