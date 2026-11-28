module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.PDE.DirichletProblem

import NASC.Support.LinearAlgebra

/-!
# Variational eigenproblems and a posteriori estimates

Min--max eigenvalues, compact spectral approximation, residual estimators, equilibrated
fluxes, adaptive contraction, and the obstacle comparison estimate. The Prager--Synge
proof uses TauCeti's identity between the Poisson energy form and the gradient inner product
(`TauCeti.PDE.energyFormH1_one_zero_zero_eq_inner`).

## Main results

* `NASC.exists_variationalEigenvalue_minmax`: the min--max characterization of eigenvalues.
* `NASC.exists_eigenvector_of_isCompactOperator_of_tendsto`: nonzero limits of eigenvalues of
  norm-convergent approximations are eigenvalues of a compact limit.
* `NASC.rayleigh_error_eq_quadratic`: the Rayleigh quotient error is quadratic.
* `NASC.norm_error_le_of_weighted_residuals`: reliability of residual estimators.
* `NASC.norm_sub_sq_add_norm_add_sq_eq_of_equilibrated`: the Prager--Synge identity.
* `NASC.exists_adaptive_error_contraction`: contraction of adaptive finite element methods.
* `NASC.falk_obstacle_error_le`: Falk's estimate for obstacle problems.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set Filter TopologicalSpace TauCeti
open scoped ENNReal Topology

/-- **Gap 19.13.** The energy eigenproblem has the min--max values of the
Rayleigh quotient when the solution operator in the pivot space is compact. -/
theorem exists_variationalEigenvalue_minmax {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (A : V →L[ℝ] StrongDual ℝ V) (hA : ∀ u v, A u v = A v u)
    {α : ℝ} (hα : 0 < α) (hpos : ∀ u, α * ‖u‖ ^ 2 ≤ A u u)
    (S : H →L[ℝ] V) (hsol : ∀ f v, A (S f) v = inner ℝ f (J v))
    (hcomp : IsCompactOperator (J.comp S)) {k : ℕ} (hk : 0 < k)
    (hV : ∃ X : Submodule ℝ V, Module.finrank ℝ X = k) :
    ∃ eig : ℝ, 0 < eig ∧
      (∃ u : V, u ≠ 0 ∧ ∀ v, A u v = eig * inner ℝ (J u) (J v)) ∧
      IsLeast {m : ℝ | ∃ X : Submodule ℝ V, Module.finrank ℝ X = k ∧
        m = sSup {r : ℝ | ∃ u : X, u ≠ 0 ∧ r = A u.val u.val / ‖J u.val‖ ^ 2}} eig := by
  sorry

/-- **Gap 19.14.** Nonzero limits of eigenvalues of norm-convergent approximations of a
compact operator belong to its point spectrum. The approximations need not be compact, and
the space need not be complete or carry an inner product. -/
theorem exists_eigenvector_of_isCompactOperator_of_tendsto {𝕜 H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (T : H →L[𝕜] H) (hT : IsCompactOperator T)
    (Tₕ : ℕ → H →L[𝕜] H) (hconv : Tendsto Tₕ atTop (𝓝 T))
    (e : ℕ → 𝕜) {r : 𝕜} (hr : r ≠ 0) (he : Tendsto e atTop (𝓝 r))
    (x : ℕ → H) (hx : ∀ n, ‖x n‖ = 1 ∧ Tₕ n (x n) = e n • x n) :
    ∃ v : H, ‖v‖ = 1 ∧ T v = r • v := by
  have hmem (n : ℕ) : T (x n) ∈ closure (T '' Metric.closedBall 0 1) :=
    subset_closure ⟨x n, by simp only [Metric.mem_closedBall, dist_zero_right, (hx n).1, le_refl],
      rfl⟩
  obtain ⟨y, _, φ, hφ, hTφ⟩ := (hT.isCompact_closure_image_closedBall 1).isSeqCompact hmem
  have hzero : Tendsto (fun n ↦ (Tₕ n - T) (x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n ↦ ‖Tₕ n - T‖) (fun n ↦ ?_) ?_
    · simpa only [(hx n).1, mul_one] using (Tₕ n - T).le_opNorm (x n)
    · have hconst : Tendsto (fun _ : ℕ ↦ T) atTop (𝓝 T) := tendsto_const_nhds
      simpa only [sub_self, norm_zero] using (hconv.sub hconst).norm
  have hTₕφ : Tendsto (fun n ↦ Tₕ (φ n) (x (φ n))) atTop (𝓝 y) := by
    simpa only [Function.comp_apply, sub_apply, sub_add_cancel, zero_add] using
      (hzero.comp hφ.tendsto_atTop).add hTφ
  have heφ := he.comp hφ.tendsto_atTop
  have hnonzero : ∀ᶠ n in atTop, e (φ n) ≠ 0 :=
    heφ.eventually (isOpen_ne.mem_nhds hr)
  have hxφ : Tendsto (fun n ↦ x (φ n)) atTop (𝓝 (r⁻¹ • y)) := by
    refine ((heφ.inv₀ hr).smul hTₕφ).congr' ?_
    filter_upwards [hnonzero] with n hn
    simp only [Function.comp_apply, (hx (φ n)).2, inv_smul_smul₀ hn]
  have hv : ‖r⁻¹ • y‖ = 1 := tendsto_nhds_unique hxφ.norm
    (by
      have heq : (fun n ↦ ‖x (φ n)‖) = fun _ : ℕ ↦ (1 : ℝ) := funext fun n ↦ (hx (φ n)).1
      rw [heq]
      exact tendsto_const_nhds)
  have hTy : T (r⁻¹ • y) = y := tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hxφ) hTφ
  exact ⟨r⁻¹ • y, hv, hTy.trans (smul_inv_smul₀ hr _).symm⟩

/-- **Gap 19.15.** The Rayleigh quotient perturbation at an eigenvector is
exactly quadratic in the eigenvector error, in both energy and pivot norms. -/
theorem rayleigh_error_eq_quadratic {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →L[ℝ] H) (A : V →L[ℝ] StrongDual ℝ V) (hA : ∀ u v, A u v = A v u)
    (u v : V) (e : ℝ) (hu : ∀ w, A u w = e * inner ℝ (J u) (J w))
    (hv : ‖J v‖ = 1) :
    A v v - e = A (v - u) (v - u) - e * ‖J (v - u)‖ ^ 2 := by
  have h₁ := hu v
  have h₂ := hu u
  rw [real_inner_self_eq_norm_sq] at h₂
  have hnorm := norm_sub_sq_real (J v) (J u)
  rw [hv, real_inner_comm (J u) (J v)] at hnorm
  simp only [map_sub, sub_apply, hnorm]
  linarith only [h₁, h₂, hA v u]

/-- **Gap 19.17.** Residual reliability from cell and face interpolation
bounds, expressed by a single weighted collection of residual terms. -/
theorem norm_error_le_of_weighted_residuals {ι V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : V →L[ℝ] StrongDual ℝ V) {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hcoerce : ∀ e, α * ‖e‖ ^ 2 ≤ A e e)
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (r : ι → H)
    (z : V → ι → H) (e : V)
    (hrep : ∀ v, A e v = ∑ i ∈ s, inner ℝ (r i) (z v i))
    (hinterp : ∀ v, (∑ i ∈ s, ‖z v i‖ ^ 2 / w i) ≤ C ^ 2 * ‖v‖ ^ 2) :
    ‖e‖ ≤ (C / α) * Real.sqrt (∑ i ∈ s, w i * ‖r i‖ ^ 2) := by
  set R := ∑ i ∈ s, w i * ‖r i‖ ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi).le (sq_nonneg _)
  have hEpos : 0 ≤ α * ‖e‖ ^ 2 := by positivity
  have hE : α * ‖e‖ ^ 2 ≤ ∑ i ∈ s, inner ℝ (r i) (z e i) := (hcoerce e).trans (hrep e).le
  have hprod : α * ‖e‖ ^ 2 ≤ C * Real.sqrt R * ‖e‖ := by
    apply (sq_le_sq₀ hEpos (by positivity)).mp
    calc
      _ ≤ (∑ i ∈ s, inner ℝ (r i) (z e i)) ^ 2 := (sq_le_sq₀ hEpos (hEpos.trans hE)).mpr hE
      _ ≤ R * ∑ i ∈ s, ‖z e i‖ ^ 2 / w i := sq_sum_inner_le_sum_mul_sum_div s hw r (z e)
      _ ≤ R * (C ^ 2 * ‖e‖ ^ 2) := mul_le_mul_of_nonneg_left (hinterp e) hR
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hR]; ring
  by_cases he : ‖e‖ = 0
  · rw [he]
    exact mul_nonneg (div_nonneg hC hα.le) (Real.sqrt_nonneg _)
  have hnorm : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
  have he' : α * ‖e‖ ≤ C * Real.sqrt R := by
    apply (mul_le_mul_iff_right₀ hnorm).mp
    nlinarith only [hprod]
  rw [div_mul_eq_mul_div, le_div_iff₀ hα]
  simpa only [mul_comm ‖e‖ α] using he'

/-- **Gap 19.18.** The Prager--Synge identity for a weak Poisson solution and
an equilibrated flux. The divergence equation is written in integrated weak form. -/
theorem norm_sub_sq_add_norm_add_sq_eq_of_equilibrated {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [μ.IsAddHaarMeasure] {Ω : Opens (EuclideanSpace ℝ (Fin d))}
    (f : Lp ℝ 2 (μ.restrict Ω)) (u uh : W1p0 μ Ω 2)
    (σ : Lp (EuclideanSpace ℝ (Fin d)) 2 (μ.restrict Ω))
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (fun _ ↦ 1) 0 0 f u)
    (hdiv : ∀ v : W1p0 μ Ω 2,
      inner ℝ σ (W1p.gradient (v : W1p μ Ω 2)) = -inner ℝ f (W1p0.valueL v)) :
    let G := fun v : W1p0 μ Ω 2 ↦ W1p.gradient (v : W1p μ Ω 2)
    ‖G u - G uh‖ ^ 2 + ‖G u + σ‖ ^ 2 = ‖G uh + σ‖ ^ 2 := by
  dsimp only
  have hu' := (TauCeti.PDE.isWeakSolutionDirichlet_iff_inner f u).mp hu (uh - u)
  rw [TauCeti.PDE.energyFormH1_one_zero_zero_eq_inner] at hu'
  have hdiv' := hdiv (uh - u)
  have hg : W1p.gradient ((uh - u : W1p0 μ Ω 2) : W1p μ Ω 2) =
      W1p.gradient (uh : W1p μ Ω 2) - W1p.gradient (u : W1p μ Ω 2) :=
    W1p.gradient_sub _ _
  rw [hg] at hu' hdiv'
  set gu := W1p.gradient (u : W1p μ Ω 2)
  set guh := W1p.gradient (uh : W1p μ Ω 2)
  have horth : inner ℝ (gu + σ) (guh - gu) = 0 := by
    rw [inner_add_left, hu', hdiv', W1p0.valueL_apply, add_neg_cancel]
  have hsum : guh + σ = (gu + σ) + (guh - gu) := by abel
  rw [hsum, sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real horth, norm_sub_rev, add_comm]

/-- **Gap 19.19.** Estimator reduction, reliability, and energy quasi-orthogonality
yield a uniform geometric contraction of a combined error. -/
theorem exists_adaptive_error_contraction
    (energy estimator jump : ℕ → ℝ) {q C R : ℝ}
    (hpos : ∀ j, 0 ≤ estimator j ∧ 0 ≤ jump j)
    (hq : 0 ≤ q) (hq' : q < 1) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hrel : ∀ j, energy j ≤ R * estimator j)
    (horth : ∀ j, energy (j + 1) + jump j ≤ energy j)
    (hred : ∀ j, estimator (j + 1) ≤ q * estimator j + C * jump j) :
    ∃ γ > (0 : ℝ), ∃ ρ ∈ Ioo (0 : ℝ) 1,
      ∀ j, energy (j + 1) + γ * estimator (j + 1) ≤ ρ * (energy j + γ * estimator j) := by
  let γ : ℝ := 1 / (1 + C)
  let δ : ℝ := γ * (1 - q) / (2 * (R + γ))
  have hγ : 0 < γ := one_div_pos.mpr (by linarith)
  have hγC : γ * C ≤ 1 := by
    have heq : γ * (1 + C) = 1 := div_mul_cancel₀ _ (by positivity)
    nlinarith only [heq, hγ]
  have hden : 0 < R + γ := add_pos_of_nonneg_of_pos hR hγ
  have hδ : 0 < δ := div_pos (mul_pos hγ (sub_pos.mpr hq')) (mul_pos two_pos hden)
  have hδeq : δ * (R + γ) = γ * (1 - q) / 2 := by
    dsimp only [δ]
    field_simp
  have hδone : δ < 1 := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    rw [mul_comm (R + γ) δ, hδeq, mul_one]
    nlinarith only [hγ, hR, mul_nonneg hγ.le hq]
  refine ⟨γ, hγ, 1 - δ, ⟨sub_pos.mpr hδone, sub_lt_self _ hδ⟩, fun j ↦ ?_⟩
  have hstep : energy (j + 1) + γ * estimator (j + 1) ≤ energy j + γ * q * estimator j := by
    have hred' := mul_le_mul_of_nonneg_left (hred j) hγ.le
    have hjump := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hγC) (hpos j).2
    linarith only [horth j, hred', hjump]
  have hbudget : δ * (energy j + γ * estimator j) ≤ γ * (1 - q) * estimator j :=
    calc
      _ ≤ δ * ((R + γ) * estimator j) :=
        mul_le_mul_of_nonneg_left (by linarith only [hrel j]) hδ.le
      _ = (γ * (1 - q) / 2) * estimator j := by rw [← mul_assoc, hδeq]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by linarith only [mul_nonneg hγ.le (sub_nonneg.mpr hq'.le)]) (hpos j).1
  linarith only [hstep, hbudget]

/-- **Gap 19.20.** Falk's comparison estimate for obstacle discretizations with
possibly nonconforming constraint sets (`Kh ⊄ K` is allowed). The sets `K` and `Kh` are
arbitrary: convexity is what makes the variational inequalities `hsol` and `hdisc` solvable,
but the estimate itself does not use it. -/
theorem falk_obstacle_error_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (f : StrongDual ℝ V) {α : ℝ} (hα : 0 < α)
    (hcoerce : ∀ v, α * ‖v‖ ^ 2 ≤ A v v)
    (K Kh : Set V) {u uh : V}
    (hsol : ∀ v ∈ K, f (v - u) ≤ A u (v - u))
    (hdisc : ∀ v ∈ Kh, f (v - uh) ≤ A uh (v - uh))
    {v vh : V} (hv : v ∈ K) (hvh : vh ∈ Kh) :
    α / 2 * ‖u - uh‖ ^ 2 ≤
      ‖A u - f‖ * (‖uh - v‖ + ‖u - vh‖) + ‖A‖ ^ 2 / (2 * α) * ‖u - vh‖ ^ 2 := by
  let e := u - uh
  let d := u - vh
  let r := A u - f
  have hrv : 0 ≤ r (v - u) := sub_nonneg.mpr (hsol v hv)
  have hre : r e ≤ ‖r‖ * ‖uh - v‖ := by
    have he : e = v - uh - (v - u) := by dsimp only [e]; abel
    have h := r.le_opNorm (v - uh)
    rw [Real.norm_eq_abs, norm_sub_rev v uh] at h
    rw [he, map_sub]
    exact (sub_le_self _ hrv).trans ((le_abs_self _).trans h)
  have hrd : -r d ≤ ‖r‖ * ‖d‖ :=
    (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using r.le_opNorm d)
  have hAe : A e d ≤ ‖A‖ * ‖e‖ * ‖d‖ :=
    calc
      _ ≤ ‖(A e) d‖ := le_abs_self _
      _ ≤ ‖A e‖ * ‖d‖ := (A e).le_opNorm d
      _ ≤ _ := mul_le_mul_of_nonneg_right (A.le_opNorm e) (norm_nonneg _)
  have hdis : A uh d - f d ≤ A uh e - f e := by
    have he : e = d + (vh - uh) := by dsimp only [e, d]; abel
    rw [he, map_add, map_add]
    linarith only [hdisc vh hvh]
  have he₁ : A e e = r e - (A uh e - f e) := by
    simp only [e, r, map_sub, sub_apply]
    ring
  have he₂ : -(A uh d - f d) = A e d - r d := by
    simp only [e, r, map_sub, sub_apply]
    ring
  have henergy : A e e ≤ ‖r‖ * (‖uh - v‖ + ‖d‖) + ‖A‖ * ‖e‖ * ‖d‖ := by
    linarith only [hre, hrd, hAe, hdis, he₁, he₂]
  have hyoung : ‖A‖ * ‖e‖ * ‖d‖ ≤ α / 2 * ‖e‖ ^ 2 + ‖A‖ ^ 2 / (2 * α) * ‖d‖ ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hα).mp
    simp only [add_mul, mul_assoc]
    have hc : ‖A‖ ^ 2 / (2 * α) * α = ‖A‖ ^ 2 / 2 := by field_simp
    rw [mul_comm (‖d‖ ^ 2) α, ← mul_assoc (‖A‖ ^ 2 / (2 * α)) α, hc]
    nlinarith only [sq_nonneg (α * ‖e‖ - ‖A‖ * ‖d‖)]
  linarith only [hcoerce e, henergy, hyoung]

end NASC
