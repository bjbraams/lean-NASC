module

public import NASC.FiniteElements
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Variational eigenproblems and a posteriori estimates

Min--max eigenvalues, compact spectral approximation, residual estimators, equilibrated
fluxes, adaptive contraction, and the obstacle comparison estimate.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set Filter TopologicalSpace TauCeti
open scoped BigOperators ENNReal

/-- **Gap 19.13.** The energy eigenproblem has the min--max values of the
Rayleigh quotient when the solution operator in the pivot space is compact. -/
theorem exists_variationalEigenvalue_minmax {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (hJd : DenseRange J)
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

/-- **Gap 19.14.** Nonzero limits of eigenvalues of norm-convergent compact
approximations belong to the point spectrum of the limit operator. -/
theorem exists_eigenvector_of_compact_normLimit {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (Tₕ : ℕ → H →L[ℝ] H) (hconv : Tendsto Tₕ atTop (nhds T))
    (e : ℕ → ℝ) {r : ℝ} (hr : r ≠ 0) (he : Tendsto e atTop (nhds r))
    (x : ℕ → H) (hx : ∀ n, ‖x n‖ = 1 ∧ Tₕ n (x n) = e n • x n) :
    ∃ v : H, ‖v‖ = 1 ∧ T v = r • v := by
  sorry

/-- **Gap 19.15.** The Rayleigh quotient perturbation at an eigenvector is
exactly quadratic in the eigenvector error, in both energy and pivot norms. -/
theorem rayleigh_error_eq_quadratic {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →L[ℝ] H) (A : V →L[ℝ] StrongDual ℝ V) (hA : ∀ u v, A u v = A v u)
    (u v : V) (e : ℝ) (hu : ∀ w, A u w = e * inner ℝ (J u) (J w))
    (hv : ‖J v‖ = 1) :
    A v v - e = A (v - u) (v - u) - e * ‖J (v - u)‖ ^ 2 := by
  sorry

/-- **Gap 19.17.** Residual reliability from cell and face interpolation
bounds, expressed by a single weighted collection of residual terms. -/
theorem norm_error_le_of_weighted_residuals {V H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : V →L[ℝ] StrongDual ℝ V) {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hcoerce : ∀ e, α * ‖e‖ ^ 2 ≤ A e e)
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (r : Fin n → H)
    (z : V → Fin n → H) (e : V)
    (hrep : ∀ v, A e v = ∑ i, inner ℝ (r i) (z v i))
    (hinterp : ∀ v, (∑ i, ‖z v i‖ ^ 2 / w i) ≤ C ^ 2 * ‖v‖ ^ 2) :
    ‖e‖ ≤ (C / α) * Real.sqrt (∑ i, w i * ‖r i‖ ^ 2) := by
  sorry

/-- **Gap 19.18.** The Prager--Synge identity for a weak Poisson solution and
an equilibrated flux. The divergence equation is written in integrated weak form. -/
theorem pragerSynge_identity {d : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [μ.IsAddHaarMeasure] {Ω : Opens (EuclideanSpace ℝ (Fin d))}
    (f : Lp ℝ 2 (μ.restrict Ω)) (u uh : W1p0 μ Ω 2)
    (σ : Lp (EuclideanSpace ℝ (Fin d)) 2 (μ.restrict Ω))
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (fun _ ↦ 1) 0 0 f u)
    (hdiv : ∀ v : W1p0 μ Ω 2,
      inner ℝ σ (W1p.gradient (v : W1p μ Ω 2)) = -inner ℝ f (W1p0.valueL v)) :
    let G := fun v : W1p0 μ Ω 2 ↦ W1p.gradient (v : W1p μ Ω 2)
    ‖G u - G uh‖ ^ 2 + ‖G u + σ‖ ^ 2 = ‖G uh + σ‖ ^ 2 := by
  sorry

/-- **Gap 19.19.** Estimator reduction, reliability, and energy quasi-orthogonality
yield a uniform geometric contraction of a combined error. -/
theorem exists_adaptive_error_contraction
    (energy estimator jump : ℕ → ℝ) {q C R : ℝ}
    (hpos : ∀ j, 0 ≤ energy j ∧ 0 ≤ estimator j ∧ 0 ≤ jump j)
    (hq : 0 ≤ q) (hq' : q < 1) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hrel : ∀ j, energy j ≤ R * estimator j)
    (horth : ∀ j, energy (j + 1) + jump j ≤ energy j)
    (hred : ∀ j, estimator (j + 1) ≤ q * estimator j + C * jump j) :
    ∃ γ > (0 : ℝ), ∃ ρ ∈ Ioo (0 : ℝ) 1,
      ∀ j, energy (j + 1) + γ * estimator (j + 1) ≤ ρ * (energy j + γ * estimator j) := by
  sorry

/-- **Gap 19.20.** Falk's comparison estimate for obstacle discretizations with
possibly nonconforming convex constraint sets. -/
theorem falk_obstacle_error_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (f : StrongDual ℝ V) {α : ℝ} (hα : 0 < α)
    (hcoerce : ∀ v, α * ‖v‖ ^ 2 ≤ A v v)
    (K Kh : Set V) {u uh : V}
    (hsol : ∀ v ∈ K, f (v - u) ≤ A u (v - u))
    (hdisc : ∀ v ∈ Kh, f (v - uh) ≤ A uh (v - uh))
    {v vh : V} (hv : v ∈ K) (hvh : vh ∈ Kh) :
    α / 2 * ‖u - uh‖ ^ 2 ≤
      ‖A u - f‖ * (‖uh - v‖ + ‖u - vh‖) + ‖A‖ ^ 2 / (2 * α) * ‖u - vh‖ ^ 2 := by
  sorry

end NASC
