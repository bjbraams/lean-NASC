module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Parabolic and spectral Galerkin methods

Energy estimates and Ritz projection defects, time discretization, smoothing for nonsmooth
initial data, discontinuous Galerkin time stepping, and Fourier and polynomial projection.
Abstract parabolic problems are written in a pivot Hilbert space `H` with a bounded positive
operator `A`, so that `⟪A v, w⟫` is the energy form.

## Main definitions

* `NASC.IsDGHeatStep`: one discontinuous-Galerkin step for the scalar test equation.
* `NASC.legendre`: the Legendre polynomial on `[-1, 1]`, from Mathlib's
  `Polynomial.shiftedLegendre`.

## Main results

* `NASC.norm_le_add_integral_of_inner_le`: the energy estimate behind the parabolic bounds,
  and `NASC.norm_le_add_integral_norm_of_hasDerivWithinAt` its form for `θ' = f - A θ`.
* `NASC.ritz_parabolic_error_le`: the semidiscrete error bound from the Ritz defect.
* `NASC.parabolic_timeStepping_error_le`: stability of the theta method for `θ ∈ [1/2, 1]`.
* `NASC.exists_parabolic_smoothing_constant`: the nonsmooth-data smoothing estimate.
* `NASC.exists_dgHeatStep_error_le_pow`: superconvergence of the dG step.
* `NASC.fourier_tail_sobolev_sq_le`: the Fourier projection tail estimate.
* `NASC.existsUnique_legendreGalerkin`, `NASC.exists_legendreGalerkin_sobolev_error_bound`:
  the Legendre--Galerkin method.
-/

public section

noncomputable section

namespace NASC

open Set Filter MeasureTheory Polynomial
open scoped Topology Interval

section Parabolic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Energy estimate: if `⟪θ', θ⟫ ≤ g ‖θ‖` on `[0, T]`, then `‖θ T‖ ≤ ‖θ 0‖ + ∫₀ᵀ g`. -/
theorem norm_le_add_integral_of_inner_le {T : ℝ} (hT : 0 ≤ T) (θ θ' : ℝ → H) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 T))
    (hθ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt θ (θ' t) (Icc 0 T) t)
    (hle : ∀ t ∈ Icc (0 : ℝ) T, inner ℝ (θ' t) (θ t) ≤ g t * ‖θ t‖) :
    ‖θ T‖ ≤ ‖θ 0‖ + ∫ t in (0 : ℝ)..T, g t := by
  sorry

/-- The energy estimate for `θ' = f - A θ` with a positive operator `A`. -/
theorem norm_le_add_integral_norm_of_hasDerivWithinAt (A : H →L[ℝ] H)
    (hpos : ∀ v, 0 ≤ inner ℝ (A v) v) {T : ℝ} (hT : 0 ≤ T) (θ f : ℝ → H)
    (hf : ContinuousOn f (Icc 0 T))
    (heq : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt θ (f t - A (θ t)) (Icc 0 T) t) :
    ‖θ T‖ ≤ ‖θ 0‖ + ∫ t in (0 : ℝ)..T, ‖f t‖ :=
  norm_le_add_integral_of_inner_le hT θ _ _ hf.norm heq fun t _ ↦ by
    rw [inner_sub_left]
    linarith only [hpos (θ t), real_inner_le_norm (f t) (θ t)]

/-- **Gap 19.2.** Semidiscrete Galerkin error from the Ritz defect `ρ = Ru - u`, its time
derivative, and the initial data error. Here `u` solves `u' + A u = F`, the Galerkin solution
`uh` takes values in the trial space `X` and satisfies the equation tested on `X`, and `Ru` is
the Ritz projection of `u`, defined by `⟪A (Ru - u), v⟫ = 0` for `v ∈ X`. In applications
`u'` is the time derivative of `u`; the proof uses only the equation `u' + A u = F`. -/
theorem ritz_parabolic_error_le (A : H →L[ℝ] H) (hpos : ∀ v, 0 ≤ inner ℝ (A v) v)
    (X : Submodule ℝ H) {T : ℝ} (hT : 0 ≤ T) (u u' uh uh' Ru Ru' F : ℝ → H)
    (huh : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt uh (uh' t) (Icc 0 T) t)
    (hRu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Ru (Ru' t) (Icc 0 T) t)
    (hρ : ContinuousOn (fun t ↦ Ru' t - u' t) (Icc 0 T))
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, u' t + A (u t) = F t)
    (hmem : ∀ t ∈ Icc (0 : ℝ) T, uh t ∈ X ∧ Ru t ∈ X)
    (hgal : ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ X, inner ℝ (uh' t + A (uh t)) v = inner ℝ (F t) v)
    (hritz : ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ X, inner ℝ (A (Ru t - u t)) v = 0) :
    ‖uh T - u T‖ ≤ ‖uh 0 - u 0‖ + ‖Ru 0 - u 0‖ + ‖Ru T - u T‖ +
      ∫ t in (0 : ℝ)..T, ‖Ru' t - u' t‖ := by
  have hθ := norm_le_add_integral_of_inner_le hT (fun t ↦ uh t - Ru t)
    (fun t ↦ uh' t - Ru' t) _ hρ.norm (fun t ht ↦ HasDerivWithinAt.sub (huh t ht) (hRu t ht))
    fun t ht ↦ by
      have hv : uh t - Ru t ∈ X := X.sub_mem (hmem t ht).1 (hmem t ht).2
      have hg := hgal t ht _ hv
      have hr := hritz t ht _ hv
      have hs : F t = u' t + A (u t) := (hsol t ht).symm
      have hA := hpos (uh t - Ru t)
      have hcs := real_inner_le_norm (u' t - Ru' t) (uh t - Ru t)
      rw [norm_sub_rev] at hcs
      simp only [hs, inner_add_left, inner_sub_left, map_sub] at hg hr hA hcs ⊢
      linarith only [hg, hr, hA, hcs]
  have h0 : ‖uh 0 - Ru 0‖ ≤ ‖uh 0 - u 0‖ + ‖Ru 0 - u 0‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (uh 0 - u 0) (Ru 0 - u 0)
  have hT' : ‖uh T - u T‖ ≤ ‖uh T - Ru T‖ + ‖Ru T - u T‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (uh T - Ru T) (Ru T - u T)
  linarith only [hθ, h0, hT']

/-- **Gap 19.3.** The theta method with `θ ∈ [1/2, 1]` (backward Euler at `θ = 1`,
Crank--Nicolson at `θ = 1/2`) accumulates at most the summed local defect when the stiffness
operator is positive. The hypotheses force `0 ≤ δ`. -/
theorem parabolic_timeStepping_error_le [CompleteSpace H]
    (A : H →L[ℝ] H) (hpos : ∀ v, 0 ≤ inner ℝ (A v) v)
    {τ θ δ : ℝ} (hτ : 0 ≤ τ) (hθ : θ ∈ Icc (1 / 2 : ℝ) 1)
    (u U g : ℕ → H)
    (hU : ∀ n, U (n + 1) - U n + τ • A (θ • U (n + 1) + (1 - θ) • U n) = τ • g n)
    (hu : ∀ n, ‖u (n + 1) - u n + τ • A (θ • u (n + 1) + (1 - θ) • u n) - τ • g n‖ ≤ δ)
    (n : ℕ) :
    ‖U n - u n‖ ≤ ‖U 0 - u 0‖ + n * δ := by
  sorry

end Parabolic

/-- **Gap 19.4.** For positive heat semigroups on finite-dimensional inner-product spaces,
the inverse operator error gives a positive-time smoothing bound, even for arbitrary pivot
data. The constant is uniform over all spaces, operators and isometric embeddings. -/
theorem exists_parabolic_smoothing_constant :
    ∃ C ≥ (0 : ℝ), ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] (A : E ≃L[ℝ] E) (Ah : F ≃L[ℝ] F) (J : F →ₗᵢ[ℝ] E),
      (A : E →L[ℝ] E).IsPositive → (Ah : F →L[ℝ] F).IsPositive →
      ∀ t > (0 : ℝ),
        ‖J.toContinuousLinearMap ∘L NormedSpace.exp ((-t) • (Ah : F →L[ℝ] F)) ∘L
            J.toContinuousLinearMap.adjoint - NormedSpace.exp ((-t) • (A : E →L[ℝ] E))‖ ≤
          C / t * ‖(A.symm : E →L[ℝ] E) -
            J.toContinuousLinearMap ∘L (Ah.symm : F →L[ℝ] F) ∘L
              J.toContinuousLinearMap.adjoint‖ := by
  sorry

/-- One discontinuous-Galerkin time step of degree less than $q$ for the scalar
test equation, scaled to the unit interval. The initial right limit can jump. -/
def IsDGHeatStep (q : ℕ) (z : ℝ) (U : ℝ[X]) : Prop :=
  U.natDegree < q ∧
    ∀ p : ℝ[X], p.natDegree < q →
      (∫ t in (0 : ℝ)..1, (U.derivative.eval t + z * U.eval t) * p.eval t) +
        (U.eval 0 - 1) * p.eval 0 = 0

/-- The defining conditions of `NASC.IsDGHeatStep`. -/
theorem isDGHeatStep_iff {q : ℕ} {z : ℝ} {U : ℝ[X]} :
    IsDGHeatStep q z U ↔ U.natDegree < q ∧
      ∀ p : ℝ[X], p.natDegree < q →
        (∫ t in (0 : ℝ)..1, (U.derivative.eval t + z * U.eval t) * p.eval t) +
          (U.eval 0 - 1) * p.eval 0 = 0 :=
  Iff.rfl

/-- **Gap 19.5.** The scalar discontinuous-Galerkin step exists, is unique,
and has endpoint superconvergence. -/
theorem exists_dgHeatStep_error_le_pow (q : ℕ) (hq : 0 < q) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ Icc (0 : ℝ) 1,
      ∃ U : ℝ[X], IsDGHeatStep q z U ∧
        (∀ V : ℝ[X], IsDGHeatStep q z V → V = U) ∧
        |U.eval 1 - Real.exp (-z)| ≤ C * z ^ (2 * q) := by
  sorry

/-- **Gap 19.6.** Weighted Fourier projection tail estimate in periodic
Sobolev coefficient norms. -/
theorem fourier_tail_sobolev_sq_le (c : ℤ → ℂ) {m μ : ℝ} (hμ : 0 ≤ μ) (hm : μ ≤ m)
    (h : Summable fun k : ℤ ↦ (1 + (k : ℝ) ^ 2) ^ m * ‖c k‖ ^ 2)
    {N : ℕ} (hN : 0 < N) :
    (∑' k : ℤ, if N < k.natAbs then (1 + (k : ℝ) ^ 2) ^ μ * ‖c k‖ ^ 2 else 0) ≤
      (2 : ℝ) ^ μ * (N : ℝ) ^ (2 * (μ - m)) *
        ∑' k : ℤ, if N < k.natAbs then |(k : ℝ)| ^ (2 * m) * ‖c k‖ ^ 2 else 0 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- the termwise bound on the tail `N < |k|`
  have hterm (k : ℤ) (hk : N < k.natAbs) :
      (1 + (k : ℝ) ^ 2) ^ μ ≤ (2 : ℝ) ^ μ * (N : ℝ) ^ (2 * (μ - m)) * |(k : ℝ)| ^ (2 * m) := by
    have hNk : (N : ℝ) < |(k : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast hk
    have hk1 : 1 ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have hk0 : 0 < |(k : ℝ)| := by linarith only [hk1]
    have hsq : (k : ℝ) ^ 2 = |(k : ℝ)| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs]
    calc
      (1 + (k : ℝ) ^ 2) ^ μ ≤ (2 * |(k : ℝ)| ^ (2 : ℝ)) ^ μ := by
        refine Real.rpow_le_rpow (by positivity) ?_ hμ
        rw [← hsq]
        nlinarith only [hk1, sq_abs (k : ℝ)]
      _ = (2 : ℝ) ^ μ * (|(k : ℝ)| ^ (2 * (μ - m)) * |(k : ℝ)| ^ (2 * m)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hk0.le,
          ← Real.rpow_add hk0]
        ring_nf
      _ ≤ (2 : ℝ) ^ μ * ((N : ℝ) ^ (2 * (μ - m)) * |(k : ℝ)| ^ (2 * m)) := by
        have hz : 2 * (μ - m) ≤ 0 := by linarith only [hm]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hN' hNk.le hz) (by positivity)) (by positivity)
      _ = _ := by ring
  -- the right-hand tail is summable by comparison with the Sobolev sum
  have hsum : Summable fun k : ℤ ↦
      if N < k.natAbs then |(k : ℝ)| ^ (2 * m) * ‖c k‖ ^ 2 else 0 := by
    refine h.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) fun k ↦ ?_
    split_ifs
    · gcongr
      rw [Real.rpow_mul (abs_nonneg _), Real.rpow_two, sq_abs]
      exact Real.rpow_le_rpow (sq_nonneg _) (by linarith only) (hμ.trans hm)
    · positivity
  have hsum' := hsum.mul_left ((2 : ℝ) ^ μ * (N : ℝ) ^ (2 * (μ - m)))
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k ↦ ?_)
    (hsum'.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) fun k ↦ ?_) hsum'
  all_goals
    split_ifs with hk
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hterm k hk) (sq_nonneg _)
    · simp

/-- **Gap 19.10.** Uniqueness and existence of the Legendre--Galerkin linear solve
with Dirichlet polynomial trial and test spaces. The load uses nodal interpolation at
arbitrary nodes. For `N ≤ 1` the trial space is `{0}`. -/
theorem existsUnique_legendreGalerkin {N : ℕ}
    (x : Fin (N + 1) → ℝ) (f : ℝ → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    ∃! U : ℝ[X], U.natDegree ≤ N ∧ U.eval (-1) = 0 ∧ U.eval 1 = 0 ∧
      ∀ v : ℝ[X], v.natDegree ≤ N → v.eval (-1) = 0 → v.eval 1 = 0 →
        (∫ t in (-1 : ℝ)..1, U.derivative.eval t * v.derivative.eval t +
          α * U.eval t * v.eval t) =
          ∫ t in (-1 : ℝ)..1, (Lagrange.interpolate Finset.univ x (f ∘ x)).eval t * v.eval t := by
  sorry

/-- The Legendre polynomial `P_n` on `[-1, 1]`, normalized by `P_n(1) = 1`. It is Mathlib's
shifted Legendre polynomial after the affine change of variable: `P_n(x) = P̃_n((1 - x) / 2)`. -/
def legendre (n : ℕ) : ℝ[X] :=
  ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X))

/-- The defining formula of `NASC.legendre`. -/
theorem legendre_def (n : ℕ) :
    legendre n = ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X)) :=
  (rfl)

/-- **Gap 19.10.** The Legendre--Galerkin error in the `H¹` norm for twice smooth solution
and forcing, using the weighted second derivative norms and interpolation at the
Gauss--Lobatto nodes (the endpoints and the critical points of `legendre N`). -/
theorem exists_legendreGalerkin_sobolev_error_bound {α : ℝ} (hα : 0 ≤ α) :
    ∃ C₀ ≥ (0 : ℝ), ∀ (N : ℕ), 2 ≤ N →
      ∀ (x : Fin (N + 1) → ℝ), StrictMono x → x 0 = -1 → x (Fin.last N) = 1 →
      (∀ i : Fin (N + 1), i ≠ 0 → i ≠ Fin.last N →
        (legendre N).derivative.eval (x i) = 0) →
      ∀ (u f : ℝ → ℝ), ContDiff ℝ 2 u → ContDiff ℝ 2 f → u (-1) = 0 → u 1 = 0 →
      (∀ t ∈ Icc (-1 : ℝ) 1, -iteratedDeriv 2 u t + α * u t = f t) →
      ∀ U : ℝ[X], U.natDegree ≤ N → U.eval (-1) = 0 → U.eval 1 = 0 →
      (∀ v : ℝ[X], v.natDegree ≤ N → v.eval (-1) = 0 → v.eval 1 = 0 →
        (∫ t in (-1 : ℝ)..1, U.derivative.eval t * v.derivative.eval t +
          α * U.eval t * v.eval t) =
          ∫ t in (-1 : ℝ)..1, (Lagrange.interpolate Finset.univ x (f ∘ x)).eval t * v.eval t) →
      let w := fun g : ℝ → ℝ ↦ Real.sqrt (∫ t in (-1 : ℝ)..1, (1 - t ^ 2) * iteratedDeriv 2 g t ^ 2)
      Real.sqrt (∫ t in (-1 : ℝ)..1, (u t - U.eval t) ^ 2 +
        (deriv u t - U.derivative.eval t) ^ 2) ≤
        C₀ / Real.sqrt N * (w u / Real.sqrt (N + 2) + w f / ((N + 2) * Real.sqrt (N + 2))) := by
  sorry

end NASC
