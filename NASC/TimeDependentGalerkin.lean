module

public import NASC.Galerkin
public import NASC.Quadrature
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Parabolic and spectral Galerkin methods

Ritz projection defects, time discretization, smoothing for nonsmooth initial data,
discontinuous Galerkin time stepping, and Fourier and polynomial projection.
-/

public section

noncomputable section

namespace NASC

open Set Filter MeasureTheory Polynomial
open scoped BigOperators Topology Interval

/-- **Gap 19.2.** Semidiscrete Galerkin error from the Ritz defect, its time
derivative, and the initial data error. The discrete error equation is written in
the pivot Hilbert norm after projection. -/
theorem ritz_parabolic_error_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u uh Ru : ℝ → H) (A : H →L[ℝ] H) (hpos : ∀ v, 0 ≤ inner ℝ (A v) v)
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → H) (hf : Continuous f)
    (heq : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s ↦ uh s - Ru s) (f t - A (uh t - Ru t)) (Icc 0 T) t) :
    ‖uh T - u T‖ ≤ ‖uh 0 - u 0‖ + ‖Ru 0 - u 0‖ + ‖Ru T - u T‖ +
      ∫ t in (0 : ℝ)..T, ‖f t‖ := by
  sorry

/-- **Gap 19.3.** Backward Euler and Crank--Nicolson accumulate at most
the summed local defect when the stiffness operator is positive. -/
theorem parabolic_timeStepping_error_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hpos : ∀ v, 0 ≤ inner ℝ (A v) v)
    {τ θ δ : ℝ} (hτ : 0 < τ) (hθ : θ = 1 ∨ θ = 1 / 2) (hδ : 0 ≤ δ)
    (u U g : ℕ → H)
    (hU : ∀ n, U (n + 1) - U n + τ • A (θ • U (n + 1) + (1 - θ) • U n) = τ • g n)
    (hu : ∀ n, ‖u (n + 1) - u n + τ • A (θ • u (n + 1) + (1 - θ) • u n) - τ • g n‖ ≤ δ)
    (n : ℕ) :
    ‖U n - u n‖ ≤ ‖U 0 - u 0‖ + n * δ := by
  sorry

/-- **Gap 19.4.** For positive self-adjoint heat semigroups the inverse operator
error gives a positive-time smoothing bound, even for arbitrary pivot data. -/
theorem exists_parabolic_smoothing_constant :
    ∃ C ≥ (0 : ℝ), ∀ (n m : ℕ)
      (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (Ah : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (J : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
      (∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) →
      (∀ v w, inner ℝ (Ah v) w = inner ℝ v (Ah w)) →
      (∀ v, 0 ≤ inner ℝ (A v) v) → (∀ v, 0 ≤ inner ℝ (Ah v) v) →
      ∀ t > (0 : ℝ),
        let a := (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        let ah := (Ah : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        let j := J.toContinuousLinearMap
        ‖j ∘L NormedSpace.exp ((-t) • ah) ∘L j.adjoint - NormedSpace.exp ((-t) • a)‖ ≤
          C / t * ‖(A.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) -
            j ∘L (Ah.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) ∘L
              j.adjoint‖ := by
  sorry

/-- One discontinuous-Galerkin time step of degree less than $q$ for the scalar
test equation, scaled to the unit interval. The initial right limit can jump. -/
def IsDGHeatStep (q : ℕ) (z : ℝ) (U : ℝ[X]) : Prop :=
  U.natDegree < q ∧
    ∀ p : ℝ[X], p.natDegree < q →
      (∫ t in (0 : ℝ)..1, (U.derivative.eval t + z * U.eval t) * p.eval t) +
        (U.eval 0 - 1) * p.eval 0 = 0

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
  sorry

/-- **Gap 19.10.** Uniqueness and existence of the Legendre--Galerkin linear solve
with Dirichlet polynomial trial and test spaces. The load uses nodal interpolation. -/
theorem existsUnique_legendreGalerkin {N : ℕ} (hN : 2 ≤ N)
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x) (f : ℝ → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    ∃! U : ℝ[X], U.natDegree ≤ N ∧ U.eval (-1) = 0 ∧ U.eval 1 = 0 ∧
      ∀ v : ℝ[X], v.natDegree ≤ N → v.eval (-1) = 0 → v.eval 1 = 0 →
        (∫ t in (-1 : ℝ)..1, U.derivative.eval t * v.derivative.eval t +
          α * U.eval t * v.eval t) =
          ∫ t in (-1 : ℝ)..1, (Lagrange.interpolate Finset.univ x (f ∘ x)).eval t * v.eval t := by
  sorry

/-- Legendre polynomial built by Rodrigues' formula. -/
def rodriguesLegendre (n : ℕ) : ℝ[X] :=
  C ((2 ^ n * n.factorial : ℝ)⁻¹) * (Polynomial.derivative^[n] ((X ^ 2 - 1) ^ n))

/-- **Gap 19.10.** The Legendre--Galerkin derivative error for twice smooth solution
and forcing, using the weighted second derivative norms and Lobatto interpolation. -/
theorem exists_legendreGalerkin_H1_error_bound {α : ℝ} (hα : 0 ≤ α) :
    ∃ C₀ ≥ (0 : ℝ), ∀ (N : ℕ), 2 ≤ N →
      ∀ (x : Fin (N + 1) → ℝ), StrictMono x → x 0 = -1 → x (Fin.last N) = 1 →
      (∀ i : Fin (N + 1), i ≠ 0 → i ≠ Fin.last N →
        (rodriguesLegendre N).derivative.eval (x i) = 0) →
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
