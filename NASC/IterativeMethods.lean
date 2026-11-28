module

public import NASC.EigenvalueMethods

import NASC.Support.LinearAlgebra

/-!
# Iterative methods for linear systems

Stationary affine iterations and matrix splittings, M-matrices, weakly regular and regular
splittings, the Stein–Rosenberg theorem, SOR (Ostrowski–Reich) and Jacobi in the energy norm,
Chebyshev semi-iteration, conjugate gradients with and without preconditioning, and GMRES.
Convergence of Krylov methods is formulated in exact arithmetic. Gap numbers refer to section 5
of `GAPS.md`. The stationary iteration criterion uses Mathlib's Gelfand formula and geometric
bound on powers.

## Notation

* Matrix norms are the Euclidean operator norms of the scoped instance
  `Matrix.Norms.L2Operator`; positive definiteness of complex matrices uses `ComplexOrder`.
* The spectral radius of a real matrix is taken after extension of scalars to `ℂ`
  (`realMatrixSpectralRadius`).

## Main definitions

* `realMatrixSpectralRadius`, `energyNorm`, `IsConjugateGradient`, `IsGMRESIterate`.

## Main results

* `iterate_affine_sub_eq`, `tendsto_iterate_affine_iff_spectralRadius_lt_one`,
  `splittingIteration_converges_iff`: convergence of stationary iterations.
* `inverse_nonneg_iff_exists_smul_one_sub` (M-matrices),
  `inverse_nonneg_iff_spectralRadius_lt_one`, `spectralRadius_regularSplitting_eq`.
* `stein_rosenberg`, `spectralRadius_sor_lt_one_iff` (Ostrowski–Reich),
  `spectralRadius_pointSOR_lt_one_iff`, `spectralRadius_blockSOR_lt_one_iff`,
  `spectralRadius_jacobi_eq_energyNorm`.
* `isLeast_chebyshevSemiIteration`.
* `IsConjugateGradient.energyNorm_sub_le`, `IsConjugateGradient.eq_of_ambient_dimension`,
  `IsConjugateGradient.energyNorm_error_le`.
* `IsGMRESIterate.isLeast_residual_polynomial`, `exists_isGMRESIterate_norm_residual_eq`
  (Greenbaum–Pták–Strakoš), `IsGMRESIterate.norm_residual_le_of_fieldOfValues` (Elman).
-/

public section

noncomputable section

namespace NASC

open scoped Matrix Matrix.Norms.L2Operator ENNReal InnerProductSpace ComplexOrder
open Filter Matrix Polynomial

/-- **Gap 5.1.** The affine iteration `y ↦ G y + (x - G x)` with fixed point `x` has the error
`G ^ k (y - x)` after `k` steps. -/
theorem iterate_affine_sub_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    (fun y ↦ G.toEuclideanLin y + (x - G.toEuclideanLin x))^[k] y - x =
      (G ^ k).toEuclideanLin (y - x) := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, Matrix.toLpLin_one,
      LinearMap.id_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      ← ih, map_sub]
    abel

/-- **Gap 5.1.** The affine iteration `y ↦ G y + (x - G x)` converges to its fixed point `x`
from every starting vector exactly when `G` has spectral radius below one. -/
theorem tendsto_iterate_affine_iff_spectralRadius_lt_one {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    (∀ y, Tendsto (fun k ↦ (fun y ↦ G.toEuclideanLin y + (x - G.toEuclideanLin x))^[k] y)
      atTop (nhds x)) ↔ spectralRadius ℂ G < 1 := by
  let T := fun y ↦ G.toEuclideanLin y + (x - G.toEuclideanLin x)
  let L := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hL (A : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℂ (Fin n)) :
      A.toEuclideanLin y = L A y := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]
  have herr (y : EuclideanSpace ℂ (Fin n)) (k : ℕ) : T^[k] y - x = L (G ^ k) (y - x) :=
    (iterate_affine_sub_eq G x y k).trans (hL _ _)
  rw [← tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one]
  constructor
  · intro h
    refine tendsto_matrix_zero_of_tendsto_toEuclideanLin_single fun j ↦ ?_
    let v := EuclideanSpace.single (𝕜 := ℂ) j 1
    have he : Tendsto (fun k ↦ T^[k] (v + x) - x) atTop (nhds 0) := by
      simpa only [sub_self] using (h (v + x)).sub_const x
    refine he.congr fun k ↦ ?_
    rw [herr, add_sub_cancel_right, hL]
  · intro h y
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp h
    have hlim : Tendsto (fun k ↦ ‖G ^ k‖ * ‖y - x‖) atTop (nhds 0) := by
      simpa only [zero_mul] using hn.mul_const ‖y - x‖
    have hp : Tendsto (fun k ↦ L (G ^ k) (y - x)) atTop (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ ↦ norm_nonneg _) (fun k ↦ by
          simpa only [L, Matrix.l2_opNorm_toEuclideanCLM] using (L (G ^ k)).le_opNorm (y - x))
    have ht := (hp.congr fun k ↦ (herr y k).symm).add_const x
    simpa only [sub_add_cancel, zero_add] using ht

/-- **Gap 5.1.** A splitting iteration has the power error formula and converges from
every starting vector exactly when the iteration matrix has spectral radius below one. -/
theorem splittingIteration_converges_iff {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) ℂ)ˣ) (N : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    let G := (↑M⁻¹ : Matrix (Fin n) (Fin n) ℂ) * N
    let T := fun y ↦ G.toEuclideanLin y + (x - G.toEuclideanLin x)
    (∀ y k, T^[k] y - x = (G ^ k).toEuclideanLin (y - x)) ∧
      ((∀ y, Tendsto (fun k ↦ T^[k] y) atTop (nhds x)) ↔ spectralRadius ℂ G < 1) :=
  ⟨iterate_affine_sub_eq _ x, tendsto_iterate_affine_iff_spectralRadius_lt_one _ x⟩

/-- Spectral radius of a real matrix computed after extending scalars to the complex field. -/
def realMatrixSpectralRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (A.map Complex.ofReal)

/-- The spectral radius of a real matrix is that of its complexification. -/
theorem realMatrixSpectralRadius_def {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixSpectralRadius A = spectralRadius ℂ (A.map Complex.ofReal) := (rfl)

/-- **Gap 5.4.** A real matrix with nonpositive off-diagonal entries is a nonsingular
M-matrix exactly when it has a positive scalar shift representation. -/
theorem inverse_nonneg_iff_exists_smul_one_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) :
    (A.det ≠ 0 ∧ ∀ i j, 0 ≤ A⁻¹ i j) ↔
      ∃ (s : ℝ) (B : Matrix (Fin n) (Fin n) ℝ), 0 < s ∧
        (∀ i j, 0 ≤ B i j) ∧ A = s • 1 - B ∧ realMatrixSpectralRadius B < ENNReal.ofReal s := by
  sorry

/-- **Gap 5.5.** For a weakly regular splitting, inverse positivity is equivalent to
convergence of the stationary iteration. -/
theorem inverse_nonneg_iff_spectralRadius_lt_one {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (hMinv : ∀ i j, 0 ≤ M⁻¹ i j) (hN : ∀ i j, 0 ≤ (M⁻¹ * N) i j) :
    ((M - N).det ≠ 0 ∧ ∀ i j, 0 ≤ (M - N)⁻¹ i j) ↔
      realMatrixSpectralRadius (M⁻¹ * N) < 1 := by
  sorry

/-- **Gap 5.5.** The spectral radius of a regular splitting expressed using
the nonnegative matrix of exact correction coefficients. -/
theorem spectralRadius_regularSplitting_eq {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) (hA : (M - N).det ≠ 0)
    (hMinv : ∀ i j, 0 ≤ M⁻¹ i j) (hAinv : ∀ i j, 0 ≤ (M - N)⁻¹ i j)
    (hN : ∀ i j, 0 ≤ N i j) :
    let ρ := realMatrixSpectralRadius ((M - N)⁻¹ * N)
    realMatrixSpectralRadius (M⁻¹ * N) = ρ / (1 + ρ) := by
  sorry

/-- **Gap 5.7.** Stein--Rosenberg comparison of the Jacobi and Gauss--Seidel radii. -/
theorem stein_rosenberg {n : ℕ} {L U : Matrix (Fin n) (Fin n) ℝ}
    (hL : ∀ i j, i ≤ j → L i j = 0) (hU : ∀ i j, j ≤ i → U i j = 0)
    (hB : ∀ i j, 0 ≤ (L + U) i j) :
    let ρJ := realMatrixSpectralRadius (L + U)
    let ρGS := realMatrixSpectralRadius ((1 - L)⁻¹ * U)
    (ρGS = 0 ∧ ρJ = 0) ∨ (0 < ρGS ∧ ρGS < ρJ ∧ ρJ < 1) ∨
      (ρGS = 1 ∧ ρJ = 1) ∨ (1 < ρJ ∧ ρJ < ρGS) := by
  sorry

/-- **Gap 5.9.** Ostrowski--Reich criterion at a relaxation parameter for which the
splitting is defined. -/
theorem spectralRadius_sor_lt_one_iff {n : ℕ}
    (D E : Matrix (Fin n) (Fin n) ℂ) {ω : ℝ} (hD : D.PosDef) (hω : 0 < ω) (hω' : ω < 2)
    (hM : (D - (ω : ℂ) • E).det ≠ 0) :
    spectralRadius ℂ ((D - (ω : ℂ) • E)⁻¹ * ((ω : ℂ) • Eᴴ + ((1 - ω : ℝ) : ℂ) • D)) <
      1 ↔ (D - E - Eᴴ).PosDef := by
  sorry

/-- **Gap 5.9.** For the point SOR splitting of a positive definite matrix, the exact
convergence interval is between zero and two. -/
theorem spectralRadius_pointSOR_lt_one_iff {n : ℕ} [NeZero n]
    (d : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ) (ω : ℝ)
    (hE : ∀ i j, i ≤ j → E i j = 0) (hA : (Matrix.diagonal d - E - Eᴴ).PosDef) :
    spectralRadius ℂ ((Matrix.diagonal d - (ω : ℂ) • E)⁻¹ *
      ((ω : ℂ) • Eᴴ + ((1 - ω : ℝ) : ℂ) • Matrix.diagonal d)) < 1 ↔
      0 < ω ∧ ω < 2 := by
  sorry

/-- **Gap 5.9.** Block SOR has the same exact relaxation interval as point SOR.
The map `block` orders the blocks, and need not order the indices within each block. -/
theorem spectralRadius_blockSOR_lt_one_iff {n m : ℕ} [NeZero n]
    (block : Fin n → Fin m) (D E : Matrix (Fin n) (Fin n) ℂ) (ω : ℝ)
    (hD : ∀ i j, block i ≠ block j → D i j = 0)
    (hE : ∀ i j, block i ≤ block j → E i j = 0) (hA : (D - E - Eᴴ).PosDef) :
    spectralRadius ℂ ((D - (ω : ℂ) • E)⁻¹ * ((ω : ℂ) • Eᴴ + ((1 - ω : ℝ) : ℂ) • D)) <
      1 ↔ 0 < ω ∧ ω < 2 := by
  sorry

/-- **Gap 5.11.** The rescaled Chebyshev polynomial attains the semi-iteration minimax
budget on a spectral interval `[a, b]` that does not contain `1`, on either side of it. -/
theorem isLeast_chebyshevSemiIteration {a b : ℝ} (hab : a < b) (h₁ : 1 ∉ Set.Icc a b)
    (m : ℕ) :
    IsLeast {t : ℝ | ∃ p : ℝ[X], p.natDegree ≤ m ∧ p.eval 1 = 1 ∧
      t = sSup ((fun x ↦ |p.eval x|) '' Set.Icc a b)}
      (1 / |(Polynomial.Chebyshev.T ℝ m).eval ((2 - a - b) / (b - a))|) := by
  sorry

/-- Energy length `√(re ⟪x, A x⟫)` induced by a positive definite self-adjoint endomorphism.
For an indefinite `A` it is the junk value `0` wherever `re ⟪x, A x⟫ < 0`. -/
def energyNorm {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : H →ₗ[𝕜] H) (x : H) : ℝ :=
  Real.sqrt (RCLike.re ⟪x, A x⟫_𝕜)

/-- The energy norm is the square root of the real part of `⟪x, A x⟫`. -/
theorem energyNorm_def {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (A : H →ₗ[𝕜] H) (x : H) :
    energyNorm A x = Real.sqrt (RCLike.re ⟪x, A x⟫_𝕜) := (rfl)

/-- **Gap 5.9.** When both the matrix and the reflected diagonal splitting are positive
definite, the Jacobi spectral radius equals the induced energy norm and is below one. -/
theorem spectralRadius_jacobi_eq_energyNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (hD : ((2 : ℂ) • Matrix.diagonal A.diag - A).PosDef) :
    let B := 1 - (Matrix.diagonal A.diag)⁻¹ * A
    let s := spectralRadius ℂ B
    s < 1 ∧ s.toReal = sSup (Set.range fun x : EuclideanSpace ℂ (Fin n) ↦
      energyNorm A.toEuclideanLin (B.toEuclideanLin x) / energyNorm A.toEuclideanLin x) := by
  sorry

/-- The exact preconditioned CG recurrence. Identity preconditioning gives ordinary CG.
After termination the residual is zero and the solution iterate is held fixed. -/
def IsConjugateGradient {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (A C : H →ₗ[𝕜] H) (b x₀ : H) (x r p : ℕ → H) : Prop :=
  x 0 = x₀ ∧ r 0 = b - A x₀ ∧ p 0 = C (r 0) ∧ ∀ k,
    (r k = 0 → x (k + 1) = x k ∧ r (k + 1) = 0 ∧ p (k + 1) = 0) ∧
    (r k ≠ 0 →
      let a := ⟪r k, C (r k)⟫_𝕜 / ⟪p k, A (p k)⟫_𝕜
      let β := ⟪r (k + 1), C (r (k + 1))⟫_𝕜 / ⟪r k, C (r k)⟫_𝕜
      x (k + 1) = x k + a • p k ∧ r (k + 1) = r k - a • A (p k) ∧
        p (k + 1) = C (r (k + 1)) + β • p k)

/-- The preconditioned CG recurrence: initial residual and direction, a frozen state after a
zero residual, and otherwise the step, residual and direction updates. -/
theorem isConjugateGradient_iff {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {A C : H →ₗ[𝕜] H} {b x₀ : H} {x r p : ℕ → H} :
    IsConjugateGradient A C b x₀ x r p ↔
      x 0 = x₀ ∧ r 0 = b - A x₀ ∧ p 0 = C (r 0) ∧ ∀ k,
        (r k = 0 → x (k + 1) = x k ∧ r (k + 1) = 0 ∧ p (k + 1) = 0) ∧
        (r k ≠ 0 →
          x (k + 1) = x k + (⟪r k, C (r k)⟫_𝕜 / ⟪p k, A (p k)⟫_𝕜) • p k ∧
          r (k + 1) = r k - (⟪r k, C (r k)⟫_𝕜 / ⟪p k, A (p k)⟫_𝕜) • A (p k) ∧
          p (k + 1) = C (r (k + 1)) +
            (⟪r (k + 1), C (r (k + 1))⟫_𝕜 / ⟪r k, C (r k)⟫_𝕜) • p k) := Iff.rfl

/-- **Gap 5.12.** The CG iterates have the true residual, lie in the affine Krylov space and
minimize the energy norm of the error there. -/
theorem IsConjugateGradient.energyNorm_sub_le {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜)
    (hA : A.IsHermitian) (hpos : ∀ x : EuclideanSpace 𝕜 (Fin n), x ≠ 0 →
      0 < RCLike.re ⟪x, A.toEuclideanLin x⟫_𝕜)
    {b x₀ sol : EuclideanSpace 𝕜 (Fin n)} {x r p : ℕ → EuclideanSpace 𝕜 (Fin n)}
    (hsol : A.toEuclideanLin sol = b)
    (h : IsConjugateGradient A.toEuclideanLin LinearMap.id b x₀ x r p) (k : ℕ) :
    r k = b - A.toEuclideanLin (x k) ∧
      x k - x₀ ∈ krylovSubmodule A.toEuclideanLin (r 0) k ∧
      ∀ y, y - x₀ ∈ krylovSubmodule A.toEuclideanLin (r 0) k →
        energyNorm A.toEuclideanLin (x k - sol) ≤ energyNorm A.toEuclideanLin (y - sol) := by
  sorry

/-- **Gap 5.12.** Exact CG terminates with the solution by the ambient dimension. -/
theorem IsConjugateGradient.eq_of_ambient_dimension {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜)
    (hA : A.IsHermitian) (hpos : ∀ x : EuclideanSpace 𝕜 (Fin n), x ≠ 0 →
      0 < RCLike.re ⟪x, A.toEuclideanLin x⟫_𝕜)
    {b x₀ sol : EuclideanSpace 𝕜 (Fin n)} {x r p : ℕ → EuclideanSpace 𝕜 (Fin n)}
    (hsol : A.toEuclideanLin sol = b)
    (h : IsConjugateGradient A.toEuclideanLin LinearMap.id b x₀ x r p) :
    x n = sol := by
  sorry

/-- **Gaps 5.13 and 5.17.** Condition-number bound for preconditioned CG in the
original energy norm. Take the preconditioner to be the identity for ordinary CG. -/
theorem IsConjugateGradient.energyNorm_error_le {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A M : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hM : M.IsHermitian)
    (hMpos : ∀ v : EuclideanSpace 𝕜 (Fin n), v ≠ 0 → 0 < RCLike.re ⟪v, M.toEuclideanLin v⟫_𝕜)
    {γ Γ : ℝ} (hγ : 0 < γ) (hΓ : γ ≤ Γ)
    (hbound : ∀ v : EuclideanSpace 𝕜 (Fin n),
      γ * RCLike.re ⟪v, M.toEuclideanLin v⟫_𝕜 ≤ RCLike.re ⟪v, A.toEuclideanLin v⟫_𝕜 ∧
      RCLike.re ⟪v, A.toEuclideanLin v⟫_𝕜 ≤ Γ * RCLike.re ⟪v, M.toEuclideanLin v⟫_𝕜)
    {b x₀ sol : EuclideanSpace 𝕜 (Fin n)} {x r p : ℕ → EuclideanSpace 𝕜 (Fin n)}
    (hsol : A.toEuclideanLin sol = b)
    (h : IsConjugateGradient A.toEuclideanLin (M⁻¹).toEuclideanLin b x₀ x r p) (k : ℕ) :
    let q := (Real.sqrt (Γ / γ) - 1) / (Real.sqrt (Γ / γ) + 1)
    energyNorm A.toEuclideanLin (x k - sol) ≤
      (2 * q ^ k / (1 + q ^ (2 * k))) * energyNorm A.toEuclideanLin (x₀ - sol) := by
  sorry

/-- A GMRES iterate is a residual minimizer in its affine Krylov space. -/
def IsGMRESIterate {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (A : H →ₗ[𝕜] H) (b x₀ : H) (k : ℕ) (x : H) : Prop :=
  let K := krylovSubmodule A (b - A x₀) k
  x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖

/-- A GMRES iterate lies in the affine Krylov space and minimizes the residual norm there. -/
theorem isGMRESIterate_iff {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {A : H →ₗ[𝕜] H} {b x₀ : H} {k : ℕ} {x : H} :
    IsGMRESIterate A b x₀ k x ↔ x - x₀ ∈ krylovSubmodule A (b - A x₀) k ∧
      ∀ y, y - x₀ ∈ krylovSubmodule A (b - A x₀) k → ‖b - A x‖ ≤ ‖b - A y‖ := Iff.rfl

/-- **Gap 5.14.** GMRES residual minimization is equivalently a normalized polynomial
minimization. -/
theorem IsGMRESIterate.isLeast_residual_polynomial {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {A : H →ₗ[𝕜] H}
    {b x₀ x : H} {k : ℕ} (h : IsGMRESIterate A b x₀ k x) :
    IsLeast {t : ℝ | ∃ p : 𝕜[X], p.natDegree ≤ k ∧ p.eval 0 = 1 ∧
      t = ‖(Polynomial.aeval A p) (b - A x₀)‖} ‖b - A x‖ := by
  sorry

/-- **Gap 5.15.** Every positive nonincreasing residual curve can occur with any
prescribed nonzero characteristic roots. -/
theorem exists_isGMRESIterate_norm_residual_eq {n : ℕ} (f : Fin (n + 1) → ℝ)
    (eigs : Fin (n + 1) → ℂ) (hf : Antitone f) (hpos : ∀ k, 0 < f k) (he : ∀ j, eigs j ≠ 0) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (b : EuclideanSpace ℂ (Fin (n + 1)))
      (x : ℕ → EuclideanSpace ℂ (Fin (n + 1))),
      A.charpoly.roots = Multiset.ofList (List.ofFn eigs) ∧
        (∀ k, IsGMRESIterate A.toEuclideanLin b 0 k (x k)) ∧
        (∀ k : Fin (n + 1), ‖b - A.toEuclideanLin (x k.val)‖ = f k) ∧
        A.toEuclideanLin (x (n + 1)) = b := by
  sorry

/-- **Gap 5.18.** A uniform positive lower bound on the modulus of the field of values
yields the geometric GMRES residual factor. -/
theorem IsGMRESIterate.norm_residual_le_of_fieldOfValues {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {ν : ℝ} (hν : 0 < ν)
    (hfield : ∀ v : EuclideanSpace ℂ (Fin (n + 1)), ‖v‖ = 1 →
      ν ≤ ‖⟪v, A.toEuclideanLin v⟫_ℂ‖)
    {b x₀ x : EuclideanSpace ℂ (Fin (n + 1))} {k : ℕ}
    (h : IsGMRESIterate A.toEuclideanLin b x₀ k x) :
    A.det ≠ 0 ∧ ‖b - A.toEuclideanLin x‖ ≤
      (Real.sqrt (1 - ν ^ 2 / ‖A‖ ^ 2)) ^ k * ‖b - A.toEuclideanLin x₀‖ := by
  sorry

end NASC
