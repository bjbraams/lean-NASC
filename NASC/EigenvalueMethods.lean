module

public import NASC.Conditioning
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs
public import Mathlib.RingTheory.Polynomial.Chebyshev

import NASC.Support.LinearAlgebra

/-!
# Eigenvalue and singular value computations

Schur and singular value factorizations, power and Rayleigh quotient iterations, the QR
algorithm, Hessenberg reduction and shifted QR steps, backward error of unitary reductions,
Arnoldi and Lanczos (Kaniel–Paige–Saad), Golub–Kahan bidiagonalization, Keldysh's theorem and
block companion linearizations of matrix polynomials. Gap numbers refer to section 4 of
`GAPS.md`.

## Notation

* Matrix norms are the Euclidean operator norms of the scoped instance
  `Matrix.Norms.L2Operator`.
* `hA.eigenvalues₀` lists the eigenvalues of a Hermitian matrix in decreasing order, from zero.

## Main definitions

* `powerStep`, `IsQRIteration`, `accumulatedQ`, `accumulatedR`, `IsUnreducedHessenberg`,
  `krylovSubmodule`, `blockCompanionPencil`.

## Main results

* `exists_schur_of_roots`, `exists_unitary_conjTranspose_mul_eq_singularValueDiagonal`.
* `exists_phase_norm_powerStep_iterate_sub_le` (power method),
  `exists_norm_rayleighQuotientStep_sub_le_cube` (Rayleigh quotient iteration).
* `IsQRIteration.eq_conjTranspose_mul_mul`, `IsQRIteration.pow_eq_mul_accumulatedR`,
  `IsQRIteration.exists_tendsto_conjTranspose_mul`: the QR algorithm.
* `exists_unitary_conjTranspose_mul_upperHessenberg`, `IsUnreducedHessenberg.shifted_qr_step`.
* `norm_conjTranspose_mul_sub_le_of_reductions`, `exists_arnoldiFrame`, `kaniel_paige_saad`,
  `exists_unitary_conjTranspose_mul_bidiagonal`.
* `exists_analyticOnNhd_sub_inv_pole_of_simple_eigenvalue` (Keldysh),
  `det_blockCompanionPencil`, `blockCompanionPencil_mulVec_eq_zero_iff`.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open Filter Matrix

/-- **Gap 4.1.** Schur triangularization with the characteristic roots in the supplied order. -/
theorem exists_schur_of_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (eigs : Fin n → ℂ) (h : Multiset.ofList (List.ofFn eigs) = A.charpoly.roots) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) ∧
      (Uᴴ * A * U).IsUpperTriangular ∧ ∀ i, (Uᴴ * A * U) i i = eigs i := by
  sorry

/-- **Gap 4.3.** Full singular-value decomposition over the real or complex field. -/
theorem exists_unitary_conjTranspose_mul_eq_singularValueDiagonal
    {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ (U : Matrix (Fin m) (Fin m) 𝕜) (V : Matrix (Fin n) (Fin n) 𝕜),
      U ∈ unitary (Matrix (Fin m) (Fin m) 𝕜) ∧ V ∈ unitary (Matrix (Fin n) (Fin n) 𝕜) ∧
      Uᴴ * A * V = singularValueDiagonal A := by
  sorry

/-- Normalize the new vector in one power iteration. When `A x = 0` the step returns `0`. -/
def powerStep {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →ₗ[𝕜] E) (x : E) : E :=
  ((‖A x‖⁻¹ : ℝ) : 𝕜) • A x

/-- A power step scales `A x` by the inverse of its norm. -/
theorem powerStep_def {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →ₗ[𝕜] E) (x : E) : powerStep A x = ((‖A x‖⁻¹ : ℝ) : 𝕜) • A x := (rfl)

/-- **Gap 4.4.** The normalized power method converges up to a unit phase to a dominant unit
eigenvector, at a rate fixed by the spectral ratio. The space is any normed space with an
eigenbasis indexed by a finite type. -/
theorem exists_phase_norm_powerStep_iterate_sub_le {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι] (A : E →ₗ[𝕜] E)
    (B : Module.Basis ι 𝕜 E) (i₀ : ι) (eigs : ι → 𝕜) (v : E) {q : ℝ}
    (hB : ∀ i, A (B i) = eigs i • B i) (hunit : ‖B i₀‖ = 1) (hv : ‖v‖ = 1)
    (hcoord : B.repr v i₀ ≠ 0) (h₀ : eigs i₀ ≠ 0) (hq : 0 ≤ q) (hq' : q < 1)
    (hgap : ∀ i ≠ i₀, ‖eigs i‖ ≤ q * ‖eigs i₀‖) :
    ∃ C ≥ (0 : ℝ), ∀ k, ∃ phase : 𝕜, ‖phase‖ = 1 ∧
      ‖(powerStep A)^[k] v‖ = 1 ∧ ‖phase • (powerStep A)^[k] v - B i₀‖ ≤ C * q ^ k := by
  sorry

/-- **Gap 4.5.** Local cubic error for Rayleigh quotient iteration at a simple real
symmetric eigenpair, whenever the shifted linear solve is nonsingular. -/
theorem exists_norm_rayleighQuotientStep_sub_le_cube {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (e : ℝ) (q : EuclideanSpace ℝ (Fin n)) (hq : ‖q‖ = 1)
    (he : A.toEuclideanLin q = e • q)
    (hsimple : Module.finrank ℝ
      (LinearMap.ker (A.toEuclideanLin - e • LinearMap.id)) = 1) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      ‖v - q‖ ≤ δ →
      let shift := inner ℝ v (A.toEuclideanLin v)
      let M := A - shift • (1 : Matrix (Fin n) (Fin n) ℝ)
      M.det ≠ 0 → ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ‖sign • powerStep (M⁻¹).toEuclideanLin v - q‖ ≤ C * ‖v - q‖ ^ 3 := by
  sorry

/-- An exact unshifted QR iteration, numbered from zero. -/
def IsQRIteration {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B Q R : ℕ → Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  B 0 = A ∧ ∀ k,
    Q k ∈ unitary (Matrix (Fin n) (Fin n) 𝕜) ∧ (R k).IsUpperTriangular ∧
    B k = Q k * R k ∧ B (k + 1) = R k * Q k

/-- An unshifted QR iteration starts at `A` and passes from `B k = Q k R k` to `R k Q k`. -/
theorem isQRIteration_iff {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) 𝕜} {B Q R : ℕ → Matrix (Fin n) (Fin n) 𝕜} :
    IsQRIteration A B Q R ↔ B 0 = A ∧ ∀ k,
      Q k ∈ unitary (Matrix (Fin n) (Fin n) 𝕜) ∧ (R k).IsUpperTriangular ∧
      B k = Q k * R k ∧ B (k + 1) = R k * Q k := Iff.rfl

/-- The accumulated unitary factor `Q₀ Q₁ ⋯ Q_{k-1}` of a QR iteration. -/
def accumulatedQ {M : Type*} [Monoid M] (Q : ℕ → M) : ℕ → M
  | 0 => 1
  | k + 1 => accumulatedQ Q k * Q k

/-- The empty accumulated unitary factor is the identity. -/
@[simp]
theorem accumulatedQ_zero {M : Type*} [Monoid M] (Q : ℕ → M) : accumulatedQ Q 0 = 1 := (rfl)

/-- The accumulated unitary factor multiplies by the next factor on the right. -/
theorem accumulatedQ_succ {M : Type*} [Monoid M] (Q : ℕ → M) (k : ℕ) :
    accumulatedQ Q (k + 1) = accumulatedQ Q k * Q k := (rfl)

/-- The accumulated triangular factor `R_{k-1} ⋯ R₁ R₀` of a QR iteration. -/
def accumulatedR {M : Type*} [Monoid M] (R : ℕ → M) : ℕ → M
  | 0 => 1
  | k + 1 => R k * accumulatedR R k

/-- The empty accumulated triangular factor is the identity. -/
@[simp]
theorem accumulatedR_zero {M : Type*} [Monoid M] (R : ℕ → M) : accumulatedR R 0 = 1 := (rfl)

/-- The accumulated triangular factor multiplies by the next factor on the left. -/
theorem accumulatedR_succ {M : Type*} [Monoid M] (R : ℕ → M) (k : ℕ) :
    accumulatedR R (k + 1) = R k * accumulatedR R k := (rfl)

section IsQRIteration

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
  {B Q R : ℕ → Matrix (Fin n) (Fin n) 𝕜}

/-- **Gap 4.6.** The accumulated unitary factor of a QR iteration is unitary and conjugates
`A` to the current iterate. -/
theorem IsQRIteration.conjTranspose_accumulatedQ_mul_self_and_mul_eq
    (h : IsQRIteration A B Q R) (k : ℕ) :
    (accumulatedQ Q k)ᴴ * accumulatedQ Q k = 1 ∧ A * accumulatedQ Q k = accumulatedQ Q k * B k := by
  induction k with
  | zero => simp only [accumulatedQ_zero, h.1, conjTranspose_one, one_mul, mul_one, and_self]
  | succ k ih =>
    obtain ⟨hQ, -, hk, hnext⟩ := h.2 k
    have hs : (Q k)ᴴ * Q k = 1 := Unitary.star_mul_self_of_mem hQ
    constructor
    · rw [accumulatedQ_succ, conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (accumulatedQ Q k)ᴴ, ih.1, one_mul, hs]
    · rw [accumulatedQ_succ, ← Matrix.mul_assoc, ih.2, hk, hnext]
      simp only [Matrix.mul_assoc]

/-- **Gap 4.6.** Each QR iterate is the unitary conjugate of `A` by the accumulated factor. -/
theorem IsQRIteration.eq_conjTranspose_mul_mul (h : IsQRIteration A B Q R) (k : ℕ) :
    B k = (accumulatedQ Q k)ᴴ * A * accumulatedQ Q k := by
  obtain ⟨h₁, h₂⟩ := h.conjTranspose_accumulatedQ_mul_self_and_mul_eq k
  rw [Matrix.mul_assoc, h₂, ← Matrix.mul_assoc, h₁, one_mul]

/-- **Gap 4.6.** One more QR step: `A P_k = P_{k+1} R_k` for the accumulated factor `P_k`. -/
theorem IsQRIteration.mul_accumulatedQ_eq (h : IsQRIteration A B Q R) (k : ℕ) :
    A * accumulatedQ Q k = accumulatedQ Q (k + 1) * R k := by
  rw [accumulatedQ_succ, Matrix.mul_assoc, ← (h.2 k).2.2.1,
    (h.conjTranspose_accumulatedQ_mul_self_and_mul_eq k).2]

/-- **Gap 4.6.** The accumulated factors give the QR factorization of the powers of `A`. -/
theorem IsQRIteration.pow_eq_mul_accumulatedR (h : IsQRIteration A B Q R) (k : ℕ) :
    A ^ k = accumulatedQ Q k * accumulatedR R k := by
  induction k with
  | zero => simp only [accumulatedQ_zero, accumulatedR_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ', ih, ← Matrix.mul_assoc, h.mul_accumulatedQ_eq, accumulatedR_succ,
      Matrix.mul_assoc]

end IsQRIteration

/-- **Gap 4.7.** Unshifted QR converges, modulo diagonal phases, to the triangular
conjugate of an eigenbasis whose inverse admits elimination without pivoting. -/
theorem IsQRIteration.exists_tendsto_conjTranspose_mul {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {B Q R : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (h : IsQRIteration A B Q R) (X : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (eigs : Fin n → ℂ) (hord : StrictAnti fun i ↦ ‖eigs i‖) (hne : ∀ i, eigs i ≠ 0)
    (hX : A = (X : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal eigs *
      (↑X⁻¹ : Matrix (Fin n) (Fin n) ℂ))
    (hLU' : ∀ (k : ℕ) (hk : k < n),
      (((↑X⁻¹ : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk.le)
        (Fin.castLE hk.le)).det ≠ 0)
    {U T : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (hT : T.IsUpperTriangular) (hQT : U * T = X.val) :
    ∃ phase : ℕ → Fin n → ℂ, (∀ k i, ‖phase k i‖ = 1) ∧
      Tendsto (fun k ↦ (Matrix.diagonal (phase k))ᴴ * B k * Matrix.diagonal (phase k))
        atTop (nhds (T * Matrix.diagonal eigs * T⁻¹)) := by
  sorry

/-- **Gap 4.8.** Householder reduction: every square matrix is unitarily similar to an upper
Hessenberg matrix by a unitary matrix with a prescribed unit first column. For real input the
reduction is orthogonal. The first column is what the implicit-Q theorem fixes. -/
theorem exists_unitary_conjTranspose_mul_upperHessenberg {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (q : EuclideanSpace 𝕜 (Fin (n + 1)))
    (hq : ‖q‖ = 1) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜, Q ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) ∧
      (∀ i, Q i 0 = q i) ∧ (Qᴴ * A * Q).IsUpperHessenberg := by
  sorry

/-- An unreduced upper Hessenberg matrix: upper Hessenberg with nonzero subdiagonal. -/
def IsUnreducedHessenberg {R : Type*} [Zero R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R) : Prop :=
  H.IsUpperHessenberg ∧ ∀ i j : Fin n, i.val = j.val + 1 → H i j ≠ 0

/-- An unreduced Hessenberg matrix vanishes below the subdiagonal and not on it. -/
theorem isUnreducedHessenberg_iff {R : Type*} [Zero R] {n : ℕ} {H : Matrix (Fin n) (Fin n) R} :
    IsUnreducedHessenberg H ↔
      (∀ i j : Fin n, j.val + 1 < i.val → H i j = 0) ∧
        ∀ i j : Fin n, i.val = j.val + 1 → H i j ≠ 0 := by
  rw [IsUnreducedHessenberg, Matrix.isUpperHessenberg_fin_iff]

/-- **Gap 4.8.** A nonsingular shifted QR step is a unitary similarity and preserves the
unreduced Hessenberg form. -/
theorem IsUnreducedHessenberg.shifted_qr_step {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {H Q R : Matrix (Fin n) (Fin n) 𝕜} (shift : 𝕜) (hH : IsUnreducedHessenberg H)
    (hQ : Q ∈ unitary (Matrix (Fin n) (Fin n) 𝕜)) (hR : R.IsUpperTriangular)
    (hQR : H - shift • 1 = Q * R) (hne : R.det ≠ 0) :
    R * Q + shift • 1 = Qᴴ * H * Q ∧ IsUnreducedHessenberg (R * Q + shift • 1) := by
  sorry

/-- **Gap 4.10.** Backward errors for successive unitary reductions add, with the
second error budget scaled by the first perturbed matrix norm. -/
theorem norm_conjTranspose_mul_sub_le_of_reductions {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A H D P Q : Matrix (Fin n) (Fin n) 𝕜} {u a b : ℝ}
    (hP : P ∈ unitary (Matrix (Fin n) (Fin n) 𝕜))
    (hQ : Q ∈ unitary (Matrix (Fin n) (Fin n) 𝕜)) (hbu : 0 ≤ b * u)
    (h₁ : ‖P * H * Pᴴ - A‖ ≤ a * u * ‖A‖) (h₂ : ‖Q * D * Qᴴ - H‖ ≤ b * u * ‖H‖) :
    ‖(P * Q) * D * (P * Q)ᴴ - A‖ ≤ (a + b * (1 + a * u)) * u * ‖A‖ := by
  let E₂ := D - Qᴴ * H * Q
  have hQQ : Q * Qᴴ = 1 := Unitary.mul_star_self_of_mem hQ
  have hQres : Q * E₂ * Qᴴ = Q * D * Qᴴ - H := by
    dsimp only [E₂]
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc Q (Qᴴ * H), ← Matrix.mul_assoc Q Qᴴ,
      hQQ, one_mul, Matrix.mul_assoc H, hQQ, mul_one]
  have h₂' : ‖E₂‖ ≤ b * u * ‖H‖ := by
    rwa [← hQres, l2_opNorm_unitary_mul_mul_conjTranspose hQ] at h₂
  have hH : ‖H‖ ≤ (1 + a * u) * ‖A‖ := by
    calc
      ‖H‖ = ‖P * H * Pᴴ‖ := (l2_opNorm_unitary_mul_mul_conjTranspose hP H).symm
      _ ≤ ‖P * H * Pᴴ - A‖ + ‖A‖ := norm_le_norm_sub_add _ _
      _ ≤ (1 + a * u) * ‖A‖ := by nlinarith only [h₁]
  have hres : (P * Q) * E₂ * (P * Q)ᴴ = P * (Q * D * Qᴴ - H) * Pᴴ := by
    rw [← hQres, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hsplit : (P * Q) * D * (P * Q)ᴴ - A =
      (P * Q) * E₂ * (P * Q)ᴴ + (P * H * Pᴴ - A) := by
    rw [hres]
    simp only [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [sub_add_sub_cancel]
    simp only [Matrix.mul_assoc]
  have hscalar (t : ℝ) : b * u * ((1 + a * u) * t) + a * u * t =
      (a + b * (1 + a * u)) * u * t := by ring
  calc
    ‖(P * Q) * D * (P * Q)ᴴ - A‖
      ≤ ‖(P * Q) * E₂ * (P * Q)ᴴ‖ + ‖P * H * Pᴴ - A‖ := by
        rw [hsplit]
        exact norm_add_le ((P * Q) * E₂ * (P * Q)ᴴ) (P * H * Pᴴ - A)
    _ = ‖E₂‖ + ‖P * H * Pᴴ - A‖ := by
      rw [l2_opNorm_unitary_mul_mul_conjTranspose (mul_mem hP hQ)]
    _ ≤ b * u * ‖H‖ + a * u * ‖A‖ := add_le_add h₂' h₁
    _ ≤ b * u * ((1 + a * u) * ‖A‖) + a * u * ‖A‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hH hbu) le_rfl
    _ = _ := hscalar ‖A‖

/-- The span of the first $k$ iterates of a vector under an endomorphism. -/
def krylovSubmodule {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (b : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun j : Fin k ↦ (A ^ j.val) b)

/-- The Krylov space of order `k` is spanned by `b, A b, …, A ^ (k - 1) b`. -/
theorem krylovSubmodule_def {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (b : E) (k : ℕ) :
    krylovSubmodule A b k = Submodule.span 𝕜 (Set.range fun j : Fin k ↦ (A ^ j.val) b) := (rfl)

/-- The Krylov space of order zero is trivial. -/
@[simp]
theorem krylovSubmodule_zero {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (b : E) : krylovSubmodule A b 0 = ⊥ := by
  rw [krylovSubmodule_def, Set.range_eq_empty, Submodule.span_empty]

/-- Krylov spaces increase with the order. -/
theorem krylovSubmodule_mono {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (b : E) {k l : ℕ} (hkl : k ≤ l) :
    krylovSubmodule A b k ≤ krylovSubmodule A b l := by
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨Fin.castLE hkl j, rfl⟩

/-- **Gap 4.13.** A full-dimensional Krylov space has a prefix-compatible orthonormal
Arnoldi frame whose compressed operator is upper Hessenberg. -/
theorem exists_arnoldiFrame {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (h : Module.finrank 𝕜 (krylovSubmodule A.toEuclideanLin b m) = m) :
    ∃ Q : Matrix (Fin n) (Fin m) 𝕜, Qᴴ * Q = 1 ∧
      (∀ (k : ℕ) (hk : k ≤ m),
        (Q.submatrix id (Fin.castLE hk)).toEuclideanLin.range =
          krylovSubmodule A.toEuclideanLin b k) ∧
      (Qᴴ * A * Q).IsUpperHessenberg := by
  sorry

/-- **Gap 4.14.** Kaniel–Paige–Saad: the upper Ritz value has the Chebyshev lower bound from
the leading spectral separation and the angle of the initial vector. -/
theorem kaniel_paige_saad {n m : ℕ}
    (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (hA : A.IsHermitian)
    (b q : EuclideanSpace ℝ (Fin (n + 3))) (hb : ‖b‖ = 1) (hq : ‖q‖ = 1)
    (hvec : A.toEuclideanLin q = hA.eigenvalues₀ 0 • q)
    (hc : ⟪q, b⟫_ℝ ≠ 0)
    (hgap : hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm (Fin.last (n + 2))) <
      hA.eigenvalues₀ 1)
    (Q : Matrix (Fin (n + 3)) (Fin (m + 1)) ℝ) (hQ : Qᴴ * Q = 1)
    (hK : Q.toEuclideanLin.range = krylovSubmodule A.toEuclideanLin b (m + 1)) :
    let top := hA.eigenvalues₀ 0
    let second := hA.eigenvalues₀ 1
    let bottom := hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm (Fin.last (n + 2)))
    let angle := (1 - ⟪q, b⟫_ℝ ^ 2) / ⟪q, b⟫_ℝ ^ 2
    let t := (Polynomial.Chebyshev.T ℝ m).eval (1 + 2 * (top - second) / (second - bottom))
    let ritz := (isHermitian_conjTranspose_mul_mul Q hA).eigenvalues₀ 0
    top - (top - bottom) * angle / t ^ 2 ≤ ritz ∧ ritz ≤ top := by
  sorry

/-- **Gap 4.16.** Golub–Kahan bidiagonalization: for every unit starting vector `v` there is a
unitary reduction `Uᴴ A V` to upper bidiagonal form with nonnegative real diagonal `d` and
superdiagonal `e`, in which `V` has first column `v`. It preserves the singular values. -/
theorem exists_unitary_conjTranspose_mul_bidiagonal {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (v : EuclideanSpace 𝕜 (Fin (n + 1))) (hv : ‖v‖ = 1) :
    ∃ (U : Matrix (Fin m) (Fin m) 𝕜) (V : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (d e : ℕ → ℝ),
      U ∈ unitary (Matrix (Fin m) (Fin m) 𝕜) ∧
      V ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) ∧ (∀ i, V i 0 = v i) ∧
      (∀ k, 0 ≤ d k) ∧ (∀ k, 0 ≤ e k) ∧
      (∀ i j, (Uᴴ * A * V) i j =
        if i.val = j.val then (d i.val : 𝕜) else if i.val + 1 = j.val then (e i.val : 𝕜) else 0) ∧
      (Uᴴ * A * V).toEuclideanLin.singularValues = A.toEuclideanLin.singularValues := by
  sorry

/-- **Gap 4.18.** Keldysh's local residue formula at a simple nonlinear eigenvalue. -/
theorem exists_analyticOnNhd_sub_inv_pole_of_simple_eigenvalue {n : ℕ}
    (F : ℂ → Matrix (Fin n) (Fin n) ℂ) {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀)
    (hd : (F z₀).det = 0) (hd' : deriv (fun z ↦ (F z).det) z₀ ≠ 0) :
    ∃ (v w : Fin n → ℂ) (r : ℝ) (R : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < r ∧
      F z₀ *ᵥ v = 0 ∧ (F z₀)ᴴ *ᵥ w = 0 ∧ dotProduct (star w) (deriv F z₀ *ᵥ v) = 1 ∧
      AnalyticOnNhd ℂ R (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ → (F z).det ≠ 0 ∧
        (F z)⁻¹ = (z - z₀)⁻¹ • Matrix.vecMulVec v (star w) + R z := by
  sorry

/-- The block companion pencil, evaluated at `z`, of the matrix polynomial
`∑_{j ≤ d + 1} z ^ j D j` of degree at most `d + 1`: the first block row holds the
coefficients, with `z D (d + 1)` added in the last block column, and the other block rows
are `I` on the block diagonal and `-z I` on the block subdiagonal. -/
def blockCompanionPencil {R : Type*} [CommRing R] {n : ℕ} (d : ℕ)
    (D : ℕ → Matrix (Fin n) (Fin n) R) (z : R) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R :=
  fun (i, a) (j, b) ↦
    if i.val = 0 then D j.val a b + (if j.val = d then z * D (d + 1) a b else 0)
    else if a ≠ b then 0
    else if i = j then 1
    else if i.val = j.val + 1 then -z else 0

/-- The entries of the block companion pencil. -/
theorem blockCompanionPencil_apply {R : Type*} [CommRing R] {n : ℕ} (d : ℕ)
    (D : ℕ → Matrix (Fin n) (Fin n) R) (z : R) (i j : Fin (d + 1)) (a b : Fin n) :
    blockCompanionPencil d D z (i, a) (j, b) =
      if i.val = 0 then D j.val a b + (if j.val = d then z * D (d + 1) a b else 0)
      else if a ≠ b then 0
      else if i = j then 1
      else if i.val = j.val + 1 then -z else 0 := (rfl)

/-- **Gap 4.19.** The determinant of the block companion pencil equals the polynomial
determinant, including the singular-polynomial case. -/
theorem det_blockCompanionPencil {R : Type*} [CommRing R] {n : ℕ} (d : ℕ)
    (D : ℕ → Matrix (Fin n) (Fin n) R) (z : R) :
    (blockCompanionPencil d D z).det = (∑ j ∈ Finset.range (d + 2), z ^ j • D j).det := by
  sorry

/-- **Gap 4.19.** Kernel vectors of the pencil are exactly lifted polynomial kernel vectors. -/
theorem blockCompanionPencil_mulVec_eq_zero_iff {R : Type*} [CommRing R] {n : ℕ}
    (d : ℕ) (D : ℕ → Matrix (Fin n) (Fin n) R) (z : R)
    (x : Fin (d + 1) × Fin n → R) :
    blockCompanionPencil d D z *ᵥ x = 0 ↔
      ∃ v : Fin n → R, (∑ j ∈ Finset.range (d + 2), z ^ j • D j) *ᵥ v = 0 ∧
        ∀ i a, x (i, a) = z ^ i.val * v a := by
  sorry

end NASC
