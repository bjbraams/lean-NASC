module

public import NASC.DirectMethods
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Eigenvalue and singular value computations

Schur and singular value factorizations, power and Rayleigh iterations, QR, Krylov reduction,
and linearizations of matrix-valued eigenproblems. See section 4 of the gap catalogue.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
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

/-- Normalize the new vector in one power iteration. -/
def powerStep {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →ₗ[𝕜] E) (x : E) : E :=
  ((‖A x‖⁻¹ : ℝ) : 𝕜) • A x

/-- **Gap 4.4.** The normalized power method converges up to a unit complex phase, at a
rate fixed by the spectral ratio. Inverse iteration applies this estimate to the resolvent. -/
theorem exists_phase_norm_powerStep_iterate_sub_le {n : ℕ}
    (A : EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)))
    (B : Module.Basis (Fin (n + 1)) ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    (eigs : Fin (n + 1) → ℂ) (v : EuclideanSpace ℂ (Fin (n + 1))) {q : ℝ}
    (hB : ∀ i, A (B i) = eigs i • B i) (hunit : ∀ i, ‖B i‖ = 1) (hv : ‖v‖ = 1)
    (hcoord : B.repr v 0 ≠ 0) (h₀ : eigs 0 ≠ 0) (hq : 0 ≤ q) (hq' : q < 1)
    (hgap : ∀ i ≠ 0, ‖eigs i‖ ≤ q * ‖eigs 0‖) :
    ∃ C ≥ (0 : ℝ), ∀ k, ∃ phase : ℂ, ‖phase‖ = 1 ∧
      ‖(powerStep A)^[k] v‖ = 1 ∧ ‖phase • (powerStep A)^[k] v - B 0‖ ≤ C * q ^ k := by
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

/-- **Gap 4.6.** Accumulated QR factors give the similarity iterates and the QR
factorization of the powers. -/
theorem IsQRIteration.exists_accumulatedFactors {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) 𝕜} {B Q R : ℕ → Matrix (Fin n) (Fin n) 𝕜}
    (h : IsQRIteration A B Q R) :
    ∃ P U : ℕ → Matrix (Fin n) (Fin n) 𝕜,
      P 0 = 1 ∧ U 0 = 1 ∧ ∀ k,
        P (k + 1) = P k * Q k ∧ U (k + 1) = R k * U k ∧
        B (k + 1) = (P (k + 1))ᴴ * A * P (k + 1) ∧ A ^ k = P k * U k ∧
        A * P k = P (k + 1) * R k := by
  obtain ⟨h0, hstep⟩ := h
  let P : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k ↦ Nat.rec 1 (fun i p ↦ p * Q i) k
  let U : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k ↦ Nat.rec 1 (fun i u ↦ R i * u) k
  have hP₀ : P 0 = 1 := rfl
  have hU₀ : U 0 = 1 := rfl
  have hP (k : ℕ) : P (k + 1) = P k * Q k := rfl
  have hU (k : ℕ) : U (k + 1) = R k * U k := rfl
  have hPB (k : ℕ) : (P k)ᴴ * P k = 1 ∧ A * P k = P k * B k := by
    induction k with
    | zero => simp only [hP₀, h0, conjTranspose_one, one_mul, mul_one, and_self]
    | succ k ih =>
      obtain ⟨hQ, -, hk, hnext⟩ := hstep k
      have hs : (Q k)ᴴ * Q k = 1 := Unitary.star_mul_self_of_mem hQ
      constructor
      · rw [hP, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (P k)ᴴ, ih.1,
          one_mul, hs]
      · rw [hP, ← Matrix.mul_assoc, ih.2, hk, hnext]
        simp only [Matrix.mul_assoc]
  have hAP (k : ℕ) : A * P k = P (k + 1) * R k := by
    rw [hP, Matrix.mul_assoc, ← (hstep k).2.2.1, (hPB k).2]
  have hpow (k : ℕ) : A ^ k = P k * U k := by
    induction k with
    | zero => simp only [hP₀, hU₀, pow_zero, mul_one]
    | succ k ih => rw [pow_succ', ih, ← Matrix.mul_assoc, hAP, hU, Matrix.mul_assoc]
  refine ⟨P, U, rfl, rfl, fun k ↦ ⟨hP k, hU k, ?_, hpow k, hAP k⟩⟩
  rw [Matrix.mul_assoc, (hPB (k + 1)).2, ← Matrix.mul_assoc, (hPB (k + 1)).1, one_mul]

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

/-- **Gap 4.8.** Every square complex matrix has a unitary Hessenberg reduction. -/
theorem exists_unitary_conjTranspose_mul_upperHessenberg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q ∈ unitary (Matrix (Fin n) (Fin n) ℂ) ∧
      ∀ i j, j.val + 1 < i.val → (Qᴴ * A * Q) i j = 0 := by
  sorry

/-- **Gap 4.8.** A nonsingular shifted QR step preserves the unreduced Hessenberg form. -/
theorem shiftedQR_upperHessenberg {n : ℕ} (H Q R : Matrix (Fin n) (Fin n) ℂ) (shift : ℂ)
    (hH : ∀ i j, j.val + 1 < i.val → H i j = 0)
    (hsub : ∀ i j, i.val = j.val + 1 → H i j ≠ 0)
    (hQ : Q ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (hR : R.IsUpperTriangular)
    (hQR : H - shift • 1 = Q * R) (hne : R.det ≠ 0) :
    let B := R * Q + shift • 1
    B = Qᴴ * H * Q ∧
      (∀ i j, j.val + 1 < i.val → B i j = 0) ∧
      ∀ i j, i.val = j.val + 1 → B i j ≠ 0 := by
  sorry

/-- Unitary similarity preserves the Euclidean operator norm. -/
theorem l2_opNorm_unitary_mul_mul_conjTranspose {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {W : Matrix (Fin n) (Fin n) 𝕜} (hW : W ∈ unitary (Matrix (Fin n) (Fin n) 𝕜))
    (Y : Matrix (Fin n) (Fin n) 𝕜) : ‖W * Y * Wᴴ‖ = ‖Y‖ := by
  have bound {U Z : Matrix (Fin n) (Fin n) 𝕜}
      (hU : U ∈ unitary (Matrix (Fin n) (Fin n) 𝕜)) : ‖U * Z * Uᴴ‖ ≤ ‖Z‖ := by
    have hstar : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
    have hs := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [hstar] at hs
    have hle : ‖(1 : Matrix (Fin n) (Fin n) 𝕜)‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
      exact ContinuousLinearMap.norm_id_le
    have hsq : ‖U‖ * ‖U‖ ≤ 1 := hs ▸ hle
    have hu : ‖U‖ ≤ 1 := by nlinarith only [hsq, norm_nonneg U]
    calc
      ‖U * Z * Uᴴ‖ ≤ ‖U * Z‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul ..
      _ ≤ ‖U * Z‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_of_le_one_right (norm_nonneg _) hu
      _ ≤ ‖U‖ * ‖Z‖ := Matrix.l2_opNorm_mul ..
      _ ≤ ‖Z‖ := mul_le_of_le_one_left (norm_nonneg _) hu
  refine le_antisymm (bound hW) ?_
  have hstar : Wᴴ * W = 1 := Unitary.star_mul_self_of_mem hW
  have hconj : Wᴴ * (W * Y * Wᴴ) * W = Y := by
    rw [← Matrix.mul_assoc Wᴴ (W * Y), ← Matrix.mul_assoc Wᴴ W, hstar, one_mul,
      Matrix.mul_assoc Y, hstar, mul_one]
  have hWU : Wᴴ ∈ unitary (Matrix (Fin n) (Fin n) 𝕜) := Unitary.star_mem hW
  have hbound := bound (Z := W * Y * Wᴴ) hWU
  rwa [conjTranspose_conjTranspose, hconj] at hbound

/-- **Gap 4.10.** Backward errors for successive unitary reductions add, with the
second error budget scaled by the first perturbed matrix norm. -/
theorem norm_conjTranspose_mul_sub_le_of_reductions {n : ℕ}
    {A H D P Q : Matrix (Fin n) (Fin n) ℂ} {u a b : ℝ}
    (hP : P ∈ unitary (Matrix (Fin n) (Fin n) ℂ))
    (hQ : Q ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (hbu : 0 ≤ b * u)
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

/-- **Gap 4.13.** A full-dimensional Krylov space has a prefix-compatible orthonormal
Arnoldi frame whose compressed operator is upper Hessenberg. -/
theorem exists_arnoldiFrame {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (h : Module.finrank 𝕜 (krylovSubmodule A.toEuclideanLin b m) = m) :
    ∃ Q : Matrix (Fin n) (Fin m) 𝕜, Qᴴ * Q = 1 ∧
      (∀ (k : ℕ) (hk : k ≤ m),
        (Q.submatrix id (Fin.castLE hk)).toEuclideanLin.range =
          krylovSubmodule A.toEuclideanLin b k) ∧
      ∀ i j : Fin m, j.val + 1 < i.val → (Qᴴ * A * Q) i j = 0 := by
  sorry

/-- **Gap 4.14.** The upper Ritz value has the Chebyshev lower bound from the leading
spectral separation and the angle of the initial vector. -/
theorem kanielPaigeSaad_upperRitz {n m : ℕ}
    (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) (hA : A.IsHermitian)
    (b q : EuclideanSpace ℝ (Fin (n + 3))) (hb : ‖b‖ = 1) (hq : ‖q‖ = 1)
    (hvec : A.toEuclideanLin q = hA.eigenvalues₀ 0 • q)
    (hc : ⟪q, b⟫_ℝ ≠ 0)
    (hgap : hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm (Fin.last (n + 2))) <
      hA.eigenvalues₀ 1)
    (Q : Matrix (Fin (n + 3)) (Fin (m + 1)) ℝ) (hQ : Qᵀ * Q = 1)
    (hK : Q.toEuclideanLin.range = krylovSubmodule A.toEuclideanLin b (m + 1))
    (hJ : (Qᵀ * A * Q).IsHermitian) :
    let top := hA.eigenvalues₀ 0
    let second := hA.eigenvalues₀ 1
    let bottom := hA.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm (Fin.last (n + 2)))
    let angle := (1 - ⟪q, b⟫_ℝ ^ 2) / ⟪q, b⟫_ℝ ^ 2
    let t := (Polynomial.Chebyshev.T ℝ m).eval (1 + 2 * (top - second) / (second - bottom))
    top - (top - bottom) * angle / t ^ 2 ≤ hJ.eigenvalues₀ 0 ∧
      hJ.eigenvalues₀ 0 ≤ top := by
  sorry

/-- **Gap 4.16.** Unitary bidiagonalization preserves the singular values of a tall
matrix. -/
theorem exists_unitary_conjTranspose_mul_bidiagonal {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (hnm : n ≤ m) :
    ∃ (U : Matrix (Fin m) (Fin m) 𝕜) (V : Matrix (Fin n) (Fin n) 𝕜),
      U ∈ unitary (Matrix (Fin m) (Fin m) 𝕜) ∧ V ∈ unitary (Matrix (Fin n) (Fin n) 𝕜) ∧
      (∀ i j, i.val ≠ j.val → i.val + 1 ≠ j.val → (Uᴴ * A * V) i j = 0) ∧
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

/-- The block companion pencil of a matrix polynomial of degree at most $d+1$. -/
def companionPencil {𝕜 : Type*} [Field 𝕜] {n : ℕ} (d : ℕ)
    (D : ℕ → Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) :
    Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) 𝕜 :=
  fun (i, a) (j, b) ↦
    if i.val = 0 then D j.val a b + (if j.val = d then z * D (d + 1) a b else 0)
    else if a ≠ b then 0
    else if i = j then 1
    else if i.val = j.val + 1 then -z else 0

/-- **Gap 4.19.** The determinant of the companion pencil equals the polynomial
determinant, including the singular-polynomial case. -/
theorem det_companionPencil {𝕜 : Type*} [Field 𝕜] {n : ℕ} (d : ℕ)
    (D : ℕ → Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) :
    (companionPencil d D z).det = (∑ j ∈ Finset.range (d + 2), z ^ j • D j).det := by
  sorry

/-- **Gap 4.19.** Kernel vectors of the pencil are exactly lifted polynomial kernel vectors. -/
theorem companionPencil_mulVec_eq_zero_iff {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (d : ℕ) (D : ℕ → Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜)
    (x : Fin (d + 1) × Fin n → 𝕜) :
    companionPencil d D z *ᵥ x = 0 ↔
      ∃ v : Fin n → 𝕜, (∑ j ∈ Finset.range (d + 2), z ^ j • D j) *ᵥ v = 0 ∧
        ∀ i a, x (i, a) = z ^ i.val * v a := by
  sorry

end NASC
