module

public import NASC.Conditioning
public import NASC.FloatingPoint
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Direct methods

LU, Cholesky and QR factorizations, elimination and rounding recurrences, normal equations,
iterative refinement and elimination graphs. See section 3 of the mathematical catalogue.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix BigOperators Matrix.Norms.L2Operator
open Matrix

/-- A unit lower triangular and upper triangular factorization. -/
def IsLU {𝕜 : Type*} [Field 𝕜] {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    (LU : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  LU.1.IsLowerTriangular ∧ (∀ i, LU.1 i i = 1) ∧ LU.2.IsUpperTriangular ∧
    LU.1 * LU.2 = A

/-- **Gap 3.1.** The proper leading principal minors characterize uniqueness of LU. -/
theorem existsUnique_isLU_iff {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃! LU, IsLU A LU) ↔
      ∀ (k : ℕ) (hk : k < n),
        (A.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0 := by
  sorry

/-- **Gap 3.1.** Leading principal determinants are products of the corresponding pivots. -/
theorem IsLU.det_leading {𝕜 : Type*} [Field 𝕜] {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) 𝕜}
    {LU : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜}
    (h : IsLU A LU) (hk : k ≤ n) :
    (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ∏ i : Fin k, LU.2 (Fin.castLE hk i) (Fin.castLE hk i) := by
  sorry

/-- **Gap 3.2.** Row pivots give an LU factorization with multipliers bounded by one. -/
theorem exists_isLU_permuted_norm_le_one {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ (p : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) 𝕜),
      IsLU (A.submatrix p id) (L, U) ∧ (∀ i j, j < i → ‖L i j‖ ≤ 1) ∧
        (U.det ≠ 0 ↔ A.det ≠ 0) := by
  sorry

/-- A pivot step swaps the chosen row with the pivot position and performs elimination in
the trailing block. A zero pivot leaves the trailing rows unchanged. -/
def partialPivotStep {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (k p : Fin n) : Matrix (Fin n) (Fin n) 𝕜 :=
  let B := A.submatrix (Equiv.swap k p) id
  fun i j ↦ if k < i ∧ k ≤ j then B i j - B i k / B k k * B k j else B i j

/-- A sequence of exact partial-pivoting stages, including the initial and final matrices. -/
def IsPartialPivotElimination {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜)
    (B : Fin (n + 1) → Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  B 0 = A ∧ ∀ (k : Fin n), ∃ p : Fin n, k ≤ p ∧
    (∀ i, k ≤ i → ‖B k.castSucc i k‖ ≤ ‖B k.castSucc p k‖) ∧
    B k.succ = partialPivotStep (B k.castSucc) k p

/-- **Gap 3.5.** Every active entry grows by at most a factor of two per elimination stage. -/
theorem IsPartialPivotElimination.norm_entry_le_two_pow {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) 𝕜} {B : Fin (n + 1) → Matrix (Fin n) (Fin n) 𝕜}
    (h : IsPartialPivotElimination A B) {M : ℝ} (hM : ∀ i j, ‖A i j‖ ≤ M)
    (k : Fin n) (i j : Fin n) :
    ‖B k.castSucc i j‖ ≤ (2 : ℝ) ^ k.val * M := by
  sorry

/-- The computed stages of unpivoted Gaussian elimination, with independently rounded
divisions, products and subtractions. The first n pivot rows lie in the m input rows. -/
def IsRoundedElimination {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℝ) (u : ℝ)
    (B : Fin (n + 1) → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  B 0 = A ∧ ∀ k : Fin n,
    let row := Fin.castLE hnm k
    (∀ j, k ≤ j → U k j = B k.castSucc row j) ∧
    (∀ j, j < k → U k j = 0) ∧
    L row k = 1 ∧
    (∀ i, i < row → L i k = 0) ∧
    (∀ i, row < i → B k.castSucc row k ≠ 0 ∧
      HasRelativeError u (B k.castSucc i k / B k.castSucc row k) (L i k) ∧
      ∀ j, k < j → ∃ p : ℝ, HasRelativeError u (L i k * U k j) p ∧
        HasRelativeError u (B k.castSucc i j - p) (B k.succ i j))

/-- **Gap 3.3.** Rounded elimination yields an entrywise residual bound in terms of the
computed factors. -/
theorem IsRoundedElimination.abs_residual_le {m n : ℕ} {hnm : n ≤ m}
    {A L : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin n) (Fin n) ℝ} {u : ℝ}
    {B : Fin (n + 1) → Matrix (Fin m) (Fin n) ℝ}
    (h : IsRoundedElimination hnm A L U u B) (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (i : Fin m) (j : Fin n) :
    |(L * U) i j - A i j| ≤ roundingGamma u n * ∑ k, |L i k| * |U k j| := by
  sorry

/-- Upper triangular Cholesky data with the relative rounding model at each dot-product,
subtraction, square-root and division operation. -/
def IsRoundedCholesky {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) : Prop :=
  R.IsUpperTriangular ∧ ∀ i j, i ≤ j →
    ∃ s : ℝ, ∃ sums : Fin (n + 1) → ℝ,
      sums 0 = 0 ∧
      s = sums i.castSucc ∧
      (∀ k : Fin n, k < i → ∃ q : ℝ,
        HasRelativeError u (R k i * R k j) q ∧
        (if k.val = 0 then sums k.succ = q else
          HasRelativeError u (sums k.castSucc + q) (sums k.succ))) ∧
      ∃ a : ℝ, (if i.val = 0 then a = A i j else HasRelativeError u (A i j - s) a) ∧
        if i = j then 0 < a ∧ HasRelativeError u (Real.sqrt a) (R i j)
        else R i i ≠ 0 ∧ HasRelativeError u (a / R i i) (R i j)

/-- **Gap 3.8.** A completed rounded Cholesky factorization has componentwise backward error
controlled by the Gram product of the entrywise absolute factor. -/
theorem IsRoundedCholesky.abs_residual_le {n : ℕ} {A R : Matrix (Fin n) (Fin n) ℝ}
    {u : ℝ} (h : IsRoundedCholesky A R u) (hA : A.IsHermitian)
    (hu : 0 ≤ u) (hn : ((n + 1 : ℕ) : ℝ) * u < 1) (i j : Fin n) :
    |(Rᵀ * R) i j - A i j| ≤ roundingGamma u (n + 1) * ∑ k, |R k i| * |R k j| := by
  sorry

/-- **Gap 3.9.** Full QR factorization of a tall matrix, including rank-deficient input. -/
theorem exists_unitary_mul_upperTrapezoidal {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (hnm : n ≤ m) :
    ∃ (Q : Matrix (Fin m) (Fin m) 𝕜) (R : Matrix (Fin m) (Fin n) 𝕜),
      Q ∈ unitary (Matrix (Fin m) (Fin m) 𝕜) ∧
        (∀ i j, j.val < i.val → R i j = 0) ∧ Q * R = A := by
  sorry

/-- **Gap 3.9.** The thin QR factorization with positive diagonal is unique at full rank. -/
theorem existsUnique_thinQR {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) 𝕜} (hA : Function.Injective A.toEuclideanLin) :
    ∃! QR : Matrix (Fin m) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜,
      QR.1ᴴ * QR.1 = 1 ∧ QR.2.IsUpperTriangular ∧
      (∀ i, 0 < RCLike.re (QR.2 i i) ∧ RCLike.im (QR.2 i i) = 0) ∧ QR.1 * QR.2 = A := by
  sorry

/-- **Gap 3.10.** Accumulation of local normwise backward errors in a sequence of
orthogonal Householder updates. The input per-stage bound is relative to the current block. -/
theorem exists_orthogonal_mul_of_householder_step_bound {m n k : ℕ}
    (B : Fin (k + 1) → Matrix (Fin m) (Fin n) ℝ)
    (v : Fin k → Fin m → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hv : ∀ i, ∑ j, v i j ^ 2 = 1)
    (hstep : ∀ i : Fin k,
      let H : Matrix (Fin m) (Fin m) ℝ := 1 - 2 • (Matrix.vecMulVec (v i) (v i))
      ∑ j, ∑ l, (B i.succ j l - (H * B i.castSucc) j l) ^ 2 ≤
        η ^ 2 * ∑ j, ∑ l, (B i.castSucc j l) ^ 2) :
    ∃ Q : Matrix (Fin m) (Fin m) ℝ, Qᵀ * Q = 1 ∧
      ∑ j, ∑ l, ((Q * B (Fin.last k)) j l - B 0 j l) ^ 2 ≤
        ((1 + η) ^ k - 1) ^ 2 * ∑ j, ∑ l, (B 0 j l) ^ 2 := by
  sorry

/-- **Gap 3.11.** Euclidean least-squares minimizers are exactly the solutions of the
matrix normal equations. -/
theorem minimizesLeastSquares_iff_normalEquation {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : EuclideanSpace 𝕜 (Fin m))
    (x : EuclideanSpace 𝕜 (Fin n)) :
    MinimizesLeastSquares A b x ↔
      (Aᴴ * A).toEuclideanLin x = Aᴴ.toEuclideanLin b := by
  sorry

/-- **Gap 3.11.** A thin QR factorization reduces least squares to a triangular solve. -/
theorem minimizesLeastSquares_iff_of_thinQR {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    {A Q : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin n) (Fin n) 𝕜}
    {b : EuclideanSpace 𝕜 (Fin m)} {x : EuclideanSpace 𝕜 (Fin n)}
    (hA : Q * R = A) (hQ : Qᴴ * Q = 1) (hR : R.det ≠ 0) :
    MinimizesLeastSquares A b x ↔ x = (R⁻¹).toEuclideanLin (Qᴴ.toEuclideanLin b) := by
  sorry

/-- **Gap 3.14.** A uniform contraction bound and a bounded perturbation give the
limiting error floor for iterative refinement. -/
theorem limsup_norm_le_of_refinement_bound {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (x₀ : E) {q c : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hc : 0 ≤ c)
    (h : ∀ i, ‖x (i + 1) - x₀‖ ≤ q * ‖x i - x₀‖ + c) :
    Filter.limsup (fun i ↦ ‖x i - x₀‖) Filter.atTop ≤ c / (1 - q) := by
  sorry

/-- An elimination graph on the same vertices after making a vertex's neighbors a clique
and isolating that vertex. -/
def eliminateVertex {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ i ≠ v ∧ j ≠ v ∧ (G.Adj i j ∨ G.Adj i v ∧ G.Adj v j)
  symm := by
    constructor
    intro i j h
    obtain ⟨hij, hiv, hjv, h⟩ := h
    exact ⟨hij.symm, hjv, hiv, h.elim (fun h ↦ Or.inl h.symm)
      (fun h ↦ Or.inr ⟨h.2.symm, h.1.symm⟩)⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Eliminate the vertices in an ordered list from a graph. -/
def eliminateVertices {V : Type*} (G : SimpleGraph V) (vs : List V) : SimpleGraph V :=
  vs.foldl eliminateVertex G

/-- **Gap 3.15.** The fill-path characterization after eliminating a list of vertices.
The walk formulation allows loop removal without changing the surviving endpoints. -/
theorem eliminateVertices_adj_iff_exists_walk {V : Type*} (G : SimpleGraph V)
    (vs : List V) {i j : V} (hij : i ≠ j) (hi : i ∉ vs) (hj : j ∉ vs) :
    (eliminateVertices G vs).Adj i j ↔
      ∃ w : G.Walk i j, ∀ v ∈ w.support, v = i ∨ v = j ∨ v ∈ vs := by
  sorry

end NASC
