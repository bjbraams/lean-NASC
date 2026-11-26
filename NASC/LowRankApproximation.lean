module

public import NASC.Conditioning
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Low-rank, randomized and tensor approximation

Frobenius approximation, Gaussian sketches, tensor rank and unfoldings, and Taylor
approximation of separated kernels. See gaps 6.8–6.16.
-/

public section

noncomputable section

namespace NASC

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal InnerProductSpace
open MeasureTheory ProbabilityTheory Set

/-- **Gap 6.8.** Truncated singular expansion attains the Frobenius optimum. The statement
uses squared Frobenius errors and zero-extended singular values. -/
theorem isLeast_rankApproximation_frobenius_sq {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    IsLeast {t : ℝ | ∃ B : Matrix (Fin m) (Fin n) 𝕜, B.rank ≤ k ∧
      t = ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2}
      (∑ i ∈ Finset.Ico k (min m n), A.toEuclideanLin.singularValues i ^ 2) := by
  sorry

/-- **Gap 6.9.** Deterministic range-finder error for a square input (zero-padded if needed).
The right inverse recovers the leading coordinates of the probe in the singular basis. -/
theorem rangeFinder_error_le {k r l : ℕ}
    (B V : Matrix (Fin (k + r)) (Fin (k + r)) ℝ)
    (X : Matrix (Fin (k + r)) (Fin l) ℝ) (J : Matrix (Fin l) (Fin k) ℝ)
    (hV : V ∈ unitary (Matrix (Fin (k + r)) (Fin (k + r)) ℝ))
    (hdiag : Vᵀ * Bᵀ * B * V =
      Matrix.diagonal fun i ↦ B.toEuclideanLin.singularValues i.val ^ 2)
    (hJ : ((Vᵀ * X).submatrix (Fin.castAdd r) id) * J = 1) :
    let Y := (B * X).toEuclideanLin.range
    let tail := (Vᵀ * X).submatrix (Fin.natAdd k) id
    let S : Matrix (Fin r) (Fin r) ℝ :=
      Matrix.diagonal fun i ↦ B.toEuclideanLin.singularValues (k + i.val)
    ‖(1 - Y.starProjection) * (Matrix.toEuclideanCLM (n := Fin (k + r)) (𝕜 := ℝ) B)‖ ≤
      B.toEuclideanLin.singularValues k + ‖S * tail * J‖ := by
  sorry

/-- A law on real matrices whose entries are independent centered normals with common
variance. The nested product law has the same entry order as the matrix type. -/
def gaussianMatrixLaw (m n : ℕ) (v : ℝ≥0) : Measure (Fin m → Fin n → ℝ) :=
  Measure.pi fun _ : Fin m ↦ Measure.pi fun _ : Fin n ↦ gaussianReal 0 v

/-- **Gap 6.10.** Gaussian Johnson--Lindenstrauss embedding for a finite Euclidean
configuration, with a dimension bound stated as two explicit tails. -/
theorem gaussianMatrixLaw_bad_pair_le {m n N : ℕ} (a : Fin N → EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hN : 2 ≤ N) (ha : Function.Injective a) {ε t : ℝ}
    (ht : 0 < t) (hε : ε < 1)
    (hsize : (1 + Real.sqrt (2 * Real.log ((N : ℝ) * (N - 1 : ℕ) / 2))) /
      Real.sqrt m + t ≤ ε) :
    gaussianMatrixLaw m n (1 / (m : ℝ≥0))
      {G | ∃ i j, i ≠ j ∧
        let v := Matrix.toEuclideanLin (m := Fin m) (n := Fin n) (𝕜 := ℝ) G (a i - a j)
        ‖v‖ < (1 - ε) * ‖a i - a j‖ ∨ (1 + ε) * ‖a i - a j‖ < ‖v‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(m : ℝ) * t ^ 2 / 2)) := by
  sorry

/-- Coordinate tensors indexed by one finite index set per mode. -/
abbrev CoordinateTensor (𝕜 : Type*) {d : ℕ} (dims : Fin d → ℕ) :=
  (∀ j, Fin (dims j)) → 𝕜

/-- A tensor is a sum of at most $r$ decomposable tensors. Zero factors pad a shorter sum. -/
def HasTensorRankLE {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} (dims : Fin d → ℕ)
    (T : CoordinateTensor 𝕜 dims) (r : ℕ) : Prop :=
  ∃ u : Fin r → ∀ j, Fin (dims j) → 𝕜,
    ∀ i, T i = ∑ k, ∏ j, u k j (i j)

/-- **Gap 6.12.** The tensors of rank at most one form a closed set. -/
theorem isClosed_setOf_hasTensorRankLE_one {𝕜 : Type*} [RCLike 𝕜]
    {d : ℕ} (dims : Fin d → ℕ) :
    IsClosed {T : CoordinateTensor 𝕜 dims | HasTensorRankLE dims T 1} := by
  sorry

/-- **Gap 6.12.** Over three two-dimensional modes, tensors of rank at most two are
not closed. -/
theorem exists_borderRankTwo_not_rankTwo {𝕜 : Type*} [RCLike 𝕜] :
    ∃ T : CoordinateTensor 𝕜 (fun _ : Fin 3 ↦ 2),
      T ∈ closure {S | HasTensorRankLE (fun _ : Fin 3 ↦ 2) S 2} ∧
        ¬HasTensorRankLE (fun _ : Fin 3 ↦ 2) T 2 ∧
        HasTensorRankLE (fun _ : Fin 3 ↦ 2) T 3 := by
  sorry

/-- The mode-$j$ matricization with repeated columns avoided by indexing only the
other modes. -/
def modeUnfold {𝕜 : Type*} {d : ℕ} {dims : Fin d → ℕ} (T : CoordinateTensor 𝕜 dims)
    (j : Fin d) : Matrix (Fin (dims j)) (∀ k : {k : Fin d // k ≠ j}, Fin (dims k.val)) 𝕜 :=
  fun a b ↦ T fun k ↦ if h : k = j then h.symm ▸ a else b ⟨k, h⟩

/-- **Gap 6.13.** Projecting onto leading mode subspaces gives the HOSVD tail bound.
Each frame is orthonormal and matches the corresponding leading Gram spectrum. -/
theorem hosvd_projection_error_sq_le {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    {dims r : Fin d → ℕ} (T : CoordinateTensor 𝕜 dims)
    (U : ∀ j, Matrix (Fin (dims j)) (Fin (r j)) 𝕜)
    (hU : ∀ j, (U j)ᴴ * U j = 1)
    (hmode : ∀ j,
      modeUnfold T j * (modeUnfold T j)ᴴ * U j =
        U j * Matrix.diagonal (fun i : Fin (r j) ↦
          (((modeUnfold T j).toEuclideanLin.singularValues i.val ^ 2 : ℝ) : 𝕜))) :
    let P := fun j ↦ U j * (U j)ᴴ
    let A : CoordinateTensor 𝕜 dims := fun i ↦ ∑ k, (∏ j, P j (i j) (k j)) * T k
    ∑ i, ‖T i - A i‖ ^ 2 ≤ ∑ j, ∑ k ∈ Finset.Ico (r j) (dims j),
      (modeUnfold T j).toEuclideanLin.singularValues k ^ 2 := by
  sorry

/-- Flattening at the cut between the first $k$ modes and the remaining modes. -/
def cutUnfold {𝕜 : Type*} {d : ℕ} {dims : Fin d → ℕ}
    (T : CoordinateTensor 𝕜 dims) (k : ℕ) :
    Matrix (∀ j : {j : Fin d // j.val < k}, Fin (dims j.val))
      (∀ j : {j : Fin d // k ≤ j.val}, Fin (dims j.val)) 𝕜 :=
  fun a b ↦ T fun j ↦ if hj : j.val < k then a ⟨j, hj⟩ else b ⟨j, Nat.le_of_not_gt hj⟩

/-- A tensor train contracts cores along finite bond indices with trivial endpoint ranks. -/
def HasTensorTrain {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} {dims : Fin d → ℕ}
    (T : CoordinateTensor 𝕜 dims) (r : Fin (d + 1) → ℕ) : Prop :=
  r 0 = 1 ∧ r (Fin.last d) = 1 ∧
    ∃ G : ∀ j : Fin d, Fin (r j.castSucc) → Fin (r j.succ) → Fin (dims j) → 𝕜,
      ∀ i, T i = ∑ b : (∀ j, Fin (r j)), ∏ j, G j (b j.castSucc) (b j.succ) (i j)

/-- **Gap 6.14.** Feasible tensor train ranks are exactly the upper bounds on the
ranks of all interior cut unfoldings. -/
theorem hasTensorTrain_iff_cutRank_le {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    {dims : Fin d → ℕ} (T : CoordinateTensor 𝕜 dims) (r : Fin (d + 1) → ℕ)
    (h : 0 < d) (h₀ : r 0 = 1) (hd : r (Fin.last d) = 1) :
    HasTensorTrain T r ↔ ∀ k : Fin (d + 1), 0 < k.val → k.val < d →
      (cutUnfold T k.val).rank ≤ r k := by
  sorry

/-- **Gap 6.16.** Directional derivative bounds on a separated convex block give a
uniform separable Taylor approximation. Derivative norms are in Euclidean coordinates. -/
theorem exists_separatedApproximation_of_fderiv_bound {m q : ℕ}
    {X Y : Set (EuclideanSpace ℝ (Fin m))} {x₀ : EuclideanSpace ℝ (Fin m)}
    (hX : Convex ℝ X) (hx₀ : x₀ ∈ X) (hq : 0 < q)
    (κ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hκ : ∀ y ∈ Y, ContDiff ℝ q (fun x ↦ κ x y)) {D M : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ X, ‖x - x₀‖ ≤ D)
    (hderiv : ∀ x ∈ X, ∀ y ∈ Y, ‖iteratedFDeriv ℝ q (fun z ↦ κ z y) x‖ ≤ M) :
    ∃ (f g : Fin ((q - 1 + m).choose m) → EuclideanSpace ℝ (Fin m) → ℝ),
      ∀ x ∈ X, ∀ y ∈ Y, |κ x y - ∑ i, f i x * g i y| ≤ M * D ^ q / q.factorial := by
  sorry

end NASC
