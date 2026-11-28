module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import NASC.Support.GaussianMatrix

/-!
# Low-rank, randomized and tensor approximation

Frobenius approximation, Gaussian sketches, tensor rank and unfoldings, and Taylor
approximation of separated kernels. See gaps 6.8–6.16.

## Main definitions

* `NASC.CoordinateTensor 𝕜 dims`, `NASC.HasTensorRankLE`, `NASC.modeUnfold`, `NASC.cutUnfold`
  and `NASC.HasTensorTrain`.

## Main results

* `NASC.isLeast_rankApproximation_frobenius_sq`: Eckart--Young in the Frobenius norm.
* `NASC.rangeFinder_error_le`: the deterministic range-finder bound.
* `NASC.gaussianMatrixLaw_exists_distorted_pair_le`: the Gaussian Johnson--Lindenstrauss bound.
* `NASC.isClosed_setOf_hasTensorRankLE_one`, `NASC.exists_borderRankTwo_not_rankTwo`:
  closedness of rank one and failure of closedness of rank two.
* `NASC.hosvd_projection_error_sq_le`: the HOSVD error bound.
* `NASC.hasTensorTrain_iff_cutRank_le`: tensor-train ranks and cut ranks.
* `NASC.exists_separatedApproximation_of_fderiv_bound`: separable Taylor approximation.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix Matrix.Norms.L2Operator ENNReal NNReal InnerProductSpace
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

/-- **Gap 6.10.** Gaussian Johnson--Lindenstrauss embedding for a finite Euclidean
configuration, with a dimension bound stated as two explicit tails. -/
theorem gaussianMatrixLaw_exists_distorted_pair_le {m n N : ℕ}
    (a : Fin N → EuclideanSpace ℝ (Fin n))
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

/-- A tensor is a linear combination of at most $r$ decomposable tensors. Zero coefficients
pad a shorter sum, so the predicate is monotone in `r`. For `d = 0` a tensor is a scalar, of
rank at most one, and of rank at most zero exactly when it vanishes. -/
def HasTensorRankLE {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} (dims : Fin d → ℕ)
    (T : CoordinateTensor 𝕜 dims) (r : ℕ) : Prop :=
  ∃ (c : Fin r → 𝕜) (u : Fin r → ∀ j, Fin (dims j) → 𝕜),
    ∀ i, T i = ∑ k, c k * ∏ j, u k j (i j)

/-- The defining property of `HasTensorRankLE`. -/
theorem hasTensorRankLE_iff {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} {dims : Fin d → ℕ}
    {T : CoordinateTensor 𝕜 dims} {r : ℕ} :
    HasTensorRankLE dims T r ↔ ∃ (c : Fin r → 𝕜) (u : Fin r → ∀ j, Fin (dims j) → 𝕜),
      ∀ i, T i = ∑ k, c k * ∏ j, u k j (i j) := by
  unfold HasTensorRankLE
  exact Iff.rfl

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

/-- The entries of the mode-$j$ matricization. -/
theorem modeUnfold_apply {𝕜 : Type*} {d : ℕ} {dims : Fin d → ℕ} (T : CoordinateTensor 𝕜 dims)
    (j : Fin d) (a : Fin (dims j)) (b : ∀ k : {k : Fin d // k ≠ j}, Fin (dims k.val)) :
    modeUnfold T j a b = T fun k ↦ if h : k = j then h.symm ▸ a else b ⟨k, h⟩ := by
  unfold modeUnfold
  rfl

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

/-- The entries of the cut unfolding. -/
theorem cutUnfold_apply {𝕜 : Type*} {d : ℕ} {dims : Fin d → ℕ}
    (T : CoordinateTensor 𝕜 dims) (k : ℕ) (a : ∀ j : {j : Fin d // j.val < k}, Fin (dims j.val))
    (b : ∀ j : {j : Fin d // k ≤ j.val}, Fin (dims j.val)) :
    cutUnfold T k a b =
      T fun j ↦ if hj : j.val < k then a ⟨j, hj⟩ else b ⟨j, Nat.le_of_not_gt hj⟩ := by
  unfold cutUnfold
  rfl

/-- A tensor train contracts cores along finite bond indices with trivial endpoint ranks,
up to a scalar factor. For `d ≥ 1` the factor can be absorbed into a core; for `d = 0` it
makes every scalar a tensor train. -/
def HasTensorTrain {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} {dims : Fin d → ℕ}
    (T : CoordinateTensor 𝕜 dims) (r : Fin (d + 1) → ℕ) : Prop :=
  r 0 = 1 ∧ r (Fin.last d) = 1 ∧
    ∃ (c : 𝕜) (G : ∀ j : Fin d, Fin (r j.castSucc) → Fin (r j.succ) → Fin (dims j) → 𝕜),
      ∀ i, T i = c * ∑ b : (∀ j, Fin (r j)), ∏ j, G j (b j.castSucc) (b j.succ) (i j)

/-- The defining property of `HasTensorTrain`. -/
theorem hasTensorTrain_iff {𝕜 : Type*} [CommSemiring 𝕜] {d : ℕ} {dims : Fin d → ℕ}
    {T : CoordinateTensor 𝕜 dims} {r : Fin (d + 1) → ℕ} :
    HasTensorTrain T r ↔ r 0 = 1 ∧ r (Fin.last d) = 1 ∧
      ∃ (c : 𝕜) (G : ∀ j : Fin d, Fin (r j.castSucc) → Fin (r j.succ) → Fin (dims j) → 𝕜),
        ∀ i, T i = c * ∑ b : (∀ j, Fin (r j)), ∏ j, G j (b j.castSucc) (b j.succ) (i j) := by
  unfold HasTensorTrain
  exact Iff.rfl

/-- **Gap 6.14.** Feasible tensor train ranks are exactly the upper bounds on the
ranks of all interior cut unfoldings. -/
theorem hasTensorTrain_iff_cutRank_le {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    {dims : Fin d → ℕ} (T : CoordinateTensor 𝕜 dims) (r : Fin (d + 1) → ℕ)
    (h₀ : r 0 = 1) (hd : r (Fin.last d) = 1) :
    HasTensorTrain T r ↔ ∀ k : Fin (d + 1), 0 < k.val → k.val < d →
      (cutUnfold T k.val).rank ≤ r k := by
  sorry

/-- **Gap 6.16.** Directional derivative bounds on a separated convex block give a
uniform separable Taylor approximation. Derivative norms are in Euclidean coordinates. For
`q = 0` the bound is `|κ x y| ≤ M`, attained by the zero approximation. -/
theorem exists_separatedApproximation_of_fderiv_bound {m q : ℕ}
    {X Y : Set (EuclideanSpace ℝ (Fin m))} {x₀ : EuclideanSpace ℝ (Fin m)}
    (hX : Convex ℝ X) (hx₀ : x₀ ∈ X)
    (κ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hκ : ∀ y ∈ Y, ContDiff ℝ q (fun x ↦ κ x y)) {D M : ℝ}
    (hdiam : ∀ x ∈ X, ‖x - x₀‖ ≤ D)
    (hderiv : ∀ x ∈ X, ∀ y ∈ Y, ‖iteratedFDeriv ℝ q (fun z ↦ κ z y) x‖ ≤ M) :
    ∃ (f g : Fin ((q - 1 + m).choose m) → EuclideanSpace ℝ (Fin m) → ℝ),
      ∀ x ∈ X, ∀ y ∈ Y, |κ x y - ∑ i, f i x * g i y| ≤ M * D ^ q / q.factorial := by
  sorry

end NASC
