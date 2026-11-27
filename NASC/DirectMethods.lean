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
The least-squares proofs use Mathlib's adjoint criterion for a residual minimizer.
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
  obtain ⟨hL, hdiag, hU, hmul⟩ := h
  let e := Fin.castLEEmb hk
  have hsub : (LU.1 * LU.2).submatrix e e = LU.1.submatrix e e * LU.2.submatrix e e := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Finset.sum_map Finset.univ e (fun a ↦ LU.1 (e i) a * LU.2 a (e j))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha ↦ ?_
    have hka : k ≤ a.val := by
      by_contra! hak
      exact ha (Finset.mem_map.mpr ⟨⟨a.val, hak⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hia : e i < a := (Fin.is_lt i).trans_le hka
    simp only [hL (i := e i) (j := a) hia, zero_mul]
  have hL' : (LU.1.submatrix e e).IsLowerTriangular :=
    fun _ _ hij ↦ hL hij
  have hU' : (LU.2.submatrix e e).IsUpperTriangular :=
    fun _ _ hij ↦ hU hij
  calc
    _ = (LU.1.submatrix e e * LU.2.submatrix e e).det := by
      rw [← hsub, hmul]
      simp only [e, Fin.coe_castLEEmb]
    _ = _ := by
      rw [Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL',
        Matrix.det_of_isUpperTriangular hU']
      simp only [Matrix.submatrix_apply, hdiag, Finset.prod_const_one, one_mul, e,
        Fin.coe_castLEEmb]

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
  have hbound (l : Fin (n + 1)) : ∀ i j, ‖B l i j‖ ≤ (2 : ℝ) ^ l.val * M := by
    induction l using Fin.induction with
    | zero => simpa only [h.1, Fin.val_zero, pow_zero, one_mul] using hM
    | succ l ih =>
      obtain ⟨p, _, hmax, hnext⟩ := h.2 l
      intro i j
      rw [hnext]
      let C := (B l.castSucc).submatrix (Equiv.swap l p) id
      have hC (a b : Fin n) : ‖C a b‖ ≤ 2 ^ l.val * M := ih (Equiv.swap l p a) b
      have hCn : 0 ≤ (2 : ℝ) ^ l.val * M := (norm_nonneg _).trans (hC i j)
      rw [Fin.val_succ, pow_succ]
      have hdouble : (2 : ℝ) ^ l.val * 2 * M = 2 ^ l.val * M + 2 ^ l.val * M := by ring
      rw [hdouble]
      dsimp only [partialPivotStep]
      split
      · rename_i hij
        have hdiv : ‖C i l / C l l‖ ≤ 1 := by
          rw [norm_div]
          by_cases h0 : ‖C l l‖ = 0
          · rw [h0, div_zero]
            exact zero_le_one
          · refine (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))).mpr ?_
            have hswap : l ≤ Equiv.swap l p i := by
              by_cases hip : i = p
              · simp [hip]
              · rw [Equiv.swap_apply_of_ne_of_ne hij.1.ne' hip]
                exact hij.1.le
            simpa only [C, Matrix.submatrix_apply, Equiv.swap_apply_left, id_eq] using hmax _ hswap
        refine (norm_sub_le _ _).trans (add_le_add (hC i j) ?_)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)).trans
          (by simpa only [one_mul] using hC l j)
      · exact (hC i j).trans (le_add_of_nonneg_right hCn)
  exact hbound k.castSucc i j

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
  rw [minimizesLeastSquares_iff]
  have h := ContinuousLinearMap.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero
    A.toEuclideanLin.toContinuousLinearMap b x
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  have h' : (∀ y, ‖b - A.toEuclideanLin x‖ ≤ ‖b - A.toEuclideanLin y‖) ↔
      Aᴴ.toEuclideanLin (b - A.toEuclideanLin x) = 0 := h
  rw [map_sub, sub_eq_zero] at h'
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, eq_comm]
  exact h'

/-- **Gap 3.11.** A thin QR factorization reduces least squares to a triangular solve. -/
theorem minimizesLeastSquares_iff_of_thinQR {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    {A Q : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin n) (Fin n) 𝕜}
    {b : EuclideanSpace 𝕜 (Fin m)} {x : EuclideanSpace 𝕜 (Fin n)}
    (hA : Q * R = A) (hQ : Qᴴ * Q = 1) (hR : R.det ≠ 0) :
    MinimizesLeastSquares A b x ↔ x = (R⁻¹).toEuclideanLin (Qᴴ.toEuclideanLin b) := by
  rw [minimizesLeastSquares_iff_normalEquation, ← hA, Matrix.conjTranspose_mul,
    Matrix.mul_assoc (Rᴴ) Qᴴ (Q * R), ← Matrix.mul_assoc Qᴴ Q R, hQ, one_mul,
    Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same, LinearMap.comp_apply, LinearMap.comp_apply]
  have hU : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hinv (S : Matrix (Fin n) (Fin n) 𝕜) (hS : IsUnit S.det) (v : EuclideanSpace 𝕜 (Fin n)) :
      (S⁻¹).toEuclideanLin (S.toEuclideanLin v) = v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.nonsing_inv_mul S hS,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have hconj : IsUnit Rᴴ.det := by
    rw [Matrix.det_conjTranspose, isUnit_iff_ne_zero]
    exact star_ne_zero.mpr hR
  have hinj : Function.Injective (Rᴴ.toEuclideanLin) :=
    Function.LeftInverse.injective (hinv _ hconj)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (hinv R hU x).symm.trans (congrArg (R⁻¹).toEuclideanLin (hinj h))
  · subst x
    rw [← LinearMap.comp_apply R.toEuclideanLin (R⁻¹).toEuclideanLin,
      ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv R hU, Matrix.toLpLin_one,
      LinearMap.id_apply]

/-- **Gap 3.14.** A uniform contraction bound and a bounded perturbation give the
limiting error floor for iterative refinement. -/
theorem limsup_norm_le_of_refinement_bound {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (x₀ : E) {q c : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hc : 0 ≤ c)
    (h : ∀ i, ‖x (i + 1) - x₀‖ ≤ q * ‖x i - x₀‖ + c) :
    Filter.limsup (fun i ↦ ‖x i - x₀‖) Filter.atTop ≤ c / (1 - q) := by
  let d := c / (1 - q)
  have hqd : q * d + c = d := by
    dsimp only [d]
    have hne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq')
    field_simp
    ring
  have hbound (i : ℕ) : ‖x i - x₀‖ ≤ q ^ i * ‖x 0 - x₀‖ + d := by
    induction i with
    | zero =>
      simpa only [pow_zero, one_mul] using
        le_add_of_nonneg_right (a := ‖x 0 - x₀‖) (div_nonneg hc (sub_nonneg.mpr hq'.le))
    | succ i ih =>
      calc
        _ ≤ q * ‖x i - x₀‖ + c := h i
        _ ≤ q * (q ^ i * ‖x 0 - x₀‖ + d) + c :=
          add_le_add_left (mul_le_mul_of_nonneg_left ih hq) c
        _ = _ := by rw [pow_succ]; nlinarith only [hqd]
  have hlim : Filter.Tendsto (fun i : ℕ ↦ q ^ i * ‖x 0 - x₀‖ + d)
      Filter.atTop (nhds d) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq').mul_const ‖x 0 - x₀‖).add_const d
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ Filter.limsup_le_of_le ?_ ?_
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop fun i ↦ norm_nonneg (x i - x₀)
  · exact (hlim.eventually_le_const ha).mono fun i hi ↦ (hbound i).trans hi

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
