module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.Spectrum

import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Matrix and inner-product helpers

Topic-free linear algebra used by several files of the library.

## Main definitions

* `NASC.symmTridiagonal d e n`: the symmetric tridiagonal matrix with diagonal `d` and
  off-diagonal `e`.

## Main results

* `NASC.l2_opNorm_unitary_mul_mul_conjTranspose`: unitary similarity preserves the Euclidean
  operator norm.
* `NASC.tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one`: in a complex Banach algebra,
  `aᵏ → 0` iff the spectral radius of `a` is less than one.
* `NASC.tendsto_matrix_zero_of_tendsto_toEuclideanLin_single`: convergence of matrices from
  convergence on the coordinate vectors.
* `NASC.sq_sum_inner_le_sum_mul_sum_div`: the weighted Cauchy–Schwarz inequality for a finite
  sum of inner products.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open Filter

/-- The symmetric tridiagonal matrix of order `n` with diagonal entries `d i` and the entry
`e (i + 1)` in positions `(i, i + 1)` and `(i + 1, i)`. The value `e 0` is not used. -/
def symmTridiagonal {R : Type*} [Zero R] (d e : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j ↦ if i = j then d i.val else if i.val + 1 = j.val then e j.val
    else if j.val + 1 = i.val then e i.val else 0

/-- The entries of `symmTridiagonal d e n`. -/
theorem symmTridiagonal_apply {R : Type*} [Zero R] (d e : ℕ → R) (n : ℕ) (i j : Fin n) :
    symmTridiagonal d e n i j =
      if i = j then d i.val else if i.val + 1 = j.val then e j.val
        else if j.val + 1 = i.val then e i.val else 0 := by
  unfold symmTridiagonal
  rfl

/-- A symmetric tridiagonal matrix is symmetric. -/
theorem symmTridiagonal_isSymm {R : Type*} [Zero R] (d e : ℕ → R) (n : ℕ) :
    (symmTridiagonal d e n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, symmTridiagonal_apply, eq_comm (a := j)]
  split_ifs <;> first | rfl | omega | (subst_vars; rfl)

/-- Unitary similarity preserves the Euclidean operator norm. -/
theorem l2_opNorm_unitary_mul_mul_conjTranspose {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {W : Matrix (Fin n) (Fin n) 𝕜} (hW : W ∈ unitary (Matrix (Fin n) (Fin n) 𝕜))
    (Y : Matrix (Fin n) (Fin n) 𝕜) : ‖W * Y * Wᴴ‖ = ‖Y‖ := by
  rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hW),
    CStarRing.norm_mem_unitary_mul _ hW]

/-- In a complex Banach algebra, powers tend to zero precisely below spectral radius one. -/
theorem tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    Tendsto (fun k : ℕ ↦ a ^ k) atTop (nhds 0) ↔ spectralRadius ℂ a < 1 := by
  rw [spectrum.spectralRadius_eq_gelfandRadius, ENNReal.ofReal_lt_one,
    tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    obtain ⟨k, hk, hnorm⟩ := ((eventually_ne_atTop (0 : ℕ)).and
      (h.eventually_lt_const zero_lt_one)).exists
    exact (pow_lt_one_iff_of_nonneg (gelfandRadius_nonneg a) hk).mp
      ((gelfandRadius_pow_le_norm_pow a hk).trans_lt hnorm)
  · intro h
    obtain ⟨q, haq, hq⟩ := exists_between h
    obtain ⟨C, _, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a haq
    have hlim : Tendsto (fun k : ℕ ↦ C * q ^ k) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          ((gelfandRadius_nonneg a).trans haq.le) hq).const_mul C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ norm_nonneg _) hC

/-- A sequence of square matrices whose action on each coordinate vector tends to zero
converges to zero in the operator norm. -/
theorem tendsto_matrix_zero_of_tendsto_toEuclideanLin_single {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {A : ℕ → Matrix (Fin n) (Fin n) 𝕜}
    (h : ∀ j : Fin n, Tendsto (fun k ↦ (A k).toEuclideanLin (EuclideanSpace.single j 1))
      atTop (nhds 0)) : Tendsto A atTop (nhds 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hcoord := (PiLp.continuous_apply 2 (fun _ : Fin n ↦ 𝕜) i).continuousAt.tendsto.comp (h j)
  simpa only [Function.comp_def, EuclideanSpace.single, Matrix.toLpLin_apply, PiLp.ofLp_single,
    WithLp.ofLp_toLp, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    PiLp.zero_apply, Matrix.zero_apply] using hcoord

/-- Weighted Cauchy--Schwarz inequality for a finite sum of inner products:
`(∑ ⟪aᵢ, bᵢ⟫)² ≤ (∑ wᵢ ‖aᵢ‖²) (∑ ‖bᵢ‖² / wᵢ)` for positive weights. -/
theorem sq_sum_inner_le_sum_mul_sum_div {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (s : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ s, 0 < w i)
    (a b : ι → H) :
    (∑ i ∈ s, inner ℝ (a i) (b i)) ^ 2 ≤
      (∑ i ∈ s, w i * ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 / w i := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    fun i hi ↦ ?_
  · exact mul_nonneg (hw i hi).le (sq_nonneg _)
  · exact div_nonneg (sq_nonneg _) (hw i hi).le
  calc
    inner ℝ (a i) (b i) ^ 2 ≤ (‖a i‖ * ‖b i‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = w i * ‖a i‖ ^ 2 * (‖b i‖ ^ 2 / w i) := by field_simp [(hw i hi).ne']

end NASC
