module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.LinearAlgebra.Matrix.Circulant

import Mathlib.LinearAlgebra.Vandermonde
import NASC.Support.Algebra
import NASC.Support.Analysis

/-!
# Discrete Fourier analysis and sampling

Fourier matrices, circulants, radix-two recursion, aliasing, trigonometric interpolation,
Shannon sampling and Prony reconstruction. The cyclic formulas use Mathlib's
unnormalized ZMod Fourier transform `ZMod.dft` and its standard additive character, circulants
are Mathlib's `Matrix.circulant`, periodic Fourier coefficients are Mathlib's `fourierCoeffOn`
on `[0, 2π]`, and the bandlimit condition uses Mathlib's Fourier transform `𝓕` (with the
`2π` in the exponent). Prony reconstruction uses Mathlib's Vandermonde nonsingularity criterion.

## Main definitions

* `NASC.fourierMatrix`: the cyclic Fourier matrix `(ζ^{-ij})` on `ZMod n`.
* `NASC.cyclicConvolution`: cyclic convolution on `ZMod n`.
* `NASC.fourierRoot`: the root of unity `exp(-2πi/n)`.
* `NASC.radixTwoTransform`: the radix-two even/odd recursion.

## Main results

* `NASC.fourierMatrix_gram_mulVec`: `Fᴴ F = n I` and `F x = dft x`.
* `NASC.dft_cyclicConvolution_and_mul`: the convolution theorem in both directions.
* `NASC.fourierMatrix_mul_circulant`: the Fourier matrix diagonalizes circulants.
* `NASC.fourierRoot_pow`: the bridge from `fourierRoot` to `ZMod.stdAddChar`.
* `NASC.radixTwoTransform_eq_sum`: the radix-two recursion computes the DFT.
* `NASC.fourierCoeffOn_aliasing`: aliasing of sampled Fourier coefficients.
* `NASC.existsUnique_trigonometric_interpolant`: trigonometric interpolation.
* `NASC.tsum_sinc_smul_samples_eq`: Shannon's sampling theorem.
* `NASC.existsUnique_prony_annihilator`, `NASC.exists_perm_of_expSum_samples_eq`: Prony's method.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Filter
open scoped FourierTransform
open scoped Matrix Interval

/-- The unnormalized cyclic Fourier matrix in the negative-exponent convention. -/
def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j ↦ ZMod.stdAddChar (-(i * j))

/-- The entry in row `i` and column `j` of the Fourier matrix. -/
theorem fourierMatrix_apply (n : ℕ) [NeZero n] (i j : ZMod n) :
    fourierMatrix n i j = ZMod.stdAddChar (-(i * j)) := by
  rfl

/-- **Gap 13.1.** The cyclic Fourier matrix has Gram matrix $nI$ and acts by the
bundled discrete Fourier transform. -/
theorem fourierMatrix_gram_mulVec (n : ℕ) [NeZero n] :
    (fourierMatrix n)ᴴ * fourierMatrix n = (n : ℂ) • 1 ∧
      ∀ x : ZMod n → ℂ, fourierMatrix n *ᵥ x = ZMod.dft x := by
  constructor
  · have hstar (t : ZMod n) : star (ZMod.stdAddChar (-t)) = ZMod.stdAddChar t := by
      rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
        Complex.star_def, ← Circle.coe_inv_eq_conj, inv_inv]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMatrix_apply, hstar,
      ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
    rw [AddChar.sum_mulShift (i - j) (ZMod.isPrimitive_stdAddChar n), ZMod.card,
      Matrix.smul_apply, Matrix.one_apply]
    simp only [sub_eq_zero, Nat.cast_ite, Nat.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero]
  · intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, fourierMatrix_apply, ZMod.dft_apply, smul_eq_mul,
      mul_comm i]

/-- Cyclic convolution on a finite cyclic group. -/
def cyclicConvolution {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j ↦ ∑ k, a k * b (j - k)

/-- Cyclic convolution evaluated at a group element. -/
theorem cyclicConvolution_apply {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) (j : ZMod n) :
    cyclicConvolution a b j = ∑ k, a k * b (j - k) := by
  rfl

/-- The Fourier transform takes cyclic convolution to pointwise multiplication. -/
theorem dft_cyclicConvolution {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) :
    ZMod.dft (cyclicConvolution a b) = ZMod.dft a * ZMod.dft b := by
  funext j
  simp only [ZMod.dft_apply, smul_eq_mul, Pi.mul_apply]
  rw [Finset.sum_mul]
  simp only [cyclicConvolution_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  refine Fintype.sum_equiv (Equiv.subRight k) _ _ fun t ↦ ?_
  simp only [Equiv.subRight_apply]
  have hangle : -(t * j) = -(k * j) + -((t - k) * j) := by ring
  rw [hangle, AddChar.map_add_eq_mul]
  ring

/-- **Gap 13.2.** The Fourier transform interchanges cyclic convolution and
pointwise multiplication with the unnormalized scale factor. -/
theorem dft_cyclicConvolution_and_mul {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) :
    ZMod.dft (cyclicConvolution a b) = ZMod.dft a * ZMod.dft b ∧
      (n : ℂ) • ZMod.dft (a * b) = cyclicConvolution (ZMod.dft a) (ZMod.dft b) := by
  refine ⟨dft_cyclicConvolution a b, ZMod.dft.injective ?_⟩
  rw [map_smul, dft_cyclicConvolution]
  funext j
  simp only [ZMod.dft_dft, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- **Gap 13.3.** The explicit Fourier similarity of a circulant, expressed
without needing a matrix inverse at a potentially empty index type. -/
theorem fourierMatrix_mul_circulant {n : ℕ} [NeZero n] (a : ZMod n → ℂ) :
    fourierMatrix n * Matrix.circulant a = Matrix.diagonal (ZMod.dft a) * fourierMatrix n := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.circulant_apply, fourierMatrix_apply,
    Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ZMod.dft_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ fun k ↦ ?_
  simp only [Equiv.subRight_apply]
  rw [mul_right_comm, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- The negative-exponent root of unity for a transform of length $n$. -/
def fourierRoot (n : ℕ) : ℂ := Complex.exp (-(2 * Real.pi / n : ℝ) * Complex.I)

/-- The defining formula of `fourierRoot`. -/
theorem fourierRoot_def (n : ℕ) :
    fourierRoot n = Complex.exp (-(2 * Real.pi / n : ℝ) * Complex.I) := by
  rfl

/-- Powers of `fourierRoot n` are the values of Mathlib's standard additive character of
`ZMod n` at negated residues; this links the `ℕ`-indexed radix-two convention to `ZMod.dft`. -/
theorem fourierRoot_pow (n : ℕ) [NeZero n] (m : ℕ) :
    fourierRoot n ^ m = ZMod.stdAddChar (-(m : ZMod n)) := by
  have hcast : (-(m : ZMod n)) = ((-(m : ℤ) : ℤ) : ZMod n) := by push_cast; rfl
  rw [hcast, ZMod.stdAddChar_coe, fourierRoot_def, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The radix-two even/odd recursion on an input of length $2^k$.
The value argument is only used at indices less than the transform length. -/
def radixTwoTransform : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, a, _ => a 0
  | k + 1, a, j =>
    let l := j % (2 ^ k)
    radixTwoTransform k (fun i ↦ a (2 * i)) l +
      fourierRoot (2 ^ (k + 1)) ^ j * radixTwoTransform k (fun i ↦ a (2 * i + 1)) l

/-- The radix-two recursion at length one returns the single input value. -/
theorem radixTwoTransform_zero (a : ℕ → ℂ) (j : ℕ) : radixTwoTransform 0 a j = a 0 := by
  rfl

/-- The radix-two butterfly: the transform of length `2 ^ (k + 1)` combines the even and
odd half-length transforms at the reduced frequency `j % 2 ^ k`. -/
theorem radixTwoTransform_succ (k : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    radixTwoTransform (k + 1) a j =
      radixTwoTransform k (fun i ↦ a (2 * i)) (j % 2 ^ k) +
        fourierRoot (2 ^ (k + 1)) ^ j * radixTwoTransform k (fun i ↦ a (2 * i + 1))
          (j % 2 ^ k) := by
  rfl

/-- **Gap 13.4.** The radix-two butterfly recursion computes the discrete
Fourier sum at every frequency `j : ℕ` (the sum is `2 ^ k`-periodic in `j`). -/
theorem radixTwoTransform_eq_sum (k : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    radixTwoTransform k a j =
      ∑ i : Fin (2 ^ k), a i.val * fourierRoot (2 ^ k) ^ (i.val * j) := by
  sorry

/-- **Gap 13.5.** Fourier sampling aliases exactly the congruent frequencies
when the continuous Fourier coefficients on `[0, 2π]` (Mathlib's `fourierCoeffOn`) are
absolutely summable. -/
theorem fourierCoeffOn_aliasing (f : ℝ → ℂ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi))
    (hs : Summable fun k : ℤ ↦ ‖fourierCoeffOn Real.two_pi_pos f k‖) {n : ℕ} (hn : 0 < n)
    (k : ℤ) :
    ((n : ℂ)⁻¹ * ∑ j : Fin n, f (2 * Real.pi * j.val / n) *
      fourierRoot n ^ ((j.val : ℤ) * k)) =
      ∑' l : ℤ, fourierCoeffOn Real.two_pi_pos f (k + l * n) := by
  sorry

/-- **Gap 13.6.** The $2n$ equispaced samples determine the $2n$ coefficients
in the half-open trigonometric frequency band. For `n = 0` both index types are empty. -/
theorem existsUnique_trigonometric_interpolant {n : ℕ} (y : Fin (2 * n) → ℂ) :
    ∃! c : Fin (2 * n) → ℂ, ∀ j : Fin (2 * n),
      (∑ k : Fin (2 * n), c k * Complex.exp
        (((k.val : ℝ) - n) * (Real.pi * j.val / n) * Complex.I)) = y j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i ↦ i.elim0, fun j ↦ j.elim0, fun _ _ ↦ funext fun i ↦ i.elim0⟩
  let θ (j : Fin (2 * n)) : ℝ := Real.pi * j.val / n
  let z (j : Fin (2 * n)) : ℂ := Circle.exp (θ j)
  let b (j : Fin (2 * n)) : ℂ := Complex.exp (-(n : ℂ) * θ j * Complex.I)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hθ (j : Fin (2 * n)) : θ j ∈ Set.Ico 0 (2 * Real.pi) := by
    have hj : (j.val : ℝ) < 2 * (n : ℝ) := by exact_mod_cast j.isLt
    refine ⟨by dsimp only [θ]; positivity, (div_lt_iff₀ hnR).2 ?_⟩
    linarith only [mul_lt_mul_of_pos_left hj Real.pi_pos]
  have hz : Function.Injective z := by
    intro i j hij
    have he := Circle.exp_injOn_Ico (sub_zero (2 * Real.pi)).le (hθ i) (hθ j)
      (Subtype.coe_injective hij)
    dsimp only [θ] at he
    apply Fin.ext
    exact_mod_cast mul_left_cancel₀ Real.pi_ne_zero ((div_left_inj₀ hnR.ne').mp he)
  let V := Matrix.vandermonde z
  let A := Matrix.diagonal b * V
  have hA : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_mul,
      Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ Complex.exp_ne_zero _)
      (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA y
  have hsample (d : Fin (2 * n) → ℂ) (j : Fin (2 * n)) :
      (A *ᵥ d) j = ∑ k : Fin (2 * n), d k * Complex.exp
        (((k.val : ℝ) - n) * (Real.pi * j.val / n) * Complex.I) := by
    simp only [Matrix.mulVec, dotProduct, A, Matrix.diagonal_mul, V, Matrix.vandermonde_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_comm _ (d k)]
    congr 1
    dsimp only [z, b]
    rw [Circle.coe_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    dsimp only [θ]
    push_cast
    ring
  refine ⟨c, fun j ↦ (hsample c j).symm.trans (congrFun hc j), fun d hd ↦ ?_⟩
  apply Matrix.mulVec_injective_of_isUnit hA
  funext j
  exact (hsample d j).trans ((hd j).trans (congrFun hc j).symm)

/-- **Gap 13.8.** A continuous integrable function whose Fourier transform vanishes at all
angular frequencies above `L` admits absolutely convergent cardinal reconstruction from its
samples with spacing `π / M`, `M ≥ L`. Mathlib's `𝓕` has `exp (-2πi x ξ)` in the integrand, so
angular frequency `2πξ` corresponds to `𝓕 f ξ`. -/
theorem tsum_sinc_smul_samples_eq {f : ℝ → ℂ} (hf : Continuous f) (hL1 : Integrable f)
    {L M : ℝ} (hL : 0 < L) (hM : L ≤ M)
    (hband : ∀ ξ : ℝ, L < 2 * Real.pi * |ξ| → 𝓕 f ξ = 0) (x : ℝ) :
    Summable (fun k : ℤ ↦ ‖Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)‖) ∧
      (∑' k : ℤ, Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)) = f x := by
  sorry

/-- The monic modal product decomposes into its leading term and lower coefficients
(`Polynomial.Monic.as_sum` at degree `n`). -/
private theorem prony_product_eq_X_pow_add_sum {n : ℕ} (z : Fin n → ℂ) :
    let P := ∏ j, (Polynomial.X - Polynomial.C (z j))
    Polynomial.X ^ n + ∑ k : Fin n, Polynomial.monomial k.val (P.coeff k.val) = P := by
  intro P
  have hmonic : P.Monic := Polynomial.monic_prod_X_sub_C z Finset.univ
  have hdegree : P.natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _
      (fun j _ ↦ Polynomial.monic_X_sub_C (z j))]
    simp
  conv_rhs => rw [hmonic.as_sum, hdegree]
  simp only [Fin.sum_univ_eq_sum_range (fun k ↦ Polynomial.monomial k (P.coeff k)),
    Polynomial.C_mul_X_pow_eq_monomial]

/-- The coefficients of the modal product satisfy the Hankel recurrence. -/
private theorem prony_product_solves {n : ℕ} (z c : Fin n → ℂ) (l : Fin n) :
    let P := ∏ j, (Polynomial.X - Polynomial.C (z j))
    let h := fun k : ℕ ↦ ∑ j, c j * z j ^ k
    (∑ k : Fin n, P.coeff k.val * h (k.val + l.val)) = -h (n + l.val) := by
  intro P h
  have hroot (j : Fin n) : P.eval (z j) = 0 := by
    dsimp only [P]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self (z j))
  have hcoeff (j : Fin n) : (∑ k : Fin n, P.coeff k.val * z j ^ k.val) = -(z j ^ n) := by
    have heval :
        (Polynomial.X ^ n + ∑ k : Fin n, Polynomial.monomial k.val (P.coeff k.val)).eval (z j) =
          P.eval (z j) :=
      congrArg (Polynomial.eval (z j)) (prony_product_eq_X_pow_add_sum z)
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, hroot] at heval
    linear_combination heval
  calc
    _ = ∑ j, (c j * z j ^ l.val) * (∑ k : Fin n, P.coeff k.val * z j ^ k.val) := by
      simp only [h, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      rw [pow_add]
      ring
    _ = _ := by
      simp only [h, hcoeff, pow_add, ← Finset.sum_neg_distrib, mul_neg]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring

/-- **Gap 13.10.** For distinct modes `z` and nonzero amplitudes `c`, the Hankel matrix of
the moments factors through the Vandermonde matrix and is nonsingular, the Prony annihilating
polynomial is uniquely determined by the Hankel equations and is the product of the modal
factors, and the amplitudes are the unique solution of the Vandermonde system. -/
theorem existsUnique_prony_annihilator {n : ℕ} (z c : Fin n → ℂ)
    (hz : Function.Injective z) (hc : ∀ j, c j ≠ 0) :
    let h := fun k : ℕ ↦ ∑ j, c j * z j ^ k
    let V : Matrix (Fin n) (Fin n) ℂ := fun k j ↦ z j ^ k.val
    let H : Matrix (Fin n) (Fin n) ℂ := fun k l ↦ h (k.val + l.val)
    let solves := fun p : Fin n → ℂ ↦ ∀ l : Fin n,
      (∑ k, p k * h (k.val + l.val)) = -h (n + l.val)
    H = V * Matrix.diagonal c * Vᵀ ∧ H.det ≠ 0 ∧ (∃! p, solves p) ∧
      (∀ p, solves p → (Polynomial.X ^ n + ∑ k : Fin n, Polynomial.monomial k.val (p k)) =
        ∏ j, (Polynomial.X - Polynomial.C (z j))) ∧
      ∀ d : Fin n → ℂ, V *ᵥ d = (fun k : Fin n ↦ h k.val) ↔ d = c := by
  classical
  intro h V H solves
  have hV : V = (Matrix.vandermonde z)ᵀ := by rfl
  have hVdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hz
  have hfactor : H = V * Matrix.diagonal c * Vᵀ := by
    ext k l
    rw [Matrix.mul_apply]
    dsimp only [H, h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.mul_diagonal c V k j, Matrix.transpose_apply, pow_add]
    dsimp only [V]
    ring
  have hHdet : H.det ≠ 0 := by
    rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hVdet (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hc i)) hVdet
  let P := ∏ j, (Polynomial.X - Polynomial.C (z j))
  let q : Fin n → ℂ := fun k ↦ P.coeff k.val
  have hq : solves q := prony_product_solves z c
  have hsol (p : Fin n → ℂ) (hp : solves p) : p = q := by
    apply Matrix.mulVec_injective_of_det_ne_zero hHdet
    funext l
    simpa only [Matrix.mulVec, dotProduct, H, Nat.add_comm, mul_comm] using (hp l).trans (hq l).symm
  refine ⟨hfactor, hHdet, ⟨q, hq, hsol⟩, fun p hp ↦ ?_, fun d ↦ ?_⟩
  · rw [hsol p hp]
    exact prony_product_eq_X_pow_add_sum z
  · have hcV : V *ᵥ c = fun k : Fin n ↦ h k.val := by
      funext k
      simp only [Matrix.mulVec, dotProduct, V, h, mul_comm]
    rw [← hcV]
    exact (Matrix.mulVec_injective_of_det_ne_zero hVdet).eq_iff

/-- **Gap 13.10.** Two exponential sums with nonzero coefficients and distinct exponents
in the same principal strip agree up to relabelling if their first `2 * n` samples agree. -/
theorem exists_perm_of_expSum_samples_eq {n : ℕ}
    (φ ψ c d : Fin n → ℂ) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hc : ∀ j, c j ≠ 0) (hd : ∀ j, d j ≠ 0)
    (hφim : ∀ j, (φ j).im ∈ Set.Ico (-Real.pi) Real.pi)
    (hψim : ∀ j, (ψ j).im ∈ Set.Ico (-Real.pi) Real.pi)
    (hsamples : ∀ k : Fin (2 * n),
      (∑ j, c j * Complex.exp (φ j * k.val)) = ∑ j, d j * Complex.exp (ψ j * k.val)) :
    ∃ e : Equiv.Perm (Fin n), ∀ j, φ j = ψ (e j) ∧ c j = d (e j) := by
  classical
  let z : Fin n → ℂ := Complex.exp ∘ φ
  let w : Fin n → ℂ := Complex.exp ∘ ψ
  have hz : Function.Injective z := fun i j h ↦
    hφ (exp_injOn_im_mem_Ico (hφim i) (hφim j) h)
  have hw : Function.Injective w := fun i j h ↦
    hψ (exp_injOn_im_mem_Ico (hψim i) (hψim j) h)
  have hs (k : ℕ) (hk : k < 2 * n) : (∑ j, c j * z j ^ k) = ∑ j, d j * w j ^ k := by
    simpa only [z, w, Function.comp_apply, ← Complex.exp_nat_mul, mul_comm (k : ℂ)] using
      hsamples ⟨k, hk⟩
  obtain ⟨_, _, ⟨p, hp, _⟩, hpz, hcz⟩ := existsUnique_prony_annihilator z c hz hc
  obtain ⟨_, _, _, hpw, _⟩ := existsUnique_prony_annihilator w d hw hd
  have hp' (l : Fin n) :
      (∑ k : Fin n, p k * (∑ j, d j * w j ^ (k.val + l.val))) =
        -(∑ j, d j * w j ^ (n + l.val)) := by
    have hkl (k : Fin n) : k.val + l.val < 2 * n := by omega
    have hnl : n + l.val < 2 * n := by omega
    simpa only [← hs _ hnl, fun k : Fin n ↦ (hs _ (hkl k)).symm] using hp l
  obtain ⟨e, he⟩ := exists_perm_of_prod_X_sub_C_eq hz ((hpz p hp).symm.trans (hpw p hp'))
  have hcd : (fun i ↦ d (e i)) = c := by
    apply (hcz _).mp
    funext k
    calc
      _ = ∑ j, d j * w j ^ k.val := by
        dsimp only [Matrix.mulVec, dotProduct]
        refine Fintype.sum_equiv e _ _ fun i ↦ ?_
        rw [he i, mul_comm]
      _ = _ := (hs k.val (by omega)).symm
  exact ⟨e, fun j ↦
    ⟨exp_injOn_im_mem_Ico (hφim j) (hψim (e j)) (he j), (congrFun hcd j).symm⟩⟩

end NASC
