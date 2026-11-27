module

public import NASC.Quadrature
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

import Mathlib.LinearAlgebra.Vandermonde

/-!
# Discrete Fourier analysis and sampling

Fourier matrices, circulants, radix-two recursion, aliasing, trigonometric interpolation,
Shannon sampling and Prony reconstruction. The cyclic formulas use Mathlib's
unnormalized ZMod Fourier transform and its standard additive character. Prony reconstruction
uses Mathlib's Vandermonde nonsingularity criterion.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Filter
open scoped Matrix BigOperators Interval

/-- The unnormalized cyclic Fourier matrix in the negative-exponent convention. -/
def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j ↦ ZMod.stdAddChar (-(i * j))

/-- The entry in row `i` and column `j` of the Fourier matrix. -/
theorem fourierMatrix_apply (n : ℕ) [NeZero n] (i j : ZMod n) :
    fourierMatrix n i j = ZMod.stdAddChar (-(i * j)) := by
  unfold fourierMatrix
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
  unfold cyclicConvolution
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
    fourierMatrix n * (Matrix.of fun i j ↦ a (i - j)) =
      Matrix.diagonal (ZMod.dft a) * fourierMatrix n := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, fourierMatrix_apply, Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ZMod.dft_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ fun k ↦ ?_
  simp only [Equiv.subRight_apply]
  rw [mul_right_comm, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- The negative-exponent root of unity for a transform of length $n$. -/
def fourierRoot (n : ℕ) : ℂ := Complex.exp (-(2 * Real.pi / n : ℝ) * Complex.I)

/-- The radix-two even/odd recursion on an input of length $2^k$.
The value argument is only used at indices less than the transform length. -/
def radixTwoTransform : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, a, _ => a 0
  | k + 1, a, j =>
    let l := j % (2 ^ k)
    radixTwoTransform k (fun i ↦ a (2 * i)) l +
      fourierRoot (2 ^ (k + 1)) ^ j * radixTwoTransform k (fun i ↦ a (2 * i + 1)) l

/-- **Gap 13.4.** The radix-two butterfly recursion computes the discrete
Fourier sum at every frequency in its transform block. -/
theorem radixTwoTransform_eq_sum (k : ℕ) (a : ℕ → ℂ) (j : Fin (2 ^ k)) :
    radixTwoTransform k a j.val =
      ∑ i : Fin (2 ^ k), a i.val * fourierRoot (2 ^ k) ^ (i.val * j.val) := by
  sorry

/-- The continuous periodic Fourier coefficient with period $2\pi$. -/
def periodicFourierCoeff (f : ℝ → ℂ) (k : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(k : ℂ) * x * Complex.I) * f x

/-- **Gap 13.5.** Fourier sampling aliases exactly the congruent frequencies
when the continuous Fourier coefficients are absolutely summable. -/
theorem periodicFourierCoeff_aliasing (f : ℝ → ℂ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi))
    (hs : Summable fun k : ℤ ↦ ‖periodicFourierCoeff f k‖) {n : ℕ} (hn : 0 < n) (k : ℤ) :
    ((n : ℂ)⁻¹ * ∑ j : Fin n, f (2 * Real.pi * j.val / n) *
      fourierRoot n ^ ((j.val : ℤ) * k)) =
      ∑' l : ℤ, periodicFourierCoeff f (k + l * n) := by
  sorry

/-- **Gap 13.6.** The $2n$ equispaced samples determine the $2n$ coefficients
in the half-open trigonometric frequency band. -/
theorem existsUnique_trigonometricInterpolate {n : ℕ} (hn : 0 < n) (y : Fin (2 * n) → ℂ) :
    ∃! c : Fin (2 * n) → ℂ, ∀ j : Fin (2 * n),
      (∑ k : Fin (2 * n), c k * Complex.exp
        (((k.val : ℝ) - n) * (Real.pi * j.val / n) * Complex.I)) = y j := by
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

/-- **Gap 13.8.** A continuous integrable bandlimited function admits absolutely
convergent cardinal reconstruction from its equally spaced samples. -/
theorem shannon_sum_eq {f : ℝ → ℂ} (hf : Continuous f) (hL1 : Integrable f)
    {L M : ℝ} (hL : 0 < L) (hM : L ≤ M)
    (hband : ∀ ξ : ℝ, L < |ξ| →
      (∫ y : ℝ, Complex.exp (-(ξ : ℂ) * y * Complex.I) * f y) = 0) (x : ℝ) :
    Summable (fun k : ℤ ↦ ‖Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)‖) ∧
      (∑' k : ℤ, Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)) = f x := by
  sorry

/-- The monic modal product decomposes into its leading term and lower coefficients. -/
private theorem prony_product_eq_X_pow_add_sum {n : ℕ} (z : Fin n → ℂ) :
    let P := ∏ j, (Polynomial.X - Polynomial.C (z j))
    Polynomial.X ^ n + ∑ k : Fin n, Polynomial.monomial k.val (P.coeff k.val) = P := by
  intro P
  have hmonic : P.Monic := Polynomial.monic_prod_X_sub_C z Finset.univ
  have hdegree : P.natDegree = n := by
    dsimp only [P]
    rw [Polynomial.natDegree_prod_of_monic Finset.univ _
      (fun j _ ↦ Polynomial.monic_X_sub_C (z j))]
    simp
  have hlead : P.coeff n = 1 := hdegree ▸ hmonic.coeff_natDegree
  have hsum := P.as_sum_range' (n + 1) (hdegree ▸ Nat.lt_succ_self n)
  simpa only [Finset.sum_range_succ, hlead, ← Fin.sum_univ_eq_sum_range,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul, add_comm] using hsum.symm

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

/-- **Gap 13.10.** The Prony annihilating polynomial is uniquely determined
by the Hankel equations and is the product of the distinct modal factors. -/
theorem prony_annihilator_unique {n : ℕ} (z c : Fin n → ℂ)
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

/-- The complex exponential is injective on the half-open strip used for modal exponents. -/
private theorem prony_exp_injOn :
    Set.InjOn Complex.exp {x | x.im ∈ Set.Ico (-Real.pi) Real.pi} := by
  intro x hx y hy he
  simp only [Set.mem_ofPred_eq, Set.mem_Ico] at hx hy
  have hneg : Complex.exp (-x) = Complex.exp (-y) := by
    rw [Complex.exp_neg, Complex.exp_neg, he]
  apply neg_injective
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ hneg
  · simpa only [Complex.neg_im, neg_lt_neg_iff] using hx.2
  · simpa only [Complex.neg_im, neg_neg] using neg_le_neg hx.1
  · simpa only [Complex.neg_im, neg_lt_neg_iff] using hy.2
  · simpa only [Complex.neg_im, neg_neg] using neg_le_neg hy.1

/-- The roots of equal modal products match under a permutation. -/
private theorem prony_reindex {n : ℕ} {z w : Fin n → ℂ} (hz : Function.Injective z)
    (hp : (∏ i, (Polynomial.X - Polynomial.C (z i))) =
      ∏ i, (Polynomial.X - Polynomial.C (w i))) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, z i = w (e i) := by
  classical
  have hmatch (i : Fin n) : ∃ j, z i = w j := by
    have hroot : (∏ j : Fin n, (z i - z j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i))
    have heval := congrArg (Polynomial.eval (z i)) hp
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, hroot] at heval
    simpa only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using heval.symm
  choose e he using hmatch
  have hinj : Function.Injective e := fun i j h ↦ hz ((he i).trans (by rw [h, ← he j]))
  exact ⟨Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj), he⟩

/-- **Gap 13.10.** Two exponential sums with nonzero coefficients and distinct exponents
in the same principal strip agree up to relabelling if their first `2 * n` samples agree. -/
theorem prony_exp_eq_up_to_reindexing {n : ℕ}
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
  have hz : Function.Injective z := fun i j h ↦ hφ (prony_exp_injOn (hφim i) (hφim j) h)
  have hw : Function.Injective w := fun i j h ↦ hψ (prony_exp_injOn (hψim i) (hψim j) h)
  have hs (k : ℕ) (hk : k < 2 * n) : (∑ j, c j * z j ^ k) = ∑ j, d j * w j ^ k := by
    simpa only [z, w, Function.comp_apply, ← Complex.exp_nat_mul, mul_comm (k : ℂ)] using
      hsamples ⟨k, hk⟩
  obtain ⟨_, _, ⟨p, hp, _⟩, hpz, hcz⟩ := prony_annihilator_unique z c hz hc
  obtain ⟨_, _, _, hpw, _⟩ := prony_annihilator_unique w d hw hd
  have hp' (l : Fin n) :
      (∑ k : Fin n, p k * (∑ j, d j * w j ^ (k.val + l.val))) =
        -(∑ j, d j * w j ^ (n + l.val)) := by
    have hkl (k : Fin n) : k.val + l.val < 2 * n := by omega
    have hnl : n + l.val < 2 * n := by omega
    simpa only [← hs _ hnl, fun k : Fin n ↦ (hs _ (hkl k)).symm] using hp l
  obtain ⟨e, he⟩ := prony_reindex hz ((hpz p hp).symm.trans (hpw p hp'))
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
    ⟨prony_exp_injOn (hφim j) (hψim (e j)) (he j), (congrFun hcd j).symm⟩⟩

end NASC
