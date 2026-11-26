module

public import NASC.Quadrature
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Discrete Fourier analysis and sampling

Fourier matrices, circulants, radix-two recursion, aliasing, trigonometric interpolation,
Shannon sampling and Prony reconstruction. The cyclic formulas use Mathlib's
unnormalized ZMod Fourier transform and its standard additive character.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Filter
open scoped Matrix BigOperators Interval

/-- The unnormalized cyclic Fourier matrix in the negative-exponent convention. -/
def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j ↦ ZMod.stdAddChar (-(i * j))

/-- **Gap 13.1.** The cyclic Fourier matrix has Gram matrix $nI$ and acts by the
bundled discrete Fourier transform. -/
theorem fourierMatrix_gram_mulVec (n : ℕ) [NeZero n] :
    (fourierMatrix n)ᴴ * fourierMatrix n = (n : ℂ) • 1 ∧
      ∀ x : ZMod n → ℂ, fourierMatrix n *ᵥ x = ZMod.dft x := by
  sorry

/-- Cyclic convolution on a finite cyclic group. -/
def cyclicConvolution {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j ↦ ∑ k, a k * b (j - k)

/-- **Gap 13.2.** The Fourier transform interchanges cyclic convolution and
pointwise multiplication with the unnormalized scale factor. -/
theorem dft_cyclicConvolution_and_mul {n : ℕ} [NeZero n] (a b : ZMod n → ℂ) :
    ZMod.dft (cyclicConvolution a b) = ZMod.dft a * ZMod.dft b ∧
      (n : ℂ) • ZMod.dft (a * b) = cyclicConvolution (ZMod.dft a) (ZMod.dft b) := by
  sorry

/-- **Gap 13.3.** The explicit Fourier similarity of a circulant, expressed
without needing a matrix inverse at a potentially empty index type. -/
theorem fourierMatrix_mul_circulant {n : ℕ} [NeZero n] (a : ZMod n → ℂ) :
    fourierMatrix n * (Matrix.of fun i j ↦ a (i - j)) =
      Matrix.diagonal (ZMod.dft a) * fourierMatrix n := by
  sorry

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
  sorry

/-- **Gap 13.8.** A continuous integrable bandlimited function admits absolutely
convergent cardinal reconstruction from its equally spaced samples. -/
theorem shannon_sum_eq {f : ℝ → ℂ} (hf : Continuous f) (hL1 : Integrable f)
    {L M : ℝ} (hL : 0 < L) (hM : L ≤ M)
    (hband : ∀ ξ : ℝ, L < |ξ| →
      (∫ y : ℝ, Complex.exp (-(ξ : ℂ) * y * Complex.I) * f y) = 0) (x : ℝ) :
    Summable (fun k : ℤ ↦ ‖Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)‖) ∧
      (∑' k : ℤ, Real.sinc (M * x - k * Real.pi) • f (k * Real.pi / M)) = f x := by
  sorry

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
  sorry

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
  sorry

end NASC
