module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Matrix functions and matrix equations

Hermite interpolation on Jordan blocks, contour and power-series calculus, and Sylvester
and Lyapunov equations. See gaps 6.1–6.7.
The Jordan block proofs use Mathlib's polynomial Taylor and Hasse derivative identities.

## Main definitions

* `NASC.jordanBlock n z`: the `n × n` Jordan block with eigenvalue `z`.
* `NASC.matrixFunctionOnCircle f c r A`: the Cauchy integral of `f` against the resolvent of
  `A` over the circle of center `c` and radius `r`.
* `NASC.sylvesterLinearMap A B`: the operator `X ↦ A * X - X * B`.

## Main results

* `NASC.aeval_jordanBlock_apply_hasseDeriv`, `NASC.aeval_jordanBlock_apply`: polynomials of a
  Jordan block are upper triangular Toeplitz matrices of (Hasse) derivatives.
* `NASC.pow_jordanBlock_apply`: the binomial formula for the powers of a Jordan block.
* `NASC.existsUnique_polynomial_iteratedDerivative`: Hermite interpolation.
* `NASC.summable_smul_pow_jordanBlock_iff`, `NASC.matrixFunctionOnCircle_jordanBlock_apply`:
  power-series and contour calculus on a Jordan block.
* `NASC.exists_hasFDerivAt_matrixFunctionOnCircle_fromBlocks`: the Fréchet derivative as an
  off-diagonal block.
* `NASC.spectrum_sylvesterLinearMap`, `NASC.sylvester_integral_spec`,
  `NASC.lyapunov_integral_spec`: Sylvester and Lyapunov equations.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix Matrix.Norms.L2Operator
open MeasureTheory Matrix Polynomial

/-- The size-$n$ Jordan block with eigenvalue $z$. -/
def jordanBlock {𝕜 : Type*} [Ring 𝕜] (n : ℕ) (z : 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun i j ↦ if i = j then z else if j.val = i.val + 1 then 1 else 0

/-- The entries of a Jordan block. -/
theorem jordanBlock_apply {𝕜 : Type*} [Ring 𝕜] (n : ℕ) (z : 𝕜) (i j : Fin n) :
    jordanBlock n z i j = if i = j then z else if j.val = i.val + 1 then 1 else 0 := by
  unfold jordanBlock
  rfl

/-- The nilpotent Jordan block has ones on its first superdiagonal. -/
theorem jordanBlock_zero_apply {𝕜 : Type*} [Ring 𝕜] {n : ℕ} (i j : Fin n) :
    jordanBlock n (0 : 𝕜) i j = if j.val = i.val + 1 then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [jordanBlock]
  · simp only [jordanBlock, ite_eq_right h]

/-- The powers of the nilpotent Jordan block shift along successive superdiagonals. -/
theorem pow_jordanBlock_zero_apply {𝕜 : Type*} [Ring 𝕜] {n : ℕ}
    (k : ℕ) (i j : Fin n) :
    (jordanBlock n (0 : 𝕜) ^ k) i j = if j.val = i.val + k then 1 else 0 := by
  induction k generalizing i with
  | zero =>
    have h : j.val = i.val ↔ i = j := by rw [eq_comm, Fin.val_inj]
    simp only [pow_zero, Matrix.one_apply, Nat.add_zero, h]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [jordanBlock_zero_apply]
    by_cases hi : i.val + 1 < n
    · let a : Fin n := ⟨i.val + 1, hi⟩
      rw [Finset.sum_eq_single a]
      · have h : j.val = a.val + k ↔ j.val = i.val + k.succ := by
          dsimp only [a]
          omega
        rw [ite_eq_left rfl, one_mul, ih]
        simp only [h]
      · intro b _ hb
        have h : b.val ≠ i.val + 1 := fun he ↦ hb (Fin.ext he)
        simp only [ite_eq_right h, zero_mul]
      · simp
    · have h (b : Fin n) : b.val ≠ i.val + 1 := by omega
      have hj : j.val ≠ i.val + k.succ := by omega
      simp only [h, ite_eq_right hj, ite_false, zero_mul, Finset.sum_const_zero]

/-- On the nilpotent block a polynomial has its coefficients on the superdiagonals. -/
theorem aeval_jordanBlock_zero_apply {R : Type*} [CommRing R] {n : ℕ} (p : R[X])
    (i j : Fin n) :
    (Polynomial.aeval (jordanBlock n (0 : R)) p) i j =
      if i ≤ j then p.coeff (j.val - i.val) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    by_cases h : i ≤ j
    · simp only [map_add, Matrix.add_apply, hp, hq, ite_eq_left h, Polynomial.coeff_add]
    · simp only [map_add, Matrix.add_apply, hp, hq, ite_eq_right h, add_zero]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def, Matrix.smul_apply,
      pow_jordanBlock_zero_apply]
    by_cases h : i ≤ j
    · have he : j.val = i.val + k ↔ j.val - i.val = k := by
        omega
      simp only [ite_eq_left h, he, Polynomial.coeff_monomial]
      by_cases hd : j.val - i.val = k
      · simp [hd]
      · simp [hd]
    · have he : j.val ≠ i.val + k := by
        omega
      simp only [ite_eq_right h, ite_eq_right he, smul_zero]

/-- Polynomial evaluation on a Jordan block over a commutative ring is the upper triangular
Toeplitz matrix of Hasse derivatives. -/
theorem aeval_jordanBlock_apply_hasseDeriv {R : Type*} [CommRing R] {n : ℕ} (p : R[X]) (z : R)
    (i j : Fin n) :
    (Polynomial.aeval (jordanBlock n z) p) i j =
      if i ≤ j then (Polynomial.hasseDeriv (j.val - i.val) p).eval z else 0 := by
  let S := jordanBlock n (0 : R)
  have hsplit : S + algebraMap R (Matrix (Fin n) (Fin n) R) z = jordanBlock n z := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext a b
    by_cases h : a = b
    · subst b
      simp [S, jordanBlock, Matrix.smul_apply]
    · simp [S, jordanBlock, Matrix.smul_apply, h]
  have ht : Polynomial.aeval S (Polynomial.taylor z p) =
      Polynomial.aeval (jordanBlock n z) p := by
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp, map_add, Polynomial.aeval_X,
      Polynomial.aeval_C, hsplit]
  rw [← ht, aeval_jordanBlock_zero_apply]
  by_cases h : i ≤ j
  · simp only [ite_eq_left h, Polynomial.taylor_coeff]
  · simp only [ite_eq_right h]

/-- **Gap 6.1.** Polynomial evaluation on a Jordan block is the upper triangular
Toeplitz matrix of normalized derivatives. -/
theorem aeval_jordanBlock_apply {K : Type*} [Field K] [CharZero K] {n : ℕ} (p : K[X]) (z : K)
    (i j : Fin n) :
    (Polynomial.aeval (jordanBlock n z) p) i j =
      if i ≤ j then (Polynomial.derivative^[j.val - i.val] p).eval z / (j.val - i.val).factorial
      else 0 := by
  rw [aeval_jordanBlock_apply_hasseDeriv]
  by_cases h : i ≤ j
  · simp only [ite_eq_left h]
    let k := j.val - i.val
    have hfact : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hd : Polynomial.derivative^[k] p = k.factorial • Polynomial.hasseDeriv k p :=
      (congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := k)) p).symm
    rw [hd, Polynomial.eval_smul, nsmul_eq_mul]
    exact (eq_div_iff hfact).mpr (mul_comm _ _)
  · simp only [ite_eq_right h]

/-- **Gap 6.1.** Given jet data at distinct eigenvalues, the Hermite interpolant is
uniquely determined in degrees smaller than the sum of the requested multiplicities. When all
multiplicities vanish the interpolant is the zero polynomial. -/
theorem existsUnique_polynomial_iteratedDerivative {K : Type*} [Field K] [CharZero K] {s : ℕ}
    (z : Fin s → K) (hz : Function.Injective z) (m : Fin s → ℕ)
    (jet : ∀ i, Fin (m i) → K) :
    ∃! p : K[X], p.degree < (∑ i, m i : ℕ) ∧
      ∀ i j, (Polynomial.derivative^[j.val] p).eval (z i) = jet i j := by
  sorry

/-- Holomorphic functional calculus by the positively oriented circle that encloses the
spectrum. The use theorems require the radius and spectral containment explicitly. -/
def matrixFunctionOnCircle {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    circleIntegral (fun z ↦ f z • (z • (1 : Matrix n n ℂ) - A)⁻¹) c r

/-- The defining formula for `matrixFunctionOnCircle`. -/
theorem matrixFunctionOnCircle_def {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (A : Matrix n n ℂ) :
    matrixFunctionOnCircle f c r A = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      circleIntegral (fun z ↦ f z • (z • (1 : Matrix n n ℂ) - A)⁻¹) c r := by
  unfold matrixFunctionOnCircle
  rfl

/-- Entries of a Jordan-block power are the corresponding binomial coefficients times
powers of its eigenvalue. -/
theorem pow_jordanBlock_apply {R : Type*} [CommRing R] {n : ℕ} (z : R) (k : ℕ) (i j : Fin n) :
    (jordanBlock n z ^ k) i j =
      if i ≤ j then (k.choose (j.val - i.val) : R) * z ^ (k - (j.val - i.val)) else 0 := by
  have h := aeval_jordanBlock_apply_hasseDeriv (Polynomial.X ^ k) z i j
  rw [map_pow, Polynomial.aeval_X] at h
  rw [h, ← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial,
    Polynomial.eval_monomial, mul_one]

/-- **Gap 6.2.** The Jordan-block power series converges precisely when its scalar
entry series, indexed by the derivatives up to the size of the block, converge. -/
theorem summable_smul_pow_jordanBlock_iff {n : ℕ} (a : ℕ → ℂ) (z : ℂ) :
    Summable (fun k ↦ a k • jordanBlock n z ^ k) ↔
      ∀ j : Fin n, Summable (fun k ↦ if j.val ≤ k then
        a k * (k.choose j.val : ℂ) * z ^ (k - j.val) else 0) := by
  have hterm (i j : Fin n) (hij : i ≤ j) (k : ℕ) :
      (a k • jordanBlock n z ^ k) i j =
        if j.val - i.val ≤ k then
          a k * (k.choose (j.val - i.val) : ℂ) * z ^ (k - (j.val - i.val)) else 0 := by
    rw [Matrix.smul_apply, smul_eq_mul, pow_jordanBlock_apply, ite_eq_left hij]
    by_cases hk : j.val - i.val ≤ k
    · rw [ite_eq_left hk, mul_assoc]
    · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk), Nat.cast_zero,
        zero_mul, mul_zero]
  have hmatrix : Summable (fun k ↦ a k • jordanBlock n z ^ k) ↔
      ∀ i j, Summable (fun k ↦ (a k • jordanBlock n z ^ k) i j) := by
    constructor
    · intro h i j
      exact Pi.summable.mp (Pi.summable.mp h i) j
    · intro h
      exact Pi.summable.mpr fun i ↦ Pi.summable.mpr (h i)
  rw [hmatrix]
  constructor
  · intro h j
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    let i : Fin n := ⟨0, hn⟩
    have hij : i ≤ j := Nat.zero_le _
    have hh := h i j
    simp only [hterm i j hij, i, Nat.sub_zero] at hh
    exact hh
  · intro h i j
    by_cases hij : i ≤ j
    · let d : Fin n := ⟨j.val - i.val, (Nat.sub_le _ _).trans_lt j.isLt⟩
      simpa only [d, hterm i j hij] using h d
    · simp only [Matrix.smul_apply, pow_jordanBlock_apply, ite_eq_right hij, smul_zero]
      exact summable_zero

/-- **Gap 6.2.** The contour functional calculus on a Jordan block uses the scalar
derivatives of the holomorphic function. -/
theorem matrixFunctionOnCircle_jordanBlock_apply {n : ℕ}
    (f : ℂ → ℂ) (c z : ℂ) {r : ℝ} (hz : z ∈ Metric.ball c r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r)) (i j : Fin n) :
    matrixFunctionOnCircle f c r (jordanBlock n z) i j =
      if i ≤ j then iteratedDeriv (j.val - i.val) f z / (j.val - i.val).factorial
      else 0 := by
  sorry

/-- **Gap 6.4.** The Fréchet derivative of the contour functional calculus appears as the
upper-right block of the same function evaluated on the block triangular input. -/
theorem exists_hasFDerivAt_matrixFunctionOnCircle_fromBlocks {n : ℕ}
    (f : ℂ → ℂ) (c : ℂ) {r : ℝ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hA : spectrum ℂ A ⊆ Metric.ball c r) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ,
      HasFDerivAt (matrixFunctionOnCircle f c r) L A ∧
        ∀ E, matrixFunctionOnCircle f c r (Matrix.fromBlocks A E 0 A) =
          Matrix.fromBlocks (matrixFunctionOnCircle f c r A) (L E) 0
            (matrixFunctionOnCircle f c r A) := by
  sorry

/-- The Sylvester linear operator $X \mapsto AX-XB$. -/
def sylvesterLinearMap {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
    (A : Matrix m m R) (B : Matrix n n R) : Matrix m n R →ₗ[R] Matrix m n R :=
  mulLeftLinearMap n R A - mulRightLinearMap m R B

/-- The Sylvester operator maps `X` to `A * X - X * B`. -/
theorem sylvesterLinearMap_apply {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
    (A : Matrix m m R) (B : Matrix n n R) (X : Matrix m n R) :
    sylvesterLinearMap A B X = A * X - X * B := by
  unfold sylvesterLinearMap
  rfl

/-- **Gap 6.6.** The Sylvester spectrum consists of differences of eigenvalues. -/
theorem spectrum_sylvesterLinearMap {K m n : Type*} [Field K] [IsAlgClosed K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix n n K) :
    spectrum K (sylvesterLinearMap A B) =
      {z | ∃ a ∈ spectrum K A, ∃ b ∈ spectrum K B, z = a - b} := by
  sorry

/-- **Gap 6.6.** The half-line integral solves the Sylvester equation for operators
with spectra in opposite open half-planes. -/
theorem sylvester_integral_spec {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hA : ∀ z ∈ spectrum ℂ A, 0 < z.re) (hB : ∀ z ∈ spectrum ℂ B, z.re < 0) :
    let X := ∫ t in Set.Ioi (0 : ℝ), NormedSpace.exp (-(t : ℂ) • A) * C *
      NormedSpace.exp ((t : ℂ) • B)
    A * X - X * B = C ∧ ∀ Y, A * Y - Y * B = C → Y = X := by
  sorry

open scoped ComplexOrder in
/-- **Gap 6.7.** A stable matrix admits a unique Lyapunov solution given by the
half-line Gramian integral. Positive semidefiniteness and definiteness are preserved. -/
theorem lyapunov_integral_spec {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ z ∈ spectrum ℂ A, z.re < 0) :
    let X := ∫ t in Set.Ioi (0 : ℝ),
      NormedSpace.exp ((t : ℂ) • A) * C * NormedSpace.exp ((t : ℂ) • Aᴴ)
    A * X + X * Aᴴ + C = 0 ∧ (∀ Y, A * Y + Y * Aᴴ + C = 0 → Y = X) ∧
      (C.PosSemidef → X.PosSemidef) ∧ (C.PosDef → X.PosDef) := by
  sorry

end NASC
