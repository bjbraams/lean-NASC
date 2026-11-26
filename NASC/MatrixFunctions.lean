module

public import NASC.EigenvalueMethods
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Matrix functions and matrix equations

Hermite interpolation on Jordan blocks, contour and power-series calculus, and Sylvester
and Lyapunov equations. See gaps 6.1–6.7.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix BigOperators Matrix.Norms.L2Operator
open MeasureTheory Matrix Polynomial

/-- The size-$n$ Jordan block with eigenvalue $z$. -/
def jordanBlock {𝕜 : Type*} [Ring 𝕜] (n : ℕ) (z : 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun i j ↦ if i = j then z else if j.val = i.val + 1 then 1 else 0

/-- **Gap 6.1.** Polynomial evaluation on a Jordan block is the upper triangular
Toeplitz matrix of normalized derivatives. -/
theorem aeval_jordanBlock_apply {n : ℕ} (p : ℂ[X]) (z : ℂ) (i j : Fin n) :
    (Polynomial.aeval (jordanBlock n z) p) i j =
      if i ≤ j then (Polynomial.derivative^[j.val - i.val] p).eval z / (j.val - i.val).factorial
      else 0 := by
  sorry

/-- **Gap 6.1.** Given jet data at distinct eigenvalues, the Hermite interpolant is
uniquely determined in degrees smaller than the sum of the requested multiplicities. -/
theorem existsUnique_polynomial_iteratedDerivative {s : ℕ}
    (z : Fin s → ℂ) (hz : Function.Injective z) (m : Fin s → ℕ)
    (hm : 0 < ∑ i, m i) (jet : ∀ i, Fin (m i) → ℂ) :
    ∃! p : ℂ[X], p.natDegree < ∑ i, m i ∧
      ∀ i j, (Polynomial.derivative^[j.val] p).eval (z i) = jet i j := by
  sorry

/-- Holomorphic functional calculus by the positively oriented circle that encloses the
spectrum. The use theorems require the radius and spectral containment explicitly. -/
def matrixFunctionOnCircle {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    circleIntegral (fun z ↦ f z • (z • (1 : Matrix n n ℂ) - A)⁻¹) c r

/-- **Gap 6.2.** The Jordan-block power series converges precisely when its scalar
entry series, indexed by the derivatives up to the size of the block, converge. -/
theorem summable_smul_pow_jordanBlock_iff {n : ℕ} (a : ℕ → ℂ) (z : ℂ) :
    Summable (fun k ↦ a k • jordanBlock n z ^ k) ↔
      ∀ j : Fin n, Summable (fun k ↦ if j.val ≤ k then
        a k * (k.choose j.val : ℂ) * z ^ (k - j.val) else 0) := by
  sorry

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
    (f : ℂ → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) (A : Matrix (Fin n) (Fin n) ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r))
    (hA : spectrum ℂ A ⊆ Metric.ball c r) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ,
      HasFDerivAt (matrixFunctionOnCircle f c r) L A ∧
        ∀ E, matrixFunctionOnCircle f c r (Matrix.fromBlocks A E 0 A) =
          Matrix.fromBlocks (matrixFunctionOnCircle f c r A) (L E) 0
            (matrixFunctionOnCircle f c r A) := by
  sorry

/-- The Sylvester linear operator $X \mapsto AX-XB$. -/
def sylvesterLinearMap {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin n) ℂ :=
  mulLeftLinearMap (Fin n) ℂ A - mulRightLinearMap (Fin m) ℂ B

/-- **Gap 6.6.** The Sylvester spectrum consists of differences of eigenvalues. -/
theorem spectrum_sylvesterLinearMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ (sylvesterLinearMap A B) =
      {z | ∃ a ∈ spectrum ℂ A, ∃ b ∈ spectrum ℂ B, z = a - b} := by
  sorry

/-- **Gap 6.6.** The half-line integral solves the Sylvester equation for operators
with spectra in opposite open half-planes. -/
theorem isUnique_sylvester_integral {m n : ℕ}
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
theorem lyapunov_integral {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ z ∈ spectrum ℂ A, z.re < 0) :
    let X := ∫ t in Set.Ioi (0 : ℝ),
      NormedSpace.exp ((t : ℂ) • A) * C * NormedSpace.exp ((t : ℂ) • Aᴴ)
    A * X + X * Aᴴ + C = 0 ∧ (∀ Y, A * Y + Y * Aᴴ + C = 0 → Y = X) ∧
      (C.PosSemidef → X.PosSemidef) ∧ (C.PosDef → X.PosDef) := by
  sorry

end NASC
