module

public import NASC.InitialValueProblems
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Stiff problems and geometric integration

Runge--Kutta and multistep stability, regular differential-algebraic pencils, exponential
Euler, quadratic invariants, modified equations and splitting. See section 15.
-/

public section

noncomputable section

namespace NASC

open Set Filter Matrix Asymptotics Polynomial
open scoped Matrix BigOperators Topology Interval Matrix.Norms.L2Operator

/-- **Gap 15.1.** The stability function of a Runge--Kutta tableau equals
the determinant quotient whenever the stage matrix is invertible. -/
theorem RungeKuttaTableau.stabilityFunction_eq_detRatio {s : ℕ}
    (T : RungeKuttaTableau s) (z : ℂ) :
    let M : Matrix (Fin s) (Fin s) ℂ := 1 - z • T.A.map Complex.ofReal
    let b : Fin s → ℂ := fun i ↦ T.b i
    let e : Fin s → ℂ := fun _ ↦ 1
    M.det ≠ 0 →
      1 + z * dotProduct b (M⁻¹ *ᵥ e) = (M + z • vecMulVec e b).det / M.det := by
  sorry

/-- Numerator polynomial for the type $(k,j)$ Padé approximant to the exponential. -/
def expPadeNumerator (k j : ℕ) : ℂ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.monomial m (((k.factorial : ℂ) * (j + k - m).factorial) /
      ((j + k).factorial * m.factorial * (k - m).factorial))

/-- **Gap 15.3.** Padé approximants of the exponential are A-stable exactly in
the first three diagonals specified by Ehle's criterion. -/
theorem expPade_AStable_iff (k j : ℕ) :
    (∀ z : ℂ, z.re ≤ 0 →
      (expPadeNumerator j k).eval (-z) ≠ 0 ∧
      ‖(expPadeNumerator k j).eval z / (expPadeNumerator j k).eval (-z)‖ ≤ 1) ↔
      k ≤ j ∧ j ≤ k + 2 := by
  sorry

/-- **Gap 15.5.** The second Dahlquist barrier for an A-stable linear
multistep method with a nonzero leading coefficient. -/
theorem multistep_order_le_two_of_AStable {k p : ℕ} (hk : 0 < k)
    (a b : Fin (k + 1) → ℝ) (ha : a (Fin.last k) ≠ 0)
    (hstab : ∀ z : ℂ, z.re ≤ 0 →
      IsZeroStable (multistepPolynomial a - Polynomial.C z * multistepPolynomial b))
    (hp : MultistepHasOrder a b p) : p ≤ 2 := by
  sorry

/-- **Gap 15.7.** Nonnegative weights and the positive semidefinite
algebraic stability matrix imply contractivity for any pair of stages. -/
theorem RungeKuttaTableau.norm_update_sub_le_of_algebraicStability {s : ℕ}
    (T : RungeKuttaTableau s)
    (hb : ∀ i, 0 ≤ T.b i)
    (hM : (Matrix.of fun i j ↦ T.b i * T.A i j + T.b j * T.A j i - T.b i * T.b j).PosSemidef)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℝ → H → H) (hdis : ∀ t u v, inner ℝ (f t u - f t v) (u - v) ≤ 0)
    (t : ℝ) {h : ℝ} (hh : 0 ≤ h) (x y : H) (X Y : Fin s → H)
    (hX : T.IsStages f t h x X) (hY : T.IsStages f t h y Y) :
    ‖T.update f t h x X - T.update f t h y Y‖ ≤ ‖x - y‖ := by
  sorry

/-- **Gap 15.9.** A regular pencil has a Weierstrass decomposition
with an ordinary differential block and a nilpotent algebraic block. -/
theorem exists_weierstrassDecomposition {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hregular : ∃ z : ℂ, (A + z • B).det ≠ 0) :
    ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin n)
      (P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)
      (C : Matrix (Fin r) (Fin r) ℂ) (N : Matrix (Fin s) (Fin s) ℂ),
      P.det ≠ 0 ∧ Q.det ≠ 0 ∧ IsNilpotent N ∧
      P * A.submatrix e e * Q = Matrix.fromBlocks C 0 0 1 ∧
      P * B.submatrix e e * Q = Matrix.fromBlocks 1 0 0 N := by
  sorry

/-- **Gap 15.11.** The exponential Euler method has first-order global error
for a contraction semigroup and time-Lipschitz forcing along the exact solution. -/
theorem exponentialEuler_error_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : ℝ → E →L[ℝ] E) (g : ℝ → E → E)
    (u : ℝ → E) (v : ℕ → E) {h L M : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hM : 0 ≤ M)
    (hS : ∀ t ≥ 0, ‖S t‖ ≤ 1) (hcont : ∀ x, Continuous fun t ↦ S t x)
    (hg : ∀ t x y, ‖g t x - g t y‖ ≤ L * ‖x - y‖)
    (hF : ∀ s t : ℝ, ‖g s (u s) - g t (u t)‖ ≤ M * |s - t|)
    (hstart : v 0 = u 0)
    (hex : ∀ n : ℕ, u ((n + 1 : ℕ) * h) = S h (u (n * h)) +
      ∫ t in (0 : ℝ)..h, S (h - t) (g (n * h + t) (u (n * h + t))))
    (hnum : ∀ n : ℕ, v (n + 1) = S h (v n) + ∫ t in (0 : ℝ)..h, S (h - t) (g (n * h) (v n)))
    (n : ℕ) :
    ‖u (n * h) - v n‖ ≤ M * h / (2 * L) * (Real.exp (L * n * h) - 1) := by
  sorry

/-- **Gap 15.13.** The symplectic coefficient identities preserve every
quadratic first integral. -/
theorem RungeKuttaTableau.quadratic_update_eq {s : ℕ} (T : RungeKuttaTableau s)
    (h : ∀ i j, T.b i * T.A i j + T.b j * T.A j i = T.b i * T.b j)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (f : E → E) (hf : ∀ x, B x (f x) = 0)
    (t d : ℝ) (x : E) (Y : Fin s → E) (hY : T.IsStages (fun _ ↦ f) t d x Y) :
    let y := T.update (fun _ ↦ f) t d x Y
    B y y = B x x := by
  sorry

/-- **Gap 15.15.** Matching the one-step series through second order
uniquely determines the first correction in the modified vector field. -/
theorem modifiedField_firstCorrection_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) (f : E → E) (d g : E)
    (Φ : ℝ → E)
    (hstep : (fun h : ℝ ↦ Φ h - (x + h • f x + h ^ 2 • d)) =O[𝓝 0] (fun h ↦ h ^ 3))
    (hflow : (fun h : ℝ ↦ Φ h -
      (x + h • f x + h ^ 2 • (g + (1 / 2 : ℝ) • fderiv ℝ f x (f x))))
        =O[𝓝 0] (fun h ↦ h ^ 3)) :
    g = d - (1 / 2 : ℝ) • fderiv ℝ f x (f x) := by
  sorry

/-- **Gap 15.16.** Exponentially small defects of the modified energy imply
long-time control of the original energy on the exponentially long step window. -/
theorem energy_error_le_of_modifiedEnergy {E : Type*} (H Hmod : E → ℝ) (x : ℕ → E)
    {h c C : ℝ} (hh : 0 < h) (hc : 0 < c) (p : ℕ)
    (hnear : ∀ j, |Hmod (x j) - H (x j)| ≤ C * h ^ p)
    (hdefect : ∀ j, |Hmod (x (j + 1)) - Hmod (x j)| ≤ h * Real.exp (-c / h))
    (n : ℕ) (hn : (n : ℝ) * h ≤ Real.exp (c / (2 * h))) :
    |H (x n) - H (x 0)| ≤ 2 * C * h ^ p + Real.exp (-c / (2 * h)) := by
  sorry

/-- **Gap 15.17.** The symmetric Strang matrix product has the cubic
commutator correction in the exponential, up to a fifth-order defect. -/
theorem strang_exp_sub_corrected_exp_isBigO {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    let comm := fun X Y : Matrix (Fin n) (Fin n) ℝ ↦ X * Y - Y * X
    let D := (-1 / 24 : ℝ) • comm A (comm A B) + (1 / 12 : ℝ) • comm B (comm B A)
    (fun t : ℝ ↦ NormedSpace.exp ((t / 2) • A) * NormedSpace.exp (t • B) *
      NormedSpace.exp ((t / 2) • A) - NormedSpace.exp (t • (A + B) + t ^ 3 • D))
      =O[𝓝 0] (fun t ↦ t ^ 5) := by
  sorry

end NASC
