module

public import NASC.InitialValueProblems
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Stiff problems and geometric integration

Runge--Kutta and multistep stability, regular differential-algebraic pencils, exponential
Euler, quadratic invariants, modified equations and splitting. See section 15.

## Main definitions

* `NASC.RungeKuttaTableau.stabilityFunction`: `R(z) = 1 + z bᵀ (I - zA)⁻¹ 𝟙`.
* `NASC.expPadeNumerator`: the numerator of the `(k, j)` Padé approximant to `exp`.
* `NASC.IsAStable`: A-stability of a rational function `P / Q`.
* `NASC.IsMultistepAStable`: A-stability of a linear multistep method.

## Main results

* `NASC.RungeKuttaTableau.stabilityFunction_eq_detRatio`: `R(z) = det(I - zA + z𝟙bᵀ) /
  det(I - zA)`.
* `NASC.expPade_isAStable_iff` (Ehle), `NASC.multistep_order_le_two_of_isMultistepAStable`
  (second Dahlquist barrier).
* `NASC.RungeKuttaTableau.norm_update_sub_le_of_algebraicStability` (B-stability),
  `NASC.RungeKuttaTableau.quadratic_update_eq`.
* `NASC.exists_weierstrassDecomposition`, `NASC.exponentialEuler_error_le`.
* `NASC.modifiedField_firstCorrection_eq`, `NASC.energy_error_le_of_modifiedEnergy`,
  `NASC.strang_exp_sub_corrected_exp_isBigO`.
-/

public section

noncomputable section

namespace NASC

open Set Filter Matrix Asymptotics Polynomial
open scoped Matrix Topology Interval

/-- The stability function `R(z) = 1 + z bᵀ (I - zA)⁻¹ 𝟙` of a Runge--Kutta tableau: the
update of the linear test equation `y' = λ y` with `z = hλ`. (Where `det (I - zA) = 0`, Lean's
inverse is `0` and `R z = 1`.) -/
def RungeKuttaTableau.stabilityFunction {s : ℕ} (T : RungeKuttaTableau s) (z : ℂ) : ℂ :=
  1 + z * dotProduct (fun i ↦ (T.b i : ℂ)) ((1 - z • T.A.map Complex.ofReal)⁻¹ *ᵥ fun _ ↦ 1)

/-- The defining formula of `RungeKuttaTableau.stabilityFunction`. -/
theorem RungeKuttaTableau.stabilityFunction_def {s : ℕ} (T : RungeKuttaTableau s) (z : ℂ) :
    T.stabilityFunction z =
      1 + z * dotProduct (fun i ↦ (T.b i : ℂ))
        ((1 - z • T.A.map Complex.ofReal)⁻¹ *ᵥ fun _ ↦ 1) := by
  rfl

/-- **Gap 15.1.** The stability function of a Runge--Kutta tableau equals
the determinant quotient `det (I - zA + z 𝟙 bᵀ) / det (I - zA)` whenever
`det (I - zA) ≠ 0`. -/
theorem RungeKuttaTableau.stabilityFunction_eq_detRatio {s : ℕ}
    (T : RungeKuttaTableau s) (z : ℂ) :
    let M : Matrix (Fin s) (Fin s) ℂ := 1 - z • T.A.map Complex.ofReal
    let b : Fin s → ℂ := fun i ↦ T.b i
    let e : Fin s → ℂ := fun _ ↦ 1
    M.det ≠ 0 →
      T.stabilityFunction z = (M + z • vecMulVec e b).det / M.det := by
  intro M b e hM
  have hrank : M + z • vecMulVec e b =
      M + replicateCol Unit (z • e) * replicateRow Unit b := by
    rw [← vecMulVec_eq, smul_vecMulVec]
  rw [hrank, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hM),
    mul_div_cancel_left₀ _ hM, Matrix.mul_assoc, ← replicateCol_mulVec, det_unique (n := Unit),
    RungeKuttaTableau.stabilityFunction_def]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, replicateRow_mul_replicateCol_apply,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, M, b, e]

/-- Numerator polynomial for the type $(k,j)$ Padé approximant to the exponential. -/
def expPadeNumerator (k j : ℕ) : ℂ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.monomial m (((k.factorial : ℂ) * (j + k - m).factorial) /
      ((j + k).factorial * m.factorial * (k - m).factorial))

/-- The defining formula of `expPadeNumerator`. -/
theorem expPadeNumerator_def (k j : ℕ) :
    expPadeNumerator k j = ∑ m ∈ Finset.range (k + 1),
      Polynomial.monomial m (((k.factorial : ℂ) * (j + k - m).factorial) /
        ((j + k).factorial * m.factorial * (k - m).factorial)) := by
  rfl

/-- A-stability of the rational function `P / Q`: on the closed left half-plane the
denominator does not vanish and the quotient has modulus at most one. -/
def IsAStable (P Q : ℂ[X]) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → Q.eval z ≠ 0 ∧ ‖P.eval z / Q.eval z‖ ≤ 1

/-- The defining property of `IsAStable`. -/
theorem isAStable_iff (P Q : ℂ[X]) :
    IsAStable P Q ↔ ∀ z : ℂ, z.re ≤ 0 → Q.eval z ≠ 0 ∧ ‖P.eval z / Q.eval z‖ ≤ 1 :=
  Iff.rfl

/-- A-stability of the linear multistep method `(ρ, σ)` with coefficient vectors `a, b`:
the polynomial `ρ - z σ` satisfies the root condition for every `z` with `re z ≤ 0`. -/
def IsMultistepAStable {k : ℕ} (a b : Fin (k + 1) → ℝ) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 →
    IsZeroStable (multistepPolynomial a - Polynomial.C z * multistepPolynomial b)

/-- The defining property of `IsMultistepAStable`. -/
theorem isMultistepAStable_iff {k : ℕ} (a b : Fin (k + 1) → ℝ) :
    IsMultistepAStable a b ↔ ∀ z : ℂ, z.re ≤ 0 →
      IsZeroStable (multistepPolynomial a - Polynomial.C z * multistepPolynomial b) :=
  Iff.rfl

/-- **Gap 15.3.** The `(k, j)` Padé approximant `N_{k,j}(z) / N_{j,k}(-z)` of the
exponential is A-stable exactly in the three diagonals `k ≤ j ≤ k + 2` (Ehle). -/
theorem expPade_isAStable_iff (k j : ℕ) :
    IsAStable (expPadeNumerator k j) ((expPadeNumerator j k).comp (-X)) ↔
      k ≤ j ∧ j ≤ k + 2 := by
  sorry

/-- **Gap 15.5.** The second Dahlquist barrier for an A-stable linear
multistep method with a nonzero leading coefficient. (For `k = 0` the order conditions
contradict `a 0 ≠ 0`.) -/
theorem multistep_order_le_two_of_isMultistepAStable {k p : ℕ}
    (a b : Fin (k + 1) → ℝ) (ha : a (Fin.last k) ≠ 0) (hstab : IsMultistepAStable a b)
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
    (hX : T.IsStageSolution f t h x X) (hY : T.IsStageSolution f t h y Y) :
    ‖T.update f t h x X - T.update f t h y Y‖ ≤ ‖x - y‖ := by
  sorry

/-- **Gap 15.9.** A regular pencil has a Weierstrass decomposition
with an ordinary differential block and a nilpotent algebraic block. -/
theorem exists_weierstrassDecomposition {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hregular : ∃ z : K, (A + z • B).det ≠ 0) :
    ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin n)
      (P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) K)
      (C : Matrix (Fin r) (Fin r) K) (N : Matrix (Fin s) (Fin s) K),
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
    (t d : ℝ) (x : E) (Y : Fin s → E) (hY : T.IsStageSolution (fun _ ↦ f) t d x Y) :
    let y := T.update (fun _ ↦ f) t d x Y
    B y y = B x x := by
  intro y
  let k : Fin s → E := fun i ↦ f (Y i)
  let P : Fin s → Fin s → ℝ := fun i j ↦ B (k i) (k j)
  have hy : y = x + d • ∑ i, T.b i • k i := T.update_def _ _ _ _ _
  have hx (i : Fin s) : B x (k i) = -(d * ∑ j, T.A i j * P i j) := by
    have h0 : B (x + d • ∑ j, T.A i j • k j) (k i) = 0 :=
      ((T.isStageSolution_iff _ _ _ _ _).mp hY i).symm ▸ hf (Y i)
    simp only [map_add, map_smul, map_sum, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul] at h0
    simp only [P, hB (k i)]
    linarith only [h0]
  have hyy : B y y = B x x + 2 * d * ∑ i, T.b i * B x (k i) +
      d ^ 2 * ∑ i, ∑ j, T.b i * T.b j * P i j := by
    let S := ∑ i, T.b i • k i
    have hxS : B x S = ∑ i, T.b i * B x (k i) := by
      simp only [S, map_sum, map_smul, smul_eq_mul]
    have hSS : B S S = ∑ i, ∑ j, T.b i * T.b j * P i j := by
      simp only [S, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ ↦ (Finset.mul_sum _ _ _).trans ?_
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hB (k j) (k i)]; ring
    rw [hy]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB S x, hxS, hSS]
    ring
  have hsum : ∑ i, ∑ j, T.b i * T.b j * P i j = 2 * ∑ i, ∑ j, T.b i * T.A i j * P i j := by
    have hswap : ∑ i, ∑ j, T.b j * T.A j i * P i j = ∑ i, ∑ j, T.b i * T.A i j * P i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        congrArg (T.b i * T.A i j * ·) (hB (k j) (k i))
    simp only [← h, add_mul, Finset.sum_add_distrib, hswap]
    ring
  have hbx : ∑ i, T.b i * B x (k i) = -(d * ∑ i, ∑ j, T.b i * T.A i j * P i j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hx, mul_neg, neg_inj]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hyy, hsum, hbx]
  ring

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
  set w := d - (g + (1 / 2 : ℝ) • fderiv ℝ f x (f x))
  have key : (fun h : ℝ ↦ h ^ 2 • w) =O[𝓝 0] (fun h ↦ h ^ 3) :=
    (hflow.sub hstep).congr_left fun h ↦ by simp only [w, smul_sub]; abel
  have hw : (fun h : ℝ ↦ (h ^ 2)⁻¹ • (h ^ 2 • w)) =O[𝓝[≠] 0] (fun h ↦ (h ^ 2)⁻¹ * h ^ 3) :=
    (isBigO_refl (fun h : ℝ ↦ (h ^ 2)⁻¹) _).smul (key.mono nhdsWithin_le_nhds)
  have hw' : (fun _ : ℝ ↦ w) =O[𝓝[≠] 0] (fun h : ℝ ↦ h) := by
    refine hw.congr' ?_ ?_ <;> filter_upwards [self_mem_nhdsWithin] with h hh
    · rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hh), one_smul]
    · field_simp
  have hlim : Tendsto (fun _ : ℝ ↦ w) (𝓝[≠] 0) (𝓝 0) :=
    hw'.trans_tendsto (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hw0 : w = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hneg : g - (d - (1 / 2 : ℝ) • fderiv ℝ f x (f x)) = -w := by
    simp only [w]
    abel
  rw [← sub_eq_zero, hneg, hw0, neg_zero]

/-- **Gap 15.16.** Exponentially small defects of the modified energy imply
long-time control of the original energy on the exponentially long step window. -/
theorem energy_error_le_of_modifiedEnergy {E : Type*} (H Hmod : E → ℝ) (x : ℕ → E)
    {h c C : ℝ} (hh : 0 < h) (p : ℕ)
    (hnear : ∀ j, |Hmod (x j) - H (x j)| ≤ C * h ^ p)
    (hdefect : ∀ j, |Hmod (x (j + 1)) - Hmod (x j)| ≤ h * Real.exp (-c / h))
    (n : ℕ) (hn : (n : ℝ) * h ≤ Real.exp (c / (2 * h))) :
    |H (x n) - H (x 0)| ≤ 2 * C * h ^ p + Real.exp (-c / (2 * h)) := by
  have htel (m : ℕ) : |Hmod (x m) - Hmod (x 0)| ≤ m * (h * Real.exp (-c / h)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc |Hmod (x (m + 1)) - Hmod (x 0)|
          ≤ |Hmod (x (m + 1)) - Hmod (x m)| + |Hmod (x m) - Hmod (x 0)| := abs_sub_le _ _ _
        _ ≤ h * Real.exp (-c / h) + m * (h * Real.exp (-c / h)) := add_le_add (hdefect m) ih
        _ = ((m + 1 : ℕ) : ℝ) * (h * Real.exp (-c / h)) := by push_cast; ring
  have hsplit : Real.exp (-c / (2 * h)) = Real.exp (c / (2 * h)) * Real.exp (-c / h) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hexp : (n : ℝ) * (h * Real.exp (-c / h)) ≤ Real.exp (-c / (2 * h)) := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
  obtain ⟨a₁, a₂⟩ := abs_le.mp (hnear n)
  obtain ⟨b₁, b₂⟩ := abs_le.mp (hnear 0)
  obtain ⟨c₁, c₂⟩ := abs_le.mp (htel n)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Gap 15.17.** The symmetric Strang product in a complete normed real algebra (for
example square matrices with an operator norm) has the cubic commutator correction in the
exponential, up to a fifth-order defect. -/
theorem strang_exp_sub_corrected_exp_isBigO {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A B : 𝔸) :
    let comm := fun X Y : 𝔸 ↦ X * Y - Y * X
    let D := (-1 / 24 : ℝ) • comm A (comm A B) + (1 / 12 : ℝ) • comm B (comm B A)
    (fun t : ℝ ↦ NormedSpace.exp ((t / 2) • A) * NormedSpace.exp (t • B) *
      NormedSpace.exp ((t / 2) • A) - NormedSpace.exp (t • (A + B) + t ^ 3 • D))
      =O[𝓝 0] (fun t ↦ t ^ 5) := by
  sorry

end NASC
