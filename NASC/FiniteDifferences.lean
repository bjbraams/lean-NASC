module

public import NASC.DiscreteFourier
public import NASC.VerifiedComputation
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Finite difference methods

Discrete Laplacians and maximum principles, power stability, CFL and theta-method bounds,
positivity-preserving stepping, and comparison for monotone schemes.
-/

public section

noncomputable section

namespace NASC

open Set Filter Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal ENNReal Topology

/-- The symmetric tridiagonal Toeplitz matrix with constant diagonal and off-diagonal. -/
def tridiagonalToeplitz (n : ℕ) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then a else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b else 0

/-- **Gap 16.2.** The discrete sine functions are the eigenvectors of
the tridiagonal Dirichlet matrix. -/
theorem tridiagonalToeplitz_mulVec_sine {n : ℕ} (a b : ℝ) (j : Fin n) :
    let θ := Real.pi * ((j.val : ℝ) + 1) / (n + 1)
    let v := fun i : Fin n ↦ Real.sin (θ * (i.val + 1))
    v ≠ 0 ∧ tridiagonalToeplitz n a b *ᵥ v = (a + 2 * b * Real.cos θ) • v := by
  sorry

/-- Five-point discrete Laplacian with mesh spacing $h$. -/
def fivePointLaplacian (h : ℝ) (v : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (v (i + 1) j + v (i - 1) j + v i (j + 1) + v i (j - 1) - 4 * v i j) / h ^ 2

/-- Homogeneous boundary inequalities on a square finite difference grid. -/
def GridBoundaryNonpos (n : ℕ) (v : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ≤ n, v i 0 ≤ 0 ∧ v i n ≤ 0 ∧ v 0 i ≤ 0 ∧ v n i ≤ 0

/-- **Gap 16.3.** The discrete Dirichlet maximum principle on the square. -/
theorem fivePoint_nonpos_of_boundary_nonpos {n : ℕ} {h : ℝ} (hh : 0 < h)
    (v : ℕ → ℕ → ℝ) (hb : GridBoundaryNonpos n v)
    (hsub : ∀ i j, 0 < i → i < n → 0 < j → j < n → 0 ≤ fivePointLaplacian h v i j) :
    ∀ i j, i ≤ n → j ≤ n → v i j ≤ 0 := by
  let S := Finset.Iic n ×ˢ Finset.Iic n
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := Finset.exists_max_image S
    (fun p : ℕ × ℕ ↦ v p.1 p.2) ⟨(0, 0), by simp [S]⟩
  have hupper (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) : v i j ≤ v a b :=
    hmax (i, j) (by simpa [S] using And.intro hi hj)
  obtain ⟨ha, hbmax⟩ : a ≤ n ∧ b ≤ n := by simpa [S] using hab
  have hleft : ∀ k ≤ n, v k b = v a b → v a b ≤ 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hkv
      by_cases hki : 0 < k ∧ k < n
      · by_cases hbi : 0 < b ∧ b < n
        · have hL := hupper (k - 1) b (by omega) hbmax
          have hR := hupper (k + 1) b (by omega) hbmax
          have hD := hupper k (b - 1) hk (by omega)
          have hU := hupper k (b + 1) hk (by omega)
          have hs := (le_div_iff₀ (pow_pos hh 2)).mp (hsub k b hki.1 hki.2 hbi.1 hbi.2)
          simp only [zero_mul] at hs
          have heq : v (k - 1) b = v a b := le_antisymm hL (by
            linarith only [hR, hD, hU, hs, hkv])
          exact ih (k - 1) (by omega) (by omega) heq
        · rcases (by omega : b = 0 ∨ b = n) with h | h
          · rw [← hkv, h]
            exact (hb k hk).1
          · rw [← hkv, h]
            exact (hb k hk).2.1
      · rcases (by omega : k = 0 ∨ k = n) with h | h
        · rw [← hkv, h]
          exact (hb b hbmax).2.2.1
        · rw [← hkv, h]
          exact (hb b hbmax).2.2.2
  exact fun i j hi hj ↦ (hupper i j hi hj).trans (hleft a ha rfl)

/-- **Gap 16.4.** A uniform truncation defect and exact boundary data give
the five-point error bound with the square barrier constant $1/8$. -/
theorem fivePoint_error_le_of_defect {n : ℕ} (hn : 0 < n)
    (u U : ℕ → ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hb : GridBoundaryNonpos n (fun i j ↦ u i j - U i j))
    (hb' : GridBoundaryNonpos n (fun i j ↦ U i j - u i j))
    (hdef : ∀ i j, 0 < i → i < n → 0 < j → j < n →
      |fivePointLaplacian (n : ℝ)⁻¹ (fun i j ↦ u i j - U i j) i j| ≤
        (n : ℝ)⁻¹ ^ 2 * M / 12) :
    ∀ i j, i ≤ n → j ≤ n → |u i j - U i j| ≤ (n : ℝ)⁻¹ ^ 2 * M / 96 := by
  let h : ℝ := (n : ℝ)⁻¹
  let K := h ^ 2 * M / 12
  let B := fun i : ℕ ↦ K / 2 * ((i : ℝ) * h) * (1 - (i : ℝ) * h)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h := inv_pos.mpr hn'
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hnh : (n : ℝ) * h = 1 := mul_inv_cancel₀ hn'.ne'
  have hB (i : ℕ) (hi : i ≤ n) : 0 ≤ B i := by
    have hle := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi : (i : ℝ) ≤ n) hh.le
    rw [hnh] at hle
    exact mul_nonneg (mul_nonneg (div_nonneg hK two_pos.le)
      (mul_nonneg (Nat.cast_nonneg _) hh.le)) (sub_nonneg.mpr hle)
  have hBmax (i : ℕ) : B i ≤ K / 8 := by
    have hs := mul_nonneg hK (sq_nonneg ((i : ℝ) * h - 1 / 2))
    dsimp only [B]
    linarith only [hs]
  have hshift (w : ℕ → ℕ → ℝ) (i j : ℕ) (hi : 0 < i) :
      fivePointLaplacian h (fun a b ↦ w a b - B a) i j = fivePointLaplacian h w i j + K := by
    have hpred : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub hi : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - ↑(1 : ℕ))
    simp only [fivePointLaplacian, B, Nat.cast_add, Nat.cast_one, hpred]
    field_simp [hh.ne']
    ring
  have hcmp (w : ℕ → ℕ → ℝ) (hw : GridBoundaryNonpos n w)
      (hL : ∀ i j, 0 < i → i < n → 0 < j → j < n → -K ≤ fivePointLaplacian h w i j)
      (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) : w i j ≤ B i := by
    have hwB : GridBoundaryNonpos n (fun a b ↦ w a b - B a) := by
      intro a ha
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hw a ha
      exact ⟨sub_nonpos.mpr (h₁.trans (hB a ha)), sub_nonpos.mpr (h₂.trans (hB a ha)),
        sub_nonpos.mpr (h₃.trans (hB 0 (Nat.zero_le n))), sub_nonpos.mpr (h₄.trans (hB n le_rfl))⟩
    refine sub_nonpos.mp (fivePoint_nonpos_of_boundary_nonpos hh _ hwB (fun a b ha han hb hbn ↦ ?_)
      i j hi hj)
    rw [hshift w a b ha]
    linarith only [hL a b ha han hb hbn]
  intro i j hi hj
  have hf₂ : ∀ a b, 0 < a → a < n → 0 < b → b < n →
      -K ≤ fivePointLaplacian h (fun x y ↦ U x y - u x y) a b := by
    intro a b ha han hb hbn
    have heq : fivePointLaplacian h (fun x y ↦ U x y - u x y) a b =
        -fivePointLaplacian h (fun x y ↦ u x y - U x y) a b := by
      dsimp only [fivePointLaplacian]
      ring
    rw [heq]
    exact neg_le_neg (abs_le.mp (hdef a b ha han hb hbn)).2
  have h₁ := (hcmp _ hb
    (fun a b ha han hb hbn ↦ (abs_le.mp (hdef a b ha han hb hbn)).1) i j hi hj).trans (hBmax i)
  have h₂ := (hcmp _ hb' hf₂ i j hi hj).trans (hBmax i)
  dsimp only [K, h] at h₁ h₂
  exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩

/-- **Gap 16.5.** Stability and strong convergence are equivalent for the
consistent linear approximation of bounded solution operators on a time interval. -/
theorem stable_iff_convergent_of_consistent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C S : ℝ → E →L[ℝ] E) (D : Set E) (hD : Dense D) {T : ℝ} (hT : 0 < T)
    (hS₀ : S 0 = 1) (hS : ∃ B, ∀ t ∈ Icc (0 : ℝ) T, ‖S t‖ ≤ B)
    (hC : ∃ B, ∀ h > (0 : ℝ), h ≤ T → ‖C h‖ ≤ B)
    (hcons : ∀ u ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ h t : ℝ, 0 < h → h ≤ δ → 0 ≤ t → t + h ≤ T →
        ‖C h (S t u) - S (t + h) u‖ ≤ h * ε) :
    (∃ B, ∀ h > (0 : ℝ), ∀ m : ℕ, (m : ℝ) * h ≤ T → ‖C h ^ m‖ ≤ B) ↔
      (∀ u : E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
        ∀ h > (0 : ℝ), ∀ m : ℕ, h ≤ δ → (m : ℝ) * h ≤ T →
          ‖(C h ^ m) u - S ((m : ℝ) * h) u‖ ≤ ε) := by
  sorry

/-- **Gap 16.6.** Periodic von Neumann stability for a two-level finite stencil
with invertible implicit symbol. -/
theorem vonNeumann_power_bounded_iff {n : ℕ} [NeZero n] (b c : ZMod n → ℂ)
    (hb : ∀ j, ZMod.dft b j ≠ 0) :
    let B := Matrix.of fun i j : ZMod n ↦ b (i - j)
    let C := Matrix.of fun i j : ZMod n ↦ c (i - j)
    (∃ R : ℝ, ∀ k : ℕ, ‖(B⁻¹ * C) ^ k‖ ≤ R) ↔
      ∀ j, ‖ZMod.dft c j / ZMod.dft b j‖ ≤ 1 := by
  sorry

/-- **Gap 16.7.** Convergence for every smooth initial function forces the CFL
condition on a family of three-point local steps. -/
theorem cfl_of_threePoint_convergence (S : ℕ → (ℤ → ℝ) → (ℤ → ℝ))
    {a T μ : ℝ} (hT : 0 < T) (hμ : 0 < μ)
    (hloc : ∀ n (u v : ℤ → ℝ) (i : ℤ),
      (∀ j ∈ Icc (i - 1) (i + 1), u j = v j) → S n u i = S n v i)
    (hconv : ∀ f : ℝ → ℝ, ContDiff ℝ ⊤ f →
      Tendsto (fun n : ℕ ↦ (S n)^[n + 1] (fun j : ℤ ↦ f ((j : ℝ) * T / ((n + 1) * μ))) 0)
        atTop (nhds (f (-a * T)))) :
    |a * μ| ≤ 1 := by
  sorry

/-- **Gap 16.9.** Theta time stepping for the centered Dirichlet heat matrix
is Euclidean contractive under its step-size criterion. -/
theorem norm_heatThetaMatrix_pow_le_one {n : ℕ} {d h τ θ : ℝ}
    (hd : 0 < d) (hh : 0 < h) (hτ : 0 < τ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hstep : 1 / 2 ≤ θ ∨ d * τ / h ^ 2 ≤ 1 / (2 - 4 * θ)) (k : ℕ) :
    let A := (d / h ^ 2) • tridiagonalToeplitz n (-2) 1
    ‖(((1 : Matrix (Fin n) (Fin n) ℝ) - (θ * τ) • A)⁻¹ *
      (1 + ((1 - θ) * τ) • A)) ^ k‖ ≤ 1 := by
  sorry

/-- Kreiss resolvent constant with infinite value at poles outside the disk. -/
def kreissConstant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  letI := Classical.propDecidable
  ⨆ z : {z : ℂ // 1 < ‖z‖},
    if z.val ∈ spectrum ℂ A then ⊤ else
      ENNReal.ofReal ((‖z.val‖ - 1) * ‖(z.val • (1 : Matrix (Fin n) (Fin n) ℂ) - A)⁻¹‖)

/-- **Gap 16.10.** The Kreiss matrix bound relates resolvent growth to power
growth in both directions, including infinite values. -/
theorem kreissConstant_le_iSup_pow_and_le {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreissConstant A ≤ (⨆ k : ℕ, ENNReal.ofReal ‖A ^ k‖) ∧
      (⨆ k : ℕ, ENNReal.ofReal ‖A ^ k‖) ≤ ENNReal.ofReal (Real.exp 1 * n) * kreissConstant A := by
  sorry

/-- **Gap 16.14.** The explicit Shu--Osher stages inherit forward-Euler
positivity under the coefficient step restrictions. -/
theorem shuOsher_nonneg {n s : ℕ} (F : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (v : Fin (s + 1) → Fin n → ℝ) (t : Fin (s + 1) → ℝ)
    (p q : Fin (s + 1) → Fin (s + 1) → ℝ) {h H : ℝ}
    (hh : 0 ≤ h) (hH : 0 < H) (hv : 0 ≤ v 0)
    (hF : ∀ t (x : Fin n → ℝ) a, 0 ≤ x → a ∈ Icc 0 H → 0 ≤ x + a • F t x)
    (hpos : ∀ i j, j < i → 0 ≤ p i j ∧ 0 ≤ q i j ∧ h * q i j ≤ H * p i j)
    (hstage : ∀ i : Fin (s + 1), i ≠ 0 →
      (∑ j ∈ Finset.univ.filter (· < i), p i j) = 1 ∧
      v i = ∑ j ∈ Finset.univ.filter (· < i), (p i j • v j + (h * q i j) • F (t j) (v j))) :
    ∀ i, 0 ≤ v i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i = 0
    · simpa only [hi] using hv
    rw [(hstage i hi).2]
    intro k
    simp only [Pi.zero_apply, Finset.sum_apply]
    apply Finset.sum_nonneg
    intro j hj
    have hji := (Finset.mem_filter.mp hj).2
    obtain ⟨hp, hq, hqle⟩ := hpos i j hji
    obtain ⟨a, ha, heq⟩ : ∃ a ∈ Icc (0 : ℝ) H, h * q i j = p i j * a := by
      by_cases hp₀ : p i j = 0
      · have hz : h * q i j = 0 := le_antisymm
          (by simpa only [hp₀, mul_zero] using hqle) (mul_nonneg hh hq)
        exact ⟨0, ⟨le_rfl, hH.le⟩, by simpa only [mul_zero] using hz⟩
      · have hp' := lt_of_le_of_ne hp (Ne.symm hp₀)
        refine ⟨h * q i j / p i j, ⟨div_nonneg (mul_nonneg hh hq) hp,
          (div_le_iff₀ hp').mpr hqle⟩, ?_⟩
        field_simp
    have hval := hF (t j) (v j) a (ih j hji) ha k
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hval ⊢
    rw [heq, mul_assoc, ← mul_add]
    exact mul_nonneg hp hval

/-- Viscosity subsolution expressed by all smooth upper tests on the domain. -/
def IsViscositySubsolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : (E → ℝ) → E → ℝ) (u : E → ℝ) : Prop :=
  UpperSemicontinuousOn u K ∧
    ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ⊤ φ → u x = φ x →
      IsLocalMaxOn (fun y ↦ u y - φ y) K x → F φ x ≤ 0

/-- Viscosity supersolution expressed by all smooth lower tests on the domain. -/
def IsViscositySupersolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : (E → ℝ) → E → ℝ) (u : E → ℝ) : Prop :=
  LowerSemicontinuousOn u K ∧
    ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ⊤ φ → u x = φ x →
      IsLocalMinOn (fun y ↦ u y - φ y) K x → 0 ≤ F φ x

/-- **Gap 16.15.** On a compact domain with comparison, a monotone scheme with
bounded continuous approximations and moving-point consistency converges uniformly.
The operator is presented by its action on smooth viscosity test functions. -/
theorem exists_uniformLimit_of_monotoneScheme {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) (hK : IsCompact K)
    (F : (E → ℝ) → E → ℝ) (S : ℝ → E → ℝ → (E → ℝ) → ℝ) (u : ℝ → E → ℝ)
    (hpert : ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ⊤ φ →
      Tendsto (fun ε : ℝ ↦ F (fun y ↦ φ y + ε * ‖y - x‖ ^ 2) x) (𝓝 0) (𝓝 (F φ x)))
    (hcomp : ∀ v w : E → ℝ, (∃ C, ∀ x ∈ K, |v x| ≤ C ∧ |w x| ≤ C) →
      IsViscositySubsolution K F v → IsViscositySupersolution K F w → ∀ x ∈ K, v x ≤ w x)
    (hmono : ∀ h > (0 : ℝ), ∀ x ∈ K, ∀ r v w, (∀ y ∈ K, v y ≤ w y) →
      S h x r w ≤ S h x r v)
    (hsolve : ∃ C, ∀ᶠ h in 𝓝[>] (0 : ℝ), ContinuousOn (u h) K ∧
      ∀ x ∈ K, |u h x| ≤ C ∧ S h x (u h x) (u h) = 0)
    (hcons : ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ⊤ φ →
      Tendsto (fun p : ℝ × E × ℝ ↦
        S p.1 p.2.1 (φ p.2.1 + p.2.2) (fun y ↦ φ y + p.2.2) / p.1)
        ((𝓝[>] (0 : ℝ)) ×ˢ ((𝓝[K] x) ×ˢ (𝓝 0))) (𝓝 (F φ x))) :
    ∃ v : E → ℝ, ContinuousOn v K ∧ IsViscositySubsolution K F v ∧
      IsViscositySupersolution K F v ∧ TendstoUniformlyOn u v (𝓝[>] (0 : ℝ)) K := by
  sorry

end NASC
