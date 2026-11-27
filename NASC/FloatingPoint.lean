module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Inv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Floating-point arithmetic and rounding error

Finite radix formats, correct rounding, error-free transformations, summation and triangular
substitution. Gap identifiers refer to section 1 of the mathematical catalogue.
-/

public section

noncomputable section

namespace NASC

open scoped BigOperators Matrix

/-- A finite-radix floating-point format with gradual underflow. -/
structure FloatingPointFormat where
  /-- Radix. -/
  radix : ℕ
  /-- Number of radix digits in the significand. -/
  precision : ℕ
  /-- Smallest exponent. -/
  emin : ℤ
  /-- Largest exponent. -/
  emax : ℤ
  /-- The radix is at least two. -/
  two_le_radix : 2 ≤ radix
  /-- The precision is at least two. -/
  two_le_precision : 2 ≤ precision
  /-- The exponent window is nontrivial. -/
  emin_lt_emax : emin < emax

namespace FloatingPointFormat

variable (F : FloatingPointFormat)

/-- The real value of an integral significand at a specified exponent. -/
def value (m e : ℤ) : ℝ := (m : ℝ) * (F.radix : ℝ) ^ (e - (F.precision : ℤ) + 1)

/-- An admissible significand and exponent in the format. -/
def Valid (m e : ℤ) : Prop :=
  |m| < (F.radix : ℤ) ^ F.precision ∧ F.emin ≤ e ∧ e ≤ F.emax

/-- The real numbers representable in the format. -/
def numbers : Set ℝ := {x | ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x}

/-- A representable number has a valid significand and exponent. -/
theorem mem_numbers_iff {x : ℝ} :
    x ∈ F.numbers ↔ ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x := Iff.rfl

/-- The spacing at the bottom of the exponent range. -/
def spacing : ℝ := (F.radix : ℝ) ^ (F.emin - (F.precision : ℤ) + 1)

/-- The smallest positive normal number. -/
def minNormal : ℝ := (F.radix : ℝ) ^ F.emin

/-- The largest representable number. -/
def maxFinite : ℝ := F.value ((F.radix : ℤ) ^ F.precision - 1) F.emax

/-- The normal real input range, including both signs. -/
def normalRange : Set ℝ := {x | F.minNormal ≤ |x| ∧ |x| ≤ F.maxFinite}

/-- Membership of the normal range is the pair of magnitude bounds. -/
theorem mem_normalRange_iff {x : ℝ} :
    x ∈ F.normalRange ↔ F.minNormal ≤ |x| ∧ |x| ≤ F.maxFinite := Iff.rfl

/-- **Gap 1.1.** The least exponent representation has a normalized significand or lies at
the bottom exponent with a subnormal significand. -/
theorem exists_minimalExponent {x : ℝ} (hx : x ∈ F.numbers) (hx₀ : x ≠ 0) :
    ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x ∧
      (∀ m' e', F.Valid m' e' → F.value m' e' = x → e ≤ e') ∧
      (F.minNormal ≤ |x| → (F.radix : ℤ) ^ (F.precision - 1) ≤ |m|) ∧
      (|x| < F.minNormal → e = F.emin ∧ |m| < (F.radix : ℤ) ^ (F.precision - 1)) := by
  sorry

/-- **Gap 1.1.** The extrema, lattice inclusion and symmetry of the finite format. -/
theorem format_extrema :
    IsLeast {x ∈ F.numbers | 0 < x} F.spacing ∧
      IsLeast {x ∈ F.numbers | F.minNormal ≤ x} F.minNormal ∧
      IsGreatest F.numbers F.maxFinite ∧
      F.numbers ⊆ Set.range (fun m : ℤ ↦ (m : ℝ) * F.spacing) ∧
      (∀ x : ℝ, -x ∈ F.numbers ↔ x ∈ F.numbers) := by
  sorry

/-- Representable extended values, including infinities for directed overflow. -/
def extendedNumbers : Set EReal := (fun x : ℝ ↦ (x : EReal)) '' F.numbers ∪ {⊥, ⊤}

/-- The four rounding directions. -/
inductive RoundingMode
  | nearest
  | down
  | up
  | towardZero
  deriving DecidableEq

/-- Correct rounding by the order or nearest-point rule, with an arbitrary choice at ties. -/
def IsRounding (mode : RoundingMode) (rnd : ℝ → EReal) : Prop :=
  match mode with
  | .nearest =>
    ∀ x, ∃ y ∈ F.numbers, rnd x = (y : EReal) ∧ ∀ t ∈ F.numbers, |y - x| ≤ |t - x|
  | .down => ∀ x : ℝ, IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x)
  | .up => ∀ x : ℝ, IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x)
  | .towardZero =>
    (∀ (x : ℝ), 0 ≤ x → IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x)) ∧
      (∀ (x : ℝ), x ≤ 0 → IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x))

/-- **Gap 1.3.** Correct rounding is monotone and fixes representable inputs. -/
theorem IsRounding.monotone_and_eq {mode : RoundingMode} {rnd : ℝ → EReal}
    (h : F.IsRounding mode rnd) :
    Monotone rnd ∧ ∀ x ∈ F.numbers, rnd x = (x : EReal) := by
  have hex (x : ℝ) (hx : x ∈ F.numbers) : (x : EReal) ∈ F.extendedNumbers :=
    Or.inl ⟨x, hx, rfl⟩
  have down_mono {x y : ℝ} (hxy : x ≤ y)
      (hx : IsGreatest {z ∈ F.extendedNumbers | z ≤ (x : EReal)} (rnd x))
      (hy : IsGreatest {z ∈ F.extendedNumbers | z ≤ (y : EReal)} (rnd y)) : rnd x ≤ rnd y :=
    hy.2 ⟨hx.1.1, hx.1.2.trans (EReal.coe_le_coe_iff.mpr hxy)⟩
  have up_mono {x y : ℝ} (hxy : x ≤ y)
      (hx : IsLeast {z ∈ F.extendedNumbers | (x : EReal) ≤ z} (rnd x))
      (hy : IsLeast {z ∈ F.extendedNumbers | (y : EReal) ≤ z} (rnd y)) : rnd x ≤ rnd y :=
    hx.2 ⟨hy.1.1, (EReal.coe_le_coe_iff.mpr hxy).trans hy.1.2⟩
  cases mode with
  | nearest =>
      rw [IsRounding] at h
      refine ⟨?_, fun x hx ↦ ?_⟩
      · intro x y hxy
        rcases hxy.eq_or_lt with rfl | hxy
        · rfl
        obtain ⟨a, ha, hra, hxa⟩ := h x
        obtain ⟨b, hb, hrb, hyb⟩ := h y
        rw [hra, hrb, EReal.coe_le_coe_iff]
        by_contra! hab
        have square_le (u v : ℝ) (huv : |u| ≤ |v|) : u ^ 2 ≤ v ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg u) huv 2
        have hxa' := square_le _ _ (hxa b hb)
        have hyb' := square_le _ _ (hyb a ha)
        have hprod := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hxy)
        nlinarith only [hxa', hyb', hprod]
      · obtain ⟨a, _, hra, hxa⟩ := h x
        have hzero : |a - x| ≤ 0 := by simpa only [sub_self, abs_zero] using hxa x hx
        rw [hra, sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))]
  | down =>
      rw [IsRounding] at h
      exact ⟨fun _ _ hxy ↦ down_mono hxy (h _) (h _),
        fun x hx ↦ le_antisymm (h x).1.2 ((h x).2 ⟨hex x hx, le_rfl⟩)⟩
  | up =>
      rw [IsRounding] at h
      exact ⟨fun _ _ hxy ↦ up_mono hxy (h _) (h _),
        fun x hx ↦ le_antisymm ((h x).2 ⟨hex x hx, le_rfl⟩) (h x).1.2⟩
  | towardZero =>
      rw [IsRounding] at h
      refine ⟨?_, fun x hx ↦ ?_⟩
      · intro x y hxy
        rcases le_total 0 x with hx | hx
        · exact down_mono hxy (h.1 x hx) (h.1 y (hx.trans hxy))
        rcases le_total y 0 with hy | hy
        · exact up_mono hxy (h.2 x hx) (h.2 y hy)
        exact (up_mono hx (h.2 x hx) (h.2 0 le_rfl)).trans (down_mono hy (h.1 0 le_rfl) (h.1 y hy))
      · rcases le_total 0 x with h₀ | h₀
        · exact le_antisymm (h.1 x h₀).1.2 ((h.1 x h₀).2 ⟨hex x hx, le_rfl⟩)
        · exact le_antisymm ((h.2 x h₀).2 ⟨hex x hx, le_rfl⟩) (h.2 x h₀).1.2

/-- The unit roundoff for a rounding mode. -/
def unitRoundoff (mode : RoundingMode) : ℝ :=
  (F.radix : ℝ) ^ (1 - (F.precision : ℤ)) / (if mode = .nearest then 2 else 1)

/-- **Gaps 1.4 and 1.5.** Both relative-error representations on the normal range, including
the sharper nearest-rounding bound. -/
theorem IsRounding.relativeError {mode : RoundingMode} {rnd : ℝ → EReal} {x : ℝ}
    (h : F.IsRounding mode rnd) (hx : x ∈ F.normalRange) :
    ∃ y δ ε : ℝ, rnd x = (y : EReal) ∧ y = x * (1 + δ) ∧ y = x / (1 + ε) ∧
      |δ| < F.unitRoundoff mode ∧ |ε| ≤ F.unitRoundoff mode ∧
      (mode = .nearest → |δ| ≤ F.unitRoundoff mode / (1 + F.unitRoundoff mode)) := by
  sorry

/-- **Gap 1.5.** Addition below the normal range is exact with gradual underflow. -/
theorem add_mem_numbers_of_abs_lt {a b : ℝ} (ha : a ∈ F.numbers) (hb : b ∈ F.numbers)
    (h : |a + b| < F.minNormal) : a + b ∈ F.numbers := by
  sorry

/-- **Gap 1.6.** Sterbenz's lemma for numbers at most a factor of two apart. -/
theorem sub_mem_numbers_of_half_le_of_le_two_mul {x y : ℝ}
    (hx : x ∈ F.numbers) (hy : y ∈ F.numbers) (h₁ : y / 2 ≤ x) (h₂ : x ≤ 2 * y) :
    x - y ∈ F.numbers := by
  sorry

/-- A real-valued nearest-rounding operation in the finite format. -/
structure Nearest where
  /-- The rounding map. -/
  round : ℝ → ℝ
  /-- The map satisfies the nearest-point rule. -/
  isRounding : F.IsRounding .nearest (fun x ↦ (round x : EReal))

/-- The Fast2Sum addition algorithm. -/
def fastTwoSum (rnd : ℝ → ℝ) (a b : ℝ) : ℝ × ℝ :=
  let s := rnd (a + b)
  (s, rnd (b - rnd (s - a)))

/-- The 2Sum addition algorithm. -/
def twoSum (rnd : ℝ → ℝ) (a b : ℝ) : ℝ × ℝ :=
  let s := rnd (a + b)
  let a' := rnd (s - b)
  let b' := rnd (s - a')
  (s, rnd (rnd (a - a') + rnd (b - b')))

/-- **Gap 1.7.** Fast2Sum is exact with ordered magnitudes and a radix at most three. -/
theorem fastTwoSum_add (rnd : F.Nearest) {a b : ℝ}
    (ha : a ∈ F.numbers) (hb : b ∈ F.numbers) (hβ : F.radix ≤ 3)
    (hab : |b| ≤ |a|) (hrange : |a + b| ≤ F.maxFinite) :
    (fastTwoSum rnd.round a b).1 + (fastTwoSum rnd.round a b).2 = a + b := by
  sorry

/-- **Gap 1.7.** 2Sum is exact when each intermediate lies within range and, outside
radix two, each nonzero intermediate is normal. -/
theorem twoSum_add (rnd : F.Nearest) {a b : ℝ} (ha : a ∈ F.numbers) (hb : b ∈ F.numbers)
    (h : let s := rnd.round (a + b)
         let a' := rnd.round (s - b)
         let b' := rnd.round (s - a')
         ∀ z ∈ [a + b, s - b, s - a', a - a', b - b',
                 rnd.round (a - a') + rnd.round (b - b')],
           |z| ≤ F.maxFinite ∧ (F.radix = 2 ∨ z = 0 ∨ F.minNormal ≤ |z|)) :
    (twoSum rnd.round a b).1 + (twoSum rnd.round a b).2 = a + b := by
  sorry

/-- **Gap 1.7.** A rounded product and its fused multiply-add residual sum exactly when
the product lies within range and its lattice is no finer than the bottom spacing. -/
theorem twoMultFMA_add (rnd : F.Nearest) {m₁ m₂ e₁ e₂ : ℤ}
    (h₁ : F.Valid m₁ e₁) (h₂ : F.Valid m₂ e₂)
    (he : F.emin + (F.precision : ℤ) - 1 ≤ e₁ + e₂)
    (hrange : |F.value m₁ e₁ * F.value m₂ e₂| ≤ F.maxFinite) :
    let p := F.value m₁ e₁ * F.value m₂ e₂
    let p' := rnd.round p
    p' + rnd.round (p - p') = p := by
  sorry

end FloatingPointFormat

/-- Accumulated relative error bound for a product of rounding factors. -/
@[expose] def roundingGamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

/-- The rational expression for the accumulated error bound. -/
theorem roundingGamma_def (u : ℝ) (n : ℕ) :
    roundingGamma u n = n * u / (1 - n * u) := rfl

/-- The standard relative error model for a scalar result. -/
def HasRelativeError (u exact computed : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ computed = exact * (1 + δ)

/-- The relative error is a bounded multiplicative perturbation. -/
theorem hasRelativeError_iff (u x y : ℝ) :
    HasRelativeError u x y ↔ ∃ δ : ℝ, |δ| ≤ u ∧ y = x * (1 + δ) := Iff.rfl

/-- The absolute error in the scalar model is at most the budget times the input magnitude. -/
theorem HasRelativeError.abs_sub_le {u a b : ℝ} (h : HasRelativeError u a b) :
    |b - a| ≤ u * |a| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have heq : a * (1 + δ) - a = a * δ := by ring
  rw [heq, abs_mul, mul_comm u]
  exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)

/-- A perturbed scalar sum and one rounding multiplication compose their error bounds. -/
theorem abs_mul_one_add_sub_le_of_abs_sub_le {a b δ p q w : ℝ}
    (hab : |a - b| ≤ p * w) (hb : |b| ≤ w) (hδ : |δ| ≤ q) :
    |a * (1 + δ) - b| ≤ (p + q + p * q) * w := by
  have ha : |a| ≤ p * w + w := by
    rw [← sub_add_cancel a b]
    exact (abs_add_le _ _).trans (add_le_add hab hb)
  have heq : a * (1 + δ) - b = (a - b) + a * δ := by ring
  rw [heq]
  calc
    _ ≤ |a - b| + |a| * |δ| := by simpa only [abs_mul] using abs_add_le (a - b) (a * δ)
    _ ≤ p * w + (p * w + w) * q :=
      add_le_add hab (mul_le_mul ha hδ (abs_nonneg _) ((abs_nonneg _).trans ha))
    _ = _ := by ring

/-- **Gap 1.8.** Two error factors compose with the sum of their budgets. -/
theorem roundingGamma_add_bound {u : ℝ} {j k : ℕ} (hu : 0 ≤ u)
    (h : ((j + k : ℕ) : ℝ) * u < 1) :
    roundingGamma u j + roundingGamma u k + roundingGamma u j * roundingGamma u k ≤
      roundingGamma u (j + k) := by
  simp only [roundingGamma_def, Nat.cast_add, add_mul] at h ⊢
  let a := (j : ℝ) * u
  let b := (k : ℝ) * u
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hu
  have hb : 0 ≤ b := mul_nonneg (Nat.cast_nonneg _) hu
  have hab : a + b < 1 := h
  have ha' : 0 < 1 - a := by linarith only [hab, hb]
  have hb' : 0 < 1 - b := by linarith only [hab, ha]
  have hden : 0 < 1 - (a + b) := sub_pos.mpr hab
  suffices a / (1 - a) + b / (1 - b) + a / (1 - a) * (b / (1 - b)) ≤
      (a + b) / (1 - (a + b)) from this
  have hfrac (c : ℝ) (hc : 1 - c ≠ 0) : 1 + c / (1 - c) = 1 / (1 - c) := by
    field_simp
    ring
  have hden_le : 1 - (a + b) ≤ (1 - a) * (1 - b) := by
    nlinarith only [mul_nonneg ha hb]
  have hle := one_div_le_one_div_of_le hden hden_le
  have heq : 1 / ((1 - a) * (1 - b)) = 1 / (1 - a) * (1 / (1 - b)) := by
    rw [div_mul_div_comm, one_mul]
  rw [heq, ← hfrac a ha'.ne', ← hfrac b hb'.ne',
    ← hfrac (a + b) hden.ne'] at hle
  linarith only [hle]

/-- Rounding factors have a nonnegative accumulated budget in its domain. -/
theorem roundingGamma_nonneg {u : ℝ} {k : ℕ} (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1) :
    0 ≤ roundingGamma u k :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr hk.le)

/-- The budget is monotone in the number of rounding factors below the pole. -/
theorem roundingGamma_mono {u : ℝ} {j k : ℕ} (hu : 0 ≤ u) (hj : j ≤ k)
    (hk : (k : ℝ) * u < 1) : roundingGamma u j ≤ roundingGamma u k := by
  have hjk : (j : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hu
  rw [roundingGamma_def, roundingGamma_def]
  apply (div_le_div_iff₀ (sub_pos.mpr (hjk.trans_lt hk)) (sub_pos.mpr hk)).mpr
  linarith only [hjk]

/-- A single forward error factor satisfies the accumulated rounding budget. -/
theorem le_roundingGamma_one {u : ℝ} (h : u < 1) : u ≤ roundingGamma u 1 := by
  simp only [roundingGamma_def, Nat.cast_one, one_mul]
  exact (le_div_iff₀ (sub_pos.mpr h)).mpr <| by nlinarith only [sq_nonneg u]

/-- The error of a product of two factors is bounded by their errors and the cross term. -/
theorem abs_mul_sub_one_le {a b p q : ℝ} (ha : |a - 1| ≤ p) (hb : |b - 1| ≤ q) :
    |a * b - 1| ≤ p + q + p * q := by
  have h : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
  rw [h]
  calc
    _ ≤ |a - 1| + |b - 1| + |(a - 1) * (b - 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (add_le_add ha hb)
        (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))

/-- A single signed factor is bounded by the single-operation budget. -/
theorem abs_zpow_one_add_sub_one_le {u δ : ℝ} (hu : 0 ≤ u) (h : u < 1)
    (hδ : |δ| ≤ u) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    |(1 + δ) ^ s - 1| ≤ roundingGamma u 1 := by
  rcases hs with rfl | rfl
  · simp only [zpow_one, add_sub_cancel_left]
    exact hδ.trans (le_roundingGamma_one h)
  · have hd : 0 < 1 + δ := by linarith only [(abs_le.mp hδ).1, h]
    have heq : 1 - (1 + δ) = -δ := by ring
    simp only [zpow_neg, zpow_one, ← one_div, div_sub_one hd.ne', heq,
      abs_div, abs_neg, abs_of_pos hd, roundingGamma_def, Nat.cast_one, one_mul]
    exact (div_le_div_of_nonneg_right hδ hd.le).trans
      (div_le_div_of_nonneg_left hu (sub_pos.mpr h) (by linarith only [(abs_le.mp hδ).1]))

/-- **Gap 1.8.** A signed product of rounding factors satisfies the accumulated bound. -/
theorem hasRelativeError_prod_zpow {u : ℝ} {n : ℕ} (hn : (n : ℝ) * u < 1)
    {δ : Fin n → ℝ} (hδ : ∀ j, |δ j| ≤ u) {s : Fin n → ℤ}
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    HasRelativeError (roundingGamma u n) 1 (∏ j, (1 + δ j) ^ s j) := by
  induction n with
  | zero =>
      exact ⟨0, by simp [roundingGamma_def], by simp⟩
  | succ n ih =>
      have hu : 0 ≤ u := (abs_nonneg _).trans (hδ 0)
      have hu' : u < 1 := by
        have h : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact ((by simpa only [one_mul] using mul_le_mul_of_nonneg_right h hu) :
          u ≤ (↑(n + 1) : ℝ) * u).trans_lt hn
      have htail : (n : ℝ) * u < 1 := by
        rw [Nat.cast_succ, add_mul, one_mul] at hn
        exact (le_add_of_nonneg_right hu).trans_lt hn
      obtain ⟨ε, hε, hprod⟩ := ih htail (fun i ↦ hδ i.succ) (fun i ↦ hs i.succ)
      simp only [one_mul] at hprod
      have htail_bound : |(∏ j : Fin n, (1 + δ j.succ) ^ s j.succ) - 1| ≤
          roundingGamma u n := by
        simpa only [hprod, add_sub_cancel_left] using hε
      rw [Fin.prod_univ_succ]
      have hadd := roundingGamma_add_bound hu (j := n) (k := 1) hn
      refine ⟨_, (abs_mul_sub_one_le (abs_zpow_one_add_sub_one_le hu hu' (hδ 0) (hs 0))
        htail_bound).trans ?_, ?_⟩
      · simpa only [add_comm (roundingGamma u n) (roundingGamma u 1),
          mul_comm (roundingGamma u n) (roundingGamma u 1)] using hadd
      · rw [one_mul, add_sub_cancel]

/-- A finite summation tree records addition order and preserves multiplicities. -/
inductive SumTree (ι : Type*)
  | leaf (i : ι)
  | branch (left right : SumTree ι)

namespace SumTree

variable {ι : Type*}

/-- Leaves in evaluation order. -/
def leaves : SumTree ι → List ι
  | .leaf i => [i]
  | .branch a b => a.leaves ++ b.leaves

/-- Depth in additions. -/
def depth : SumTree ι → ℕ
  | .leaf _ => 0
  | .branch a b => max a.depth b.depth + 1

/-- Evaluation with one rounding operation at each branch. -/
def eval (rnd : ℝ → ℝ) (x : ι → ℝ) : SumTree ι → ℝ
  | .leaf i => x i
  | .branch a b => rnd (a.eval rnd x + b.eval rnd x)

/-- The standard model holds at every internal addition. -/
def HasStableEvaluation (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) : SumTree ι → Prop
  | .leaf _ => True
  | .branch a b =>
    a.HasStableEvaluation rnd x u ∧ b.HasStableEvaluation rnd x u ∧
    HasRelativeError u (a.eval rnd x + b.eval rnd x) ((branch a b).eval rnd x)

/-- The absolute value of a leaf sum is bounded by the sum of leaf magnitudes. -/
theorem abs_sum_le_sum_abs_leaves (t : SumTree ι) (x : ι → ℝ) :
    |(t.leaves.map x).sum| ≤ (t.leaves.map fun i ↦ |x i|).sum := by
  induction t with
  | leaf i => simp [leaves]
  | branch a b iha ihb =>
      simp only [leaves, List.map_append, List.sum_append]
      exact (abs_add_le _ _).trans (add_le_add iha ihb)

/-- A tree with preperturbed leaves has the leaf error budget plus its depth in additions. -/
theorem abs_eval_sub_sum_le_of_leaf_error (t : SumTree ι)
    {rnd : ℝ → ℝ} {x y : ι → ℝ} {u : ℝ} {k : ℕ} (hu : 0 ≤ u)
    (hd : ((k + t.depth : ℕ) : ℝ) * u < 1) (ht : t.HasStableEvaluation rnd x u)
    (hleaf : ∀ i, |x i - y i| ≤ roundingGamma u k * |y i|) :
    |t.eval rnd x - (t.leaves.map y).sum| ≤
      roundingGamma u (k + t.depth) * (t.leaves.map fun i ↦ |y i|).sum := by
  induction t with
  | leaf i => simpa only [depth, eval, leaves, Nat.add_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] using hleaf i
  | branch a b iha ihb =>
      rw [HasStableEvaluation] at ht
      obtain ⟨ha, hb, δ, hδ, hnode⟩ := ht
      let d := k + max a.depth b.depth
      have hd' : ((d + 1 : ℕ) : ℝ) * u < 1 := by simpa only [depth, ← Nat.add_assoc] using hd
      have hlt {i : ℕ} (hi : i ≤ d + 1) : (i : ℝ) * u < 1 :=
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hu).trans_lt hd'
      have hweaken {i : ℕ} (hi : i ≤ d) (w : ℝ) (hw : 0 ≤ w) :
          roundingGamma u i * w ≤ roundingGamma u d * w :=
        mul_le_mul_of_nonneg_right (roundingGamma_mono hu hi (hlt (Nat.le_succ d))) hw
      have ha' : k + a.depth ≤ d := Nat.add_le_add_left (le_max_left _ _) k
      have hb' : k + b.depth ≤ d := Nat.add_le_add_left (le_max_right _ _) k
      have hnonneg (v : SumTree ι) : 0 ≤ (v.leaves.map fun i ↦ |y i|).sum :=
        List.sum_nonneg fun _ h ↦ by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
          exact abs_nonneg _
      have hdiff : |a.eval rnd x + b.eval rnd x - (a.leaves.map y ++ b.leaves.map y).sum| ≤
          roundingGamma u d * ((a.leaves ++ b.leaves).map fun i ↦ |y i|).sum := by
        rw [List.map_append, List.sum_append, List.sum_append, mul_add]
        have heq : a.eval rnd x + b.eval rnd x - ((a.leaves.map y).sum + (b.leaves.map y).sum) =
            (a.eval rnd x - (a.leaves.map y).sum) + (b.eval rnd x - (b.leaves.map y).sum) := by ring
        rw [heq]
        exact (abs_add_le _ _).trans (add_le_add
          ((iha (hlt (ha'.trans (Nat.le_succ d))) ha).trans (hweaken ha' _ (hnonneg a)))
          ((ihb (hlt (hb'.trans (Nat.le_succ d))) hb).trans (hweaken hb' _ (hnonneg b))))
      rw [hnode, leaves, List.map_append]
      have hu' : u < 1 := by simpa only [Nat.cast_one, one_mul] using hlt (Nat.succ_le_succ
        (Nat.zero_le d))
      have hδ' := hδ.trans (le_roundingGamma_one hu')
      exact (abs_mul_one_add_sub_le_of_abs_sub_le hdiff
        (by simpa only [leaves, List.map_append] using (branch a b).abs_sum_le_sum_abs_leaves y)
        hδ').trans (mul_le_mul_of_nonneg_right (roundingGamma_add_bound hu hd')
          (hnonneg (branch a b)))

/-- Every finite binary sum tree has more leaves than the number of additions on any path. -/
theorem depth_lt_length_leaves (t : SumTree ι) : t.depth < t.leaves.length := by
  induction t with
  | leaf i => simp [depth, leaves]
  | branch a b iha ihb =>
      simp only [depth, leaves, List.length_append]
      omega

/-- **Gap 1.9.** Summation on a tree of depth $d$ has budget $\gamma_d$. -/
theorem abs_eval_sub_sum_le (t : SumTree ι) {rnd : ℝ → ℝ} {x : ι → ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hd : (t.depth : ℝ) * u < 1) (ht : t.HasStableEvaluation rnd x u) :
    |t.eval rnd x - (t.leaves.map x).sum| ≤
      roundingGamma u t.depth * (t.leaves.map fun i ↦ |x i|).sum := by
  simpa only [Nat.zero_add] using t.abs_eval_sub_sum_le_of_leaf_error (k := 0) (y := x)
    hu (by simpa only [Nat.zero_add] using hd) ht (fun i ↦ by simp [roundingGamma_def])

/-- The absolute sum of computed internal nodes, including the root when it is a branch. -/
def sumAbsComputed (rnd : ℝ → ℝ) (x : ι → ℝ) : SumTree ι → ℝ
  | .leaf _ => 0
  | .branch a b => |(branch a b).eval rnd x| + a.sumAbsComputed rnd x + b.sumAbsComputed rnd x

/-- The inverse form of the standard model at each addition. -/
def HasInverseRelativeError (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) : SumTree ι → Prop
  | .leaf _ => True
  | .branch a b => a.HasInverseRelativeError rnd x u ∧ b.HasInverseRelativeError rnd x u ∧
    HasRelativeError u ((branch a b).eval rnd x) (a.eval rnd x + b.eval rnd x)

/-- **Gap 1.9.** Summation errors can be bounded a posteriori by the magnitudes
of computed intermediate sums using the inverse relative-error model. -/
theorem abs_eval_sub_sum_le_computed (t : SumTree ι) {rnd : ℝ → ℝ} {x : ι → ℝ} {u : ℝ}
    (ht : t.HasInverseRelativeError rnd x u) :
    |t.eval rnd x - (t.leaves.map x).sum| ≤ u * t.sumAbsComputed rnd x := by
  induction t with
  | leaf i =>
      simp [eval, leaves, sumAbsComputed]
  | branch a b iha ihb =>
      rw [HasInverseRelativeError] at ht
      obtain ⟨ha, hb, hnode⟩ := ht
      have hlocal_bound := hnode.abs_sub_le
      rw [abs_sub_comm] at hlocal_bound
      rw [leaves, List.map_append, List.sum_append, sumAbsComputed]
      calc
        _ = |((branch a b).eval rnd x - (a.eval rnd x + b.eval rnd x)) +
              (a.eval rnd x - (a.leaves.map x).sum) +
              (b.eval rnd x - (b.leaves.map x).sum)| := by
          congr 1
          ring
        _ ≤ |(branch a b).eval rnd x - (a.eval rnd x + b.eval rnd x)| +
            |a.eval rnd x - (a.leaves.map x).sum| +
            |b.eval rnd x - (b.leaves.map x).sum| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by
          simpa only [mul_add] using add_le_add (add_le_add hlocal_bound (iha ha)) (ihb hb)

/-- A scalar dot-product error within a weighted budget can be assigned to perturbations
of the first factor, with the same relative budget at every entry. -/
theorem exists_dotProduct_perturbation {ι : Type*} [Fintype ι] (x y : ι → ℝ) {e γ : ℝ}
    (hγ : 0 ≤ γ) (hbound : |e| ≤ γ * ∑ i, |x i * y i|) :
    ∃ dx : ι → ℝ, (∀ i, |dx i| ≤ γ * |x i|) ∧ (∑ i, dx i * y i) = e := by
  let p := fun i ↦ x i * y i
  let S := ∑ i, |p i|
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hb : |e| ≤ γ * S := hbound
  by_cases hS : S = 0
  · have he : e = 0 := abs_eq_zero.mp <| le_antisymm
      (by simpa only [hS, mul_zero] using hb) (abs_nonneg _)
    refine ⟨fun _ ↦ 0, fun i ↦ ?_, ?_⟩
    · simpa only [abs_zero] using mul_nonneg hγ (abs_nonneg (x i))
    · simp [he]
  have hpos := lt_of_le_of_ne hs (Ne.symm hS)
  let dx : ι → ℝ := fun i ↦ if 0 ≤ y i then e / S * |x i| else -(e / S * |x i|)
  have habs : |e / S| ≤ γ := by
    rw [abs_div, abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr hb
  refine ⟨dx, fun i ↦ ?_, ?_⟩
  · by_cases hiy : 0 ≤ y i
    · simpa only [dx, ite_eq_left hiy, abs_mul, abs_abs] using
        mul_le_mul_of_nonneg_right habs (abs_nonneg (x i))
    · simpa only [dx, ite_eq_right hiy, abs_neg, abs_mul, abs_abs] using
        mul_le_mul_of_nonneg_right habs (abs_nonneg (x i))
  · have hterm (i : ι) : dx i * y i = e / S * |p i| := by
      by_cases hiy : 0 ≤ y i
      · simp only [dx, ite_eq_left hiy, p, abs_mul, abs_of_nonneg hiy, mul_assoc]
      · simp only [dx, ite_eq_right hiy, p, abs_mul, abs_of_neg (lt_of_not_ge hiy), neg_mul,
          mul_neg, mul_assoc]
    simp only [hterm, ← Finset.mul_sum]
    exact div_mul_cancel₀ _ hS

/-- A sum tree that enumerates a finite dot product gives a componentwise perturbation. -/
theorem exists_dotProduct_eq_sum_mul_perturbed_of_sums {ι : Type*} [Fintype ι]
    {m : ℕ} {t : SumTree ι} {x y : ι → ℝ} {u : ℝ} {rnd : ℝ → ℝ}
    (hu : 0 ≤ u) (hm : (m : ℝ) * u < 1) (hlen : t.leaves.length = m)
    (hsum : ∀ f : ι → ℝ, (t.leaves.map f).sum = ∑ i, f i)
    (hmul : ∀ i, HasRelativeError u (x i * y i) (rnd (x i * y i)))
    (ht : t.HasStableEvaluation rnd (fun i ↦ rnd (x i * y i)) u) :
    ∃ dx : ι → ℝ, (∀ i, |dx i| ≤ roundingGamma u m * |x i|) ∧
      t.eval rnd (fun i ↦ rnd (x i * y i)) = ∑ i, (x i + dx i) * y i := by
  let p := fun i ↦ x i * y i
  have hdepth := t.depth_lt_length_leaves
  have hd : 1 + t.depth ≤ m := by omega
  have hsmall : ((1 + t.depth : ℕ) : ℝ) * u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) hu).trans_lt hm
  have hm' : (1 : ℕ) ≤ m := by omega
  have hmono : u ≤ (m : ℝ) * u := by
    simpa only [Nat.cast_one, one_mul] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm') hu
  have hu' : u < 1 := hmono.trans_lt hm
  have hleaf (i : ι) : |rnd (p i) - p i| ≤ roundingGamma u 1 * |p i| :=
    (hmul i).abs_sub_le.trans (mul_le_mul_of_nonneg_right (le_roundingGamma_one hu')
      (abs_nonneg _))
  let S := ∑ i, |p i|
  let e := t.eval rnd (fun i ↦ rnd (p i)) - ∑ i, p i
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hbound : |e| ≤ roundingGamma u m * S := by
    have h := t.abs_eval_sub_sum_le_of_leaf_error hu hsmall ht hleaf
    rw [hsum, hsum] at h
    exact h.trans (mul_le_mul_of_nonneg_right (roundingGamma_mono hu hd hm) hs)
  obtain ⟨dx, hdx, hpert⟩ := exists_dotProduct_perturbation x y
    (roundingGamma_nonneg hu hm) hbound
  refine ⟨dx, hdx, ?_⟩
  simp only [add_mul, Finset.sum_add_distrib, hpert, e, p]
  abel

/-- **Gap 1.10.** A dot product computed with one multiplication per entry admits a
componentwise backward error under the standard arithmetic model. -/
theorem exists_dotProduct_eq_sum_mul_perturbed {n : ℕ} {t : SumTree (Fin n)}
    {x y : Fin n → ℝ} {u : ℝ} {rnd : ℝ → ℝ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (hperm : t.leaves.Perm (List.finRange n))
    (hmul : ∀ i, HasRelativeError u (x i * y i) (rnd (x i * y i)))
    (ht : t.HasStableEvaluation rnd (fun i ↦ rnd (x i * y i)) u) :
    ∃ dx : Fin n → ℝ, (∀ i, |dx i| ≤ roundingGamma u n * |x i|) ∧
      t.eval rnd (fun i ↦ rnd (x i * y i)) = ∑ i, (x i + dx i) * y i := by
  refine exists_dotProduct_eq_sum_mul_perturbed_of_sums hu hn
    (hperm.length_eq.trans List.length_finRange) ?_ hmul ht
  intro f
  rw [(hperm.map f).sum_eq, List.finRange, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **Gap 1.10.** Computing each matrix entry by a rounded inner product
gives the componentwise matrix multiplication error estimate. -/
theorem abs_matrixProduct_error_le {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (t : Fin m → Fin p → SumTree (Fin n))
    {rnd : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (hperm : ∀ i j, (t i j).leaves.Perm (List.finRange n))
    (hmul : ∀ i k j, HasRelativeError u (A i k * B k j) (rnd (A i k * B k j)))
    (ht : ∀ i j, (t i j).HasStableEvaluation rnd (fun k ↦ rnd (A i k * B k j)) u) :
    ∀ i j, |(A * B) i j - (t i j).eval rnd (fun k ↦ rnd (A i k * B k j))| ≤
      roundingGamma u n * ∑ k, |A i k| * |B k j| := by
  intro i j
  obtain ⟨dx, hdx, heval⟩ :=
    exists_dotProduct_eq_sum_mul_perturbed hu hn (hperm i j) (fun k ↦ hmul i k j) (ht i j)
  rw [Matrix.mul_apply, heval, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, |A i k * B k j - (A i k + dx k) * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ roundingGamma u n * ∑ k, |A i k| * |B k j| := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ ↦ ?_
      have hk : A i k * B k j - (A i k + dx k) * B k j = -(dx k) * B k j := by ring
      rw [hk, abs_mul, abs_neg, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdx k) (abs_nonneg _)

end SumTree

/-- Kahan's computed sum and its compensation. -/
def kahanAccumulator (rnd : ℝ → ℝ) (xs : List ℝ) : ℝ × ℝ :=
  xs.foldl (fun (s, e) x ↦
    let y := rnd (x + e)
    let t := rnd (s + y)
    (t, rnd (rnd (s - t) + y))) (0, 0)

/-- The standard model at the four operations of a Kahan update. -/
def IsStableKahanStep (rnd : ℝ → ℝ) (u s e x : ℝ) : Prop :=
  let y := rnd (x + e)
  let t := rnd (s + y)
  let z := rnd (s - t)
  HasRelativeError u (x + e) y ∧ HasRelativeError u (s + y) t ∧
    HasRelativeError u (s - t) z ∧ HasRelativeError u (z + y) (rnd (z + y))

/-- **Gap 1.12.** Kahan error bound with first-order coefficient $2u$ and a uniform
quadratic remainder in the small accumulated-error regime. -/
theorem abs_kahanAccumulator_sub_sum_le :
    ∃ C > (0 : ℝ), ∀ (u : ℝ) (rnd : ℝ → ℝ) (xs : List ℝ),
      0 ≤ u → (xs.length : ℝ) * u ≤ 1 / 2 →
      (∀ (xs₀ : List ℝ) (x : ℝ) (suffix : List ℝ), xs = xs₀ ++ x :: suffix →
        IsStableKahanStep rnd u (kahanAccumulator rnd xs₀).1
          (kahanAccumulator rnd xs₀).2 x) →
      |(kahanAccumulator rnd xs).1 - xs.sum| ≤
        (2 * u + C * xs.length * u ^ 2) * (xs.map abs).sum := by
  sorry

/-- Rounded forward substitution with error at each row operation and arbitrary addition
orders within rows. The first row performs only division. -/
def IsRoundedForwardSubstitution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (rnd : ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ i, ∃ s : ℝ,
    (if i.val = 0 then s = 0 else
      ∃ t : SumTree {j : Fin n // j < i},
        t.leaves.Perm (Finset.univ.toList : List {j : Fin n // j < i}) ∧
        t.HasStableEvaluation rnd (fun j ↦ rnd (T i j.val * x j.val)) u ∧
        s = t.eval rnd (fun j ↦ rnd (T i j.val * x j.val))) ∧
    (∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) ∧
    (if i.val = 0 then HasRelativeError u (b i / T i i) (x i) else
      HasRelativeError u (b i - s) (rnd (b i - s)) ∧
      HasRelativeError u (rnd (b i - s) / T i i) (x i))

/-- One division, with an optional rounded numerator, perturbs only the divisor.
The integer budget is one for an exact numerator and two for a rounded one. -/
theorem exists_perturbed_divisor {u a t x : ℝ} {k : ℕ} (hu : 0 ≤ u) (hu₁ : u < 1)
    (hk : (k : ℝ) * u < 1) (ht : t ≠ 0)
    (hx : (k = 1 ∧ HasRelativeError u (a / t) x) ∨
      (k = 2 ∧ ∃ b, HasRelativeError u a b ∧ HasRelativeError u (b / t) x)) :
    ∃ d, |d| ≤ roundingGamma u k * |t| ∧ (t + d) * x = a := by
  have perturb (r : ℝ) (hr : |r - 1| ≤ roundingGamma u k) (he : r * t * x = a) :
      ∃ d, |d| ≤ roundingGamma u k * |t| ∧ (t + d) * x = a := by
    refine ⟨(r - 1) * t, ?_, ?_⟩
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    · calc
        _ = r * t * x := by ring
        _ = _ := he
  have pos {δ : ℝ} (hδ : |δ| ≤ u) : 0 < 1 + δ := by
    linarith only [(abs_le.mp hδ).1, hu₁]
  have one {δ : ℝ} (hδ : |δ| ≤ u) : |(1 + δ)⁻¹ - 1| ≤ roundingGamma u 1 := by
    simpa only [zpow_neg_one] using abs_zpow_one_add_sub_one_le hu hu₁ hδ (Or.inr rfl)
  rcases hx with ⟨h₁, δ, hδ, hδeq⟩ | ⟨h₂, b, ⟨δ, hδ, hδeq⟩, ⟨ε, hε, hεeq⟩⟩
  · refine perturb _ (by simpa only [h₁] using one hδ) ?_
    rw [hδeq]
    field_simp [(pos hδ).ne', ht]
  · have herr := abs_mul_sub_one_le (one hδ) (one hε)
    have hγ := roundingGamma_add_bound hu (j := 1) (k := 1) (by simpa only [h₂] using hk)
    refine perturb _ (by simpa only [h₂] using herr.trans hγ) ?_
    rw [hεeq, hδeq]
    field_simp [(pos hδ).ne', (pos hε).ne', ht]

/-- The strict subdiagonal dot product in a row has a componentwise backward error. -/
theorem exists_subdiagonal_backwardError {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) {rnd : ℝ → ℝ} {u s : ℝ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (i : Fin n) (hs : if i.val = 0 then s = 0 else
      ∃ t : SumTree {j : Fin n // j < i},
        t.leaves.Perm (Finset.univ.toList : List {j : Fin n // j < i}) ∧
        t.HasStableEvaluation rnd (fun j ↦ rnd (T i j.val * x j.val)) u ∧
        s = t.eval rnd (fun j ↦ rnd (T i j.val * x j.val)))
    (hmul : ∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) :
    ∃ e : {j : Fin n // j < i} → ℝ, (∀ j, |e j| ≤ roundingGamma u n * |T i j.val|) ∧
      ∑ j : {j : Fin n // j < i}, (T i j.val + e j) * x j.val = s := by
  by_cases hi : i.val = 0
  · rw [ite_eq_left hi] at hs
    let hEmpty : IsEmpty {j : Fin n // j < i} := ⟨fun j ↦
      (Nat.not_lt_zero j.val.val) (hi ▸ Fin.lt_def.mp j.prop)⟩
    refine ⟨fun j ↦ isEmptyElim j, fun j ↦ isEmptyElim j, ?_⟩
    simp [hs]
  rw [ite_eq_right hi] at hs
  obtain ⟨t, hperm, ht, ht_sum⟩ := hs
  have hcard : Fintype.card {j : Fin n // j < i} = i.val := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter fun j : Fin n ↦ j < i) = Finset.Iio i := by
      ext j
      simp
    rw [hset, Fin.card_Iio]
  have hlen : t.leaves.length = i.val := by
    rw [hperm.length_eq, Finset.length_toList, Finset.card_univ, hcard]
  have hsum (f : {j : Fin n // j < i} → ℝ) : (t.leaves.map f).sum = ∑ j, f j := by
    rw [(hperm.map f).sum_eq, Finset.sum_eq_multiset_sum, ← Finset.coe_toList,
      Multiset.map_coe, Multiset.sum_coe]
  have hsmall : (i.val : ℝ) * u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr i.isLt.le) hu).trans_lt hn
  obtain ⟨e, he, hsum⟩ := SumTree.exists_dotProduct_eq_sum_mul_perturbed_of_sums
    hu hsmall hlen hsum (fun j ↦ hmul _ j.prop) ht
  refine ⟨e, fun j ↦ (he j).trans (mul_le_mul_of_nonneg_right
    (roundingGamma_mono hu i.isLt.le hn) (abs_nonneg _)), ?_⟩
  rw [ht_sum, hsum]

/-- A lower-triangular row is the sum of its diagonal and strict subdiagonal terms. -/
theorem exists_row_backwardError {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (htri : ∀ i j, i < j → T i j = 0) (i : Fin n) {s d : ℝ}
    (hd : |d| ≤ roundingGamma u n * |T i i|) (hds : (T i i + d) * x i = b i - s)
    (e : {j : Fin n // j < i} → ℝ) (he : ∀ j, |e j| ≤ roundingGamma u n * |T i j.val|)
    (hes : ∑ j : {j : Fin n // j < i}, (T i j.val + e j) * x j.val = s) :
    ∃ r : Fin n → ℝ, (∀ j, |r j| ≤ roundingGamma u n * |T i j|) ∧
      ∑ j, (T i j + r j) * x j = b i := by
  let r : Fin n → ℝ := fun j ↦ if j = i then d else if h : j < i then e ⟨j, h⟩ else 0
  have hsub (j : {j : Fin n // j < i}) : r j.val = e j := by
    simp only [r, ite_eq_right j.prop.ne, dite_eq_left j.prop]
  have hdiag : r i = d := by simp [r]
  refine ⟨r, fun j ↦ ?_, ?_⟩
  · rcases lt_trichotomy j i with hj | rfl | hj
    · simpa only [hsub ⟨j, hj⟩] using (he ⟨j, hj⟩)
    · simpa only [hdiag] using hd
    · have hzero : r j = 0 := by
        simp only [r, ite_eq_right hj.ne', dite_eq_right (not_lt_of_ge hj.le)]
      simp only [hzero, abs_zero]
      exact mul_nonneg (roundingGamma_nonneg hu hn) (abs_nonneg _)
  have hsubset : Finset.Iio i ⊆ Finset.univ.erase i := fun j hj ↦
    Finset.mem_erase.mpr ⟨(Finset.mem_Iio.mp hj).ne, Finset.mem_univ _⟩
  have heq : (∑ j ∈ Finset.Iio i, (T i j + r j) * x j) =
      ∑ j ∈ Finset.univ.erase i, (T i j + r j) * x j := by
    refine Finset.sum_subset hsubset fun j hj hji ↦ ?_
    have hlt : i < j := lt_of_le_of_ne (le_of_not_gt fun h ↦ hji (Finset.mem_Iio.mpr h))
      (Finset.mem_erase.mp hj).1.symm
    simp only [r, ite_eq_right hlt.ne', dite_eq_right (not_lt_of_ge hlt.le),
      htri _ _ hlt, add_zero, zero_mul]
  calc
    _ = (∑ j ∈ Finset.univ.erase i, (T i j + r j) * x j) + (T i i + r i) * x i :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    _ = s + (b i - s) := by
      have hsubtype := Finset.sum_subtype (F := inferInstance) (Finset.Iio i)
        (fun j : Fin n ↦ Finset.mem_Iio) (fun j ↦ (T i j + r j) * x j)
      rw [hdiag, hds, ← heq, hsubtype]
      simp only [hsub, hes]
    _ = b i := by abel

/-- **Gap 1.13.** Forward substitution has a componentwise backward-error certificate. -/
theorem IsRoundedForwardSubstitution.exists_backwardError {n : ℕ}
    {T : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ} {rnd : ℝ → ℝ} {u : ℝ}
    (h : IsRoundedForwardSubstitution T b x rnd u) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (htri : ∀ i j, i < j → T i j = 0)
    (hdiag : ∀ i, T i i ≠ 0) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, (T + E) *ᵥ x = b ∧
      ∀ i j, |E i j| ≤ roundingGamma u n * |T i j| := by
  classical
  have hrow (i : Fin n) :
      ∃ r : Fin n → ℝ, (∀ j, |r j| ≤ roundingGamma u n * |T i j|) ∧
        ∑ j, (T i j + r j) * x j = b i := by
    obtain ⟨s, hs, hmul, hstep⟩ := h i
    obtain ⟨e, he, hes⟩ := exists_subdiagonal_backwardError T x hu hn i hs hmul
    let k := if i.val = 0 then 1 else 2
    have hk : k ≤ n := by
      by_cases hi : i.val = 0
      · simpa only [k, ite_eq_left hi] using Nat.one_le_of_lt (hi ▸ i.isLt)
      · have hi' := i.isLt
        simp only [k, ite_eq_right hi]
        omega
    have hlt {l : ℕ} (hl : l ≤ n) : (l : ℝ) * u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hl) hu).trans_lt hn
    have hu₁ : u < 1 := by
      simpa only [Nat.cast_one, one_mul] using
        hlt (Nat.one_le_of_lt (i.val.zero_le.trans_lt i.isLt))
    obtain ⟨d, hd, hds⟩ := exists_perturbed_divisor hu hu₁ (hlt hk) (hdiag i)
        (a := b i - s) (x := x i) (by
      by_cases hi : i.val = 0
      · rw [ite_eq_left hi] at hs hstep
        exact Or.inl ⟨ite_eq_left hi, by simpa only [hs, sub_zero] using hstep⟩
      · rw [ite_eq_right hi] at hstep
        exact Or.inr ⟨ite_eq_right hi, _, hstep⟩)
    exact exists_row_backwardError T b x hu hn htri i
      (hd.trans (mul_le_mul_of_nonneg_right (roundingGamma_mono hu hk hn) (abs_nonneg _)))
      hds e he hes
  choose r hr hrs using hrow
  refine ⟨Matrix.of r, ?_, hr⟩
  ext i
  exact hrs i

end NASC
