module

public import Mathlib.Data.EReal.Inv

/-!
# Floating-point formats and correct rounding

Finite radix formats with gradual underflow, their numbers, spacing and range, correct
rounding in the four directions, the relative error of correct rounding, exact subnormal
addition, and the error-free transformations. Gap numbers refer to section 1 of `GAPS.md`.

## Notation

* `β = F.radix`, `p = F.precision`; a number is `F.value m e = m * β ^ (e - p + 1)` with
  `|m| < β ^ p` and `emin ≤ e ≤ emax`.
* `u = F.unitRoundoff mode` is `β ^ (1 - p) / 2` for rounding to nearest and `β ^ (1 - p)` for
  a directed rounding.

## Main definitions

* `NASC.FloatingPointFormat`, `FloatingPointFormat.numbers`, `FloatingPointFormat.spacing`,
  `FloatingPointFormat.minNormal`, `FloatingPointFormat.maxFinite`.
* `FloatingPointFormat.RoundingMode`, `FloatingPointFormat.IsRounding`,
  `FloatingPointFormat.unitRoundoff`, `FloatingPointFormat.Nearest`.
* `FloatingPointFormat.fastTwoSum`, `FloatingPointFormat.twoSum`,
  `FloatingPointFormat.twoMultFMA`.

## Main results

* `FloatingPointFormat.isLeast_spacing`, `FloatingPointFormat.isLeast_minNormal`,
  `FloatingPointFormat.isGreatest_maxFinite`,
  `FloatingPointFormat.numbers_subset_range_mul_spacing`,
  `FloatingPointFormat.neg_mem_numbers_iff`: the extrema, lattice and symmetry of the format.
* `FloatingPointFormat.exists_minimal_exponent`: the representation with least exponent is
  normalized or subnormal.
* `FloatingPointFormat.IsRounding.monotone`, `FloatingPointFormat.IsRounding.apply_coe_of_mem`:
  correct rounding is monotone and fixes numbers.
* `FloatingPointFormat.IsRounding.exists_eq_mul_one_add`: the relative error of correct
  rounding on the normal range, in both the multiplicative and the divisive form.
* `FloatingPointFormat.add_mem_numbers_of_abs_lt`: addition below the normal range is exact.
* `FloatingPointFormat.fastTwoSum_add`, `FloatingPointFormat.twoSum_add`,
  `FloatingPointFormat.twoMultFMA_add`: the error-free transformations.
-/

public section

noncomputable section

namespace NASC
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
  /-- The exponent window is nonempty. -/
  emin_le_emax : emin ≤ emax

namespace FloatingPointFormat

variable (F : FloatingPointFormat)

/-- The real value of an integral significand at a specified exponent. -/
def value (m e : ℤ) : ℝ := (m : ℝ) * (F.radix : ℝ) ^ (e - (F.precision : ℤ) + 1)

/-- The value of a significand and exponent is `m * β ^ (e - p + 1)`. -/
theorem value_def (m e : ℤ) :
    F.value m e = (m : ℝ) * (F.radix : ℝ) ^ (e - (F.precision : ℤ) + 1) := (rfl)

/-- An admissible significand and exponent in the format. -/
def Valid (m e : ℤ) : Prop :=
  |m| < (F.radix : ℤ) ^ F.precision ∧ F.emin ≤ e ∧ e ≤ F.emax

/-- A significand and exponent are admissible when `|m| < β ^ p` and `emin ≤ e ≤ emax`. -/
theorem valid_iff {m e : ℤ} :
    F.Valid m e ↔ |m| < (F.radix : ℤ) ^ F.precision ∧ F.emin ≤ e ∧ e ≤ F.emax := Iff.rfl

/-- The real numbers representable in the format. -/
def numbers : Set ℝ := {x | ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x}

/-- A representable number has a valid significand and exponent. -/
theorem mem_numbers_iff {x : ℝ} :
    x ∈ F.numbers ↔ ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x := Iff.rfl

/-- The spacing at the bottom of the exponent range. -/
def spacing : ℝ := (F.radix : ℝ) ^ (F.emin - (F.precision : ℤ) + 1)

/-- The bottom spacing is `β ^ (emin - p + 1)`. -/
theorem spacing_def : F.spacing = (F.radix : ℝ) ^ (F.emin - (F.precision : ℤ) + 1) := (rfl)

/-- The smallest positive normal number. -/
def minNormal : ℝ := (F.radix : ℝ) ^ F.emin

/-- The smallest positive normal number is `β ^ emin`. -/
theorem minNormal_def : F.minNormal = (F.radix : ℝ) ^ F.emin := (rfl)

/-- The largest representable number. -/
def maxFinite : ℝ := F.value ((F.radix : ℤ) ^ F.precision - 1) F.emax

/-- The largest representable number has the largest significand at the top exponent. -/
theorem maxFinite_def : F.maxFinite = F.value ((F.radix : ℤ) ^ F.precision - 1) F.emax := (rfl)

/-- The normal real input range, including both signs. -/
def normalRange : Set ℝ := {x | F.minNormal ≤ |x| ∧ |x| ≤ F.maxFinite}

/-- Membership of the normal range is the pair of magnitude bounds. -/
theorem mem_normalRange_iff {x : ℝ} :
    x ∈ F.normalRange ↔ F.minNormal ≤ |x| ∧ |x| ≤ F.maxFinite := Iff.rfl

/-- The radix, as a real number, exceeds one. -/
theorem one_lt_radix : (1 : ℝ) < F.radix := by
  exact_mod_cast (Nat.one_lt_two.trans_le F.two_le_radix)

/-- The bottom spacing is positive. -/
theorem spacing_pos : 0 < F.spacing := zpow_pos (zero_lt_one.trans F.one_lt_radix) _

/-- A number at an exponent `e ≥ emin` is an integral multiple of the bottom spacing. -/
theorem value_eq_mul_spacing {m e : ℤ} (he : F.emin ≤ e) :
    F.value m e = ((m * (F.radix : ℤ) ^ (e - F.emin).toNat : ℤ) : ℝ) * F.spacing := by
  have hβ : (F.radix : ℝ) ≠ 0 := (zero_lt_one.trans F.one_lt_radix).ne'
  have hpow : (F.radix : ℝ) ^ (e - F.emin).toNat = (F.radix : ℝ) ^ (e - F.emin) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr he)]
  rw [value_def, spacing_def, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hpow, mul_assoc,
    ← zpow_add₀ hβ]
  ring_nf

/-- **Gap 1.1.** Every number is an integral multiple of the bottom spacing. -/
theorem numbers_subset_range_mul_spacing :
    F.numbers ⊆ Set.range (fun m : ℤ ↦ (m : ℝ) * F.spacing) := by
  rintro x ⟨m, e, hv, rfl⟩
  exact ⟨_, (F.value_eq_mul_spacing hv.2.1).symm⟩

/-- **Gap 1.1.** The format is symmetric under negation. -/
theorem neg_mem_numbers_iff {x : ℝ} : -x ∈ F.numbers ↔ x ∈ F.numbers := by
  have key {y : ℝ} (hy : y ∈ F.numbers) : -y ∈ F.numbers := by
    obtain ⟨m, e, hv, rfl⟩ := hy
    refine ⟨-m, e, ⟨by rw [abs_neg]; exact hv.1, hv.2⟩, ?_⟩
    rw [value_def, value_def, Int.cast_neg, neg_mul]
  exact ⟨fun h ↦ by simpa only [neg_neg] using key h, key⟩

/-- **Gap 1.1.** The bottom spacing is the least positive number. -/
theorem isLeast_spacing : IsLeast {x ∈ F.numbers | 0 < x} F.spacing := by
  have hp : (1 : ℤ) < (F.radix : ℤ) ^ F.precision :=
    one_lt_pow₀ (by exact_mod_cast Nat.one_lt_two.trans_le F.two_le_radix)
      (by have := F.two_le_precision; omega)
  refine ⟨⟨⟨1, F.emin, ⟨by simpa only [abs_one] using hp, le_rfl, F.emin_le_emax⟩, ?_⟩,
    F.spacing_pos⟩, ?_⟩
  · rw [value_def, spacing_def, Int.cast_one, one_mul]
  rintro x ⟨hx, hx₀⟩
  obtain ⟨k, rfl⟩ := F.numbers_subset_range_mul_spacing hx
  have hk : (0 : ℤ) < k := by exact_mod_cast pos_of_mul_pos_left hx₀ F.spacing_pos.le
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk' F.spacing_pos.le

/-- **Gap 1.1.** The smallest positive normal number is a number of the format. -/
theorem minNormal_mem_numbers : F.minNormal ∈ F.numbers := by
  have hp := F.two_le_precision
  have hβ : (F.radix : ℝ) ≠ 0 := (zero_lt_one.trans F.one_lt_radix).ne'
  refine ⟨(F.radix : ℤ) ^ (F.precision - 1), F.emin, ⟨?_, le_rfl, F.emin_le_emax⟩, ?_⟩
  · rw [abs_of_nonneg (by positivity)]
    exact pow_lt_pow_right₀ (by exact_mod_cast Nat.one_lt_two.trans_le F.two_le_radix)
      (by omega)
  · rw [value_def, minNormal_def, Int.cast_pow, Int.cast_natCast, ← zpow_natCast,
      ← zpow_add₀ hβ, Nat.cast_sub (by omega)]
    ring_nf

/-- **Gap 1.1.** The smallest positive normal number is least among numbers above it. -/
theorem isLeast_minNormal : IsLeast {x ∈ F.numbers | F.minNormal ≤ x} F.minNormal :=
  ⟨⟨F.minNormal_mem_numbers, le_rfl⟩, fun _ hx ↦ hx.2⟩

/-- **Gap 1.1.** The largest number is `(β ^ p - 1) β ^ (emax - p + 1)`. -/
theorem isGreatest_maxFinite : IsGreatest F.numbers F.maxFinite := by
  have hβ1 := F.one_lt_radix
  have hr : (0 : ℤ) < (F.radix : ℤ) ^ F.precision :=
    pow_pos (by exact_mod_cast zero_lt_two.trans_le F.two_le_radix) _
  have hr1 : (0 : ℤ) ≤ (F.radix : ℤ) ^ F.precision - 1 := by omega
  refine ⟨⟨_, F.emax, ⟨?_, F.emin_le_emax, le_rfl⟩, rfl⟩, ?_⟩
  · rw [abs_of_nonneg (by omega)]
    omega
  rintro x ⟨m, e, ⟨hm, -, he⟩, rfl⟩
  have hm' : ((|m| : ℤ) : ℝ) ≤ (((F.radix : ℤ) ^ F.precision - 1 : ℤ) : ℝ) := by
    exact_mod_cast Int.le_sub_one_of_lt hm
  have hz : (F.radix : ℝ) ^ (e - (F.precision : ℤ) + 1) ≤
      (F.radix : ℝ) ^ (F.emax - (F.precision : ℤ) + 1) :=
    zpow_le_zpow_right₀ hβ1.le (by omega)
  calc
    F.value m e ≤ |F.value m e| := le_abs_self _
    _ = ((|m| : ℤ) : ℝ) * (F.radix : ℝ) ^ (e - (F.precision : ℤ) + 1) := by
      rw [value_def, abs_mul, abs_of_pos (zpow_pos (zero_lt_one.trans hβ1) _), Int.cast_abs]
    _ ≤ _ := by
      rw [maxFinite_def, value_def]
      exact mul_le_mul hm' hz (zpow_pos (zero_lt_one.trans hβ1) _).le (by exact_mod_cast hr1)

/-- **Gap 1.1.** The least exponent representation has a normalized significand or lies at
the bottom exponent with a subnormal significand. -/
theorem exists_minimal_exponent {x : ℝ} (hx : x ∈ F.numbers) (hx₀ : x ≠ 0) :
    ∃ m e : ℤ, F.Valid m e ∧ F.value m e = x ∧
      (∀ m' e', F.Valid m' e' → F.value m' e' = x → e ≤ e') ∧
      (F.minNormal ≤ |x| → (F.radix : ℤ) ^ (F.precision - 1) ≤ |m|) ∧
      (|x| < F.minNormal → e = F.emin ∧ |m| < (F.radix : ℤ) ^ (F.precision - 1)) := by
  sorry

/-- Representable extended values, including infinities for directed overflow. -/
def extendedNumbers : Set EReal := (fun x : ℝ ↦ (x : EReal)) '' F.numbers ∪ {⊥, ⊤}

/-- An extended number is a coerced number or one of the two infinities. -/
theorem mem_extendedNumbers_iff {y : EReal} :
    y ∈ F.extendedNumbers ↔ (∃ x ∈ F.numbers, (x : EReal) = y) ∨ y = ⊥ ∨ y = ⊤ := Iff.rfl

/-- The four rounding directions. -/
inductive RoundingMode
  /-- Rounding to a nearest number, with an arbitrary choice at ties. -/
  | nearest
  /-- Rounding downward, toward `-∞`. -/
  | down
  /-- Rounding upward, toward `+∞`. -/
  | up
  /-- Rounding toward zero. -/
  | towardZero
  deriving DecidableEq

/-- Correct rounding by the order or nearest-point rule, with an arbitrary choice at ties.
Rounding to nearest never overflows: it saturates at `±maxFinite`. The directed modes return
`⊥` or `⊤` beyond the finite range. -/
def IsRounding (mode : RoundingMode) (rnd : ℝ → EReal) : Prop :=
  match mode with
  | .nearest =>
    ∀ x, ∃ y ∈ F.numbers, rnd x = (y : EReal) ∧ ∀ t ∈ F.numbers, |y - x| ≤ |t - x|
  | .down => ∀ x : ℝ, IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x)
  | .up => ∀ x : ℝ, IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x)
  | .towardZero =>
    (∀ (x : ℝ), 0 ≤ x → IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x)) ∧
      (∀ (x : ℝ), x ≤ 0 → IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x))

/-- Rounding to nearest returns a nearest number. -/
theorem isRounding_nearest_iff {rnd : ℝ → EReal} :
    F.IsRounding .nearest rnd ↔
      ∀ x, ∃ y ∈ F.numbers, rnd x = (y : EReal) ∧ ∀ t ∈ F.numbers, |y - x| ≤ |t - x| :=
  Iff.rfl

/-- Rounding down returns the greatest extended number below the input. -/
theorem isRounding_down_iff {rnd : ℝ → EReal} :
    F.IsRounding .down rnd ↔
      ∀ x : ℝ, IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x) := Iff.rfl

/-- Rounding up returns the least extended number above the input. -/
theorem isRounding_up_iff {rnd : ℝ → EReal} :
    F.IsRounding .up rnd ↔
      ∀ x : ℝ, IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x) := Iff.rfl

/-- Rounding toward zero rounds down on nonnegative inputs and up on nonpositive inputs. -/
theorem isRounding_towardZero_iff {rnd : ℝ → EReal} :
    F.IsRounding .towardZero rnd ↔
      (∀ (x : ℝ), 0 ≤ x → IsGreatest {y ∈ F.extendedNumbers | y ≤ (x : EReal)} (rnd x)) ∧
        (∀ (x : ℝ), x ≤ 0 → IsLeast {y ∈ F.extendedNumbers | (x : EReal) ≤ y} (rnd x)) :=
  Iff.rfl

/-- Two rounded-down values are ordered like their inputs. -/
theorem isGreatest_rounding_mono {rnd : ℝ → EReal} {x y : ℝ} (hxy : x ≤ y)
    (hx : IsGreatest {z ∈ F.extendedNumbers | z ≤ (x : EReal)} (rnd x))
    (hy : IsGreatest {z ∈ F.extendedNumbers | z ≤ (y : EReal)} (rnd y)) : rnd x ≤ rnd y :=
  hy.2 ⟨hx.1.1, hx.1.2.trans (EReal.coe_le_coe_iff.mpr hxy)⟩

/-- Two rounded-up values are ordered like their inputs. -/
theorem isLeast_rounding_mono {rnd : ℝ → EReal} {x y : ℝ} (hxy : x ≤ y)
    (hx : IsLeast {z ∈ F.extendedNumbers | (x : EReal) ≤ z} (rnd x))
    (hy : IsLeast {z ∈ F.extendedNumbers | (y : EReal) ≤ z} (rnd y)) : rnd x ≤ rnd y :=
  hx.2 ⟨hy.1.1, (EReal.coe_le_coe_iff.mpr hxy).trans hy.1.2⟩

variable {F} in
/-- **Gap 1.3.** Rounding to nearest is monotone. -/
theorem IsRounding.monotone_nearest {rnd : ℝ → EReal} (h : F.IsRounding .nearest rnd) :
    Monotone rnd := by
  intro x y hxy
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

variable {F} in
/-- **Gap 1.3.** Correct rounding is monotone in every mode. -/
theorem IsRounding.monotone {mode : RoundingMode} {rnd : ℝ → EReal}
    (h : F.IsRounding mode rnd) : Monotone rnd := by
  cases mode with
  | nearest => exact h.monotone_nearest
  | down => exact fun _ _ hxy ↦ F.isGreatest_rounding_mono hxy (h _) (h _)
  | up => exact fun _ _ hxy ↦ F.isLeast_rounding_mono hxy (h _) (h _)
  | towardZero =>
      intro x y hxy
      rcases le_total 0 x with hx | hx
      · exact F.isGreatest_rounding_mono hxy (h.1 x hx) (h.1 y (hx.trans hxy))
      rcases le_total y 0 with hy | hy
      · exact F.isLeast_rounding_mono hxy (h.2 x hx) (h.2 y hy)
      exact (F.isLeast_rounding_mono hx (h.2 x hx) (h.2 0 le_rfl)).trans
        (F.isGreatest_rounding_mono hy (h.1 0 le_rfl) (h.1 y hy))

variable {F} in
/-- **Gap 1.3.** Correct rounding fixes every number of the format. -/
theorem IsRounding.apply_coe_of_mem {mode : RoundingMode} {rnd : ℝ → EReal}
    (h : F.IsRounding mode rnd) {x : ℝ} (hx : x ∈ F.numbers) : rnd x = (x : EReal) := by
  have hex : (x : EReal) ∈ F.extendedNumbers := Or.inl ⟨x, hx, rfl⟩
  cases mode with
  | nearest =>
      obtain ⟨a, _, hra, hxa⟩ := h x
      have hzero : |a - x| ≤ 0 := by simpa only [sub_self, abs_zero] using hxa x hx
      rw [hra, sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))]
  | down => exact le_antisymm (h x).1.2 ((h x).2 ⟨hex, le_rfl⟩)
  | up => exact le_antisymm ((h x).2 ⟨hex, le_rfl⟩) (h x).1.2
  | towardZero =>
      rcases le_total 0 x with h₀ | h₀
      · exact le_antisymm (h.1 x h₀).1.2 ((h.1 x h₀).2 ⟨hex, le_rfl⟩)
      · exact le_antisymm ((h.2 x h₀).2 ⟨hex, le_rfl⟩) (h.2 x h₀).1.2

/-- The unit roundoff for a rounding mode. -/
def unitRoundoff (mode : RoundingMode) : ℝ :=
  (F.radix : ℝ) ^ (1 - (F.precision : ℤ)) / (if mode = .nearest then 2 else 1)

/-- The unit roundoff is `β ^ (1 - p) / 2` for rounding to nearest and `β ^ (1 - p)`
otherwise. -/
theorem unitRoundoff_def (mode : RoundingMode) :
    F.unitRoundoff mode =
      (F.radix : ℝ) ^ (1 - (F.precision : ℤ)) / (if mode = .nearest then 2 else 1) := (rfl)

/-- **Gaps 1.4 and 1.5.** Both relative-error representations on the normal range, including
the sharper nearest-rounding bound. -/
theorem IsRounding.exists_eq_mul_one_add {mode : RoundingMode} {rnd : ℝ → EReal} {x : ℝ}
    (h : F.IsRounding mode rnd) (hx : x ∈ F.normalRange) :
    ∃ y δ ε : ℝ, rnd x = (y : EReal) ∧ y = x * (1 + δ) ∧ y = x / (1 + ε) ∧
      |δ| < F.unitRoundoff mode ∧ |ε| ≤ F.unitRoundoff mode ∧
      (mode = .nearest → |δ| ≤ F.unitRoundoff mode / (1 + F.unitRoundoff mode)) := by
  sorry

/-- **Gap 1.5.** Addition below the normal range is exact with gradual underflow. -/
theorem add_mem_numbers_of_abs_lt {a b : ℝ} (ha : a ∈ F.numbers) (hb : b ∈ F.numbers)
    (h : |a + b| < F.minNormal) : a + b ∈ F.numbers := by
  obtain ⟨k₁, rfl⟩ := F.numbers_subset_range_mul_spacing ha
  obtain ⟨k₂, rfl⟩ := F.numbers_subset_range_mul_spacing hb
  have hβ : (F.radix : ℝ) ≠ 0 := (zero_lt_one.trans F.one_lt_radix).ne'
  have hsum : (k₁ : ℝ) * F.spacing + k₂ * F.spacing = ((k₁ + k₂ : ℤ) : ℝ) * F.spacing := by
    push_cast
    ring
  rw [hsum] at h ⊢
  have hmin : F.minNormal = (F.radix : ℝ) ^ ((F.precision : ℤ) - 1) * F.spacing := by
    rw [minNormal_def, spacing_def, ← zpow_add₀ hβ]
    ring_nf
  rw [abs_mul, abs_of_pos F.spacing_pos, hmin] at h
  have hk : ((|k₁ + k₂| : ℤ) : ℝ) < ((F.radix : ℤ) ^ F.precision : ℤ) := by
    have h₁ := lt_of_mul_lt_mul_right h F.spacing_pos.le
    have h₂ : (F.radix : ℝ) ^ ((F.precision : ℤ) - 1) ≤ (F.radix : ℝ) ^ (F.precision : ℤ) :=
      zpow_le_zpow_right₀ F.one_lt_radix.le (by omega)
    rw [zpow_natCast] at h₂
    rw [Int.cast_abs, Int.cast_pow, Int.cast_natCast]
    exact h₁.trans_le h₂
  refine ⟨k₁ + k₂, F.emin, ⟨by exact_mod_cast hk, le_rfl, F.emin_le_emax⟩, ?_⟩
  rw [value_def, spacing_def]

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

variable {F}

/-- A nearest rounding returns a number of the format. -/
theorem Nearest.round_mem (rnd : F.Nearest) (x : ℝ) : rnd.round x ∈ F.numbers := by
  obtain ⟨y, hy, hr, -⟩ := rnd.isRounding x
  rwa [EReal.coe_eq_coe_iff.mp hr]

/-- A nearest rounding is at least as close to the input as every number of the format. -/
theorem Nearest.abs_round_sub_le (rnd : F.Nearest) (x : ℝ) {t : ℝ} (ht : t ∈ F.numbers) :
    |rnd.round x - x| ≤ |t - x| := by
  obtain ⟨y, -, hr, hmin⟩ := rnd.isRounding x
  rw [EReal.coe_eq_coe_iff.mp hr]
  exact hmin t ht

variable (F)

/-- The Fast2Sum addition algorithm. -/
def fastTwoSum (rnd : ℝ → ℝ) (a b : ℝ) : ℝ × ℝ :=
  let s := rnd (a + b)
  (s, rnd (b - rnd (s - a)))

/-- Fast2Sum returns `s = ∘(a + b)` and `∘(b - ∘(s - a))`. -/
theorem fastTwoSum_def (rnd : ℝ → ℝ) (a b : ℝ) :
    fastTwoSum rnd a b = (rnd (a + b), rnd (b - rnd (rnd (a + b) - a))) := (rfl)

/-- The 2Sum addition algorithm. -/
def twoSum (rnd : ℝ → ℝ) (a b : ℝ) : ℝ × ℝ :=
  let s := rnd (a + b)
  let a' := rnd (s - b)
  let b' := rnd (s - a')
  (s, rnd (rnd (a - a') + rnd (b - b')))

/-- 2Sum returns `s = ∘(a + b)` and `∘(∘(a - a') + ∘(b - b'))`, where `a' = ∘(s - b)` and
`b' = ∘(s - a')`. -/
theorem twoSum_def (rnd : ℝ → ℝ) (a b : ℝ) :
    twoSum rnd a b =
      (rnd (a + b), rnd (rnd (a - rnd (rnd (a + b) - b)) +
        rnd (b - rnd (rnd (a + b) - rnd (rnd (a + b) - b))))) := (rfl)

/-- The product and its fused multiply-add residual: `p = ∘(x₁ x₂)` and `∘(x₁ x₂ - p)`. -/
def twoMultFMA (rnd : ℝ → ℝ) (x₁ x₂ : ℝ) : ℝ × ℝ :=
  (rnd (x₁ * x₂), rnd (x₁ * x₂ - rnd (x₁ * x₂)))

/-- TwoMultFMA returns `∘(x₁ x₂)` and `∘(x₁ x₂ - ∘(x₁ x₂))`. -/
theorem twoMultFMA_def (rnd : ℝ → ℝ) (x₁ x₂ : ℝ) :
    twoMultFMA rnd x₁ x₂ = (rnd (x₁ * x₂), rnd (x₁ * x₂ - rnd (x₁ * x₂))) := (rfl)

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
    (twoMultFMA rnd.round (F.value m₁ e₁) (F.value m₂ e₂)).1 +
      (twoMultFMA rnd.round (F.value m₁ e₁) (F.value m₂ e₂)).2 =
        F.value m₁ e₁ * F.value m₂ e₂ := by
  sorry

end FloatingPointFormat

end NASC
