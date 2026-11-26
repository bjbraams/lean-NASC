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
  sorry

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

/-- **Gap 1.8.** A signed product of rounding factors satisfies the accumulated bound. -/
theorem hasRelativeError_prod_zpow {u : ℝ} {n : ℕ} (hn : (n : ℝ) * u < 1)
    {δ : Fin n → ℝ} (hδ : ∀ j, |δ j| ≤ u) {s : Fin n → ℤ}
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    HasRelativeError (roundingGamma u n) 1 (∏ j, (1 + δ j) ^ s j) := by
  sorry

/-- **Gap 1.8.** Two error factors compose with the sum of their budgets. -/
theorem roundingGamma_add_bound {u : ℝ} {j k : ℕ} (hu : 0 ≤ u)
    (h : ((j + k : ℕ) : ℝ) * u < 1) :
    roundingGamma u j + roundingGamma u k + roundingGamma u j * roundingGamma u k ≤
      roundingGamma u (j + k) := by
  sorry

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

/-- **Gap 1.9.** Summation on a tree of depth $d$ has budget $\gamma_d$. -/
theorem abs_eval_sub_sum_le (t : SumTree ι) {rnd : ℝ → ℝ} {x : ι → ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hd : (t.depth : ℝ) * u < 1) (ht : t.HasStableEvaluation rnd x u) :
    |t.eval rnd x - (t.leaves.map x).sum| ≤
      roundingGamma u t.depth * (t.leaves.map fun i ↦ |x i|).sum := by
  sorry

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
  sorry

/-- **Gap 1.10.** A dot product computed with one multiplication per entry admits a
componentwise backward error under the standard arithmetic model. -/
theorem exists_dotProduct_eq_sum_mul_perturbed {n : ℕ} {t : SumTree (Fin n)}
    {x y : Fin n → ℝ} {u : ℝ} {rnd : ℝ → ℝ} (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (hperm : t.leaves.Perm (List.finRange n))
    (hmul : ∀ i, HasRelativeError u (x i * y i) (rnd (x i * y i)))
    (ht : t.HasStableEvaluation rnd (fun i ↦ rnd (x i * y i)) u) :
    ∃ dx : Fin n → ℝ, (∀ i, |dx i| ≤ roundingGamma u n * |x i|) ∧
      t.eval rnd (fun i ↦ rnd (x i * y i)) = ∑ i, (x i + dx i) * y i := by
  sorry

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
  sorry

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
orders within rows. -/
def IsRoundedForwardSubstitution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (rnd : ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ i, ∃ s : ℝ,
    (if i.val = 0 then s = 0 else
      ∃ t : SumTree {j : Fin n // j < i},
        t.leaves.Perm (Finset.univ.toList : List {j : Fin n // j < i}) ∧
        t.HasStableEvaluation rnd (fun j ↦ rnd (T i j.val * x j.val)) u ∧
        s = t.eval rnd (fun j ↦ rnd (T i j.val * x j.val))) ∧
    (∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) ∧
    HasRelativeError u (b i - s) (rnd (b i - s)) ∧
    HasRelativeError u (rnd (b i - s) / T i i) (x i)

/-- **Gap 1.13.** Forward substitution has a componentwise backward-error certificate. -/
theorem IsRoundedForwardSubstitution.exists_backwardError {n : ℕ}
    {T : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ} {rnd : ℝ → ℝ} {u : ℝ}
    (h : IsRoundedForwardSubstitution T b x rnd u) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (htri : ∀ i j, i < j → T i j = 0)
    (hdiag : ∀ i, T i i ≠ 0) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, (T + E) *ᵥ x = b ∧
      ∀ i j, |E i j| ≤ roundingGamma u n * |T i j| := by
  sorry

end NASC
