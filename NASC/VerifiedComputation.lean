module

public import NASC.FloatingPoint
public import NASC.IterativeMethods
public import Mathlib.Order.Interval.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Interval arithmetic and verified computation

Endpoint arithmetic, inclusion over expression trees, interval Newton and Krawczyk
certificates, and a Banach-space existence certificate. See section 7 of the gap catalogue.
The interval Newton proof uses Mathlib's real mean value and intermediate value theorems.
-/

public section

noncomputable section

namespace NASC

open Set Filter
open scoped Matrix Matrix.Norms.L2Operator BigOperators Interval

/-- The four possible evaluations of a binary operation on endpoint pairs. -/
def intervalCorners (op : ℝ → ℝ → ℝ) (X Y : NonemptyInterval ℝ) : Finset ℝ :=
  {op X.fst Y.fst, op X.fst Y.snd, op X.snd Y.fst, op X.snd Y.snd}

/-- **Gap 7.1.** Addition, subtraction, multiplication and admissible division have
exact ranges given by the smallest and largest corner values. -/
theorem image2_eq_Icc_intervalCorners (op : ℝ → ℝ → ℝ) (X Y : NonemptyInterval ℝ)
    (hop : op = (· + ·) ∨ op = (· - ·) ∨ op = (· * ·) ∨ op = (· / ·) ∧ 0 ∉ Y) :
    Set.image2 op (X : Set ℝ) (Y : Set ℝ) =
      Icc (sInf (↑(intervalCorners op X Y) : Set ℝ))
        (sSup (↑(intervalCorners op X Y) : Set ℝ)) := by
  sorry

/-- An interval expression records the operation graph and the domain of each division
and unary primitive. -/
inductive IntervalExpr (ι : Type*)
  | var (i : ι)
  | const (x : ℝ)
  | add (a b : IntervalExpr ι)
  | sub (a b : IntervalExpr ι)
  | mul (a b : IntervalExpr ι)
  | div (a b : IntervalExpr ι)
  | unary (f : ℝ → ℝ) (domain : Set ℝ) (a : IntervalExpr ι)

namespace IntervalExpr

variable {ι : Type*}

/-- Scalar evaluation. The admissibility predicate supplies the required domain
checks when this total Lean function is used. -/
def eval (x : ι → ℝ) : IntervalExpr ι → ℝ
  | .var i => x i
  | .const z => z
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .mul a b => a.eval x * b.eval x
  | .div a b => a.eval x / b.eval x
  | .unary f _ a => f (a.eval x)

/-- Natural range extension. Each occurrence of a variable ranges independently.
Admissibility ensures the exact intermediate sets are compact intervals. -/
def enclosure (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Set ℝ
  | .var i => X i
  | .const z => {z}
  | .add a b => image2 (· + ·) (a.enclosure X) (b.enclosure X)
  | .sub a b => image2 (· - ·) (a.enclosure X) (b.enclosure X)
  | .mul a b => image2 (· * ·) (a.enclosure X) (b.enclosure X)
  | .div a b => image2 (· / ·) (a.enclosure X) (b.enclosure X)
  | .unary f _ a => f '' a.enclosure X

/-- Every division avoids zero and unary primitives are continuous on the enclosing domain. -/
def Admissible (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Prop
  | .var _ | .const _ => True
  | .add a b | .sub a b | .mul a b => a.Admissible X ∧ b.Admissible X
  | .div a b => a.Admissible X ∧ b.Admissible X ∧ 0 ∉ b.enclosure X
  | .unary f domain a =>
    a.Admissible X ∧ a.enclosure X ⊆ domain ∧ ContinuousOn f domain

/-- Occurrences of variables, with multiplicity. -/
def variableOccurrences : IntervalExpr ι → List ι
  | .var i => [i]
  | .const _ => []
  | .add a b | .sub a b | .mul a b | .div a b => a.variableOccurrences ++ b.variableOccurrences
  | .unary _ _ a => a.variableOccurrences

/-- Evaluation of a point in the box belongs to the natural enclosure. -/
theorem eval_mem_enclosure (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ X i) : e.eval x ∈ e.enclosure X := by
  induction e with
  | var i => exact hx i
  | const t => exact Set.mem_singleton t
  | unary f domain a ha => exact ⟨a.eval x, ha, rfl⟩
  | add a b ha hb => exact ⟨a.eval x, ha, b.eval x, hb, rfl⟩
  | sub a b ha hb => exact ⟨a.eval x, ha, b.eval x, hb, rfl⟩
  | mul a b ha hb => exact ⟨a.eval x, ha, b.eval x, hb, rfl⟩
  | div a b ha hb => exact ⟨a.eval x, ha, b.eval x, hb, rfl⟩

/-- A smaller box preserves admissibility and shrinks the associated enclosure. -/
theorem admissible_enclosure_mono (e : IntervalExpr ι) {X Y : ι → NonemptyInterval ℝ}
    (h : e.Admissible X) (hYX : ∀ i, Y i ≤ X i) :
    e.Admissible Y ∧ e.enclosure Y ⊆ e.enclosure X := by
  induction e with
  | var i => exact ⟨trivial, NonemptyInterval.coe_subset_coe.mpr (hYX i)⟩
  | const t => exact ⟨trivial, Subset.rfl⟩
  | unary f domain a ha =>
    have ha' := ha h.1
    exact ⟨⟨ha'.1, ha'.2.trans h.2.1, h.2.2⟩, image_mono ha'.2⟩
  | add a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2
    exact ⟨⟨ha'.1, hb'.1⟩, image2_subset ha'.2 hb'.2⟩
  | sub a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2
    exact ⟨⟨ha'.1, hb'.1⟩, image2_subset ha'.2 hb'.2⟩
  | mul a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2
    exact ⟨⟨ha'.1, hb'.1⟩, image2_subset ha'.2 hb'.2⟩
  | div a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2.1
    exact ⟨⟨ha'.1, hb'.1, fun hy ↦ h.2.2 (hb'.2 hy)⟩, image2_subset ha'.2 hb'.2⟩

/-- Evaluation depends only on the entries of the variables occurring in the expression. -/
theorem eval_eq_of_eqOn_occurrences (e : IntervalExpr ι) {x y : ι → ℝ}
    (h : ∀ i ∈ e.variableOccurrences, x i = y i) : e.eval x = e.eval y := by
  induction e with
  | var i => exact h i List.mem_cons_self
  | const t => rfl
  | unary f domain a ha => exact congrArg f (ha h)
  | add a b ha hb =>
    exact congrArg₂ (· + ·)
      (ha fun i hi ↦ h i (List.mem_append_left _ hi))
      (hb fun i hi ↦ h i (List.mem_append_right _ hi))
  | sub a b ha hb =>
    exact congrArg₂ (· - ·)
      (ha fun i hi ↦ h i (List.mem_append_left _ hi))
      (hb fun i hi ↦ h i (List.mem_append_right _ hi))
  | mul a b ha hb =>
    exact congrArg₂ (· * ·)
      (ha fun i hi ↦ h i (List.mem_append_left _ hi))
      (hb fun i hi ↦ h i (List.mem_append_right _ hi))
  | div a b ha hb =>
    exact congrArg₂ (· / ·)
      (ha fun i hi ↦ h i (List.mem_append_left _ hi))
      (hb fun i hi ↦ h i (List.mem_append_right _ hi))

/-- Independent subexpressions can realize any pair from their respective enclosures together. -/
theorem image2_enclosure_subset_range {a b : IntervalExpr ι} {X : ι → NonemptyInterval ℝ}
    (op : ℝ → ℝ → ℝ) (hd : a.variableOccurrences.Disjoint b.variableOccurrences)
    (ha : a.enclosure X ⊆ a.eval '' {x | ∀ i, x i ∈ X i})
    (hb : b.enclosure X ⊆ b.eval '' {x | ∀ i, x i ∈ X i}) :
    image2 op (a.enclosure X) (b.enclosure X) ⊆
      (fun x ↦ op (a.eval x) (b.eval x)) '' {x | ∀ i, x i ∈ X i} := by
  classical
  rintro t ⟨r, hr, s, hs, rfl⟩
  obtain ⟨x, hx, rfl⟩ := ha hr
  obtain ⟨y, hy, rfl⟩ := hb hs
  let z := fun i ↦ if i ∈ a.variableOccurrences then x i else y i
  have hz : ∀ i, z i ∈ X i := by
    intro i
    by_cases hi : i ∈ a.variableOccurrences
    · simpa only [z, ite_eq_left hi] using hx i
    · simpa only [z, ite_eq_right hi] using hy i
  have haz : a.eval z = a.eval x :=
    a.eval_eq_of_eqOn_occurrences fun i hi ↦ ite_eq_left hi
  have hbz : b.eval z = b.eval y :=
    b.eval_eq_of_eqOn_occurrences fun i hi ↦ ite_eq_right fun ha' ↦ List.disjoint_left.mp hd ha' hi
  exact ⟨z, hz, congrArg₂ op haz hbz⟩

/-- An enclosure of an expression is attained on the box when each variable occurs at most once. -/
theorem enclosure_subset_range_of_nodup (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ}
    (h : e.variableOccurrences.Nodup) :
    e.enclosure X ⊆ e.eval '' {x | ∀ i, x i ∈ X i} := by
  classical
  induction e with
  | var i =>
    intro t ht
    refine ⟨Function.update (fun j ↦ (X j).fst) i t, ?_, Function.update_self ..⟩
    intro j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self, ← SetLike.mem_coe]
      simpa only [enclosure] using ht
    · rw [Function.update_of_ne hj]
      exact ⟨le_rfl, (X j).fst_le_snd⟩
  | const t =>
    rintro s (rfl : s = t)
    exact ⟨fun i ↦ (X i).fst, fun i ↦ ⟨le_rfl, (X i).fst_le_snd⟩, rfl⟩
  | unary f domain a ha =>
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨x, hx, rfl⟩ := ha h ht
    exact ⟨x, hx, rfl⟩
  | add a b ha hb =>
    have hs := List.nodup_append'.mp h
    exact image2_enclosure_subset_range (· + ·) hs.2.2 (ha hs.1) (hb hs.2.1)
  | sub a b ha hb =>
    have hs := List.nodup_append'.mp h
    exact image2_enclosure_subset_range (· - ·) hs.2.2 (ha hs.1) (hb hs.2.1)
  | mul a b ha hb =>
    have hs := List.nodup_append'.mp h
    exact image2_enclosure_subset_range (· * ·) hs.2.2 (ha hs.1) (hb hs.2.1)
  | div a b ha hb =>
    have hs := List.nodup_append'.mp h
    exact image2_enclosure_subset_range (· / ·) hs.2.2 (ha hs.1) (hb hs.2.1)

/-- **Gap 7.3.** The natural interval extension encloses the range, is inclusion isotone,
and is exact for expressions with no repeated variable. -/
theorem range_subset_enclosure (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ}
    (h : e.Admissible X) :
    let box := {x : ι → ℝ | ∀ i, x i ∈ X i}
    (fun x ↦ e.eval x) '' box ⊆ e.enclosure X ∧
      (∀ Y : ι → NonemptyInterval ℝ, (∀ i, Y i ≤ X i) →
        e.Admissible Y ∧ e.enclosure Y ⊆ e.enclosure X) ∧
      (e.variableOccurrences.Nodup → e.enclosure X = (fun x ↦ e.eval x) '' box) := by
  have hr : e.eval '' {x | ∀ i, x i ∈ X i} ⊆ e.enclosure X :=
    by rintro y ⟨x, hx, rfl⟩; exact e.eval_mem_enclosure hx
  exact ⟨hr, fun Y hYX ↦ e.admissible_enclosure_mono h hYX,
    fun hn ↦ (e.enclosure_subset_range_of_nodup hn).antisymm hr⟩

/-- The same domain tests as admissibility, with a Lipschitz bound for each primitive
on its argument enclosure. -/
def LipschitzOnEnclosures (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Prop
  | .var _ | .const _ => True
  | .add a b | .sub a b | .mul a b | .div a b =>
    a.LipschitzOnEnclosures X ∧ b.LipschitzOnEnclosures X
  | .unary f _ a =>
    a.LipschitzOnEnclosures X ∧ ∃ L, LipschitzOnWith L f (a.enclosure X)

/-- **Gap 7.7.** The enclosure width is at most linear in the largest input width
inside an admissible reference box. -/
theorem exists_enclosure_width_le {ι : Type*} [Fintype ι]
    (e : IntervalExpr ι) (X : ι → NonemptyInterval ℝ)
    (h : e.Admissible X) (hLip : e.LipschitzOnEnclosures X) :
    ∃ C ≥ (0 : ℝ), ∀ (Y : ι → NonemptyInterval ℝ), (∀ i, Y i ≤ X i) →
      sSup (e.enclosure Y) - sInf (e.enclosure Y) ≤ C * ‖fun i ↦ (Y i).snd - (Y i).fst‖ := by
  sorry

end IntervalExpr

/-- **Gap 7.5.** Rounding the endpoints outwards gives the least containing interval
with representable endpoints. The input is within the finite representable range. -/
theorem FloatingPointFormat.exists_least_outwardInterval (F : FloatingPointFormat)
    (X : NonemptyInterval ℝ) (down up : ℝ → EReal)
    (hd : F.IsRounding .down down) (hu : F.IsRounding .up up)
    (hX : -F.maxFinite ≤ X.fst ∧ X.snd ≤ F.maxFinite) :
    ∃ Y : NonemptyInterval ℝ, (Y.fst : EReal) = down X.fst ∧ (Y.snd : EReal) = up X.snd ∧
      IsLeast {Z : NonemptyInterval ℝ | X ≤ Z ∧ Z.fst ∈ F.numbers ∧ Z.snd ∈ F.numbers} Y := by
  sorry

/-- **Gap 7.7.** The excess width of the mean-value enclosure is quadratic
when each derivative interval has width linear in the box diameter. -/
theorem meanValueEnclosure_excessWidth_le {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (X D : Fin n → NonemptyInterval ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x : Fin n → ℝ, (∀ i, x i ∈ X i) → ∀ i,
      fderiv ℝ f x (Pi.single i 1) ∈ D i)
    (hwidth : ∀ i, (D i).snd - (D i).fst ≤ L * ‖fun j ↦ (X j).snd - (X j).fst‖) :
    let box := {x : Fin n → ℝ | ∀ i, x i ∈ X i}
    let m := fun i ↦ ((X i).fst + (X i).snd) / 2
    let F := {y : ℝ | ∃ (a x : Fin n → ℝ), (∀ i, a i ∈ D i) ∧ x ∈ box ∧
      y = f m + ∑ i, a i * (x i - m i)}
    let R := f '' box
    R ⊆ F ∧
      (sSup F - sInf F) - (sSup R - sInf R) ≤
        2 * n * L * ‖fun i ↦ (X i).snd - (X i).fst‖ ^ 2 := by
  sorry

/-- A secant slope between two points in an interval belongs to any interval enclosing
all derivatives. For a repeated point one may take any member of the derivative interval. -/
theorem exists_intervalSlope {f : ℝ → ℝ} (X D : NonemptyInterval ℝ)
    (hf : ContinuousOn f (X : Set ℝ))
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d (X : Set ℝ) x)
    {a b : ℝ} (ha : a ∈ X) (hb : b ∈ X) :
    ∃ d ∈ D, f b - f a = d * (b - a) := by
  have ho {u v : ℝ} (hu : u ∈ X) (hv : v ∈ X) (huv : u < v) :
      ∃ d ∈ D, f v - f u = d * (v - u) := by
    have hs : Icc u v ⊆ (X : Set ℝ) := Icc_subset_Icc hu.1 hv.2
    have hd {x : ℝ} (hx : x ∈ Ioo u v) :
        ∃ d ∈ D, HasDerivAt f d x := by
      obtain ⟨d, hdD, hd⟩ := hderiv x (hs (Ioo_subset_Icc_self hx))
      exact ⟨d, hdD, hd.hasDerivAt <|
        Filter.mem_of_superset (Icc_mem_nhds hx.1 hx.2) hs⟩
    obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope f huv (hf.mono hs)
      (fun x hx ↦ (hd hx).choose_spec.2.differentiableAt.differentiableWithinAt)
    obtain ⟨d, hdD, hd⟩ := hd hx
    rw [hd.deriv] at he
    exact ⟨d, hdD, ((eq_div_iff (sub_ne_zero.mpr huv.ne')).mp he).symm⟩
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact ho ha hb hlt
  · exact ⟨D.fst, ⟨le_rfl, D.fst_le_snd⟩, by simp⟩
  · obtain ⟨d, hd, he⟩ := ho hb ha hgt
    exact ⟨d, hd, by linarith only [he]⟩

/-- **Gap 7.8.** The interval Newton image encloses all zeros, and inclusion of that
image in the input interval certifies a unique zero. -/
theorem intervalNewton_univariate {f : ℝ → ℝ} (X D : NonemptyInterval ℝ) {x₀ : ℝ}
    (hx : x₀ ∈ X) (hD : 0 ∉ D)
    (hf : ContDiffOn ℝ 1 f (X : Set ℝ))
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d (X : Set ℝ) x) :
    let N := (fun d ↦ x₀ - f x₀ / d) '' (D : Set ℝ)
    {x ∈ (X : Set ℝ) | f x = 0} ⊆ N ∧
      (N ⊆ (X : Set ℝ) → ∃! x, x ∈ X ∧ f x = 0) := by
  have hd0 {d : ℝ} (hd : d ∈ D) : d ≠ 0 := fun he ↦ hD (he ▸ hd)
  have hsign : (∀ d ∈ D, 0 < d) ∨ (∀ d ∈ D, d < 0) := by
    by_cases h : D.snd < 0
    · exact Or.inr fun d hd ↦ hd.2.trans_lt h
    · have hp : 0 < D.fst := lt_of_not_ge fun he ↦ hD ⟨he, le_of_not_gt h⟩
      exact Or.inl fun d hd ↦ hp.trans_le hd.1
  have hsl {a b : ℝ} (ha : a ∈ X) (hb : b ∈ X) :=
    exists_intervalSlope X D hf.continuousOn hderiv ha hb
  refine ⟨?_, ?_⟩
  · rintro y ⟨hy, hry⟩
    obtain ⟨d, hd, hs⟩ := hsl hx hy
    refine ⟨d, hd, ?_⟩
    have he : f x₀ / d * d = f x₀ := div_mul_cancel₀ _ (hd0 hd)
    have hmul : d * (x₀ - f x₀ / d - y) = 0 := by linarith only [hs, hry, he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (hd0 hd))
  · intro hN
    have hsignAt {y : ℝ} (hy : y ∈ X) :
        ∃ d ∈ D, x₀ - f x₀ / d ∈ X ∧ f y = d * (y - (x₀ - f x₀ / d)) := by
      obtain ⟨d, hd, hs⟩ := hsl hx hy
      refine ⟨d, hd, hN ⟨d, hd, rfl⟩, ?_⟩
      linarith only [hs, div_mul_cancel₀ (f x₀) (hd0 hd)]
    obtain ⟨dl, hdl, hl, hl'⟩ := hsignAt ⟨le_rfl, X.fst_le_snd⟩
    obtain ⟨dr, hdr, hr, hr'⟩ := hsignAt ⟨X.fst_le_snd, le_rfl⟩
    have hz : (0 : ℝ) ∈ f '' (X : Set ℝ) := by
      rcases hsign with hpos | hneg
      · apply intermediate_value_Icc X.fst_le_snd hf.continuousOn
        exact ⟨by rw [hl']; exact mul_nonpos_of_nonneg_of_nonpos (hpos _ hdl).le
                   (sub_nonpos.mpr hl.1),
          by rw [hr']; exact mul_nonneg (hpos _ hdr).le (sub_nonneg.mpr hr.2)⟩
      · apply intermediate_value_Icc' X.fst_le_snd hf.continuousOn
        exact ⟨by rw [hr']; exact mul_nonpos_of_nonpos_of_nonneg (hneg _ hdr).le
                   (sub_nonneg.mpr hr.2),
          by rw [hl']; exact mul_nonneg_of_nonpos_of_nonpos (hneg _ hdl).le
                   (sub_nonpos.mpr hl.1)⟩
    obtain ⟨z, hzX, hzf⟩ := hz
    refine ⟨z, ⟨hzX, hzf⟩, fun y hy ↦ ?_⟩
    obtain ⟨d, hd, hs⟩ := hsl hzX hy.1
    have he : d * (y - z) = 0 := by rw [← hs, hy.2, hzf, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hd0 hd))

/-- The product box of a family of real intervals. -/
def intervalBox {n : ℕ} (X : Fin n → NonemptyInterval ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ X i}

/-- A matrix box, expressing independent entrywise interval bounds. -/
def intervalMatrix {n : ℕ} (J : Fin n → Fin n → NonemptyInterval ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) := {A | ∀ i j, A i j ∈ J i j}

/-- **Gap 7.9.** The interval Newton operator in finite dimensions gives a unique
root when the image is contained in the initial box. -/
theorem intervalNewton_unique {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (X : Fin n → NonemptyInterval ℝ) (J : Fin n → Fin n → NonemptyInterval ℝ)
    {x₀ : Fin n → ℝ} (hx : x₀ ∈ intervalBox X) (hf : ContDiff ℝ 1 f)
    (hJ : ∀ x ∈ intervalBox X, ∃ A ∈ intervalMatrix J,
      ∀ v, fderiv ℝ f x v = A *ᵥ v)
    (hnon : ∀ A ∈ intervalMatrix J, A.det ≠ 0) :
    let N := (fun A : Matrix (Fin n) (Fin n) ℝ ↦ x₀ - A⁻¹ *ᵥ f x₀) '' intervalMatrix J
    {x ∈ intervalBox X | f x = 0} ⊆ N ∧
      (N ⊆ intervalBox X → ∃! x, x ∈ intervalBox X ∧ f x = 0) := by
  sorry

/-- **Gap 7.10.** Strict inclusion of the Krawczyk image certifies nonsingularity,
uniqueness and a root enclosure. -/
theorem krawczyk_unique {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (X : Fin n → NonemptyInterval ℝ) (J : Fin n → Fin n → NonemptyInterval ℝ)
    (x₀ : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hx : 0 ∈ intervalBox X) (hf : ContDiff ℝ 1 f)
    (hJ : ∀ y ∈ intervalBox X, ∃ A ∈ intervalMatrix J,
      ∀ v, fderiv ℝ f (x₀ + y) v = A *ᵥ v) :
    let K := {z | ∃ A ∈ intervalMatrix J, ∃ y ∈ intervalBox X,
      z = -(R *ᵥ f x₀) + (1 - R * A) *ᵥ y}
    K ⊆ interior (intervalBox X) →
      R.det ≠ 0 ∧ (∀ A ∈ intervalMatrix J, A.det ≠ 0) ∧
      (∃! y, y ∈ intervalBox X ∧ f (x₀ + y) = 0) ∧
      ∀ y ∈ intervalBox X, f (x₀ + y) = 0 → y ∈ K := by
  sorry

/-- **Gap 7.11.** A preconditioned residual yields a rigorous normwise error bound
when the approximate inverse has defect of norm less than one. -/
theorem norm_error_le_of_approximateInverse {n : ℕ}
    (A R : Matrix (Fin n) (Fin n) ℝ) (b x : EuclideanSpace ℝ (Fin n))
    (h : ‖1 - R * A‖ < 1) :
    A.det ≠ 0 ∧ R.det ≠ 0 ∧
      ‖(A⁻¹).toEuclideanLin b - x‖ ≤
        ‖R.toEuclideanLin (b - A.toEuclideanLin x)‖ / (1 - ‖1 - R * A‖) := by
  have hRA : IsUnit (R * A) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h
  have hdet : R.det * A.det ≠ 0 := by
    simpa only [Matrix.det_mul, isUnit_iff_ne_zero] using
      (Matrix.isUnit_iff_isUnit_det _).mp hRA
  have hA := right_ne_zero_of_mul hdet
  have hR := left_ne_zero_of_mul hdet
  refine ⟨hA, hR, ?_⟩
  let e := (A⁻¹).toEuclideanLin b - x
  have hAx : A.toEuclideanLin ((A⁻¹).toEuclideanLin b) = b := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.toLpLin_one,
      LinearMap.id_apply]
  have hsplit : e = R.toEuclideanLin (b - A.toEuclideanLin x) +
      (1 - R * A).toEuclideanLin e := by
    simp only [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply,
      Matrix.toLpLin_mul_same, LinearMap.comp_apply, e, hAx]
    abel
  have hbound := (Matrix.l2_opNorm_mulVec (1 - R * A) e :
    ‖(1 - R * A).toEuclideanLin e‖ ≤ ‖1 - R * A‖ * ‖e‖)
  exact (le_div_iff₀ (sub_pos.mpr h)).mpr <| calc
    ‖e‖ * (1 - ‖1 - R * A‖) =
        ‖e‖ - ‖1 - R * A‖ * ‖e‖ := by ring
    _ ≤ ‖e‖ - ‖(1 - R * A).toEuclideanLin e‖ := sub_le_sub_left hbound _
    _ ≤ ‖R.toEuclideanLin (b - A.toEuclideanLin x)‖ := by
      have htri := norm_add_le (R.toEuclideanLin (b - A.toEuclideanLin x))
        ((1 - R * A).toEuclideanLin e)
      rw [← hsplit] at htri
      exact sub_le_iff_le_add.mpr htri

/-- **Gap 7.12.** A strict interior affine enclosure forces the linear part to
have spectral radius less than one. -/
theorem realMatrixSpectralRadius_lt_one_of_image_subset_interior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → NonemptyInterval ℝ) (b : Fin n → ℝ)
    (h : (fun x ↦ b + A *ᵥ x) '' intervalBox X ⊆ interior (intervalBox X)) :
    realMatrixSpectralRadius A < 1 := by
  sorry

/-- **Gap 7.13.** Plum's quantitative enclosure in the dense-range case. The
derivative lower bound and density ensure invertibility at the center. -/
theorem exists_zero_mem_closedBall_of_plum_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (ω : E) (g : ℝ → ℝ) {K δ α : ℝ}
    (hK : 0 < K) (hα : 0 < α) (hg : Monotone g) (hg₀ : g 0 = 0)
    (hf : Differentiable ℝ f) (hω : ‖f ω‖ ≤ δ)
    (hinv : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ f ω v‖) (hdense : DenseRange (fderiv ℝ f ω))
    (hvar : ∀ v, ‖fderiv ℝ f (ω + v) - fderiv ℝ f ω‖ ≤ g ‖v‖)
    (hδ : δ ≤ α / K - ∫ t in (0 : ℝ)..α, g t) (hsmall : K * g α < 1) :
    ∃ u ∈ Metric.closedBall ω α, f u = 0 ∧ Function.Bijective (fderiv ℝ f u) := by
  sorry

end NASC
