module

public import NASC.FloatingPoint.Basic
public import NASC.IterativeMethods
public import Mathlib.Order.Interval.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import NASC.Support.Analysis

/-!
# Interval arithmetic and verified computation

Endpoint arithmetic, inclusion over expression trees, outward rounding, the mean-value form,
interval Newton and Krawczyk certificates, approximate-inverse error bounds, and Plum's
Banach-space existence certificate. See section 7 of the gap catalogue.
The interval Newton proof uses Mathlib's real mean value and intermediate value theorems.

## Main definitions

* `NASC.intervalCorners op X Y`: the four endpoint values of a binary operation.
* `NASC.intervalBox X`, `NASC.intervalMatrix J`: boxes of vectors and of matrices.
* `NASC.IntervalExpr ι`: expression trees with operations `NASC.IntervalExpr.BinOp`, with
  their scalar evaluation `IntervalExpr.eval`, natural interval extension
  `IntervalExpr.enclosure`, admissibility `IntervalExpr.Admissible` and variable occurrences
  `IntervalExpr.variableOccurrences`.

## Main results

* `NASC.image2_eq_Icc_intervalCorners`: exact ranges of the four interval operations.
* `NASC.IntervalExpr.range_subset_enclosure`: the fundamental theorem of interval arithmetic,
  with `IntervalExpr.image_eval_subset_enclosure` and
  `IntervalExpr.enclosure_eq_image_eval_of_nodup`.
* `NASC.IntervalExpr.exists_enclosure_width_le`: linear width of the natural extension.
* `NASC.FloatingPointFormat.exists_least_outwardInterval`: outward rounding.
* `NASC.meanValueEnclosure_excessWidth_le`: quadratic excess width of the mean-value form.
* `NASC.zeros_subset_intervalNewton_and_existsUnique`: the scalar interval Newton theorem.
* `NASC.zeros_subset_intervalNewtonBox_and_existsUnique`,
  `NASC.existsUnique_zero_of_krawczyk_subset_interior`: interval Newton and Krawczyk in boxes.
* `NASC.norm_sub_le_of_norm_one_sub_comp_lt_one`, `NASC.norm_error_le_of_approximateInverse`:
  the approximate-inverse error bound.
* `NASC.realMatrixSpectralRadius_lt_one_of_image_subset_interior`: strict affine inclusion.
* `NASC.exists_zero_mem_closedBall_of_plum_bound`: Plum's existence theorem.
-/

public section

noncomputable section

namespace NASC

open Set Filter
open scoped Matrix Matrix.Norms.L2Operator Interval

/-- The four possible evaluations of a binary operation on endpoint pairs. -/
def intervalCorners (op : ℝ → ℝ → ℝ) (X Y : NonemptyInterval ℝ) : Finset ℝ :=
  {op X.fst Y.fst, op X.fst Y.snd, op X.snd Y.fst, op X.snd Y.snd}

/-- The defining formula for the corner values. -/
theorem intervalCorners_def (op : ℝ → ℝ → ℝ) (X Y : NonemptyInterval ℝ) :
    intervalCorners op X Y = {op X.fst Y.fst, op X.fst Y.snd, op X.snd Y.fst, op X.snd Y.snd} := by
  unfold intervalCorners
  rfl

/-- **Gap 7.1.** Addition, subtraction, multiplication and admissible division have
exact ranges given by the smallest and largest corner values. -/
theorem image2_eq_Icc_intervalCorners (op : ℝ → ℝ → ℝ) (X Y : NonemptyInterval ℝ)
    (hop : op = (· + ·) ∨ op = (· - ·) ∨ op = (· * ·) ∨ op = (· / ·) ∧ 0 ∉ Y) :
    Set.image2 op (X : Set ℝ) (Y : Set ℝ) =
      Icc (sInf (↑(intervalCorners op X Y) : Set ℝ))
        (sSup (↑(intervalCorners op X Y) : Set ℝ)) := by
  sorry

/-- The product box of a family of real intervals. -/
def intervalBox {ι : Type*} (X : ι → NonemptyInterval ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun i ↦ (X i : Set ℝ)

/-- Membership in a product box is coordinatewise membership. -/
@[simp] theorem mem_intervalBox {ι : Type*} {X : ι → NonemptyInterval ℝ} {x : ι → ℝ} :
    x ∈ intervalBox X ↔ ∀ i, x i ∈ X i := by
  simp only [intervalBox, Set.mem_univ_pi, SetLike.mem_coe]

/-- The lower corner of a box lies in the box. -/
theorem fst_mem_intervalBox {ι : Type*} (X : ι → NonemptyInterval ℝ) :
    (fun i ↦ (X i).fst) ∈ intervalBox X :=
  mem_intervalBox.mpr fun i ↦ ⟨le_rfl, (X i).fst_le_snd⟩

/-- A matrix box, expressing independent entrywise interval bounds. -/
def intervalMatrix {m n : Type*} (J : m → n → NonemptyInterval ℝ) : Set (Matrix m n ℝ) :=
  {A | ∀ i j, A i j ∈ J i j}

/-- Membership in a matrix box is entrywise membership. -/
@[simp] theorem mem_intervalMatrix {m n : Type*} {J : m → n → NonemptyInterval ℝ}
    {A : Matrix m n ℝ} : A ∈ intervalMatrix J ↔ ∀ i j, A i j ∈ J i j := by
  unfold intervalMatrix
  exact Iff.rfl

/-- The four binary operations of interval expressions. -/
inductive IntervalExpr.BinOp
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division; its divisor enclosure must avoid zero. -/
  | div

/-- The real operation denoted by a binary operation symbol. -/
def IntervalExpr.BinOp.eval : IntervalExpr.BinOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

/-- The operation `add` is addition. -/
@[simp] theorem IntervalExpr.BinOp.eval_add (a b : ℝ) : BinOp.add.eval a b = a + b := by
  unfold IntervalExpr.BinOp.eval
  rfl

/-- The operation `sub` is subtraction. -/
@[simp] theorem IntervalExpr.BinOp.eval_sub (a b : ℝ) : BinOp.sub.eval a b = a - b := by
  unfold IntervalExpr.BinOp.eval
  rfl

/-- The operation `mul` is multiplication. -/
@[simp] theorem IntervalExpr.BinOp.eval_mul (a b : ℝ) : BinOp.mul.eval a b = a * b := by
  unfold IntervalExpr.BinOp.eval
  rfl

/-- The operation `div` is division. -/
@[simp] theorem IntervalExpr.BinOp.eval_div (a b : ℝ) : BinOp.div.eval a b = a / b := by
  unfold IntervalExpr.BinOp.eval
  rfl

/-- An interval expression records the operation graph and the domain of each division
and unary primitive. -/
inductive IntervalExpr (ι : Type*)
  /-- The variable with index `i`. -/
  | var (i : ι)
  /-- A real constant. -/
  | const (x : ℝ)
  /-- A binary operation applied to two subexpressions. -/
  | bin (op : IntervalExpr.BinOp) (a b : IntervalExpr ι)
  /-- A unary primitive `f`, with its domain, applied to a subexpression. -/
  | unary (f : ℝ → ℝ) (domain : Set ℝ) (a : IntervalExpr ι)

namespace IntervalExpr

variable {ι : Type*}

/-- Scalar evaluation. The admissibility predicate supplies the required domain
checks when this total Lean function is used. -/
def eval (x : ι → ℝ) : IntervalExpr ι → ℝ
  | .var i => x i
  | .const z => z
  | .bin op a b => op.eval (a.eval x) (b.eval x)
  | .unary f _ a => f (a.eval x)

/-- A variable evaluates to its coordinate. -/
@[simp] theorem eval_var (x : ι → ℝ) (i : ι) : (var i).eval x = x i := by
  rw [eval]

/-- A constant evaluates to itself. -/
@[simp] theorem eval_const (x : ι → ℝ) (z : ℝ) : (const z : IntervalExpr ι).eval x = z := by
  rw [eval]

/-- A binary operation evaluates its operands. -/
@[simp] theorem eval_bin (x : ι → ℝ) (op : BinOp) (a b : IntervalExpr ι) :
    (bin op a b).eval x = op.eval (a.eval x) (b.eval x) := by
  rw [eval]

/-- A unary primitive is applied to the value of its operand. -/
@[simp] theorem eval_unary (x : ι → ℝ) (f : ℝ → ℝ) (domain : Set ℝ) (a : IntervalExpr ι) :
    (unary f domain a).eval x = f (a.eval x) := by
  rw [eval]

/-- Natural range extension. Each occurrence of a variable ranges independently.
Admissibility ensures the exact intermediate sets are compact intervals. -/
def enclosure (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Set ℝ
  | .var i => X i
  | .const z => {z}
  | .bin op a b => image2 op.eval (a.enclosure X) (b.enclosure X)
  | .unary f _ a => f '' a.enclosure X

/-- The enclosure of a variable is its interval. -/
@[simp] theorem enclosure_var (X : ι → NonemptyInterval ℝ) (i : ι) :
    (var i).enclosure X = X i := by
  rw [enclosure]

/-- The enclosure of a constant is a singleton. -/
@[simp] theorem enclosure_const (X : ι → NonemptyInterval ℝ) (z : ℝ) :
    (const z : IntervalExpr ι).enclosure X = {z} := by
  rw [enclosure]

/-- The enclosure of a binary operation is the image of the operand enclosures. -/
@[simp] theorem enclosure_bin (X : ι → NonemptyInterval ℝ) (op : BinOp) (a b : IntervalExpr ι) :
    (bin op a b).enclosure X = image2 op.eval (a.enclosure X) (b.enclosure X) := by
  rw [enclosure]

/-- The enclosure of a unary primitive is the image of the operand enclosure. -/
@[simp] theorem enclosure_unary (X : ι → NonemptyInterval ℝ) (f : ℝ → ℝ) (domain : Set ℝ)
    (a : IntervalExpr ι) : (unary f domain a).enclosure X = f '' a.enclosure X := by
  rw [enclosure]

/-- Every division avoids zero and unary primitives are continuous on the enclosing domain. -/
def Admissible (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Prop
  | .var _ | .const _ => True
  | .bin op a b => a.Admissible X ∧ b.Admissible X ∧ (op = .div → 0 ∉ b.enclosure X)
  | .unary f domain a =>
    a.Admissible X ∧ a.enclosure X ⊆ domain ∧ ContinuousOn f domain

/-- Variables are admissible. -/
@[simp] theorem admissible_var (X : ι → NonemptyInterval ℝ) (i : ι) : (var i).Admissible X :=
  trivial

/-- Constants are admissible. -/
@[simp] theorem admissible_const (X : ι → NonemptyInterval ℝ) (z : ℝ) :
    (const z : IntervalExpr ι).Admissible X :=
  trivial

/-- A binary operation is admissible when its operands are and a divisor avoids zero. -/
@[simp] theorem admissible_bin (X : ι → NonemptyInterval ℝ) (op : BinOp) (a b : IntervalExpr ι) :
    (bin op a b).Admissible X ↔
      a.Admissible X ∧ b.Admissible X ∧ (op = .div → 0 ∉ b.enclosure X) := by
  rw [Admissible]

/-- A unary primitive is admissible when its operand is, the operand enclosure lies in the
domain, and the primitive is continuous on the domain. -/
@[simp] theorem admissible_unary (X : ι → NonemptyInterval ℝ) (f : ℝ → ℝ) (domain : Set ℝ)
    (a : IntervalExpr ι) :
    (unary f domain a).Admissible X ↔
      a.Admissible X ∧ a.enclosure X ⊆ domain ∧ ContinuousOn f domain := by
  rw [Admissible]

/-- Occurrences of variables, with multiplicity. -/
def variableOccurrences : IntervalExpr ι → List ι
  | .var i => [i]
  | .const _ => []
  | .bin _ a b => a.variableOccurrences ++ b.variableOccurrences
  | .unary _ _ a => a.variableOccurrences

/-- A variable occurs once. -/
@[simp] theorem variableOccurrences_var (i : ι) : (var i).variableOccurrences = [i] := by
  rw [variableOccurrences]

/-- A constant has no variable occurrences. -/
@[simp] theorem variableOccurrences_const (z : ℝ) :
    (const z : IntervalExpr ι).variableOccurrences = [] := by
  rw [variableOccurrences]

/-- The occurrences of a binary operation are those of its operands. -/
@[simp] theorem variableOccurrences_bin (op : BinOp) (a b : IntervalExpr ι) :
    (bin op a b).variableOccurrences = a.variableOccurrences ++ b.variableOccurrences := by
  rw [variableOccurrences]

/-- The occurrences of a unary primitive are those of its operand. -/
@[simp] theorem variableOccurrences_unary (f : ℝ → ℝ) (domain : Set ℝ) (a : IntervalExpr ι) :
    (unary f domain a).variableOccurrences = a.variableOccurrences := by
  rw [variableOccurrences]

/-- Evaluation of a point in the box belongs to the natural enclosure. -/
theorem eval_mem_enclosure (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ} {x : ι → ℝ}
    (hx : x ∈ intervalBox X) : e.eval x ∈ e.enclosure X := by
  induction e with
  | var i => exact mem_intervalBox.mp hx i
  | const t => exact Set.mem_singleton t
  | bin op a b ha hb => exact ⟨a.eval x, ha, b.eval x, hb, rfl⟩
  | unary f domain a ha => exact ⟨a.eval x, ha, rfl⟩

/-- A smaller box preserves admissibility and shrinks the associated enclosure. -/
theorem admissible_enclosure_mono (e : IntervalExpr ι) {X Y : ι → NonemptyInterval ℝ}
    (h : e.Admissible X) (hYX : ∀ i, Y i ≤ X i) :
    e.Admissible Y ∧ e.enclosure Y ⊆ e.enclosure X := by
  induction e with
  | var i => exact ⟨trivial, NonemptyInterval.coe_subset_coe.mpr (hYX i)⟩
  | const t => exact ⟨trivial, Subset.rfl⟩
  | bin op a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2.1
    exact ⟨⟨ha'.1, hb'.1, fun hop hy ↦ h.2.2 hop (hb'.2 hy)⟩, image2_subset ha'.2 hb'.2⟩
  | unary f domain a ha =>
    have ha' := ha h.1
    exact ⟨⟨ha'.1, ha'.2.trans h.2.1, h.2.2⟩, image_mono ha'.2⟩

/-- Evaluation depends only on the entries of the variables occurring in the expression. -/
theorem eval_eq_of_eqOn_occurrences (e : IntervalExpr ι) {x y : ι → ℝ}
    (h : ∀ i ∈ e.variableOccurrences, x i = y i) : e.eval x = e.eval y := by
  induction e with
  | var i => exact h i List.mem_cons_self
  | const t => rfl
  | bin op a b ha hb =>
    exact congrArg₂ op.eval
      (ha fun i hi ↦ h i (List.mem_append_left _ hi))
      (hb fun i hi ↦ h i (List.mem_append_right _ hi))
  | unary f domain a ha => exact congrArg f (ha h)

/-- Independent subexpressions can realize any pair from their respective enclosures together. -/
theorem image2_enclosure_subset_range {a b : IntervalExpr ι} {X : ι → NonemptyInterval ℝ}
    (op : ℝ → ℝ → ℝ) (hd : a.variableOccurrences.Disjoint b.variableOccurrences)
    (ha : a.enclosure X ⊆ a.eval '' intervalBox X)
    (hb : b.enclosure X ⊆ b.eval '' intervalBox X) :
    image2 op (a.enclosure X) (b.enclosure X) ⊆
      (fun x ↦ op (a.eval x) (b.eval x)) '' intervalBox X := by
  classical
  rintro t ⟨r, hr, s, hs, rfl⟩
  obtain ⟨x, hx, rfl⟩ := ha hr
  obtain ⟨y, hy, rfl⟩ := hb hs
  let z := fun i ↦ if i ∈ a.variableOccurrences then x i else y i
  have hz : z ∈ intervalBox X := by
    refine mem_intervalBox.mpr fun i ↦ ?_
    by_cases hi : i ∈ a.variableOccurrences
    · simpa only [z, ite_eq_left hi] using mem_intervalBox.mp hx i
    · simpa only [z, ite_eq_right hi] using mem_intervalBox.mp hy i
  have haz : a.eval z = a.eval x :=
    a.eval_eq_of_eqOn_occurrences fun i hi ↦ ite_eq_left hi
  have hbz : b.eval z = b.eval y :=
    b.eval_eq_of_eqOn_occurrences fun i hi ↦ ite_eq_right fun ha' ↦ List.disjoint_left.mp hd ha' hi
  exact ⟨z, hz, congrArg₂ op haz hbz⟩

/-- An enclosure of an expression is attained on the box when each variable occurs at most once. -/
theorem enclosure_subset_range_of_nodup (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ}
    (h : e.variableOccurrences.Nodup) :
    e.enclosure X ⊆ e.eval '' intervalBox X := by
  classical
  induction e with
  | var i =>
    intro t ht
    refine ⟨Function.update (fun j ↦ (X j).fst) i t, mem_intervalBox.mpr fun j ↦ ?_,
      Function.update_self ..⟩
    by_cases hj : j = i
    · subst j
      rw [Function.update_self, ← SetLike.mem_coe]
      simpa only [enclosure] using ht
    · rw [Function.update_of_ne hj]
      exact ⟨le_rfl, (X j).fst_le_snd⟩
  | const t =>
    rintro s (rfl : s = t)
    exact ⟨fun i ↦ (X i).fst, fst_mem_intervalBox X, rfl⟩
  | bin op a b ha hb =>
    have hs := List.nodup_append'.mp h
    exact image2_enclosure_subset_range op.eval hs.2.2 (ha hs.1) (hb hs.2.1)
  | unary f domain a ha =>
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨x, hx, rfl⟩ := ha h ht
    exact ⟨x, hx, rfl⟩

/-- The natural interval extension encloses the range of an expression on the box. -/
theorem image_eval_subset_enclosure (e : IntervalExpr ι) (X : ι → NonemptyInterval ℝ) :
    e.eval '' intervalBox X ⊆ e.enclosure X := by
  rintro y ⟨x, hx, rfl⟩
  exact e.eval_mem_enclosure hx

/-- The natural interval extension is exact for an expression with no repeated variable. -/
theorem enclosure_eq_image_eval_of_nodup (e : IntervalExpr ι) (X : ι → NonemptyInterval ℝ)
    (h : e.variableOccurrences.Nodup) : e.enclosure X = e.eval '' intervalBox X :=
  (e.enclosure_subset_range_of_nodup h).antisymm (e.image_eval_subset_enclosure X)

/-- **Gap 7.3.** The natural interval extension encloses the range, is inclusion isotone,
and is exact for expressions with no repeated variable. -/
theorem range_subset_enclosure (e : IntervalExpr ι) {X : ι → NonemptyInterval ℝ}
    (h : e.Admissible X) :
    e.eval '' intervalBox X ⊆ e.enclosure X ∧
      (∀ Y : ι → NonemptyInterval ℝ, (∀ i, Y i ≤ X i) →
        e.Admissible Y ∧ e.enclosure Y ⊆ e.enclosure X) ∧
      (e.variableOccurrences.Nodup → e.enclosure X = e.eval '' intervalBox X) :=
  ⟨e.image_eval_subset_enclosure X, fun _ hYX ↦ e.admissible_enclosure_mono h hYX,
    e.enclosure_eq_image_eval_of_nodup X⟩

/-- Each unary primitive is Lipschitz on the enclosure of its argument. This predicate
contains no domain tests; those are supplied by `IntervalExpr.Admissible`. -/
def LipschitzOnEnclosures (X : ι → NonemptyInterval ℝ) : IntervalExpr ι → Prop
  | .var _ | .const _ => True
  | .bin _ a b => a.LipschitzOnEnclosures X ∧ b.LipschitzOnEnclosures X
  | .unary f _ a =>
    a.LipschitzOnEnclosures X ∧ ∃ L, LipschitzOnWith L f (a.enclosure X)

/-- Variables satisfy the Lipschitz condition. -/
@[simp] theorem lipschitzOnEnclosures_var (X : ι → NonemptyInterval ℝ) (i : ι) :
    (var i).LipschitzOnEnclosures X :=
  trivial

/-- Constants satisfy the Lipschitz condition. -/
@[simp] theorem lipschitzOnEnclosures_const (X : ι → NonemptyInterval ℝ) (z : ℝ) :
    (const z : IntervalExpr ι).LipschitzOnEnclosures X :=
  trivial

/-- A binary operation satisfies the Lipschitz condition when its operands do. -/
@[simp] theorem lipschitzOnEnclosures_bin (X : ι → NonemptyInterval ℝ) (op : BinOp)
    (a b : IntervalExpr ι) :
    (bin op a b).LipschitzOnEnclosures X ↔
      a.LipschitzOnEnclosures X ∧ b.LipschitzOnEnclosures X := by
  rw [LipschitzOnEnclosures]

/-- A unary primitive satisfies the Lipschitz condition when its operand does and the
primitive is Lipschitz on the operand enclosure. -/
@[simp] theorem lipschitzOnEnclosures_unary (X : ι → NonemptyInterval ℝ) (f : ℝ → ℝ)
    (domain : Set ℝ) (a : IntervalExpr ι) :
    (unary f domain a).LipschitzOnEnclosures X ↔
      a.LipschitzOnEnclosures X ∧ ∃ L, LipschitzOnWith L f (a.enclosure X) := by
  rw [LipschitzOnEnclosures]

/-- **Gap 7.7.** The enclosure width is at most linear in the largest input width
inside an admissible reference box. -/
theorem exists_enclosure_width_le [Fintype ι]
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
when each derivative interval has width linear in the box diameter. The function is `C¹`
near the box. -/
theorem meanValueEnclosure_excessWidth_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (X D : ι → NonemptyInterval ℝ)
    (hf : ∀ x ∈ intervalBox X, ContDiffAt ℝ 1 f x) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x ∈ intervalBox X, ∀ i, fderiv ℝ f x (Pi.single i 1) ∈ D i)
    (hwidth : ∀ i, (D i).snd - (D i).fst ≤ L * ‖fun j ↦ (X j).snd - (X j).fst‖) :
    let m := fun i ↦ ((X i).fst + (X i).snd) / 2
    let F := {y : ℝ | ∃ (a x : ι → ℝ), (∀ i, a i ∈ D i) ∧ x ∈ intervalBox X ∧
      y = f m + ∑ i, a i * (x i - m i)}
    let R := f '' intervalBox X
    R ⊆ F ∧
      (sSup F - sInf F) - (sSup R - sInf R) ≤
        2 * Fintype.card ι * L * ‖fun i ↦ (X i).snd - (X i).fst‖ ^ 2 := by
  sorry

/-- A secant slope between two points in an interval belongs to any interval enclosing
all derivatives. For a repeated point one may take any member of the derivative interval. -/
theorem exists_intervalSlope {f : ℝ → ℝ} (X D : NonemptyInterval ℝ)
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d (X : Set ℝ) x)
    {a b : ℝ} (ha : a ∈ X) (hb : b ∈ X) :
    ∃ d ∈ D, f b - f a = d * (b - a) := by
  have hf : ContinuousOn f (X : Set ℝ) := continuousOn_of_forall_hasDerivWithinAt hderiv
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

/-- A real interval that does not contain zero lies on one side of it. -/
theorem forall_pos_or_forall_neg_of_zero_notMem {D : NonemptyInterval ℝ} (hD : 0 ∉ D) :
    (∀ d ∈ D, 0 < d) ∨ (∀ d ∈ D, d < 0) := by
  by_cases h : D.snd < 0
  · exact Or.inr fun d hd ↦ hd.2.trans_lt h
  · have hp : 0 < D.fst := lt_of_not_ge fun he ↦ hD ⟨he, le_of_not_gt h⟩
    exact Or.inl fun d hd ↦ hp.trans_le hd.1

/-- A function whose derivatives on an interval lie in an interval avoiding zero is injective
there. -/
theorem injOn_of_forall_hasDerivWithinAt {f : ℝ → ℝ} (X D : NonemptyInterval ℝ) (hD : 0 ∉ D)
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d (X : Set ℝ) x) :
    InjOn f (X : Set ℝ) := by
  intro a ha b hb hab
  obtain ⟨d, hd, hs⟩ := exists_intervalSlope X D hderiv ha hb
  have he : d * (b - a) = 0 := by rw [← hs, hab, sub_self]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left fun h ↦ hD (h ▸ hd))).symm

/-- **Gap 7.8.** The interval Newton image encloses all zeros, and inclusion of that
image in the input interval certifies a unique zero. -/
theorem zeros_subset_intervalNewton_and_existsUnique {f : ℝ → ℝ} (X D : NonemptyInterval ℝ)
    {x₀ : ℝ} (hx : x₀ ∈ X) (hD : 0 ∉ D)
    (hderiv : ∀ x ∈ X, ∃ d ∈ D, HasDerivWithinAt f d (X : Set ℝ) x) :
    let N := (fun d ↦ x₀ - f x₀ / d) '' (D : Set ℝ)
    {x ∈ (X : Set ℝ) | f x = 0} ⊆ N ∧
      (N ⊆ (X : Set ℝ) → ∃! x, x ∈ X ∧ f x = 0) := by
  have hd0 {d : ℝ} (hd : d ∈ D) : d ≠ 0 := fun he ↦ hD (he ▸ hd)
  have hf : ContinuousOn f (X : Set ℝ) := continuousOn_of_forall_hasDerivWithinAt hderiv
  have hsl {a b : ℝ} (ha : a ∈ X) (hb : b ∈ X) := exists_intervalSlope X D hderiv ha hb
  refine ⟨?_, fun hN ↦ ?_⟩
  · rintro y ⟨hy, hry⟩
    obtain ⟨d, hd, hs⟩ := hsl hx hy
    refine ⟨d, hd, ?_⟩
    have he : f x₀ / d * d = f x₀ := div_mul_cancel₀ _ (hd0 hd)
    have hmul : d * (x₀ - f x₀ / d - y) = 0 := by linarith only [hs, hry, he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (hd0 hd))
  have hsignAt {y : ℝ} (hy : y ∈ X) :
      ∃ d ∈ D, x₀ - f x₀ / d ∈ X ∧ f y = d * (y - (x₀ - f x₀ / d)) := by
    obtain ⟨d, hd, hs⟩ := hsl hx hy
    refine ⟨d, hd, hN ⟨d, hd, rfl⟩, ?_⟩
    linarith only [hs, div_mul_cancel₀ (f x₀) (hd0 hd)]
  obtain ⟨dl, hdl, hl, hl'⟩ := hsignAt ⟨le_rfl, X.fst_le_snd⟩
  obtain ⟨dr, hdr, hr, hr'⟩ := hsignAt ⟨X.fst_le_snd, le_rfl⟩
  have hz : (0 : ℝ) ∈ f '' (X : Set ℝ) := by
    rcases forall_pos_or_forall_neg_of_zero_notMem hD with hpos | hneg
    · apply intermediate_value_Icc X.fst_le_snd hf
      exact ⟨by rw [hl']; exact mul_nonpos_of_nonneg_of_nonpos (hpos _ hdl).le
                 (sub_nonpos.mpr hl.1),
        by rw [hr']; exact mul_nonneg (hpos _ hdr).le (sub_nonneg.mpr hr.2)⟩
    · apply intermediate_value_Icc' X.fst_le_snd hf
      exact ⟨by rw [hr']; exact mul_nonpos_of_nonpos_of_nonneg (hneg _ hdr).le
                 (sub_nonneg.mpr hr.2),
        by rw [hl']; exact mul_nonneg_of_nonpos_of_nonpos (hneg _ hdl).le
                 (sub_nonpos.mpr hl.1)⟩
  obtain ⟨z, hzX, hzf⟩ := hz
  exact ⟨z, ⟨hzX, hzf⟩, fun y hy ↦
    injOn_of_forall_hasDerivWithinAt X D hD hderiv hy.1 hzX (hy.2.trans hzf.symm)⟩

/-- **Gap 7.9.** The interval Newton operator in finite dimensions gives a unique
root when the image is contained in the initial box. The map is `C¹` near the box. -/
theorem zeros_subset_intervalNewtonBox_and_existsUnique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → (ι → ℝ)) (X : ι → NonemptyInterval ℝ) (J : ι → ι → NonemptyInterval ℝ)
    {x₀ : ι → ℝ} (hx : x₀ ∈ intervalBox X) (hf : ∀ x ∈ intervalBox X, ContDiffAt ℝ 1 f x)
    (hJ : ∀ x ∈ intervalBox X, ∃ A ∈ intervalMatrix J,
      ∀ v, fderiv ℝ f x v = A *ᵥ v)
    (hnon : ∀ A ∈ intervalMatrix J, A.det ≠ 0) :
    let N := (fun A : Matrix ι ι ℝ ↦ x₀ - A⁻¹ *ᵥ f x₀) '' intervalMatrix J
    {x ∈ intervalBox X | f x = 0} ⊆ N ∧
      (N ⊆ intervalBox X → ∃! x, x ∈ intervalBox X ∧ f x = 0) := by
  sorry

/-- **Gap 7.10.** Strict inclusion of the Krawczyk image certifies nonsingularity,
uniqueness and a root enclosure. The map is `C¹` near the shifted box `x₀ + X`. -/
theorem existsUnique_zero_of_krawczyk_subset_interior {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → (ι → ℝ)) (X : ι → NonemptyInterval ℝ) (J : ι → ι → NonemptyInterval ℝ)
    (x₀ : ι → ℝ) (R : Matrix ι ι ℝ)
    (hx : 0 ∈ intervalBox X) (hf : ∀ y ∈ intervalBox X, ContDiffAt ℝ 1 f (x₀ + y))
    (hJ : ∀ y ∈ intervalBox X, ∃ A ∈ intervalMatrix J,
      ∀ v, fderiv ℝ f (x₀ + y) v = A *ᵥ v) :
    let K := {z | ∃ A ∈ intervalMatrix J, ∃ y ∈ intervalBox X,
      z = -(R *ᵥ f x₀) + (1 - R * A) *ᵥ y}
    K ⊆ interior (intervalBox X) →
      R.det ≠ 0 ∧ (∀ A ∈ intervalMatrix J, A.det ≠ 0) ∧
      (∃! y, y ∈ intervalBox X ∧ f (x₀ + y) = 0) ∧
      ∀ y ∈ intervalBox X, f (x₀ + y) = 0 → y ∈ K := by
  sorry

/-- A preconditioned residual bounds the error of an approximate solution of `A y = b` when the
approximate inverse `R` has defect `1 - R ∘ A` of norm less than one. No completeness or
invertibility is needed. -/
theorem norm_sub_le_of_norm_one_sub_comp_lt_one {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (R : F →L[𝕜] E) {b : F} {x y : E} (hy : A y = b)
    (h : ‖(1 : E →L[𝕜] E) - R.comp A‖ < 1) :
    ‖y - x‖ ≤ ‖R (b - A x)‖ / (1 - ‖(1 : E →L[𝕜] E) - R.comp A‖) := by
  have hsplit : y - x = R (b - A x) + ((1 : E →L[𝕜] E) - R.comp A) (y - x) := by
    rw [← hy, ← map_sub, sub_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, add_sub_cancel]
  have hbound := ((1 : E →L[𝕜] E) - R.comp A).le_opNorm (y - x)
  have htri := norm_add_le (R (b - A x)) (((1 : E →L[𝕜] E) - R.comp A) (y - x))
  rw [← hsplit] at htri
  rw [le_div_iff₀ (sub_pos.mpr h)]
  nlinarith only [htri, hbound]

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
  have hAx : A.toEuclideanLin ((A⁻¹).toEuclideanLin b) = b := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.toLpLin_one,
      LinearMap.id_apply]
  have hE : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (1 - R * A) =
      1 - (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) R).comp
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := by
    rw [map_sub, map_one, map_mul]
    rfl
  have hnorm : ‖1 - R * A‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (1 - R * A)‖ := rfl
  have hAx' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A ((A⁻¹).toEuclideanLin b) = b := hAx
  have hres : ‖R.toEuclideanLin (b - A.toEuclideanLin x)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) R
        (b - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x)‖ := rfl
  rw [hnorm, hE] at h ⊢
  rw [hres]
  exact norm_sub_le_of_norm_one_sub_comp_lt_one _ _ hAx' h

/-- **Gap 7.12.** A strict interior affine enclosure forces the linear part to
have spectral radius less than one. -/
theorem realMatrixSpectralRadius_lt_one_of_image_subset_interior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → NonemptyInterval ℝ) (b : Fin n → ℝ)
    (h : (fun x ↦ b + A *ᵥ x) '' intervalBox X ⊆ interior (intervalBox X)) :
    realMatrixSpectralRadius A < 1 := by
  sorry

/-- **Gap 7.13.** Plum's quantitative enclosure in the dense-range case. The
derivative lower bound, density and completeness of `E` ensure invertibility at the center,
so `F` need not be complete. -/
theorem exists_zero_mem_closedBall_of_plum_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (ω : E) (g : ℝ → ℝ) {K δ α : ℝ}
    (hK : 0 < K) (hα : 0 < α) (hg : Monotone g) (hg₀ : g 0 = 0)
    (hf : Differentiable ℝ f) (hω : ‖f ω‖ ≤ δ)
    (hinv : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ f ω v‖) (hdense : DenseRange (fderiv ℝ f ω))
    (hvar : ∀ v, ‖fderiv ℝ f (ω + v) - fderiv ℝ f ω‖ ≤ g ‖v‖)
    (hδ : δ ≤ α / K - ∫ t in (0 : ℝ)..α, g t) (hsmall : K * g α < 1) :
    ∃ u ∈ Metric.closedBall ω α, f u = 0 ∧ Function.Bijective (fderiv ℝ f u) := by
  sorry

end NASC
