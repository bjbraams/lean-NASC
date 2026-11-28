module

public import NASC.FloatingPoint.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import NASC.Support.Algebra

/-!
# Rounding error analysis in the standard model

The standard model of floating-point arithmetic and its consequences: the accumulated budget
`γₙ` of a product of rounding factors, summation along a tree, dot and matrix products,
Kahan's compensated summation in a format with rounding to nearest, and forward
substitution. Gap numbers refer to section 1 of `GAPS.md`.

## Notation

* `γₙ = roundingGamma u n = n u / (1 - n u)`, the accumulated budget of `n` rounding factors.
* The standard model `HasRelativeError u x y` says `y = x (1 + δ)` with `|δ| ≤ u`.

## Main definitions

* `NASC.roundingGamma`, `NASC.HasRelativeError`.
* `NASC.SumTree`, `SumTree.eval`, `SumTree.depth`, `SumTree.leaves`.
* `NASC.kahanStep`, `NASC.kahanAccumulator`.
* `NASC.IsRoundedRowSum`, `NASC.IsRoundedForwardSubstitution`.

## Main results

* `NASC.roundingGamma_add_add_mul_le`: `γⱼ + γₖ + γⱼ γₖ ≤ γⱼ₊ₖ`.
* `NASC.hasRelativeError_prod_zpow`: a signed product of rounding factors has budget `γₙ`.
* `SumTree.abs_eval_sub_sum_le`: summation along a tree of depth `d` has budget `γ_d`.
* `SumTree.exists_dotProduct_eq_sum_mul_perturbed`, `SumTree.abs_mul_apply_sub_eval_le`:
  componentwise backward error of dot products and forward error of matrix products.
* `NASC.abs_kahanAccumulator_sub_sum_le`: Kahan's bound `(2u + O(n u²)) ∑ |xᵢ|` for correct
  rounding to nearest.
* `IsRoundedForwardSubstitution.exists_add_mulVec_eq`: componentwise backward error of
  forward substitution.
-/

public section

noncomputable section

namespace NASC

open scoped Matrix

/-- Accumulated relative error bound `γₙ = n u / (1 - n u)` for a product of `n` rounding
factors. It is meaningful for `n u < 1`; at the pole `n u = 1` it takes the junk value `0`. -/
def roundingGamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

/-- The rational expression for the accumulated error bound. -/
theorem roundingGamma_def (u : ℝ) (n : ℕ) :
    roundingGamma u n = n * u / (1 - n * u) := (rfl)

/-- No rounding factor has zero budget. -/
@[simp]
theorem roundingGamma_zero (u : ℝ) : roundingGamma u 0 = 0 := by
  simp [roundingGamma_def]

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

/-- **Gap 1.8.** Two error factors compose with the sum of their budgets. -/
theorem roundingGamma_add_add_mul_le {u : ℝ} {j k : ℕ} (hu : 0 ≤ u)
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
      exact ⟨0, by simp, by simp⟩
  | succ n ih =>
      have hu : 0 ≤ u := (abs_nonneg _).trans (hδ 0)
      have hu' : u < 1 := lt_one_of_natCast_mul_lt_one hu (Nat.succ_pos n) hn
      have htail : (n : ℝ) * u < 1 := natCast_mul_lt_one_of_le hu (Nat.le_succ n) hn
      obtain ⟨ε, hε, hprod⟩ := ih htail (fun i ↦ hδ i.succ) (fun i ↦ hs i.succ)
      simp only [one_mul] at hprod
      have htail_bound : |(∏ j : Fin n, (1 + δ j.succ) ^ s j.succ) - 1| ≤
          roundingGamma u n := by
        simpa only [hprod, add_sub_cancel_left] using hε
      rw [Fin.prod_univ_succ]
      have hadd := roundingGamma_add_add_mul_le hu (j := n) (k := 1) hn
      refine ⟨_, (abs_mul_sub_one_le (abs_zpow_one_add_sub_one_le hu hu' (hδ 0) (hs 0))
        htail_bound).trans ?_, ?_⟩
      · simpa only [add_comm (roundingGamma u n) (roundingGamma u 1),
          mul_comm (roundingGamma u n) (roundingGamma u 1)] using hadd
      · rw [one_mul, add_sub_cancel]

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

/-- A finite summation tree records addition order and preserves multiplicities. -/
inductive SumTree (ι : Type*)
  /-- A single summand, the term with index `i`. -/
  | leaf (i : ι)
  /-- The rounded sum of the values of two subtrees. -/
  | branch (left right : SumTree ι)

namespace SumTree

variable {ι : Type*}

/-- Leaves in evaluation order. -/
def leaves : SumTree ι → List ι
  | .leaf i => [i]
  | .branch a b => a.leaves ++ b.leaves

/-- A leaf lists its own index. -/
@[simp]
theorem leaves_leaf (i : ι) : (leaf i).leaves = [i] := (rfl)

/-- A branch lists the leaves of its left subtree before those of its right subtree. -/
@[simp]
theorem leaves_branch (a b : SumTree ι) : (branch a b).leaves = a.leaves ++ b.leaves := (rfl)

/-- Depth in additions. -/
def depth : SumTree ι → ℕ
  | .leaf _ => 0
  | .branch a b => max a.depth b.depth + 1

/-- A leaf performs no addition. -/
@[simp]
theorem depth_leaf (i : ι) : (leaf i).depth = 0 := (rfl)

/-- A branch adds one addition to the deeper of its subtrees. -/
@[simp]
theorem depth_branch (a b : SumTree ι) : (branch a b).depth = max a.depth b.depth + 1 := (rfl)

/-- Evaluation with one rounding operation at each branch. -/
def eval (rnd : ℝ → ℝ) (x : ι → ℝ) : SumTree ι → ℝ
  | .leaf i => x i
  | .branch a b => rnd (a.eval rnd x + b.eval rnd x)

/-- A leaf evaluates to its summand. -/
@[simp]
theorem eval_leaf (rnd : ℝ → ℝ) (x : ι → ℝ) (i : ι) : (leaf i).eval rnd x = x i := (rfl)

/-- A branch rounds the sum of the values of its subtrees. -/
@[simp]
theorem eval_branch (rnd : ℝ → ℝ) (x : ι → ℝ) (a b : SumTree ι) :
    (branch a b).eval rnd x = rnd (a.eval rnd x + b.eval rnd x) := (rfl)

/-- The standard model holds at every internal addition. -/
def HasStableEvaluation (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) : SumTree ι → Prop
  | .leaf _ => True
  | .branch a b =>
    a.HasStableEvaluation rnd x u ∧ b.HasStableEvaluation rnd x u ∧
    HasRelativeError u (a.eval rnd x + b.eval rnd x) ((branch a b).eval rnd x)

/-- A leaf has no addition to check. -/
@[simp]
theorem hasStableEvaluation_leaf (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) (i : ι) :
    (leaf i).HasStableEvaluation rnd x u := trivial

/-- A branch satisfies the standard model at its root addition and in both subtrees. -/
theorem hasStableEvaluation_branch_iff {rnd : ℝ → ℝ} {x : ι → ℝ} {u : ℝ} {a b : SumTree ι} :
    (branch a b).HasStableEvaluation rnd x u ↔
      a.HasStableEvaluation rnd x u ∧ b.HasStableEvaluation rnd x u ∧
        HasRelativeError u (a.eval rnd x + b.eval rnd x) ((branch a b).eval rnd x) := Iff.rfl

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
      have hlt {i : ℕ} (hi : i ≤ d + 1) : (i : ℝ) * u < 1 := natCast_mul_lt_one_of_le hu hi hd'
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
      have hu' : u < 1 := lt_one_of_natCast_mul_lt_one hu (Nat.succ_le_succ (Nat.zero_le d)) hd'
      have hδ' := hδ.trans (le_roundingGamma_one hu')
      exact (abs_mul_one_add_sub_le_of_abs_sub_le hdiff
        (by simpa only [leaves, List.map_append] using (branch a b).abs_sum_le_sum_abs_leaves y)
        hδ').trans (mul_le_mul_of_nonneg_right (roundingGamma_add_add_mul_le hu hd')
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
    hu (by simpa only [Nat.zero_add] using hd) ht (fun i ↦ by simp)

/-- The absolute sum of computed internal nodes, including the root when it is a branch. -/
def sumAbsComputed (rnd : ℝ → ℝ) (x : ι → ℝ) : SumTree ι → ℝ
  | .leaf _ => 0
  | .branch a b => |(branch a b).eval rnd x| + a.sumAbsComputed rnd x + b.sumAbsComputed rnd x

/-- A leaf computes no intermediate sum. -/
@[simp]
theorem sumAbsComputed_leaf (rnd : ℝ → ℝ) (x : ι → ℝ) (i : ι) :
    (leaf i).sumAbsComputed rnd x = 0 := (rfl)

/-- A branch adds the magnitude of its computed value to those of its subtrees. -/
theorem sumAbsComputed_branch (rnd : ℝ → ℝ) (x : ι → ℝ) (a b : SumTree ι) :
    (branch a b).sumAbsComputed rnd x =
      |(branch a b).eval rnd x| + a.sumAbsComputed rnd x + b.sumAbsComputed rnd x := (rfl)

/-- The inverse form of the standard model at each addition. -/
def HasInverseRelativeError (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) : SumTree ι → Prop
  | .leaf _ => True
  | .branch a b => a.HasInverseRelativeError rnd x u ∧ b.HasInverseRelativeError rnd x u ∧
    HasRelativeError u ((branch a b).eval rnd x) (a.eval rnd x + b.eval rnd x)

/-- A leaf has no addition to check. -/
@[simp]
theorem hasInverseRelativeError_leaf (rnd : ℝ → ℝ) (x : ι → ℝ) (u : ℝ) (i : ι) :
    (leaf i).HasInverseRelativeError rnd x u := trivial

/-- A branch satisfies the inverse model at its root addition and in both subtrees. -/
theorem hasInverseRelativeError_branch_iff {rnd : ℝ → ℝ} {x : ι → ℝ} {u : ℝ}
    {a b : SumTree ι} :
    (branch a b).HasInverseRelativeError rnd x u ↔
      a.HasInverseRelativeError rnd x u ∧ b.HasInverseRelativeError rnd x u ∧
        HasRelativeError u ((branch a b).eval rnd x) (a.eval rnd x + b.eval rnd x) := Iff.rfl

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
  have hsmall : ((1 + t.depth : ℕ) : ℝ) * u < 1 := natCast_mul_lt_one_of_le hu hd hm
  have hu' : u < 1 := lt_one_of_natCast_mul_lt_one hu (by omega) hm
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
theorem abs_mul_apply_sub_eval_le {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
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

/-- One step of Kahan's compensated summation on the state `(s, e)`: `y = ∘(x + e)`,
`t = ∘(s + y)` and `e' = ∘(∘(s - t) + y)`; the new state is `(t, e')`. -/
def kahanStep (rnd : ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  let y := rnd (x + p.2)
  let t := rnd (p.1 + y)
  (t, rnd (rnd (p.1 - t) + y))

/-- A Kahan step returns `t = ∘(s + ∘(x + e))` and `∘(∘(s - t) + ∘(x + e))`. -/
theorem kahanStep_def (rnd : ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ) :
    kahanStep rnd p x = (rnd (p.1 + rnd (x + p.2)),
      rnd (rnd (p.1 - rnd (p.1 + rnd (x + p.2))) + rnd (x + p.2))) := (rfl)

/-- The four exact results that a Kahan step rounds. -/
def kahanStepArgs (rnd : ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ) : List ℝ :=
  let y := rnd (x + p.2)
  let t := rnd (p.1 + y)
  [x + p.2, p.1 + y, p.1 - t, rnd (p.1 - t) + y]

/-- The arguments of the four roundings of a Kahan step, in order. -/
theorem kahanStepArgs_def (rnd : ℝ → ℝ) (p : ℝ × ℝ) (x : ℝ) :
    kahanStepArgs rnd p x =
      [x + p.2, p.1 + rnd (x + p.2), p.1 - rnd (p.1 + rnd (x + p.2)),
        rnd (p.1 - rnd (p.1 + rnd (x + p.2))) + rnd (x + p.2)] := (rfl)

/-- Kahan's computed sum and its compensation, starting from the state `(0, 0)`. -/
def kahanAccumulator (rnd : ℝ → ℝ) (xs : List ℝ) : ℝ × ℝ :=
  xs.foldl (kahanStep rnd) (0, 0)

/-- Kahan's accumulator folds the Kahan step over the summands. -/
theorem kahanAccumulator_def (rnd : ℝ → ℝ) (xs : List ℝ) :
    kahanAccumulator rnd xs = xs.foldl (kahanStep rnd) (0, 0) := (rfl)

/-- The empty sum leaves the state `(0, 0)`. -/
@[simp]
theorem kahanAccumulator_nil (rnd : ℝ → ℝ) : kahanAccumulator rnd [] = (0, 0) := (rfl)

/-- Appending a summand performs one Kahan step. -/
theorem kahanAccumulator_append_singleton (rnd : ℝ → ℝ) (xs : List ℝ) (x : ℝ) :
    kahanAccumulator rnd (xs ++ [x]) = kahanStep rnd (kahanAccumulator rnd xs) x := by
  rw [kahanAccumulator_def, kahanAccumulator_def, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- **Gap 1.12.** Kahan's error bound: there is an absolute constant `C` such that, for
correct rounding to nearest in any format, summands in the format, no overflow in any of the
roundings and `n u ≤ 1/2`, the computed sum is within `(2u + C n u²) ∑ |xᵢ|` of the exact sum.
The standard model at the four roundings of each step does not suffice. -/
theorem abs_kahanAccumulator_sub_sum_le :
    ∃ C > (0 : ℝ), ∀ (F : FloatingPointFormat) (rnd : F.Nearest) (xs : List ℝ),
      (∀ x ∈ xs, x ∈ F.numbers) →
      (∀ i : Fin xs.length, ∀ z ∈ kahanStepArgs rnd.round
        (kahanAccumulator rnd.round (xs.take i)) (xs.get i), |z| ≤ F.maxFinite) →
      (xs.length : ℝ) * F.unitRoundoff .nearest ≤ 1 / 2 →
      |(kahanAccumulator rnd.round xs).1 - xs.sum| ≤
        (2 * F.unitRoundoff .nearest + C * xs.length * F.unitRoundoff .nearest ^ 2) *
          (xs.map abs).sum := by
  sorry

/-- The strict subdiagonal part of row `i` of a forward substitution, `s = ∑_{j < i} T i j x j`,
computed by rounded products summed along a tree in the standard model. The first row has no
such terms and `s = 0`. -/
def IsRoundedRowSum {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (rnd : ℝ → ℝ)
    (u : ℝ) (i : Fin n) (s : ℝ) : Prop :=
  if i.val = 0 then s = 0 else
    ∃ t : SumTree {j : Fin n // j < i},
      t.leaves.Perm (Finset.univ.toList : List {j : Fin n // j < i}) ∧
      t.HasStableEvaluation rnd (fun j ↦ rnd (T i j.val * x j.val)) u ∧
      s = t.eval rnd (fun j ↦ rnd (T i j.val * x j.val))

/-- A rounded row sum is zero in the first row and a stable tree sum in the other rows. -/
theorem isRoundedRowSum_iff {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    {rnd : ℝ → ℝ} {u : ℝ} {i : Fin n} {s : ℝ} :
    IsRoundedRowSum T x rnd u i s ↔
      if i.val = 0 then s = 0 else
        ∃ t : SumTree {j : Fin n // j < i},
          t.leaves.Perm (Finset.univ.toList : List {j : Fin n // j < i}) ∧
          t.HasStableEvaluation rnd (fun j ↦ rnd (T i j.val * x j.val)) u ∧
          s = t.eval rnd (fun j ↦ rnd (T i j.val * x j.val)) := Iff.rfl

/-- Rounded forward substitution with error at each row operation and arbitrary addition
orders within rows. The first row performs only division. -/
def IsRoundedForwardSubstitution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (rnd : ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ i, ∃ s : ℝ, IsRoundedRowSum T x rnd u i s ∧
    (∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) ∧
    (if i.val = 0 then HasRelativeError u (b i / T i i) (x i) else
      HasRelativeError u (b i - s) (rnd (b i - s)) ∧
      HasRelativeError u (rnd (b i - s) / T i i) (x i))

/-- Each row of a rounded forward substitution has a rounded strict subdiagonal sum, rounded
products and a rounded final subtraction and division. -/
theorem isRoundedForwardSubstitution_iff {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    {b x : Fin n → ℝ} {rnd : ℝ → ℝ} {u : ℝ} :
    IsRoundedForwardSubstitution T b x rnd u ↔
      ∀ i, ∃ s : ℝ, IsRoundedRowSum T x rnd u i s ∧
        (∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) ∧
        (if i.val = 0 then HasRelativeError u (b i / T i i) (x i) else
          HasRelativeError u (b i - s) (rnd (b i - s)) ∧
          HasRelativeError u (rnd (b i - s) / T i i) (x i)) := Iff.rfl

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
    have hγ := roundingGamma_add_add_mul_le hu (j := 1) (k := 1) (by simpa only [h₂] using hk)
    refine perturb _ (by simpa only [h₂] using herr.trans hγ) ?_
    rw [hεeq, hδeq]
    field_simp [(pos hδ).ne', (pos hε).ne', ht]

/-- The strict subdiagonal dot product in a row has a componentwise backward error. -/
theorem IsRoundedRowSum.exists_sum_add_mul_eq {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → ℝ} {rnd : ℝ → ℝ} {u s : ℝ} {i : Fin n} (hs : IsRoundedRowSum T x rnd u i s)
    (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1)
    (hmul : ∀ j < i, HasRelativeError u (T i j * x j) (rnd (T i j * x j))) :
    ∃ e : {j : Fin n // j < i} → ℝ, (∀ j, |e j| ≤ roundingGamma u n * |T i j.val|) ∧
      ∑ j : {j : Fin n // j < i}, (T i j.val + e j) * x j.val = s := by
  rw [isRoundedRowSum_iff] at hs
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
  have hsmall : (i.val : ℝ) * u < 1 := natCast_mul_lt_one_of_le hu i.isLt.le hn
  obtain ⟨e, he, hsum⟩ := SumTree.exists_dotProduct_eq_sum_mul_perturbed_of_sums
    hu hsmall hlen hsum (fun j ↦ hmul _ j.prop) ht
  refine ⟨e, fun j ↦ (he j).trans (mul_le_mul_of_nonneg_right
    (roundingGamma_mono hu i.isLt.le hn) (abs_nonneg _)), ?_⟩
  rw [ht_sum, hsum]

/-- A lower-triangular row is the sum of its diagonal and strict subdiagonal terms, so
perturbations of the diagonal and of the strict subdiagonal combine to one row perturbation. -/
theorem exists_sum_add_mul_eq_of_diag_of_subdiag {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
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
theorem IsRoundedForwardSubstitution.exists_add_mulVec_eq {n : ℕ}
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
    obtain ⟨e, he, hes⟩ := hs.exists_sum_add_mul_eq hu hn hmul
    let k := if i.val = 0 then 1 else 2
    have hk : k ≤ n := by
      by_cases hi : i.val = 0
      · simpa only [k, ite_eq_left hi] using Nat.one_le_of_lt (hi ▸ i.isLt)
      · have hi' := i.isLt
        simp only [k, ite_eq_right hi]
        omega
    have hlt {l : ℕ} (hl : l ≤ n) : (l : ℝ) * u < 1 := natCast_mul_lt_one_of_le hu hl hn
    have hu₁ : u < 1 :=
      lt_one_of_natCast_mul_lt_one hu (Nat.one_le_of_lt (i.val.zero_le.trans_lt i.isLt)) hn
    obtain ⟨d, hd, hds⟩ := exists_perturbed_divisor hu hu₁ (hlt hk) (hdiag i)
        (a := b i - s) (x := x i) (by
      by_cases hi : i.val = 0
      · rw [isRoundedRowSum_iff, ite_eq_left hi] at hs
        rw [ite_eq_left hi] at hstep
        exact Or.inl ⟨ite_eq_left hi, by simpa only [hs, sub_zero] using hstep⟩
      · rw [ite_eq_right hi] at hstep
        exact Or.inr ⟨ite_eq_right hi, _, hstep⟩)
    exact exists_sum_add_mul_eq_of_diag_of_subdiag T b x hu hn htri i
      (hd.trans (mul_le_mul_of_nonneg_right (roundingGamma_mono hu hk hn) (abs_nonneg _)))
      hds e he hes
  choose r hr hrs using hrow
  refine ⟨Matrix.of r, ?_, hr⟩
  ext i
  exact hrs i

end NASC
