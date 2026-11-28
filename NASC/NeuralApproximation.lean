module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

import Mathlib.Algebra.Order.SuccPred

/-!
# Univariate approximation by deep ReLU networks

The fixed-width quantitative Lipschitz approximation theorem, using TauCeti's affine
multilayer perceptron evaluator and an identity output activation.

## Main definitions

* `NASC.reluScalarSpec`: scalar input and output, `L` hidden ReLU layers of width `W`.
* `NASC.reluScalarEval`: the real-valued output of such a network.

## Main results

* `NASC.exists_reluScalarEval_error_le`: width `11` and depth `16 n + 2` approximate the unit
  ball of `Lip 1` on `[0, 1]` uniformly to within `6 / n²` (DeVore–Hanin–Petrova).
-/

public section

noncomputable section

namespace NASC

open Set TauCeti.Neuromanifold

/-- Scalar input and output, with $L$ hidden ReLU layers of width $W$. -/
def reluScalarSpec (W L : ℕ) : MLPSpec ℝ (L + 1) where
  width i := if i.val = 0 ∨ i.val = L + 1 then 1 else W
  activation _ x := max x 0

/-- The layer widths of `reluScalarSpec`: one at the input and output layers, `W` between. -/
theorem reluScalarSpec_width (W L : ℕ) (i : Fin (L + 2)) :
    (reluScalarSpec W L).width i = if i.val = 0 ∨ i.val = L + 1 then 1 else W := by
  rfl

/-- Every layer of `reluScalarSpec` uses the ReLU activation `x ↦ max x 0`. -/
theorem reluScalarSpec_activation (W L : ℕ) (i) (x : ℝ) :
    (reluScalarSpec W L).activation i x = max x 0 := by
  rfl

/-- Real-valued output of the specified scalar-input ReLU network. -/
def reluScalarEval {W L : ℕ} (θ : (reluScalarSpec W L).Parameters) (x : ℝ) : ℝ :=
  (reluScalarSpec W L).evalPrefix θ (fun _ ↦ x) (Fin.last (L + 1))
    ⟨0, by simp [reluScalarSpec]⟩

/-- The defining formula of `reluScalarEval`. -/
theorem reluScalarEval_def {W L : ℕ} (θ : (reluScalarSpec W L).Parameters) (x : ℝ) :
    reluScalarEval θ x = (reluScalarSpec W L).evalPrefix θ (fun _ ↦ x) (Fin.last (L + 1))
      ⟨0, by simp [reluScalarSpec]⟩ := by
  rfl

/-- **Gap 24.17.** Width eleven and depth $16n+2$ give worst-case uniform error at most
$6/n^2$ on the unit ball of Lipschitz functions on the unit interval: every such `f` is
approximated to within `6 / n ^ 2 + ε` for every `ε > 0` (the `sup inf` form of the source,
which does not assert that the infimum is attained). -/
theorem exists_reluScalarEval_error_le (n : ℕ) (hn : 0 < n) (heven : Even n)
    (f : ℝ → ℝ) (h : ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ M + L ≤ 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ M) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ L * |x - y|) :
    ∀ ε > (0 : ℝ), ∃ θ : (reluScalarSpec 11 (16 * n + 2)).Parameters,
      ∀ x ∈ Icc (0 : ℝ) 1, |f x - reluScalarEval θ x| ≤ 6 / (n : ℝ) ^ 2 + ε := by
  sorry

end NASC
