module

public import NASC.Approximation
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# Univariate approximation by deep ReLU networks

The fixed-width quantitative Lipschitz approximation theorem, using TauCeti's affine
multilayer perceptron evaluator and an identity output activation.
-/

public section

noncomputable section

namespace NASC

open Set TauCeti.Neuromanifold

/-- Scalar input and output, with $L$ hidden ReLU layers of width $W$. -/
def reluScalarSpec (W L : ℕ) : MLPSpec ℝ (L + 1) where
  width i := if i.val = 0 ∨ i.val = L + 1 then 1 else W
  activation _ x := max x 0

/-- Real-valued output of the specified scalar-input ReLU network. -/
def reluScalarEval {W L : ℕ} (θ : (reluScalarSpec W L).Parameters) (x : ℝ) : ℝ :=
  (reluScalarSpec W L).evalPrefix θ (fun _ ↦ x) (Fin.last (L + 1))
    ⟨0, by simp [reluScalarSpec]⟩

/-- **Gap 24.17.** Width eleven and depth $16n+2$ attain a uniform $6/n^2$
error on the unit ball of Lipschitz functions on the unit interval. -/
theorem exists_reluScalarEval_error_le (n : ℕ) (hn : 0 < n) (heven : Even n)
    (f : ℝ → ℝ) (h : ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ M + L ≤ 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ M) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ L * |x - y|) :
    ∃ θ : (reluScalarSpec 11 (16 * n + 2)).Parameters,
      ∀ x ∈ Icc (0 : ℝ) 1, |f x - reluScalarEval θ x| ≤ 6 / (n : ℝ) ^ 2 := by
  sorry

end NASC
