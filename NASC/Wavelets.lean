module

public import NASC.SplinesAndKernels
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Wavelets and approximation spaces

Refinement filters, Daubechies wavelets, and the Jackson--Bernstein characterization of an
approximation space. See gaps 11.15–11.18.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory
open scoped BigOperators ENNReal

/-- The dilation by two followed by a shift, before $L^2$ normalization. -/
def scaleTranslate (φ : ℝ → ℝ) (j : ℤ) : ℝ → ℝ := fun x ↦ φ (2 * x - j)

/-- **Gap 11.15.** An orthonormal compactly supported scaling function has a
finite refinement mask and the even-shift quadrature identities. -/
theorem exists_finite_refinementMask (φ : ℝ → ℝ) (hφ : HasCompactSupport φ)
    (hL : MemLp φ 2 (volume : Measure ℝ))
    (hL₀ : ∀ j : ℤ, MemLp (fun x : ℝ ↦ φ (x - j)) 2 (volume : Measure ℝ))
    (hL₁ : ∀ j : ℤ, MemLp (scaleTranslate φ j) 2 (volume : Measure ℝ))
    (horth : Orthonormal ℝ (fun j ↦ (hL₀ j).toLp (fun x : ℝ ↦ φ (x - j))))
    (hspan : hL.toLp φ ∈ (Submodule.span ℝ (range
      (fun j ↦ (hL₁ j).toLp (scaleTranslate φ j)))).topologicalClosure) :
    ∃ h : ℤ →₀ ℝ,
      (∀ᵐ x : ℝ ∂volume, φ x = ∑ j ∈ h.support, h j * scaleTranslate φ j x) ∧
      ∀ k : ℤ, ∑ j ∈ h.support, h j * h (j + 2 * k) = if k = 0 then 2 else 0 := by
  sorry

/-- **Gap 11.16.** The compactly supported Daubechies scaling mask produces a
unit-integral scaling function and a wavelet with the specified vanishing moments. -/
theorem exists_daubechies_vanishingMoments (n : ℕ) (hn : 0 < n) :
    ∃ (h : Fin (2 * n) → ℝ) (φ ψ : ℝ → ℝ),
      Integrable φ ∧ (∫ x, φ x) = 1 ∧
      Function.support φ ⊆ Icc (0 : ℝ) (2 * n - 1) ∧
      Function.support ψ ⊆ Icc (1 - (n : ℝ)) n ∧
      (∀ᵐ x : ℝ ∂volume, φ x = ∑ j, h j * φ (2 * x - j.val)) ∧
      (∀ᵐ x : ℝ ∂volume, ψ x = ∑ j : Fin (2 * n),
        (-1 : ℝ) ^ j.val * h j.rev * φ (2 * x - (j.val : ℝ) - 2 + 2 * n)) ∧
      (∀ j : ℤ, (∫ x : ℝ, φ x * φ (x - j)) = if j = 0 then 1 else 0) ∧
      ∀ k < n, Integrable (fun x : ℝ ↦ x ^ k * ψ x) ∧ (∫ x, x ^ k * ψ x) = 0 := by
  sorry

/-- **Gap 11.18.** Jackson and Bernstein inequalities characterize the approximation
space with summability exponent infinity by the real $K$-method. -/
theorem bddAbove_approximation_iff_bddAbove_KFunctional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : Submodule ℝ E) (p : Seminorm ℝ Y)
    (A : ℕ → Set E) (hA : Monotone A) (h₀ : A 0 = {0}) (c : ℕ)
    (hadd : ∀ n x y, x ∈ A n → y ∈ A n → x + y ∈ A (c * n))
    (hscale : ∀ n (a : ℝ) x, x ∈ A n → a • x ∈ A n)
    {r α C : ℝ} (hα : 0 < α) (hr : α < r) (hC : 0 < C)
    (hJ : ∀ (y : Y) n, 0 < n →
      bestApproximationError (A n) y.val ≤ C * (n : ℝ) ^ (-r) * p y)
    (hB : ∀ n, 0 < n → ∀ x ∈ A n, ∃ y : Y, y.val = x ∧ p y ≤ C * (n : ℝ) ^ r * ‖x‖)
    (x : E) :
    BddAbove {s : ℝ | ∃ n : ℕ, 0 < n ∧ s = (n : ℝ) ^ α * bestApproximationError (A n) x} ↔
      BddAbove {s : ℝ | ∃ t > (0 : ℝ),
        s = t ^ (-α / r) * sInf (range (fun y : Y ↦ ‖x - y.val‖ + t * (‖y.val‖ + p y)))} := by
  sorry

end NASC
