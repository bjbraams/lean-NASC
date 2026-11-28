module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian random matrices

The law of a real `m × n` matrix with independent centered normal entries of common
variance, used by the randomized embedding and sparse recovery results.

## Main definitions

* `NASC.gaussianMatrixLaw m n v`: the nested product of `m n` copies of `gaussianReal 0 v`
  on `Fin m → Fin n → ℝ`.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A law on real matrices whose entries are independent centered normals with common
variance. The nested product law has the same entry order as the matrix type. -/
def gaussianMatrixLaw (m n : ℕ) (v : ℝ≥0) : Measure (Fin m → Fin n → ℝ) :=
  Measure.pi fun _ : Fin m ↦ Measure.pi fun _ : Fin n ↦ gaussianReal 0 v

/-- The defining formula for `gaussianMatrixLaw` as a nested product of centered normals. -/
theorem gaussianMatrixLaw_def (m n : ℕ) (v : ℝ≥0) :
    gaussianMatrixLaw m n v = Measure.pi fun _ : Fin m ↦ Measure.pi fun _ : Fin n ↦
      gaussianReal 0 v := by
  unfold gaussianMatrixLaw
  rfl

end NASC
