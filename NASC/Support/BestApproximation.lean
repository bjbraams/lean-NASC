module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Best approximation error

The distance from a point of a normed group to a set of approximants, as used by the
quasi-optimality estimates of Galerkin and boundary element methods, by approximation
spaces and by Kolmogorov widths.

## Main definitions

* `NASC.bestApproximationError A x`: the distance `Metric.infDist x A` from `x` to `A`.

## Main results

* `NASC.bestApproximationError_eq_infDist`, `NASC.bestApproximationError_def`: the error as
  `Metric.infDist` and as the infimum of `‖x - y‖` over `y ∈ A`.
-/

public section

noncomputable section

namespace NASC

open Set

/-- Best approximation error of `x` from a set `A` of approximants: the distance
`Metric.infDist x A`. For empty `A` it is the junk value `0`. -/
def bestApproximationError {E : Type*} [NormedAddCommGroup E] (A : Set E) (x : E) : ℝ :=
  Metric.infDist x A

/-- The best approximation error is Mathlib's distance from a point to a set. -/
theorem bestApproximationError_eq_infDist {E : Type*} [NormedAddCommGroup E] (A : Set E)
    (x : E) : bestApproximationError A x = Metric.infDist x A := by
  unfold bestApproximationError
  rfl

/-- The best approximation error is the infimum of the distances to the approximants
(both sides are `0` for empty `A`). -/
theorem bestApproximationError_def {E : Type*} [NormedAddCommGroup E] (A : Set E) (x : E) :
    bestApproximationError A x = sInf ((fun y ↦ ‖x - y‖) '' A) := by
  rw [bestApproximationError_eq_infDist, Metric.infDist_eq_iInf, image_eq_range]
  simp only [dist_eq_norm]
  rfl

end NASC
