module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Viscosity solutions and monotone schemes

Viscosity sub- and supersolutions of a second-order equation `F(x, u, Du, D²u) = 0` on a set
`K`, tested with smooth (`C^∞`) functions, and the Barles–Souganidis convergence theorem for
monotone, stable and consistent approximation schemes. See section 16 of `GAPS.md`.

## Notation

* `F x r p X`: the operator at the point `x`, value `r`, gradient `p` and Hessian `X`.
* `S h x r v`: a scheme with mesh parameter `h`, evaluated at `x` with the value `r` at `x`
  and the grid function `v` elsewhere.

## Main definitions

* `NASC.IsDegenerateElliptic F`: `F` is nonincreasing in the Hessian.
* `NASC.IsViscositySubsolution K F u`, `NASC.IsViscositySupersolution K F u`.

## Main results

* `NASC.exists_uniformLimit_of_monotoneScheme` (Barles–Souganidis): under comparison, a
  monotone, stable and consistent scheme converges uniformly on `K` to a continuous viscosity
  solution.
-/

public section

noncomputable section

namespace NASC

open Set Filter
open scoped Topology ContDiff

/-- Degenerate ellipticity of a second-order operator `F x r p X` (point, value, gradient,
Hessian): `F` is nonincreasing in the Hessian for the order `X ≤ Y ↔ ∀ v, X v v ≤ Y v v`. -/
def IsDegenerateElliptic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) : Prop :=
  ∀ x r p (X Y : E →L[ℝ] E →L[ℝ] ℝ), (∀ v, X v v ≤ Y v v) → F x r p Y ≤ F x r p X

/-- The defining property of `IsDegenerateElliptic`. -/
theorem isDegenerateElliptic_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) :
    IsDegenerateElliptic F ↔
      ∀ x r p (X Y : E →L[ℝ] E →L[ℝ] ℝ), (∀ v, X v v ≤ Y v v) → F x r p Y ≤ F x r p X :=
  Iff.rfl

/-- Viscosity subsolution of `F(x, u, Du, D²u) = 0` on `K`: `u` is upper semicontinuous on
`K`, and at every point of `K` where `u - φ` has a local maximum relative to `K`, for a smooth
test function `φ`, `F(x, u x, Dφ x, D²φ x) ≤ 0`. The operator sees `φ` only through its
first two derivatives at `x`, so the notion is local. -/
def IsViscositySubsolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) (u : E → ℝ) : Prop :=
  UpperSemicontinuousOn u K ∧
    ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → IsLocalMaxOn (fun y ↦ u y - φ y) K x →
      F x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0

/-- The defining property of `IsViscositySubsolution`. -/
theorem isViscositySubsolution_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) (u : E → ℝ) :
    IsViscositySubsolution K F u ↔ UpperSemicontinuousOn u K ∧
      ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → IsLocalMaxOn (fun y ↦ u y - φ y) K x →
        F x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0 :=
  Iff.rfl

/-- Viscosity supersolution of `F(x, u, Du, D²u) = 0` on `K`: `u` is lower semicontinuous on
`K`, and at every point of `K` where `u - φ` has a local minimum relative to `K`, for a smooth
test function `φ`, `0 ≤ F(x, u x, Dφ x, D²φ x)`. -/
def IsViscositySupersolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) (u : E → ℝ) : Prop :=
  LowerSemicontinuousOn u K ∧
    ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → IsLocalMinOn (fun y ↦ u y - φ y) K x →
      0 ≤ F x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x)

/-- The defining property of `IsViscositySupersolution`. -/
theorem isViscositySupersolution_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ) (u : E → ℝ) :
    IsViscositySupersolution K F u ↔ LowerSemicontinuousOn u K ∧
      ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → IsLocalMinOn (fun y ↦ u y - φ y) K x →
        0 ≤ F x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) :=
  Iff.rfl

/-- **Gap 16.15.** Barles–Souganidis: for a continuous, degenerate elliptic equation
`F(x, u, Du, D²u) = 0` on a compact set `K` of a finite-dimensional inner product space, with
comparison between bounded viscosity sub- and supersolutions, a monotone scheme with bounded
continuous solutions `u h` and consistency at moving points `S(h, y, φ y + ξ, φ + ξ) / h →
F(x, φ x, Dφ x, D²φ x)` converges uniformly on `K` to a continuous viscosity solution. -/
theorem exists_uniformLimit_of_monotoneScheme {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (hK : IsCompact K)
    (F : E → ℝ → (E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ) → ℝ)
    (hFc : ContinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      F q.1 q.2.1 q.2.2.1 q.2.2.2) (K ×ˢ univ))
    (hFe : IsDegenerateElliptic F)
    (S : ℝ → E → ℝ → (E → ℝ) → ℝ) (u : ℝ → E → ℝ)
    (hcomp : ∀ v w : E → ℝ, (∃ C, ∀ x ∈ K, |v x| ≤ C ∧ |w x| ≤ C) →
      IsViscositySubsolution K F v → IsViscositySupersolution K F w → ∀ x ∈ K, v x ≤ w x)
    (hmono : ∀ h > (0 : ℝ), ∀ x ∈ K, ∀ r v w, (∀ y ∈ K, v y ≤ w y) →
      S h x r w ≤ S h x r v)
    (hsolve : ∃ C, ∀ᶠ h in 𝓝[>] (0 : ℝ), ContinuousOn (u h) K ∧
      ∀ x ∈ K, |u h x| ≤ C ∧ S h x (u h x) (u h) = 0)
    (hcons : ∀ x ∈ K, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ →
      Tendsto (fun p : ℝ × E × ℝ ↦
        S p.1 p.2.1 (φ p.2.1 + p.2.2) (fun y ↦ φ y + p.2.2) / p.1)
        ((𝓝[>] (0 : ℝ)) ×ˢ ((𝓝[K] x) ×ˢ (𝓝 0)))
        (𝓝 (F x (φ x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x)))) :
    ∃ v : E → ℝ, ContinuousOn v K ∧ IsViscositySubsolution K F v ∧
      IsViscositySupersolution K F v ∧ TendstoUniformlyOn u v (𝓝[>] (0 : ℝ)) K := by
  sorry

end NASC
