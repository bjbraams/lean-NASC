module

public import NASC.FiniteDifferences
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Conservation laws and finite volume methods

Weak and entropy formulations, scalar Riemann solvers, consistency and monotonicity of
finite volume schemes, and small-variation solutions of hyperbolic systems.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Interval

/-- A smooth compactly supported test for the weak conservation law. -/
def IsConservationTest (φ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ

/-- Weak conservation law with the initial term at time zero. Test functions act
on time and space, in that order. -/
def IsWeakConservationLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (u₀ : ℝ → E) (u : ℝ → ℝ → E) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, IsConservationTest φ →
    (∫ t in Ioi (0 : ℝ), ∫ x : ℝ,
      fderiv ℝ φ (t, x) (1, 0) • u t x + fderiv ℝ φ (t, x) (0, 1) • f (u t x)) +
    (∫ x : ℝ, φ (0, x) • u₀ x) = 0

/-- **Gap 17.1.** A single moving jump is weakly conservative exactly when
its speed satisfies the Rankine--Hugoniot identity. -/
theorem isWeakConservationLaw_singleJump_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (l r : E) (s : ℝ) :
    IsWeakConservationLaw f (fun x ↦ if x < 0 then l else r)
      (fun t x ↦ if x < s * t then l else r) ↔
      f r - f l = s • (r - l) := by
  sorry

/-- The scalar Kružkov entropy formulation, with a representative continuous in
time in local $L^1$. -/
def IsScalarEntropySolution (f u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Measurable (fun p : ℝ × ℝ ↦ u p.1 p.2) ∧
  (∃ C, ∀ t ≥ 0, ∀ x, |u t x| ≤ C) ∧
  (∀ᵐ x : ℝ ∂volume, u 0 x = u₀ x) ∧
  (∀ s ≥ 0, ∀ R > (0 : ℝ),
    ContinuousOn (fun t ↦ ∫ x in (-R)..R, |u t x - u s x|) (Ici 0)) ∧
  IsWeakConservationLaw f u₀ u ∧
  ∀ c (φ : ℝ × ℝ → ℝ), IsConservationTest φ → (∀ z, 0 ≤ φ z) →
    0 ≤ (∫ t in Ioi (0 : ℝ), ∫ x : ℝ,
      |u t x - c| * fderiv ℝ φ (t, x) (1, 0) +
      ((if c ≤ u t x then 1 else -1) * (f (u t x) - f c)) * fderiv ℝ φ (t, x) (0, 1)) +
      ∫ x : ℝ, |u₀ x - c| * φ (0, x)

/-- **Gap 17.3.** Kružkov's existence and $L^1$ contraction for bounded scalar
initial data, with extended-valued norms if the initial difference is nonintegrable. -/
theorem exists_scalarEntropySolution_and_contraction (f u₀ : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hu₀ : Measurable u₀) (hbound : ∃ C, ∀ x, |u₀ x| ≤ C) :
    ∃ u, IsScalarEntropySolution f u₀ u ∧
      ∀ v₀ v, Measurable v₀ → IsScalarEntropySolution f v₀ v → ∀ t ≥ 0,
        (∫⁻ x : ℝ, ENNReal.ofReal |u t x - v t x|) ≤
          ∫⁻ x : ℝ, ENNReal.ofReal |u₀ x - v₀ x| := by
  sorry

/-- **Gap 17.4.** The rarefaction fan for a strictly convex flux uses the
inverse derivative between the two characteristic edge speeds. -/
theorem isScalarEntropySolution_rarefaction {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hcv : StrictMono (deriv f)) {l r : ℝ} (hlr : l < r) :
    let init := fun x : ℝ ↦ if x < 0 then l else r
    let fan := fun t x : ℝ ↦
      if t ≤ 0 then init x else if x / t ≤ deriv f l then l
      else if deriv f r ≤ x / t then r else Function.invFun (deriv f) (x / t)
    IsScalarEntropySolution f init fan := by
  sorry

/-- **Gap 17.4.** Decreasing Riemann data for a convex flux give the
entropy shock at the Rankine--Hugoniot speed. -/
theorem isScalarEntropySolution_riemann_shock {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hcv : ConvexOn ℝ univ f) {l r : ℝ} (hlr : r < l) :
    let s := (f l - f r) / (l - r)
    IsScalarEntropySolution f (fun x ↦ if x < 0 then l else r)
      (fun t x ↦ if x < s * t then l else r) := by
  sorry

/-- The conservative three-point update associated with a two-point flux. -/
def conservativeUpdate (g : ℝ → ℝ → ℝ) (ν : ℝ) (a b c : ℝ) : ℝ :=
  b - ν * (g b c - g a b)

/-- Piecewise constant reconstruction from a uniform space-time grid. -/
def finiteVolumeReconstruction (dt dx : ℝ) (V : ℕ → ℤ → ℝ) (t x : ℝ) : ℝ :=
  V (Nat.floor (t / dt)) (Int.floor (x / dx))

/-- **Gap 17.5.** A bounded local $L^1$ limit of consistent conservative
finite volume approximations satisfies the weak conservation law. -/
theorem isWeakConservationLaw_of_finiteVolume_limit
    (f : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (V : ℕ → ℕ → ℤ → ℝ) (dt dx : ℕ → ℝ)
    (hg : Continuous (Function.uncurry g)) (hcons : ∀ a, g a a = f a)
    (hdt : ∀ k, 0 < dt k) (hdx : ∀ k, 0 < dx k)
    (hlt : Tendsto dt atTop (𝓝 0)) (hlx : Tendsto dx atTop (𝓝 0))
    (hstep : ∀ k n j, V k (n + 1) j =
      conservativeUpdate g (dt k / dx k) (V k n (j - 1)) (V k n j) (V k n (j + 1)))
    (hbd : ∃ C, (∀ k n j, |V k n j| ≤ C) ∧ (∀ t ≥ 0, ∀ x, |u t x| ≤ C) ∧ ∀ x, |u₀ x| ≤ C)
    (hu : Measurable (Function.uncurry u)) (hu₀ : Measurable u₀)
    (h₀ : ∀ R > (0 : ℝ), Tendsto (fun k ↦ ∫ x in (-R)..R,
      |finiteVolumeReconstruction (dt k) (dx k) (V k) 0 x - u₀ x|) atTop (𝓝 0))
    (hlim : ∀ R T : ℝ, 0 < R → 0 < T → Tendsto
      (fun k ↦ ∫ t in (0 : ℝ)..T, ∫ x in (-R)..R,
        |finiteVolumeReconstruction (dt k) (dx k) (V k) t x - u t x|) atTop (𝓝 0)) :
    IsWeakConservationLaw f u₀ u := by
  sorry

/-- **Gap 17.7.** A monotone three-point conservative update satisfies the cell
entropy inequality for the numerical Kružkov flux. -/
theorem monotoneUpdate_entropy_inequality (g : ℝ → ℝ → ℝ) (ν : ℝ)
    (hmono : ∀ a b c a' b' c' : ℝ, a ≤ a' → b ≤ b' → c ≤ c' →
      conservativeUpdate g ν a b c ≤ conservativeUpdate g ν a' b' c')
    (a b c k : ℝ) :
    let G := fun x y ↦ g (max x k) (max y k) - g (min x k) (min y k)
    |conservativeUpdate g ν a b c - k| ≤ |b - k| - ν * (G b c - G a b) := by
  sorry

/-- **Gap 17.8.** A positive linear stencil satisfying second-order moment
matching can only realize an integral-grid shift. -/
theorem exists_int_eq_of_positive_stencil_secondMoment
    (I : Finset ℤ) (c : ℤ → ℝ) (ν : ℝ) (hpos : ∀ j ∈ I, 0 ≤ c j)
    (hone : ∑ j ∈ I, c j = 1) (hfirst : ∑ j ∈ I, (j : ℝ) * c j = ν)
    (hsecond : ∑ j ∈ I, (j : ℝ) ^ 2 * c j = ν ^ 2) :
    ∃ j ∈ I, (j : ℝ) = ν ∧ c j = 1 ∧ ∀ k ∈ I, k ≠ j → c k = 0 := by
  sorry

/-- **Gap 17.10.** For smooth positive transport speed, the monotone upwind
scheme has a square-root $L^1$ error bound on bounded-variation initial data.
The step ratio is fixed and the initial values are cell averages. -/
theorem upwind_L1_error_le_sqrt_mesh (u₀ : ℝ → ℝ) (hu₀ : Integrable u₀)
    (hvar : eVariationOn u₀ univ < ⊤) {ν : ℝ} (hν : ν ∈ Ioc (0 : ℝ) 1) :
    ∃ C ≥ (0 : ℝ), ∀ (dx : ℝ), 0 < dx → ∀ (V : ℕ → ℤ → ℝ),
      (∀ j : ℤ, V 0 j = (∫ x in (j : ℝ) * dx..((j : ℝ) + 1) * dx, u₀ x) / dx) →
      (∀ n j, V (n + 1) j = (1 - ν) * V n j + ν * V n (j - 1)) →
      ∀ n : ℕ,
      (∫⁻ x : ℝ, ENNReal.ofReal |V n (Int.floor (x / dx)) - u₀ (x - (n : ℝ) * ν * dx)|) ≤
        ENNReal.ofReal (C * (dx + Real.sqrt ((n : ℝ) * ν) * dx) *
          (eVariationOn u₀ univ).toReal) := by
  sorry

/-- **Gap 17.11.** Tadmor's entropy potential condition gives a cell entropy
inequality with the consistent averaged numerical entropy flux. -/
theorem tadmor_cell_entropy_le (w ψ : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (h : ∀ a b, (w b - w a) * g a b ≤ ψ b - ψ a) (a b c : ℝ) :
    let q := fun x y ↦ ((w x + w y) * g x y - ψ x - ψ y) / 2
    w b * (g a b - g b c) + (q b c - q a b) ≤ 0 := by
  sorry

/-- Characteristic data for a strictly hyperbolic flux on an open state domain.
Each family is genuinely nonlinear everywhere or linearly degenerate everywhere. -/
def IsHyperbolicOn {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ)
    (U : Set (Fin n → ℝ)) (speed : Fin n → (Fin n → ℝ) → ℝ)
    (field : Fin n → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  (∀ z ∈ U, StrictMono (fun i ↦ speed i z) ∧
    (∀ i, field i z ≠ 0 ∧ fderiv ℝ f z (field i z) = speed i z • field i z)) ∧
  ∀ i, ContDiffOn ℝ 1 (speed i) U ∧ ContinuousOn (field i) U ∧
    ((∀ z ∈ U, fderiv ℝ (speed i) z (field i z) ≠ 0) ∨
      (∀ z ∈ U, fderiv ℝ (speed i) z (field i z) = 0))

/-- **Gap 17.14.** Nearby Riemann data for a strictly hyperbolic system admit a
self-similar weak solution with a bounded, small-variation profile. -/
theorem exists_selfSimilar_riemann_solution {n : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ) (hf : ContDiff ℝ 2 f)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (l : Fin n → ℝ) (hl : l ∈ U)
    (speed : Fin n → (Fin n → ℝ) → ℝ) (field : Fin n → (Fin n → ℝ) → (Fin n → ℝ))
    (h : IsHyperbolicOn f U speed field) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r ∈ Metric.ball l δ,
      ∃ W : ℝ → Fin n → ℝ, Measurable W ∧
        (∀ ξ, W ξ ∈ U) ∧ (∀ ξ < -C, W ξ = l) ∧ (∀ ξ > C, W ξ = r) ∧
        eVariationOn W univ ≤ ENNReal.ofReal (C * ‖r - l‖) ∧
        IsWeakConservationLaw f (fun x ↦ if x < 0 then l else r) (fun t x ↦ W (x / t)) := by
  sorry

/-- **Gap 17.15.** Small-variation data for a strictly hyperbolic flux lie in an
invariant domain of weak solutions with a uniform $L^1$ Lipschitz semigroup bound. -/
theorem exists_smallVariation_conservation_semigroup {n : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ) (hf : ContDiff ℝ 2 f)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (a : Fin n → ℝ) (ha : a ∈ U)
    (speed : Fin n → (Fin n → ℝ) → ℝ) (field : Fin n → (Fin n → ℝ) → (Fin n → ℝ))
    (h : IsHyperbolicOn f U speed field) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∃ (D : Set (ℝ → Fin n → ℝ)) (S : ℝ → (ℝ → Fin n → ℝ) → ℝ → Fin n → ℝ),
      (∀ v : ℝ → Fin n → ℝ, Measurable v → Integrable (fun x ↦ v x - a) →
        eVariationOn v univ < ENNReal.ofReal δ → (∀ x, ‖v x - a‖ < δ) → v ∈ D) ∧
      (∀ v ∈ D, IsWeakConservationLaw f v (fun t x ↦ S t v x)) ∧
      (∀ v ∈ D, S 0 v =ᵐ[volume] v) ∧
      (∀ v ∈ D, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        S t v ∈ D ∧ S (s + t) v =ᵐ[volume] S s (S t v)) ∧
      ∀ v ∈ D, ∀ w ∈ D, ∀ t ≥ 0,
        (∫⁻ x : ℝ, ENNReal.ofReal ‖S t v x - S t w x‖) ≤
          ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal ‖v x - w x‖ := by
  sorry

end NASC
