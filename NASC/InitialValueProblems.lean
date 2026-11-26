module

public import NASC.Approximation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# One-step and multistep methods for initial value problems

Euler polygons, variable-step convergence, Runge--Kutta stages and rooted trees, collocation,
linear multistep order and stability. See section 14 of the gap catalogue.
-/

public section

noncomputable section

namespace NASC

open Set Filter Polynomial Asymptotics
open scoped BigOperators Matrix Topology Interval

/-- **Gap 14.1.** Euler polygons converge uniformly on the certified Picard rectangle.
An interpolant is described by its value at every point of each mesh interval. -/
theorem exists_eulerPolygon_uniform_limit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) {a b M L : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hf : ContinuousOn (fun p : ℝ × E ↦ f p.1 p.2)
      (Icc t₀ (t₀ + a) ×ˢ Metric.closedBall y₀ b))
    (hbd : ∀ t ∈ Icc t₀ (t₀ + a), ∀ y ∈ Metric.closedBall y₀ b, ‖f t y‖ ≤ M)
    (hLip : ∀ t ∈ Icc t₀ (t₀ + a), ∀ x ∈ Metric.closedBall y₀ b,
      ∀ y ∈ Metric.closedBall y₀ b, ‖f t x - f t y‖ ≤ L * ‖x - y‖) :
    let T := t₀ + min a (b / M)
    ∃ u : ℝ → E, u t₀ = y₀ ∧
      (∀ t ∈ Icc t₀ T, u t ∈ Metric.closedBall y₀ b ∧
        HasDerivWithinAt u (f t (u t)) (Icc t₀ T) t) ∧
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (n : ℕ) (t : Fin (n + 1) → ℝ)
        (y : Fin (n + 1) → E), StrictMono t → t 0 = t₀ → t (Fin.last n) = T → y 0 = y₀ →
        (∀ i : Fin n, t i.succ - t i.castSucc ≤ δ ∧
          y i.succ = y i.castSucc + (t i.succ - t i.castSucc) • f (t i.castSucc) (y i.castSucc)) →
        ∀ (i : Fin n) (s : ℝ), s ∈ Icc (t i.castSucc) (t i.succ) →
          ‖u s - (y i.castSucc + (s - t i.castSucc) • f (t i.castSucc) (y i.castSucc))‖ ≤ ε := by
  sorry

/-- **Gap 14.4.** An order-$p$ local defect and a Lipschitz increment function give the
variable-step one-step convergence bound. -/
theorem oneStep_final_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t) (u : ℝ → E) (y : Fin (n + 1) → E)
    (Φ : ℝ → E → ℝ → E) (p : ℕ) {h C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hh : 0 ≤ h)
    (h₀ : y 0 = u (t 0))
    (hstep : ∀ i : Fin n,
      let d := t i.succ - t i.castSucc
      d ≤ h ∧ y i.succ = y i.castSucc + d • Φ (t i.castSucc) (y i.castSucc) d ∧
        ‖u (t i.succ) - u (t i.castSucc) - d • Φ (t i.castSucc) (u (t i.castSucc)) d‖ ≤
          C * d ^ (p + 1))
    (hLip : ∀ t x z d, ‖Φ t x d - Φ t z d‖ ≤ L * ‖x - z‖) :
    ‖u (t (Fin.last n)) - y (Fin.last n)‖ ≤
      h ^ p * (C / L) * (Real.exp (L * (t (Fin.last n) - t 0)) - 1) := by
  sorry

/-- Coefficients of a Runge--Kutta tableau. -/
structure RungeKuttaTableau (s : ℕ) where
  /-- Stage matrix. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- Final weights. -/
  b : Fin s → ℝ
  /-- Stage abscissas. -/
  c : Fin s → ℝ

namespace RungeKuttaTableau

variable {s : ℕ} (T : RungeKuttaTableau s)

/-- The implicit Runge--Kutta stage equations at time $t$. -/
def IsStages {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → E → E) (t h : ℝ) (y : E) (Y : Fin s → E) : Prop :=
  ∀ i, Y i = y + h • ∑ j, T.A i j • f (t + T.c j * h) (Y j)

/-- The Runge--Kutta update from a specified solution of the stage equations. -/
def update {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → E → E) (t h : ℝ) (y : E) (Y : Fin s → E) : E :=
  y + h • ∑ j, T.b j • f (t + T.c j * h) (Y j)

/-- **Gap 14.5.** The stage equations have a unique solution under the
maximum absolute row sum contraction criterion. -/
theorem existsUnique_stages {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t h : ℝ) (y : E) {L q : ℝ} (hL : 0 ≤ L) (hq : 0 ≤ q) (hq' : q < 1)
    (hf : ∀ t x z, ‖f t x - f t z‖ ≤ L * ‖x - z‖)
    (hcontract : ∀ i, |h| * L * (∑ j, |T.A i j|) ≤ q) :
    ∃! Y : Fin s → E, T.IsStages f t h y Y := by
  sorry

end RungeKuttaTableau

/-- A finite rooted tree with ordered children. The coefficient identities
are invariant under permutations of the children. -/
inductive RungeKuttaTree
  | node (m : ℕ) (child : Fin m → RungeKuttaTree)

namespace RungeKuttaTree

/-- Number of vertices of a rooted tree. -/
def order : RungeKuttaTree → ℕ
  | .node _ f => 1 + ∑ i, order (f i)

/-- Tree density, the product of the subtree orders at every vertex. -/
def density : RungeKuttaTree → ℕ
  | t@(.node _ f) => t.order * ∏ i, density (f i)

/-- Product of the factorials of the numbers of children. This denominator
works when summing over ordered rooted trees. -/
def orderedWeight : RungeKuttaTree → ℕ
  | .node m f => m.factorial * ∏ i, orderedWeight (f i)

/-- The elementary Runge--Kutta stage weight of a tree. -/
def stageWeight {s : ℕ} (T : RungeKuttaTableau s) : RungeKuttaTree → Fin s → ℝ
  | .node _ f, i => ∏ k, ∑ j, T.A i j * stageWeight T (f k) j

/-- The elementary Runge--Kutta weight of a tree. -/
def weight {s : ℕ} (T : RungeKuttaTableau s) (t : RungeKuttaTree) : ℝ :=
  ∑ i, T.b i * t.stageWeight T i

/-- The elementary differential of a rooted tree for an autonomous vector field. -/
def differential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y : E) : RungeKuttaTree → E
  | .node m c => iteratedFDeriv ℝ m f y (fun i ↦ differential f y (c i))

end RungeKuttaTree

/-- Autonomous order tested on smooth finite-dimensional initial value problems.
The stage family must follow the local branch through the initial value. -/
def RungeKuttaTableau.HasAutonomousOrder {s : ℕ} (T : RungeKuttaTableau s) (p : ℕ) : Prop :=
  ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin n))
    (Y : ℝ → Fin s → EuclideanSpace ℝ (Fin n)),
    ContDiff ℝ (p + 1 : ℕ) f →
    (∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t) →
    (∀ i, Tendsto (fun h ↦ Y h i) (𝓝 0) (𝓝 (u 0))) →
    (∀ᶠ h in 𝓝 0, T.IsStages (fun _ ↦ f) 0 h (u 0) (Y h)) →
    (fun h ↦ T.update (fun _ ↦ f) 0 h (u 0) (Y h) - u h) =O[𝓝 0] (fun h ↦ h ^ (p + 1))

/-- **Gap 14.6.** The rooted-tree coefficient equations characterize the order
of a Runge--Kutta tableau. -/
theorem RungeKuttaTableau.hasAutonomousOrder_iff_treeWeight {s : ℕ}
    (T : RungeKuttaTableau s) (p : ℕ) :
    T.HasAutonomousOrder p ↔ ∀ t : RungeKuttaTree, t.order ≤ p →
      t.weight T = ((t.density : ℝ)⁻¹) := by
  sorry

/-- **Gap 14.8.** Butcher's simplifying assumptions imply the corresponding tree
order bound. -/
theorem RungeKuttaTableau.hasAutonomousOrder_of_simplifying {s : ℕ}
    (T : RungeKuttaTableau s) (p η ζ : ℕ)
    (hp : p ≤ η + ζ + 1) (hp' : p ≤ 2 * η + 2)
    (hB : ∀ q < p, (∑ i, T.b i * T.c i ^ q) = ((q + 1 : ℕ) : ℝ)⁻¹)
    (hC : ∀ q < η, ∀ i, (∑ j, T.A i j * T.c j ^ q) = T.c i ^ (q + 1) / (q + 1))
    (hD : ∀ q < ζ, ∀ j, (∑ i, T.b i * T.c i ^ q * T.A i j) =
      T.b j * (1 - T.c j ^ (q + 1)) / (q + 1)) :
    T.HasAutonomousOrder p := by
  sorry

/-- **Gap 14.9.** Orthogonality of the node polynomial gives the gain in
collocation order above the number of stages. -/
theorem RungeKuttaTableau.collocation_hasAutonomousOrder {s : ℕ} (hs : 0 < s)
    (T : RungeKuttaTableau s) (hc : Function.Injective T.c) (r : ℕ)
    (hA : ∀ i j, T.A i j = ∫ t in (0 : ℝ)..T.c i, (Lagrange.basis Finset.univ T.c j).eval t)
    (hb : ∀ j, T.b j = ∫ t in (0 : ℝ)..1, (Lagrange.basis Finset.univ T.c j).eval t)
    (hm : ∀ q < r, (∫ t in (0 : ℝ)..1, t ^ q * ∏ i, (t - T.c i)) = 0) :
    T.HasAutonomousOrder (s + r) := by
  sorry

/-- **Gap 14.16.** The Runge--Kutta update has the truncated B-series expansion,
summing over ordered rooted trees and dividing by their ordered weights. -/
theorem RungeKuttaTableau.exists_update_bSeries {s : ℕ} (T : RungeKuttaTableau s) (p : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (y : E) (Y : ℝ → Fin s → E)
    (hf : ContDiff ℝ (p + 1 : ℕ) f)
    (hY : ∀ i, Tendsto (fun h ↦ Y h i) (𝓝 0) (𝓝 y))
    (hstep : ∀ᶠ h in 𝓝 0, T.IsStages (fun _ ↦ f) 0 h y (Y h)) :
    ∃ S : Finset RungeKuttaTree, (∀ t, t ∈ S ↔ t.order ≤ p) ∧
      (fun h ↦ T.update (fun _ ↦ f) 0 h y (Y h) -
        (y + ∑ t ∈ S, (h ^ t.order * t.weight T / t.orderedWeight) • t.differential f y))
        =O[𝓝 0] (fun h ↦ h ^ (p + 1)) := by
  sorry

/-- Characteristic polynomial of a real multistep coefficient vector. -/
def multistepPolynomial {k : ℕ} (a : Fin (k + 1) → ℝ) : ℂ[X] :=
  ∑ j, monomial j.val (a j : ℂ)

/-- Classical algebraic root condition for zero stability. -/
def IsZeroStable (ρ : ℂ[X]) : Prop :=
  ρ ≠ 0 ∧ ∀ z : ℂ, ρ.eval z = 0 → ‖z‖ ≤ 1 ∧ (‖z‖ = 1 → ρ.derivative.eval z ≠ 0)

/-- Moment conditions for a linear multistep method of order at least $p$. -/
def MultistepHasOrder {k : ℕ} (a b : Fin (k + 1) → ℝ) (p : ℕ) : Prop :=
  (∑ j, a j) = 0 ∧ ∀ q < p, (∑ j, a j * (j.val : ℝ) ^ (q + 1)) =
    (q + 1) * ∑ j, b j * (j.val : ℝ) ^ q

/-- **Gap 14.10.** The multistep order conditions characterize vanishing
Taylor defect through the specified order for every smooth scalar trajectory. -/
theorem multistepHasOrder_iff_defect_isBigO {k : ℕ} (a b : Fin (k + 1) → ℝ) (p : ℕ) :
    MultistepHasOrder a b p ↔ ∀ f : ℝ → ℝ, ContDiff ℝ (p + 1 : ℕ) f →
      (fun h ↦ ∑ j, (a j * f (j.val * h) - h * b j * deriv f (j.val * h)))
        =O[𝓝 0] (fun h ↦ h ^ (p + 1)) := by
  sorry

/-- **Gap 14.11.** The root condition is equivalent to bounded propagation
for every initial history in the unforced multistep recurrence. -/
theorem isZeroStable_iff_bounded_recurrence {k : ℕ} (hk : 0 < k)
    (a : Fin (k + 1) → ℝ) (ha : a (Fin.last k) ≠ 0) :
    IsZeroStable (multistepPolynomial a) ↔
      ∃ C ≥ (0 : ℝ), ∀ u : ℕ → ℂ,
        (∀ j < k, ‖u j‖ ≤ 1) →
        (∀ n, (∑ j : Fin (k + 1), (a j : ℂ) * u (n + j.val)) = 0) →
        ∀ n, ‖u n‖ ≤ C := by
  sorry

/-- **Gap 14.12.** The first Dahlquist barrier, including the stronger bound
for explicit multistep methods. -/
theorem multistep_order_le_dahlquist {k p : ℕ} (hk : 0 < k)
    (a b : Fin (k + 1) → ℝ) (ha : a (Fin.last k) ≠ 0)
    (hstab : IsZeroStable (multistepPolynomial a)) (hp : MultistepHasOrder a b p) :
    p ≤ k + (if Even k then 2 else 1) ∧ (b (Fin.last k) / a (Fin.last k) ≤ 0 → p ≤ k) := by
  sorry

/-- Characteristic polynomial of the backward differentiation formula of degree $k$. -/
def bdfPolynomial (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.Icc 1 k, C ((j : ℂ)⁻¹) * X ^ (k - j) * (X - 1) ^ j

/-- **Gap 14.13.** Backward differentiation satisfies the root condition exactly
up to order six. -/
theorem isZeroStable_bdfPolynomial_iff {k : ℕ} (hk : 0 < k) :
    IsZeroStable (bdfPolynomial k) ↔ k ≤ 6 := by
  sorry

end NASC
