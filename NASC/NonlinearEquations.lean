module

public import NASC.DirectMethods
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Nonlinear equations and algorithmic differentiation

Bisection, secant and Newton convergence, tangent predictors, and derivative propagation
through finite programs. See section 8 of the gap catalogue.
-/

public section

noncomputable section

namespace NASC

open Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- One bisection step, selecting the half whose left endpoint still has negative value. -/
def bisect (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  let m := (ab.1 + ab.2) / 2
  if f m < 0 then (m, ab.2) else (ab.1, m)

/-- **Gap 8.3.** Nested bisection intervals contain a common root, with exact geometric
width and midpoint error. -/
theorem exists_bisection_root {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ z ∈ Icc a b, f z = 0 ∧ ∀ k : ℕ,
      let ab := (bisect f)^[k] (a, b)
      z ∈ Icc ab.1 ab.2 ∧ f ab.1 < 0 ∧ 0 ≤ f ab.2 ∧
        ab.2 - ab.1 = (b - a) / 2 ^ k ∧ |(ab.1 + ab.2) / 2 - z| ≤ (b - a) / 2 ^ (k + 1) := by
  sorry

/-- One secant step, holding the current point fixed after an exact zero. -/
def secantStep (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, if f x.2 = 0 then x.2 else x.2 - f x.2 * (x.2 - x.1) / (f x.2 - f x.1))

/-- **Gap 8.4.** A nonvanishing derivative and the local curvature bound imply the
golden-ratio error estimate for the secant iteration. -/
theorem secant_error_le_rpow {f : ℝ → ℝ} {z a b r M : ℝ}
    (hf : ContDiff ℝ 2 f) (hz : f z = 0)
    (ha : a ∈ Icc (z - r) (z + r)) (hb : b ∈ Icc (z - r) (z + r)) (hab : a ≠ b)
    (hM : 0 ≤ M) (hsmall : r * M < 1)
    (hne : ∀ x ∈ Icc (z - r) (z + r), deriv f x ≠ 0)
    (hbound : ∀ s ∈ Icc (z - r) (z + r), ∀ t ∈ Icc (z - r) (z + r),
      |iteratedDeriv 2 f s / (2 * deriv f t)| ≤ M) :
    let p := (1 + Real.sqrt 5) / 2
    let E := max (M * |a - z|) ((M * |b - z|) ^ (1 / p))
    let x := fun k ↦ ((secantStep f)^[k] (a, b)).1
    (∀ k : ℕ, x k ∈ Icc (z - r) (z + r) ∧ M * |x k - z| ≤ E ^ (p ^ k)) ∧
      Tendsto x atTop (nhds z) := by
  sorry

section Newton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Newton step at a point where the derivative is bijective. Theorems using it give
the bijectivity needed for the inverse function to be the linear inverse. -/
def newtonStep {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : E :=
  x - Function.invFun (fderiv ℝ f x) (f x)

/-- **Gap 8.5.** Local quadratic Newton convergence on the guaranteed ball around a
nondegenerate root, with uniform Lipschitz control of the derivative. -/
theorem newtonStep_iterate_quadratic {f : E → E} {z x₀ : E} {C L R : ℝ}
    (D : E ≃L[ℝ] E) (hD : HasFDerivAt f (D : E →L[ℝ] E) z)
    (hC : 0 < C) (hCi : ‖(D.symm : E →L[ℝ] E)‖ ≤ C)
    (hL : 0 < L) (hR : 0 < R) (hz : f z = 0)
    (hf : ∀ x ∈ Metric.ball z R, DifferentiableAt ℝ f x)
    (hLip : ∀ x ∈ Metric.ball z R, ∀ y ∈ Metric.ball z R,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖)
    (hx : x₀ ∈ Metric.ball z (min R (1 / (2 * C * L)))) :
    let x := fun k ↦ (newtonStep f)^[k] x₀
    Tendsto x atTop (nhds z) ∧ ∀ k : ℕ, x k ∈ Metric.ball z (min R (1 / (2 * C * L))) ∧
      Function.Bijective (fderiv ℝ f (x k)) ∧ ‖x (k + 1) - z‖ ≤ C * L * ‖x k - z‖ ^ 2 := by
  sorry

/-- **Gap 8.6.** The Newton--Kantorovich majorant gives a root and a quantitative
iteration bound. Continuity holds on the closed majorant ball, including in the critical case. -/
theorem exists_newtonKantorovich_root {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x₀ : E} (D : E ≃L[ℝ] F)
    (hD : HasFDerivAt f (D : E →L[ℝ] F) x₀) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsmall : a * b * c ≤ 1 / 2)
    (hinit : ‖D.symm (f x₀)‖ ≤ a) (hinv : ‖(D.symm : F →L[ℝ] E)‖ ≤ b)
    (hf : ∀ x ∈ Metric.ball x₀ (1 / (b * c)), DifferentiableAt ℝ f x)
    (hcont : ContinuousOn f
      (Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * a * b * c)) / (b * c))))
    (hLip : ∀ x ∈ Metric.ball x₀ (1 / (b * c)),
      ∀ y ∈ Metric.ball x₀ (1 / (b * c)), ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ c * ‖x - y‖) :
    let r := 1 / (b * c)
    let r₀ := (1 - Real.sqrt (1 - 2 * a * b * c)) * r
    let r₁ := (1 + Real.sqrt (1 - 2 * a * b * c)) * r
    (∀ y ∈ Metric.ball x₀ r, Function.Bijective (fderiv ℝ f y)) ∧
    ∃ z ∈ Metric.closedBall x₀ r₀, f z = 0 ∧
      (∀ k : ℕ, let x := (newtonStep f)^[k] x₀
        x ∈ Metric.ball x₀ r₀ ∧ ‖x - z‖ ≤ r / 2 ^ k * (r₀ / r) ^ (2 ^ k)) ∧
      Tendsto (fun k : ℕ ↦ (newtonStep f)^[k] x₀) atTop (nhds z) ∧
      (a * b * c = 1 / 2 → ∀ y ∈ Metric.closedBall x₀ r, f y = 0 → y = z) ∧
      (a * b * c < 1 / 2 →
        (∀ x ∈ Metric.ball x₀ r₁, DifferentiableAt ℝ f x) →
        (∀ x ∈ Metric.ball x₀ r₁, ∀ y ∈ Metric.ball x₀ r₁,
          ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ c * ‖x - y‖) →
        ∀ y ∈ Metric.ball x₀ r₁, f y = 0 → y = z) := by
  sorry

/-- **Gap 8.8.** Any damped Newton sequence with Armijo backtracking on the squared
residual has only zeros as cluster points under the compact-level-set hypotheses. -/
theorem eq_zero_of_mapClusterPt_dampedNewton {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) {z : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1) (hf : ContDiff ℝ 1 f)
    (hK : IsCompact {y | ‖f y‖ ≤ ‖f (x 0)‖})
    (hD : ∀ y, ‖f y‖ ≤ ‖f (x 0)‖ → Function.Bijective (fderiv ℝ f y))
    (hstep : ∀ k, ∃ j : ℕ,
      let d := Function.invFun (fderiv ℝ f (x k)) (f (x k))
      let y := fun i : ℕ ↦ x k - ((2 : ℝ)⁻¹ ^ i) • d
      x (k + 1) = y j ∧
        ‖f (y j)‖ ^ 2 ≤ (1 - σ * (2 : ℝ)⁻¹ ^ j) * ‖f (x k)‖ ^ 2 ∧
        ∀ i < j, (1 - σ * (2 : ℝ)⁻¹ ^ i) * ‖f (x k)‖ ^ 2 < ‖f (y i)‖ ^ 2)
    (hz : MapClusterPt z atTop x) : f z = 0 := by
  sorry

/-- **Gap 8.9.** Inexact Newton iterates close to a nondegenerate zero converge with
a uniform linear factor when their forcing terms are sufficiently small. -/
theorem exists_inexactNewton_linear_bound {f : E → E} {z : E} (hf : ContDiff ℝ 1 f)
    (hz : f z = 0) (hD : Function.Bijective (fderiv ℝ f z)) :
    ∃ δ > (0 : ℝ), ∃ η > (0 : ℝ), ∃ q ∈ Ioo (0 : ℝ) 1,
      ∀ x p : ℕ → E, x 0 ∈ Metric.ball z δ →
      (∀ k, x (k + 1) = x k + p k ∧
        ‖f (x k) + fderiv ℝ f (x k) (p k)‖ ≤ η * ‖f (x k)‖) →
      ∀ k, ‖x (k + 1) - z‖ ≤ q * ‖x k - z‖ := by
  sorry

end Newton

/-- **Gap 8.11.** The local Gauss--Newton error follows from the scaled Jacobian
variation bound and the small stationary-residual term. -/
theorem norm_gaussNewtonStep_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x z : E} (P : F →L[ℝ] E) {ω κ : ℝ}
    (hf : ContDiff ℝ 1 f) (hP : ∀ v, P (fderiv ℝ f x v) = v)
    (hres : ‖P (f z)‖ ≤ κ * ‖x - z‖)
    (hvar : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖P ((fderiv ℝ f (x + s • (z - x)) - fderiv ℝ f x) (z - x))‖ ≤
        s * ω * ‖z - x‖ ^ 2) :
    ‖x - P (f x) - z‖ ≤ (ω / 2) * ‖x - z‖ ^ 2 + κ * ‖x - z‖ := by
  sorry

/-- **Gap 8.13.** The tangent predictor has a quadratic error with the half-curvature
constant. -/
theorem norm_sub_tangentPredictor_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {r C t : ℝ} (hf : ContDiff ℝ 2 f) (ht : |t| ≤ r)
    (hC : ∀ s ∈ Icc (-r) r, ‖iteratedDeriv 2 f s‖ ≤ C) :
    ‖f t - (f 0 + t • deriv f 0)‖ ≤ C / 2 * |t| ^ 2 := by
  sorry

/-- One scalar instruction of an arithmetic program. Register indices appear as operands. -/
inductive ScalarInstruction (ι : Type*)
  | constant (x : ℝ)
  | add (left right : ι)
  | mul (left right : ι)
  | unary (f : ℝ → ℝ) (input : ι)

namespace ScalarInstruction

variable {ι : Type*}

/-- Evaluate an instruction using the current register state. -/
def eval (x : ι → ℝ) : ScalarInstruction ι → ℝ
  | .constant a => a
  | .add i j => x i + x j
  | .mul i j => x i * x j
  | .unary f i => f (x i)

/-- Propagate a tangent through one instruction. -/
def tangent (x dx : ι → ℝ) : ScalarInstruction ι → ℝ
  | .constant _ => 0
  | .add i j => dx i + dx j
  | .mul i j => dx i * x j + x i * dx j
  | .unary f i => deriv f (x i) * dx i

/-- The unary operations have differentiable primitives. -/
def DifferentiablePrimitive : ScalarInstruction ι → Prop
  | .unary f _ => Differentiable ℝ f
  | _ => True

/-- **Gap 8.14.** Forward propagation through an ordered register program computes the
Fréchet derivative applied to the input tangent. Overwriting is allowed here. -/
theorem evalProgram_fderiv_apply [Fintype ι] [DecidableEq ι]
    (program : List (ι × ScalarInstruction ι))
    (h : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx : ι → ℝ) :
    let run := fun input : ι → ℝ ↦ program.foldl
      (fun v a ↦ Function.update v a.1 (a.2.eval v)) input
    let forward := program.foldl (fun (v, dv) a ↦
      (Function.update v a.1 (a.2.eval v), Function.update dv a.1 (a.2.tangent v dv))) (x, dx)
    fderiv ℝ run x dx = forward.2 := by
  sorry

/-- **Gap 8.14.** Reverse accumulation computes the transposed derivative of a
register program. Retaining the old register state handles overwrites and repeated operands. -/
theorem evalProgram_reverse_dot_eq [Fintype ι] [DecidableEq ι]
    (program : List (ι × ScalarInstruction ι))
    (hp : ∀ a ∈ program, a.2.DifferentiablePrimitive) (x dx seed : ι → ℝ) :
    let step := fun (v : ι → ℝ) (a : ι × ScalarInstruction ι) ↦
      Function.update v a.1 (a.2.eval v)
    let run := fun input ↦ program.foldl step input
    let back := (List.range program.length).reverse.foldl
      (fun c k ↦
        match program[k]? with
        | none => c
        | some a => fun j ↦ (if j = a.1 then 0 else c j) +
          c a.1 * a.2.tangent ((program.take k).foldl step x) (Pi.single j 1)) seed
    (∑ j, back j * dx j) = ∑ j, seed j * fderiv ℝ run x dx j := by
  sorry

/-- Primal and reverse work in the unit-cost scalar arithmetic model.
One derivative evaluation of a unary primitive is one operation. -/
def reverseWork : ScalarInstruction ι → ℕ × ℕ
  | .constant _ => (0, 0)
  | .add _ _ => (1, 2)
  | .mul _ _ => (1, 4)
  | .unary _ _ => (1, 3)

/-- **Gap 8.15.** Reverse accumulation costs at most four times the primal operation
count in the unit-cost scalar model, in addition to the primal pass. -/
theorem sum_reverseWork_le (program : List (ScalarInstruction ι)) :
    (program.map fun a ↦ a.reverseWork.2).sum ≤ 4 * (program.map fun a ↦ a.reverseWork.1).sum := by
  induction program with
  | nil => simp
  | cons a rest ih =>
    cases a <;> simp_all [reverseWork, Nat.mul_add] <;> omega

end ScalarInstruction

end NASC
