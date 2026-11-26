module

public import NASC.BayesianInverseProblems
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Monte Carlo and quasi-Monte Carlo

Studentized estimation, importance sampling, detailed balance, discrepancy,
component-by-component lattice selection and multilevel work estimates.
-/

public section

noncomputable section

namespace NASC

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

/-- Sample mean of the first $n$ observations. -/
def sampleMean {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, Z k ω) / n

/-- Bias-corrected sample variance, used with at least two observations. -/
def sampleVariance {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range n, (Z k ω - sampleMean Z n ω) ^ 2) / (n - 1)

/-- **Gap 23.1.** The sample variance is strongly consistent, and the studentized
normal interval has asymptotically correct coverage for positive variance. -/
theorem sampleVariance_tendsto_and_coverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hind : iIndepFun Z P)
    (hlaw : ∀ n, P.map (Z n) = P.map (Z 0)) (h₂ : Integrable (fun x ↦ Z 0 x ^ 2) P) :
    let μ := ∫ x, Z 0 x ∂P
    let v := ∫ x, (Z 0 x - μ) ^ 2 ∂P
    (∀ᵐ x ∂P, Tendsto (fun n ↦ sampleVariance Z (n + 2) x) atTop (𝓝 v)) ∧
    (0 < v → ∀ q : ℝ, 0 < q → Tendsto
      (fun n : ℕ ↦ P {x | |sampleMean Z (n + 2) x - μ| ≤
        q * Real.sqrt (sampleVariance Z (n + 2) x / ((n : ℝ) + 2))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-q) q)))) := by
  sorry

/-- **Gap 23.3.** The absolute-integrand proposal attains the least second
moment among admissible importance sampling laws, including infinite moments. -/
theorem importanceSampling_optimal_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z) (hI : Integrable Z P)
    (hpos : 0 < ∫ x, |Z x| ∂P) :
    let a := ∫ x, |Z x| ∂P
    let Q₀ := P.withDensity (fun x ↦ ENNReal.ofReal (|Z x| / a))
    let L₀ := fun x ↦ a / |Z x|
    let S := {x | Z x ≠ 0}
    Q₀ univ = 1 ∧ P.restrict S = (Q₀.withDensity (fun x ↦ ENNReal.ofReal (L₀ x))).restrict S ∧
    (∫⁻ x, ENNReal.ofReal ((Z x * L₀ x) ^ 2) ∂Q₀) = ENNReal.ofReal (a ^ 2) ∧
    ∀ (Q : Measure Ω) (_ : IsProbabilityMeasure Q) (L : Ω → ℝ),
      Measurable L → (∀ x, 0 ≤ L x) →
      P.restrict S = (Q.withDensity fun x ↦ ENNReal.ofReal (L x)).restrict S →
      ENNReal.ofReal (a ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((Z x * L x) ^ 2) ∂Q := by
  sorry

/-- Metropolis--Hastings transition weights from a proposal and unnormalized target. -/
def metropolisHastings {X : Type*} [DecidableEq X] (π : X → ℝ) (q : X → X → ℝ) (x y : X) :
    ℝ :=
  if x = y then 1 - ∑' z : X, if z = x then 0 else min (q x z) (π z * q z x / π x)
  else min (q x y) (π y * q y x / π x)

/-- **Gap 23.4.** Metropolis--Hastings gives a reversible stochastic transition
matrix and leaves the target weights invariant. -/
theorem metropolisHastings_detailedBalance {X : Type*} [Countable X] [DecidableEq X]
    (π : X → ℝ) (q : X → X → ℝ) (hπ : ∀ x, 0 < π x) (hs : Summable π)
    (hq : ∀ x y, 0 ≤ q x y) (hqs : ∀ x, Summable (q x) ∧ (∑' y, q x y) = 1) :
    let p := metropolisHastings π q
    (∀ x y, 0 ≤ p x y ∧ π x * p x y = π y * p y x) ∧
      (∀ x, (∑' y, p x y) = 1) ∧ ∀ y, (∑' x, π x * p x y) = π y := by
  sorry

/-- Star discrepancy of a finite list in the cube, using lower closed boxes. -/
def starDiscrepancy {s n : ℕ} (P : Fin n → Fin s → ℝ) : ℝ :=
  letI := Classical.propDecidable
  sSup {r : ℝ | ∃ x : Fin s → ℝ, x ∈ Icc (0 : Fin s → ℝ) 1 ∧
    r = |((Finset.univ.filter (fun i : Fin n ↦ ∀ j, P i j ≤ x j)).card : ℝ) / n -
      ∏ j, x j|}

/-- Mixed derivative along the coordinate directions indexed by a face. -/
def faceDerivative {s : ℕ} (f : (Fin s → ℝ) → ℝ) (A : Finset (Fin s))
    (x : Fin s → ℝ) : ℝ :=
  iteratedFDeriv ℝ A.card f x (fun i ↦ Pi.single (A.orderEmbOfFin rfl i) 1)

/-- **Gap 23.5.** Smooth Koksma--Hlawka with the anchored mixed derivatives,
integrated over the faces where the remaining coordinates equal one. -/
theorem quadrature_error_le_starDiscrepancy {s n : ℕ} (hn : 0 < n)
    (P : Fin n → Fin s → ℝ) (hP : ∀ i, P i ∈ Icc (0 : Fin s → ℝ) 1)
    (f : (Fin s → ℝ) → ℝ) (hf : ContDiff ℝ s f) :
    let variation := ∑ A ∈ (Finset.univ : Finset (Fin s)).powerset.erase ∅,
      ∫ u : (i : A) → ℝ in Icc 0 1,
        |faceDerivative f A (fun j ↦ if h : j ∈ A then u ⟨j, h⟩ else 1)|
    |(∑ i, f (P i)) / n - ∫ x in Icc (0 : Fin s → ℝ) 1, f x| ≤ starDiscrepancy P * variation := by
  sorry

/-- Algebraic expression for the squared shifted lattice error, restricted to the first
$r$ coordinates, using the second Bernoulli polynomial. -/
def shiftedLatticeErrorSq {s : ℕ} (n r : ℕ) (γ : Finset (Fin s) → ℝ)
    (z : Fin s → ℕ) : ℝ :=
  ∑ A ∈ ((Finset.univ : Finset (Fin s)).filter (fun i ↦ i.val < r)).powerset.erase ∅, γ A *
    ((∑ k ∈ Finset.range n, ∏ j ∈ A,
      let x := Int.fract ((k : ℝ) * z j / n)
      x ^ 2 - x + 1 / 6) / n)

/-- **Gap 23.7.** The component-by-component minimizers satisfy the fractional-moment
bound on the shift-averaged lattice error. -/
theorem shiftedLatticeErrorSq_le_of_cbc {s n : ℕ} (hn : 2 ≤ n)
    (γ : Finset (Fin (s + 1)) → ℝ) (hγ : ∀ A, 0 ≤ γ A)
    (z : Fin (s + 1) → ℕ) (hz₀ : z 0 = 1) (hz : ∀ i, z i < n ∧ Nat.Coprime (z i) n)
    (hgreedy : ∀ i ≠ 0, ∀ w : ℕ, w < n → Nat.Coprime w n →
      shiftedLatticeErrorSq n (i.val + 1) γ z ≤
        shiftedLatticeErrorSq n (i.val + 1) γ (Function.update z i w))
    {l : ℝ} (hl : l ∈ Ioc (1 / 2 : ℝ) 1) :
    let ζ := ∑' k : ℕ, ((k : ℝ) + 1) ^ (-2 * l)
    let c := 2 * ζ / (2 * Real.pi ^ 2) ^ l
    shiftedLatticeErrorSq n (s + 1) γ z ≤
      ((∑ A ∈ (Finset.univ : Finset (Fin (s + 1))).powerset.erase ∅,
        γ A ^ l * c ^ A.card) / n.totient) ^ l⁻¹ := by
  sorry

/-- **Gap 23.8.** Multilevel sample allocation under bias, variance and work
exponents, with the three standard work regimes. The variance terms are those
of independent level estimates. -/
theorem exists_multilevel_sampleBudget (bias V W : ℕ → ℝ) {a b c K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (ha' : min b c / 2 ≤ a)
    (h : ∀ k, |bias k| ≤ K * (2 : ℝ) ^ (-a * k) ∧
      0 ≤ V k ∧ V k ≤ K * (2 : ℝ) ^ (-b * k) ∧ 0 ≤ W k ∧ W k ≤ K * (2 : ℝ) ^ (c * k)) :
    ∃ C > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) (Real.exp (-1)),
      ∃ (L : ℕ) (N : Fin (L + 1) → ℕ), (∀ k, 0 < N k) ∧
        bias L ^ 2 + (∑ k, V k.val / N k) < ε ^ 2 ∧
        (∑ k, N k * W k.val) ≤
          C * (if c < b then ε⁻¹ ^ 2 else if c = b then ε⁻¹ ^ 2 * Real.log ε ^ 2
            else ε ^ (-2 - (c - b) / a)) := by
  sorry

end NASC
