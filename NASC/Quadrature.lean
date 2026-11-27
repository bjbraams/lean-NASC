module

public import NASC.Approximation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.NumberTheory.Bernoulli

/-!
# Orthogonal polynomials and quadrature

Moment orthogonality, Gaussian quadrature and its spectral construction, derivative error
formulas, and the analytic trapezoidal rule. See section 12 of the gap catalogue.
The Gauss-rule proof uses Mathlib's nodal polynomial, Lagrange basis, and integral positivity.
-/

public section

noncomputable section

namespace NASC

open Set MeasureTheory Polynomial
open scoped BigOperators Matrix Interval

/-- A moment measure has all polynomial moments and has no finite set of full measure. -/
def HasInfiniteMomentSupport (μ : Measure ℝ) : Prop :=
  (∀ k : ℕ, Integrable (fun x : ℝ ↦ x ^ k) μ) ∧
    ∀ s : Finset ℝ, ¬(∀ᵐ x ∂μ, x ∈ s)

/-- A moment measure integrates every real polynomial. -/
theorem HasInfiniteMomentSupport.integrable_eval {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) (p : ℝ[X]) :
    Integrable (fun x ↦ p.eval x) μ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      exact (hp.add hq).congr (.of_forall fun x ↦ by simp only [Pi.add_apply, eval_add])
  | monomial n c => simpa only [eval_monomial] using (hμ.1 n).const_mul c

/-- The real bilinear pairing of two polynomials under a moment measure. -/
def polynomialMomentPair (μ : Measure ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ x, p.eval x * q.eval x ∂μ

/-- The polynomial moment pairing is the integral of the product. -/
theorem polynomialMomentPair_def (μ : Measure ℝ) (p q : ℝ[X]) :
    polynomialMomentPair μ p q = ∫ x, p.eval x * q.eval x ∂μ := by
  unfold polynomialMomentPair
  rfl

/-- Products of two polynomial evaluations are integrable under a moment measure. -/
theorem HasInfiniteMomentSupport.integrable_eval_mul {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) (p q : ℝ[X]) :
    Integrable (fun x ↦ p.eval x * q.eval x) μ := by
  simpa only [eval_mul] using hμ.integrable_eval (p * q)

/-- The polynomial moment pairing is symmetric. -/
theorem polynomialMomentPair_comm (μ : Measure ℝ) (p q : ℝ[X]) :
    polynomialMomentPair μ p q = polynomialMomentPair μ q p := by
  simp only [polynomialMomentPair_def, mul_comm (p.eval _) (q.eval _)]

/-- The moment pairing respects subtraction in its first argument. -/
theorem HasInfiniteMomentSupport.polynomialMomentPair_sub_left {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) (p q r : ℝ[X]) :
    polynomialMomentPair μ (p - q) r =
      polynomialMomentPair μ p r - polynomialMomentPair μ q r := by
  simp only [polynomialMomentPair_def, eval_sub, sub_mul]
  exact integral_sub (hμ.integrable_eval_mul p r) (hμ.integrable_eval_mul q r)

/-- Multiplication by a constant scales the moment pairing. -/
theorem polynomialMomentPair_C_mul_left (μ : Measure ℝ) (c : ℝ) (p q : ℝ[X]) :
    polynomialMomentPair μ (C c * p) q = c * polynomialMomentPair μ p q := by
  simp only [polynomialMomentPair_def, eval_mul, eval_C, mul_assoc, integral_const_mul]

/-- The square of a nonzero polynomial has positive integral under a moment
measure with no finite set of full measure. -/
theorem HasInfiniteMomentSupport.polynomialMomentPair_self_pos {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {p : ℝ[X]} (hp : p ≠ 0) :
    0 < polynomialMomentPair μ p p := by
  classical
  rw [polynomialMomentPair_def]
  have hnonneg : 0 ≤ fun x ↦ p.eval x * p.eval x := fun x ↦ mul_self_nonneg _
  have hint := hμ.integrable_eval_mul p p
  by_contra! h
  have hz := (integral_eq_zero_iff_of_nonneg hnonneg hint).mp
    (le_antisymm h (integral_nonneg hnonneg))
  apply hμ.2 p.roots.toFinset
  filter_upwards [hz] with x hx
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact mul_self_eq_zero.mp hx

/-- Monic polynomials of successive degrees orthogonal for the given moment measure. -/
def AreMonicOrthogonal (μ : Measure ℝ) (p : ℕ → ℝ[X]) : Prop :=
  (∀ n, (p n).Monic ∧ (p n).natDegree = n) ∧
    ∀ i j, i ≠ j → (∫ x, (p i).eval x * (p j).eval x ∂μ) = 0

/-- A monic sequence spanning all lower degrees tests orthogonality against
any polynomial of degree strictly below the cutoff. -/
theorem polynomialMomentPair_eq_zero_of_degree_lt {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {n : ℕ} (p : ℕ → ℝ[X]) (u q : ℝ[X])
    (hp : ∀ i < n, (p i).Monic ∧ (p i).natDegree = i)
    (horth : ∀ i < n, polynomialMomentPair μ (p i) u = 0) (hq : q.degree < n) :
    polynomialMomentPair μ q u = 0 := by
  induction n generalizing q with
  | zero =>
      have hzero : q = 0 := AddMonoidAlgebra.ext <| Finsupp.ext fun i ↦
        ((degree_lt_iff_coeff_zero q 0).mp hq i (Nat.zero_le i)).trans (coeff_zero _).symm
      simp only [hzero, polynomialMomentPair_def, eval_zero, zero_mul, integral_zero]
  | succ n ih =>
      let r := q - C (q.coeff n) * p n
      have hpn := hp n (Nat.lt_succ_self n)
      have hpnC : (p n).coeff n = 1 :=
        (congrArg (p n).coeff hpn.2.symm).trans hpn.1.coeff_natDegree
      have hr : r.degree < n := (degree_lt_iff_coeff_zero _ _).mpr fun k hk ↦ by
        rcases hk.eq_or_lt with rfl | hk
        · simp only [r, coeff_sub, coeff_C_mul, hpnC, mul_one, sub_self]
        · dsimp only [r]
          rw [coeff_sub, coeff_C_mul,
            (degree_lt_iff_coeff_zero _ _).mp hq k (by omega),
            coeff_eq_zero_of_natDegree_lt (hpn.2.trans_lt hk), mul_zero, sub_zero]
      have hzero := ih r (fun i hi ↦ hp i (Nat.lt_succ_of_lt hi))
        (fun i hi ↦ horth i (Nat.lt_succ_of_lt hi)) hr
      simpa only [r, hμ.polynomialMomentPair_sub_left, polynomialMomentPair_C_mul_left,
        horth n (Nat.lt_succ_self n), mul_zero, sub_zero] using hzero

/-- Monicity and orthogonality against all lower degrees determine a polynomial
uniquely. -/
theorem eq_of_monic_polynomialMomentPair_eq_zero {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {n : ℕ} {p q : ℝ[X]}
    (hp : p.Monic) (hq : q.Monic) (hpD : p.natDegree = n) (hqD : q.natDegree = n)
    (hpO : ∀ r : ℝ[X], r.degree < n → polynomialMomentPair μ r p = 0)
    (hqO : ∀ r : ℝ[X], r.degree < n → polynomialMomentPair μ r q = 0) : p = q := by
  have hpd : p.degree = n := by rwa [degree_eq_natDegree hp.ne_zero, Nat.cast_inj]
  have hqd : q.degree = n := by rwa [degree_eq_natDegree hq.ne_zero, Nat.cast_inj]
  have hr : (p - q).degree < n := hpd ▸
    degree_sub_lt_left (hpd.trans hqd.symm) hp.ne_zero (hp.trans hq.symm)
  have hzero : polynomialMomentPair μ (p - q) (p - q) = 0 := by
    rw [hμ.polynomialMomentPair_sub_left,
      polynomialMomentPair_comm μ p (p - q), polynomialMomentPair_comm μ q (p - q),
      hpO _ hr, hqO _ hr, sub_self]
  by_contra h
  exact (hμ.polynomialMomentPair_self_pos (sub_ne_zero.mpr h)).ne' hzero

/-- **Gap 12.1.** The sequence of monic orthogonal polynomials exists and is unique. -/
theorem existsUnique_monicOrthogonal (μ : Measure ℝ) (hμ : HasInfiniteMomentSupport μ) :
    ∃! p : ℕ → ℝ[X], AreMonicOrthogonal μ p := by
  sorry

/-- **Gap 12.2.** Multiplication by the coordinate yields the monic three-term
recurrence with strictly positive lower recurrence coefficients. -/
theorem exists_monicOrthogonal_threeTerm (μ : Measure ℝ) (hμ : HasInfiniteMomentSupport μ)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < b (n + 1)) ∧ p 0 = 1 ∧
      p 1 = X - C (a 0) ∧
      ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n := by
  sorry

/-- **Gap 12.2.** Favard's theorem realizes positive recurrence coefficients
by orthogonality for a probability measure with infinite moment support. -/
theorem exists_measure_monicOrthogonal_of_threeTerm (a b : ℕ → ℝ) (p : ℕ → ℝ[X])
    (hb : ∀ n, 0 < b (n + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hrec : ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ HasInfiniteMomentSupport μ ∧
      AreMonicOrthogonal μ p := by
  sorry

/-- **Gap 12.3.** The real roots of successive monic orthogonal polynomials are
simple, lie in the interior of a supporting interval, and strictly interlace. -/
theorem exists_monicOrthogonal_interlacing_roots (μ : Measure ℝ)
    (hμ : HasInfiniteMomentSupport μ) (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p)
    {a b : ℝ} (hI : ∀ᵐ x ∂μ, x ∈ Icc a b) (n : ℕ) :
    ∃ (x : Fin n → ℝ) (y : Fin (n + 1) → ℝ),
      (p n).roots = Multiset.ofList (List.ofFn x) ∧
      (p (n + 1)).roots = Multiset.ofList (List.ofFn y) ∧
      (∀ i, y i ∈ Ioo a b) ∧ (∀ i, y i.castSucc < x i ∧ x i < y i.succ) := by
  sorry

/-- The symmetric Jacobi matrix associated with the monic three-term recurrence. -/
def jacobiMatrix (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then a i.val else if i.val + 1 = j.val then Real.sqrt (b j.val)
    else if j.val + 1 = i.val then Real.sqrt (b i.val) else 0

/-- **Gap 12.4.** Determinants of successive Jacobi sections satisfy the given
three-term recurrence. -/
theorem charpoly_jacobiMatrix_eq (a b : ℕ → ℝ) (p : ℕ → ℝ[X])
    (hb : ∀ i, 0 ≤ b (i + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hp : ∀ n, p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n)
    (n : ℕ) : (jacobiMatrix a b n).charpoly = p n := by
  sorry

/-- Exactness through degree $2n-1$ for an $n$-node formula. -/
def IsGaussRule {n : ℕ} (μ : Measure ℝ) (x w : Fin n → ℝ) : Prop :=
  Function.Injective x ∧
    ∀ p : ℝ[X], p.natDegree < 2 * n → (∫ y, p.eval y ∂μ) = ∑ i, w i * p.eval (x i)

/-- **Gap 12.6.** An exact Gauss rule has positive Christoffel weights and its
nodes are precisely the roots of the monic orthogonal polynomial. -/
theorem IsGaussRule.roots_and_weights {n : ℕ} {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {x w : Fin n → ℝ} (h : IsGaussRule μ x w)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) :
    (p n).roots = Multiset.ofList (List.ofFn x) ∧ ∀ i,
      0 < w i ∧ w i = ∫ z, (Lagrange.basis Finset.univ x i).eval z ^ 2 ∂μ := by
  classical
  let q := Lagrange.nodal Finset.univ x
  have hqD : q.natDegree = n := by rw [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hqM : q.Monic := Lagrange.nodal_monic
  have hq0 (i : Fin n) : q.eval (x i) = 0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hqO (j : ℕ) (hj : j < n) : polynomialMomentPair μ (p j) q = 0 := by
    have hdeg : (p j * q).natDegree < 2 * n := natDegree_mul_le.trans_lt (by
      rw [(hp.1 j).2, hqD]
      omega)
    have he := h.2 (p j * q) hdeg
    simpa only [polynomialMomentPair_def, eval_mul, hq0, mul_zero, Finset.sum_const_zero] using he
  have hpO (j : ℕ) (hj : j < n) : polynomialMomentPair μ (p j) (p n) = 0 :=
    hp.2 j n hj.ne
  have hpq : p n = q :=
    eq_of_monic_polynomialMomentPair_eq_zero hμ (hp.1 n).1 hqM (hp.1 n).2 hqD
      (fun r hr ↦ polynomialMomentPair_eq_zero_of_degree_lt hμ p (p n) r
        (fun j _ ↦ hp.1 j) hpO hr)
      (fun r hr ↦ polynomialMomentPair_eq_zero_of_degree_lt hμ p q r
        (fun j _ ↦ hp.1 j) hqO hr)
  constructor
  · rw [hpq]
    dsimp only [q]
    rw [Lagrange.nodal_eq, roots_prod _ _ hqM.ne_zero]
    simp only [roots_X_sub_C, Multiset.bind_singleton, Finset.val_univ_fin, List.ofFn_eq_map,
      Multiset.map_coe]
  · intro i
    let B := Lagrange.basis Finset.univ x i
    have hBi : B.eval (x i) = 1 := Lagrange.eval_basis_self h.1.injOn (Finset.mem_univ i)
    have hBne : B ≠ 0 := Lagrange.basis_ne_zero h.1.injOn (Finset.mem_univ i)
    have hBD : B.natDegree = n - 1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Lagrange.natDegree_basis (s := Finset.univ) h.1.injOn (Finset.mem_univ i)
    have hBdeg : (B ^ 2).natDegree < 2 * n := natDegree_pow_le.trans_lt (by
      rw [hBD]
      have hi := i.isLt
      omega)
    have hW : (∫ z, B.eval z ^ 2 ∂μ) = w i := by
      simp only [← eval_pow]
      rw [h.2 _ hBdeg, Finset.sum_eq_single i]
      · rw [eval_pow, hBi, one_pow, mul_one]
      · intro j _ hj
        have hzero : B.eval (x j) = 0 := Lagrange.eval_basis_of_ne hj.symm (Finset.mem_univ j)
        rw [eval_pow, hzero, zero_pow (by decide), mul_zero]
      · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
    exact ⟨hW ▸ (by simpa only [polynomialMomentPair_def, pow_two] using
      hμ.polynomialMomentPair_self_pos hBne), hW.symm⟩

/-- **Gap 12.7.** Golub--Welsch constructs an exact Gauss rule using the first
row of an orthogonal diagonalization of the Jacobi matrix. -/
theorem isGaussRule_of_jacobiDiagonalization {n : ℕ} {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p)
    (a b : ℕ → ℝ) (hb : ∀ j, 0 < b (j + 1)) (h₀ : p 0 = 1) (h₁ : p 1 = X - C (a 0))
    (hrec : ∀ j, p (j + 2) = (X - C (a (j + 1))) * p (j + 1) - C (b (j + 1)) * p j)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ)
    (hQ : Qᵀ * Q = 1) (hx : jacobiMatrix a b (n + 1) * Q = Q * Matrix.diagonal x) :
    IsGaussRule μ x (fun i ↦ (μ Set.univ).toReal * Q 0 i ^ 2) := by
  sorry

/-- **Gap 12.8.** The Gaussian quadrature error is a derivative at an interior point
times the squared norm of the monic orthogonal polynomial. -/
theorem exists_gauss_remainder {n : ℕ} (hn : 0 < n) {μ : Measure ℝ}
    (hμ : HasInfiniteMomentSupport μ) {a b : ℝ} (hab : a < b)
    (hs : ∀ᵐ t ∂μ, t ∈ Icc a b) {x w : Fin n → ℝ} (hG : IsGaussRule μ x w)
    (p : ℕ → ℝ[X]) (hp : AreMonicOrthogonal μ p) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (2 * n : ℕ) f) :
    ∃ z ∈ Ioo a b, (∫ t, f t ∂μ) - (∑ i, w i * f (x i)) =
      (iteratedDeriv (2 * n) f z / (2 * n).factorial) * ∫ t, (p n).eval t ^ 2 ∂μ := by
  sorry

/-- **Gap 12.10.** Peano's integral error representation for a point-value quadrature
formula that is exact through degree $n$. -/
theorem quadrature_error_eq_peanoKernel {k n : ℕ} {a b : ℝ} (hab : a < b)
    (x w : Fin k → ℝ) (hx : ∀ i, x i ∈ Icc a b)
    (hexact : ∀ p : ℝ[X], p.natDegree ≤ n →
      (∑ i, w i * p.eval (x i)) = ∫ y in a..b, p.eval y)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    let R := fun g : ℝ → ℝ ↦ (∑ i, w i * g (x i)) - ∫ y in a..b, g y
    R f = ∫ t in a..b, (R (fun y ↦ if t ≤ y then (y - t) ^ n else 0) / n.factorial) *
      iteratedDeriv (n + 1) f t := by
  sorry

/-- **Gap 12.12.** Composite Euler--Maclaurin on a uniform mesh with the
pointwise derivative remainder. -/
theorem exists_compositeTrapezoid_eulerMaclaurin {a b : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (m N : ℕ) (hN : 0 < N) (hf : ContDiff ℝ (2 * m + 2 : ℕ) f) :
    let h := (b - a) / N
    let T := h * (f a / 2 + (∑ i ∈ Finset.Ico 1 N, f (a + i * h)) + f b / 2)
    ∃ z ∈ Ioo a b, T = (∫ x in a..b, f x) +
      (∑ j ∈ Finset.Icc 1 m, (bernoulli (2 * j) : ℝ) / (2 * j).factorial * h ^ (2 * j) *
        (iteratedDeriv (2 * j - 1) f b - iteratedDeriv (2 * j - 1) f a)) +
      (bernoulli (2 * m + 2) : ℝ) / (2 * m + 2).factorial * h ^ (2 * m + 2) *
        (b - a) * iteratedDeriv (2 * m + 2) f z := by
  sorry

/-- **Gap 12.14.** Bounded holomorphy on a strip gives the analytic periodic
trapezoidal error bound. -/
theorem norm_trapezoid_sub_integral_le_of_analyticOnStrip
    (f : ℂ → ℂ) {a M : ℝ} (ha : 0 < a)
    (hf : AnalyticOnNhd ℂ f {z | |z.im| < a}) (hM : ∀ z, |z.im| < a → ‖f z‖ ≤ M)
    (hper : Function.Periodic (fun x : ℝ ↦ f x) (2 * Real.pi))
    (N : ℕ) (hN : 0 < N) :
    let h := 2 * Real.pi / N
    ‖h • (∑ j : Fin N, f ((j.val : ℝ) * h)) -
      ∫ x in (0 : ℝ)..(2 * Real.pi), f (x : ℂ)‖ ≤ 4 * Real.pi * M / (Real.exp (a * N) - 1) := by
  sorry

end NASC
