module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Elementary algebraic helpers

Topic-free facts used by several files of the library: inequalities for products of factors
close to one, a conjugation identity in a ring, and the matching of the roots of two products
of linear factors.

## Main results

* `NASC.abs_mul_sub_one_le`, `NASC.abs_mul_one_add_sub_le_of_abs_sub_le`: composition of
  relative and absolute error bounds.
* `NASC.natCast_mul_lt_one_of_le`, `NASC.lt_one_of_natCast_mul_lt_one`: consequences of
  `k u < 1`.
* `NASC.sub_units_conj_add_eq`: `c - (S Λ S⁻¹ + E) = S ((c - Λ) - S⁻¹ E S) S⁻¹` for central `c`.
* `NASC.exists_perm_of_prod_X_sub_C_eq`: equal products of linear factors with distinct
  roots have the same roots up to a permutation.
-/

public section

namespace NASC

/-- If `k u < 1` with `u ≥ 0`, then `j u < 1` for every `j ≤ k`. -/
theorem natCast_mul_lt_one_of_le {u : ℝ} {j k : ℕ} (hu : 0 ≤ u) (hjk : j ≤ k)
    (hk : (k : ℝ) * u < 1) : (j : ℝ) * u < 1 :=
  (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjk) hu).trans_lt hk

/-- If `k u < 1` with `u ≥ 0` and `k ≥ 1`, then `u < 1`. -/
theorem lt_one_of_natCast_mul_lt_one {u : ℝ} {k : ℕ} (hu : 0 ≤ u) (hk : 1 ≤ k)
    (h : (k : ℝ) * u < 1) : u < 1 := by
  simpa only [Nat.cast_one, one_mul] using natCast_mul_lt_one_of_le hu hk h

/-- An absolute error `|a - b| ≤ p w` with `|b| ≤ w`, followed by a relative perturbation
`a (1 + δ)` with `|δ| ≤ q`, has absolute error at most `(p + q + p q) w`. -/
theorem abs_mul_one_add_sub_le_of_abs_sub_le {a b δ p q w : ℝ}
    (hab : |a - b| ≤ p * w) (hb : |b| ≤ w) (hδ : |δ| ≤ q) :
    |a * (1 + δ) - b| ≤ (p + q + p * q) * w := by
  have ha : |a| ≤ p * w + w := by
    rw [← sub_add_cancel a b]
    exact (abs_add_le _ _).trans (add_le_add hab hb)
  have heq : a * (1 + δ) - b = (a - b) + a * δ := by ring
  rw [heq]
  calc
    _ ≤ |a - b| + |a| * |δ| := by simpa only [abs_mul] using abs_add_le (a - b) (a * δ)
    _ ≤ p * w + (p * w + w) * q :=
      add_le_add hab (mul_le_mul ha hδ (abs_nonneg _) ((abs_nonneg _).trans ha))
    _ = _ := by ring

/-- If `|a - 1| ≤ p` and `|b - 1| ≤ q`, then `|a b - 1| ≤ p + q + p q`. -/
theorem abs_mul_sub_one_le {a b p q : ℝ} (ha : |a - 1| ≤ p) (hb : |b - 1| ≤ q) :
    |a * b - 1| ≤ p + q + p * q := by
  have h : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
  rw [h]
  calc
    _ ≤ |a - 1| + |b - 1| + |(a - 1) * (b - 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (add_le_add ha hb)
        (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))

/-- In a ring, a central shift `c` of a perturbed conjugate is the conjugate of the shifted
element minus the conjugated perturbation: `c - (S Λ S⁻¹ + E) = S ((c - Λ) - S⁻¹ E S) S⁻¹`. -/
theorem sub_units_conj_add_eq {R : Type*} [Ring R] (S : Rˣ) {c : R} (hc : ∀ y, c * y = y * c)
    (Λ E : R) : c - (S * Λ * ↑S⁻¹ + E) = S * ((c - Λ) - ↑S⁻¹ * E * S) * ↑S⁻¹ := by
  have h₁ : (S : R) * c * ↑S⁻¹ = c := by rw [← hc, mul_assoc, S.mul_inv, mul_one]
  have h₂ : (S : R) * (↑S⁻¹ * E * S) * ↑S⁻¹ = E := by
    rw [← mul_assoc, ← mul_assoc, S.mul_inv, one_mul, mul_assoc, S.mul_inv, mul_one]
  rw [mul_sub, sub_mul, mul_sub, sub_mul, h₁, h₂, sub_sub]

/-- If a product of linear factors with distinct roots `z` equals another product of the
same number of linear factors, the roots `w` are a permutation of `z`. -/
theorem exists_perm_of_prod_X_sub_C_eq {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {z w : Fin n → R} (hz : Function.Injective z)
    (hp : (∏ i, (Polynomial.X - Polynomial.C (z i))) =
      ∏ i, (Polynomial.X - Polynomial.C (w i))) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, z i = w (e i) := by
  classical
  have hmatch (i : Fin n) : ∃ j, z i = w j := by
    have hroot : (∏ j : Fin n, (z i - z j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (z i))
    have heval := congrArg (Polynomial.eval (z i)) hp
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, hroot] at heval
    simpa only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using heval.symm
  choose e he using hmatch
  have hinj : Function.Injective e := fun i j h ↦ hz ((he i).trans (by rw [h, ← he j]))
  exact ⟨Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj), he⟩

end NASC
