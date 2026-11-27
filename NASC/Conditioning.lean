module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Conditioning and matrix perturbations

Local amplification, backward error, perturbations of eigenvalues and singular values,
pseudospectra and the leading singular subspaces. Singular values use Mathlib's zero-based
indexing. The conditioning proofs use Mathlib’s converse local Lipschitz estimate for
Fréchet derivatives and Hahn–Banach norming functionals.
-/

public section

noncomputable section

namespace NASC

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator
open Set Filter

section NormedSpaces

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Absolute local amplification over nonzero increments within the domain. -/
def absoluteConditionNumber (f : E → F) (s : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ d : {r : ℝ // 0 < r}, ⨆ y : E, ⨆ (_ : y ∈ s ∧ y ≠ x ∧ ‖y - x‖ ≤ d.val),
    ENNReal.ofReal (‖f y - f x‖ / ‖y - x‖)

/-- The condition number uses the infimum of the local upper amplifications. -/
theorem absoluteConditionNumber_def (f : E → F) (s : Set E) (x : E) :
    absoluteConditionNumber f s x =
      ⨅ d : {r : ℝ // 0 < r}, ⨆ y : E, ⨆ (_ : y ∈ s ∧ y ≠ x ∧ ‖y - x‖ ≤ d.val),
        ENNReal.ofReal (‖f y - f x‖ / ‖y - x‖) := by
  unfold absoluteConditionNumber
  rfl

/-- **Gap 2.1.** The exact absolute amplification of a differentiable map over
the real field is the operator norm of the derivative. -/
theorem HasFDerivAt.absoluteConditionNumber_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : E →L[ℝ] F} {s : Set E} {x : E} (hf : HasFDerivAt f D x)
    (hs : s ∈ nhds x) :
    absoluteConditionNumber f s x = ENNReal.ofReal ‖D‖ := by
  rw [absoluteConditionNumber_def]
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hε' : (0 : ℝ) < ε := hε
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (norm_nonneg _) hε'.le]
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.isLittleO.bound hε')
    refine (iInf_le _ ⟨r / 2, half_pos hr⟩).trans ?_
    refine iSup_le fun y ↦ iSup_le fun hy ↦ ENNReal.ofReal_le_ofReal ?_
    have hyball : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt hy.2.2 (half_lt_self hr)
    have hrem : ‖f y - f x - D (y - x)‖ ≤ ε * ‖y - x‖ := hball hyball
    refine (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hy.2.1))).mpr ?_
    calc
      ‖f y - f x‖ ≤ ‖D (y - x)‖ + ‖f y - f x - D (y - x)‖ := by
        rw [norm_sub_rev (f y - f x)]
        exact norm_le_insert _ _
      _ ≤ ‖D‖ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (D.le_opNorm _) hrem
      _ = (‖D‖ + ε) * ‖y - x‖ := (add_mul ..).symm
  · refine le_iInf fun d ↦ ?_
    let M := ⨆ y : E, ⨆ (_ : y ∈ s ∧ y ≠ x ∧ ‖y - x‖ ≤ d.val),
      ENNReal.ofReal (‖f y - f x‖ / ‖y - x‖)
    obtain htop | hfinite := eq_or_ne M ⊤
    · calc
        _ ≤ ⊤ := le_top
        _ = M := htop.symm
    refine (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr (hf.le_of_lip' ENNReal.toReal_nonneg ?_)
    filter_upwards [hs, Metric.ball_mem_nhds x d.prop] with y hys hyball
    by_cases hy : y = x
    · simp only [hy, sub_self, norm_zero, mul_zero, le_refl]
    have hy' : y ∈ s ∧ y ≠ x ∧ ‖y - x‖ ≤ d := by
      refine ⟨hys, hy, ?_⟩
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hyball).le
    have hle : ENNReal.ofReal (‖f y - f x‖ / ‖y - x‖) ≤ M :=
      le_iSup_of_le y (le_iSup_of_le hy' le_rfl)
    have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    rw [ENNReal.ofReal_le_iff_le_toReal hfinite, div_le_iff₀ hpos] at hle
    exact hle

end NormedSpaces

section LinearSystems

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Gap 2.4.** Normwise forward error when simultaneous perturbations affect the
operator and right-hand side of a linear solve. -/
theorem norm_sub_le_of_perturbed_eq (A : E ≃L[ℝ] E) {x y db : E} {dA : E →L[ℝ] E}
    {ε a b : ℝ} (hε : 0 ≤ ε) (hdA : ‖dA‖ ≤ ε * a) (hdb : ‖db‖ ≤ ε * b)
    (hx : x ≠ 0) (hy : A y + dA y = A x + db)
    (hsmall : ε * ‖(A.symm : E →L[ℝ] E)‖ * a < 1) :
    ‖x - y‖ / ‖x‖ ≤ ε / (1 - ε * ‖(A.symm : E →L[ℝ] E)‖ * a) *
      (‖(A.symm : E →L[ℝ] E)‖ * b / ‖x‖ + ‖(A.symm : E →L[ℝ] E)‖ * a) := by
  rcases hε.eq_or_lt with hzero | hpos
  · have hmap : dA = 0 := norm_eq_zero.mp (le_antisymm
      (by simpa only [← hzero, zero_mul] using hdA) (norm_nonneg _))
    have hb : db = 0 := norm_eq_zero.mp (le_antisymm
      (by simpa only [← hzero, zero_mul] using hdb) (norm_nonneg _))
    have hxy : y = x := A.injective (by simpa only [hmap, hb, zero_apply,
      add_zero] using hy)
    simp only [hxy, sub_self, norm_zero, zero_div, ← hzero, zero_mul, le_refl]
  let c := ‖(A.symm : E →L[ℝ] E)‖
  have hc : 0 ≤ c := norm_nonneg _
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ha : 0 ≤ a := nonneg_of_mul_nonneg_right ((norm_nonneg dA).trans hdA) hpos
  have hdpos : 0 ≤ ε * a := mul_nonneg hpos.le ha
  have heq : A (y - x) = db - dA y := by
    rw [map_sub, sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm, add_left_comm, add_assoc] using hy
  have hcalc : ‖y - x‖ ≤ c * (ε * b + ε * a * (‖y - x‖ + ‖x‖)) := by
    calc
      ‖y - x‖ = ‖A.symm (db - dA y)‖ := by rw [← heq, A.symm_apply_apply]
      _ ≤ c * ‖db - dA y‖ := (A.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ c * (‖db‖ + ‖dA y‖) := mul_le_mul_of_nonneg_left (norm_sub_le ..) hc
      _ ≤ c * (ε * b + ε * a * (‖y - x‖ + ‖x‖)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply add_le_add hdb
        calc
          ‖dA y‖ ≤ ‖dA‖ * ‖y‖ := dA.le_opNorm y
          _ ≤ (ε * a) * ‖y‖ := mul_le_mul_of_nonneg_right hdA (norm_nonneg _)
          _ ≤ (ε * a) * (‖y - x‖ + ‖x‖) :=
            mul_le_mul_of_nonneg_left (norm_le_norm_sub_add y x) hdpos
  have hden : 0 < 1 - ε * c * a := sub_pos.mpr hsmall
  rw [norm_sub_rev, div_mul_eq_mul_div, le_div_iff₀ hden]
  field_simp [ne_of_gt hxpos]
  dsimp only [c] at hcalc ⊢
  nlinarith only [hcalc]

omit [FiniteDimensional ℝ E] in
/-- **Gap 2.5.** Rigal--Gaches sharp attained weighted normwise backward error. -/
theorem isLeast_normwiseBackwardError (A : E →L[ℝ] E) (x b : E) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h : 0 < a * ‖x‖ + c) :
    IsLeast {ε : ℝ | 0 ≤ ε ∧ ∃ dA : E →L[ℝ] E, ∃ db : E,
      (A + dA) x = b + db ∧ ‖dA‖ ≤ ε * a ∧ ‖db‖ ≤ ε * c}
      (‖b - A x‖ / (a * ‖x‖ + c)) := by
  let d := a * ‖x‖ + c
  have hd : 0 ≤ d := h.le
  let r := b - A x
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, hφn, hφx⟩ := exists_dual_vector'' ℝ x
    -- Mathlib supplies the norming functional by Hahn–Banach.
    have hφval : φ x = ‖x‖ := hφx
    let D := φ.smulRight ((a / d) • r)
    let g := -((c / d) • r)
    refine ⟨div_nonneg (norm_nonneg _) h.le, D, g, ?_, ?_, ?_⟩
    · have hcoeff : ‖x‖ * (a / d) + c / d = 1 := by
        rw [← mul_div_assoc, ← add_div, mul_comm ‖x‖ a]
        exact div_self (ne_of_gt h)
      have hs : (‖x‖ * (a / d)) • r + (c / d) • r = r := by
        rw [← add_smul, hcoeff, one_smul]
      have hr : A x + r = b := by
        dsimp only [r]
        abel
      simp only [add_apply, D, ContinuousLinearMap.smulRight_apply, hφval,
        smul_smul, g]
      rw [← hr, ← sub_eq_add_neg, eq_sub_iff_add_eq, add_assoc, hs]
    · dsimp only [D]
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
        Real.norm_of_nonneg (div_nonneg ha hd)]
      calc
        ‖φ‖ * ((a / d) * ‖r‖) ≤ 1 * ((a / d) * ‖r‖) :=
          mul_le_mul_of_nonneg_right hφn (mul_nonneg (div_nonneg ha hd) (norm_nonneg _))
        _ = ‖r‖ / d * a := by ring
    · dsimp only [g]
      rw [norm_neg, norm_smul, Real.norm_of_nonneg (div_nonneg hc hd)]
      calc
        c / d * ‖r‖ = ‖r‖ / d * c := by ring
        _ ≤ _ := le_rfl
  · rintro ε ⟨_, D, g, heq, hD, hg⟩
    have hr : b - A x = D x - g := by
      rw [sub_eq_sub_iff_add_eq_add]
      simpa only [add_apply, add_comm] using heq.symm
    apply (div_le_iff₀ h).mpr
    calc
      ‖b - A x‖ = ‖D x - g‖ := congrArg norm hr
      _ ≤ ‖D x‖ + ‖g‖ := norm_sub_le _ _
      _ ≤ ‖D‖ * ‖x‖ + ‖g‖ := add_le_add (D.le_opNorm x) le_rfl
      _ ≤ (ε * a) * ‖x‖ + ε * c := add_le_add (by gcongr) hg
      _ = _ := by ring


/-- **Gap 2.4.** Sharp first-order amplification for simultaneous normwise perturbations. -/
theorem tendsto_normwisePerturbation_amplification (A : E ≃L[ℝ] E) {x : E} (hx : x ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun ε : ℝ ↦ sSup {r : ℝ |
      ∃ (D : E →L[ℝ] E) (g y : E),
        ‖D‖ ≤ ε * a ∧ ‖g‖ ≤ ε * b ∧ A y + D y = A x + g ∧
          r = ‖y - x‖ / (ε * ‖x‖)}) (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (‖(A.symm : E →L[ℝ] E)‖ * b / ‖x‖ + ‖(A.symm : E →L[ℝ] E)‖ * a)) := by
  sorry

end LinearSystems

/-- **Gap 2.6.** Componentwise backward-error feasibility is equivalent to the residual
being enclosed by the prescribed componentwise budget. This also covers zero budgets. -/
theorem exists_componentwisePerturbation_iff {m n : ℕ}
    (A W : Matrix (Fin m) (Fin n) ℝ) (b f : Fin m → ℝ) (y : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hW : ∀ i j, 0 ≤ W i j) (hf : ∀ i, 0 ≤ f i) :
    (∃ D : Matrix (Fin m) (Fin n) ℝ, ∃ g : Fin m → ℝ,
      (A + D) *ᵥ y = b + g ∧ (∀ i j, |D i j| ≤ ε * W i j) ∧
        (∀ i, |g i| ≤ ε * f i)) ↔
    ∀ i, |b i - (A *ᵥ y) i| ≤ ε * ((W *ᵥ (fun j ↦ |y j|)) i + f i) := by
  sorry

/-- **Gap 2.6.** The exact componentwise backward error, with the empty feasible set
assigned infinite error and zero-over-zero components assigned zero. -/
theorem sInf_componentwiseBackwardError {m n : ℕ}
    (A W : Matrix (Fin m) (Fin n) ℝ) (b f : Fin m → ℝ) (y : Fin n → ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hf : ∀ i, 0 ≤ f i) :
    sInf {ε : ℝ≥0∞ | ∃ D : Matrix (Fin m) (Fin n) ℝ, ∃ g : Fin m → ℝ,
      (A + D) *ᵥ y = b + g ∧ (∀ i j, ENNReal.ofReal |D i j| ≤ ε * ENNReal.ofReal (W i j)) ∧
        (∀ i, ENNReal.ofReal |g i| ≤ ε * ENNReal.ofReal (f i))} =
    ⨆ i, ENNReal.ofReal |b i - (A *ᵥ y) i| /
      ENNReal.ofReal ((W *ᵥ (fun j ↦ |y j|)) i + f i) := by
  sorry

/-- **Gap 2.3.** The Euclidean distance to a singular matrix is the last singular value,
attained by a rank-one perturbation. -/
theorem exists_rank_one_isLeast_singularPerturbation {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (hA : A.det ≠ 0) :
    ∃ D : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜, D.rank = 1 ∧
      (A + D).det = 0 ∧ ‖D‖ = A.toEuclideanLin.singularValues n ∧
      IsLeast {t : ℝ | ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜,
        (A + B).det = 0 ∧ ‖B‖ = t} ‖D‖ := by
  sorry

/-- Rectangular diagonal matrix given a real sequence, with each entry cast to the scalar
field of the ambient matrix. -/
def singularValueDiagonal {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) : Matrix (Fin m) (Fin n) 𝕜 :=
  fun i j ↦ if i.val = j.val then (A.toEuclideanLin.singularValues i.val : 𝕜) else 0

/-- The entries of the singular-value diagonal use the zero-based singular values. -/
theorem singularValueDiagonal_apply {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (i : Fin m) (j : Fin n) :
    singularValueDiagonal A i j =
      (if i.val = j.val then (A.toEuclideanLin.singularValues i.val : 𝕜) else 0) := by
  unfold singularValueDiagonal
  rfl

/-- **Gap 2.10.** Mirsky's inequality for a unitarily invariant seminorm on rectangular
matrices. -/
theorem seminorm_singularValueDiagonal_sub_le {m n : ℕ}
    (p : Seminorm ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hp : ∀ (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
      U ∈ unitary (Matrix (Fin m) (Fin m) ℂ) → V ∈ unitary (Matrix (Fin n) (Fin n) ℂ) →
      ∀ X, p (U * X * V) = p X)
    (A B : Matrix (Fin m) (Fin n) ℂ) :
    p (singularValueDiagonal A - singularValueDiagonal B) ≤ p (A - B) := by
  sorry

/-- **Gap 2.10.** Singular-value interlacing after deletion of one column, in the
zero-extended indexing of Mathlib. -/
theorem singularValues_submatrix_interlace {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℂ) (e : Fin n ↪ Fin (n + 1)) (i : ℕ) :
    A.toEuclideanLin.singularValues (i + 1) ≤ (A.submatrix id e).toEuclideanLin.singularValues i ∧
      (A.submatrix id e).toEuclideanLin.singularValues i ≤ A.toEuclideanLin.singularValues i := by
  sorry

/-- **Gap 2.11.** Spectra of normal matrices admit a matching controlled in Frobenius
norm. The input lists enumerate characteristic roots with multiplicity. -/
theorem exists_perm_sum_norm_sq_le_of_isStarNormal {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) (hB : IsStarNormal B)
    {α β : Fin n → ℂ} (hα : Multiset.ofList (List.ofFn α) = A.charpoly.roots)
    (hβ : Multiset.ofList (List.ofFn β) = B.charpoly.roots) :
    ∃ e : Equiv.Perm (Fin n),
      ∑ i, ‖α i - β (e i)‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2 := by
  sorry

/-- The closed Gershgorin disc centered at a diagonal entry. -/
def gershgorinDisc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Set ℂ :=
  Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖)

/-- **Gap 2.12.** A union of Gershgorin discs disjoint from all the others contains
exactly as many characteristic roots, counted with multiplicity, as indices. -/
theorem card_roots_filter_mem_gershgorinDiscs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (I : Finset (Fin n))
    (h : Disjoint (⋃ i ∈ I, gershgorinDisc A i) (⋃ i ∉ I, gershgorinDisc A i)) :
    letI := Classical.propDecidable
    (A.charpoly.roots.filter (fun z ↦ z ∈ ⋃ i ∈ I, gershgorinDisc A i)).card = I.card := by
  sorry

/-- **Gap 2.13.** Bauer--Fike in the Euclidean operator norm. -/
theorem exists_norm_sub_eigenvalue_le_of_diagonalization {n : ℕ}
    (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (eigs : Fin n → ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((S : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal eigs *
      (↑S⁻¹ : Matrix (Fin n) (Fin n) ℂ) + E)) :
    ∃ i, ‖μ - eigs i‖ ≤ ‖(S : Matrix (Fin n) (Fin n) ℂ)‖ *
      ‖(↑S⁻¹ : Matrix (Fin n) (Fin n) ℂ)‖ * ‖E‖ := by
  by_contra! hgap
  let M := Matrix (Fin n) (Fin n) ℂ
  let T : M := ↑S⁻¹
  let K := ‖(S : M)‖ * ‖T‖ * ‖E‖
  let D : M := Matrix.diagonal fun i ↦ μ - eigs i
  let V : M := Matrix.diagonal fun i ↦ (μ - eigs i)⁻¹
  let F : M := T * E * (S : M)
  have hK : 0 ≤ K := by positivity
  have hne (i : Fin n) : μ - eigs i ≠ 0 := norm_pos_iff.mp (hK.trans_lt (hgap i))
  have hd (i : Fin n) : (μ - eigs i) * (μ - eigs i)⁻¹ = 1 := mul_inv_cancel₀ (hne i)
  have hDV : D * V = 1 := by
    dsimp only [D, V, M]
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [hd] using (Matrix.diagonal_one (n := Fin n) (α := ℂ))
  have hnormF : ‖F‖ ≤ K := by
    calc
      ‖F‖ ≤ ‖T * E‖ * ‖(S : M)‖ := Matrix.l2_opNorm_mul ..
      _ ≤ (‖T‖ * ‖E‖) * ‖(S : M)‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul ..) (norm_nonneg _)
      _ = K := by dsimp only [K]; ring
  have hnormV : ‖V‖ * K < 1 := by
    dsimp only [V, M]
    rw [Matrix.l2_opNorm_diagonal, mul_comm, ← Real.norm_of_nonneg hK, ← Complex.norm_real,
      ← norm_smul]
    refine (pi_norm_lt_iff zero_lt_one).mpr fun i ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK,
      norm_inv, ← div_eq_mul_inv, div_lt_one (norm_pos_iff.mpr (hne i))]
    exact hgap i
  have hunit : IsUnit (1 - V * F) := isUnit_one_sub_of_norm_lt_one <|
    ((Matrix.l2_opNorm_mul ..).trans (mul_le_mul_of_nonneg_left hnormF (norm_nonneg V))).trans_lt
      hnormV
  have hST : (S : M) * T = 1 := Units.mul_inv S
  have hd_eq : D = μ • (1 : M) - Matrix.diagonal eigs := by
    dsimp only [D, M]
    simpa only [Matrix.smul_one_eq_diagonal] using
      (Matrix.diagonal_sub (fun _ : Fin n ↦ μ) eigs).symm
  have hd_conj : (S : M) * D * T = μ • (1 : M) - (S : M) * Matrix.diagonal eigs * T := by
    rw [hd_eq, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hST]
  have hf_conj : ((S : M) * D) * (V * F) * T = E := by
    rw [← Matrix.mul_assoc (_ * D) V, Matrix.mul_assoc (S : M) D V, hDV, mul_one]
    dsimp only [F]
    rw [← Matrix.mul_assoc (S : M) (T * E), ← Matrix.mul_assoc (S : M) T, hST, one_mul,
      Matrix.mul_assoc E (S : M) T, hST, mul_one]
  apply spectrum.mem_iff.mp hμ
  rw [Algebra.algebraMap_eq_smul_one, ← sub_sub, ← hd_conj, ← hf_conj,
    ← Matrix.sub_mul]
  have hfactor : (S : M) * D - (S : M) * D * (V * F) = ((S : M) * D) * (1 - V * F) := by
    rw [Matrix.mul_sub, mul_one]
  rw [hfactor]
  exact ((S.isUnit.mul (isUnit_iff_exists_inv.mpr ⟨V, hDV⟩)).mul hunit).mul S⁻¹.isUnit

/-- Euclidean least-squares optimality, including rank-deficient designs. -/
def MinimizesLeastSquares {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin m)) (x : EuclideanSpace 𝕜 (Fin n)) : Prop :=
  ∀ y, ‖b - A.toEuclideanLin x‖ ≤ ‖b - A.toEuclideanLin y‖

/-- Least-squares optimality is the pointwise comparison against all trial vectors. -/
theorem minimizesLeastSquares_iff {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : EuclideanSpace 𝕜 (Fin m))
    (x : EuclideanSpace 𝕜 (Fin n)) :
    MinimizesLeastSquares A b x ↔ ∀ y, ‖b - A.toEuclideanLin x‖ ≤ ‖b - A.toEuclideanLin y‖ := by
  unfold MinimizesLeastSquares
  rfl

/-- **Gap 2.15.** Perturbation bounds for the solution and residual of a full-column-rank
least-squares problem. -/
theorem leastSquares_perturbation {m n : ℕ}
    {A D : Matrix (Fin m) (Fin (n + 1)) ℝ} {b d : EuclideanSpace ℝ (Fin m)}
    {x y : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ}
    (hA : Function.Injective A.toEuclideanLin) (hx₀ : x ≠ 0) (hb₀ : b ≠ 0)
    (hx : MinimizesLeastSquares A b x) (hy : MinimizesLeastSquares (A + D) (b + d) y)
    (hε : 0 ≤ ε) (hD : ‖D‖ ≤ ε * ‖A‖) (hd : ‖d‖ ≤ ε * ‖b‖)
    (hsmall : (‖A‖ / A.toEuclideanLin.singularValues n) * ε < 1) :
    let κ := ‖A‖ / A.toEuclideanLin.singularValues n
    let r := b - A.toEuclideanLin x
    let s := b + d - (A + D).toEuclideanLin y
    Function.Injective (A + D).toEuclideanLin ∧
      ‖x - y‖ / ‖x‖ ≤ κ * ε / (1 - κ * ε) * (2 + (κ + 1) * ‖r‖ / (‖A‖ * ‖x‖)) ∧
      ‖r - s‖ / ‖b‖ ≤ (1 + 2 * κ) * ε := by
  sorry

/-- Open Euclidean pseudospectrum, expressed by an approximate unit eigenvector. -/
def pseudospectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : Set ℂ :=
  {z | ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧ ‖z • v - A.toEuclideanLin v‖ < ε}

/-- **Gap 2.16.** Equivalence of the perturbation, residual and least-singular-value
descriptions of the open pseudospectrum. -/
theorem mem_pseudospectrum_iff {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    (z ∈ pseudospectrum A ε ↔ ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ‖E‖ < ε ∧ z ∈ spectrum ℂ (A + E)) ∧
    (z ∈ pseudospectrum A ε ↔
      ((z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) - A).toEuclideanLin.singularValues n <
        ε) := by
  sorry

/-- **Gap 2.16.** Every connected component of the pseudospectrum contains an eigenvalue. -/
theorem connectedComponentIn_pseudospectrum_inter_spectrum_nonempty {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ pseudospectrum A ε) :
    (connectedComponentIn (pseudospectrum A ε) z ∩ spectrum ℂ A).Nonempty := by
  sorry

/-- **Gap 2.16.** The resolvent description has an explicit pole branch at eigenvalues. -/
theorem mem_pseudospectrum_iff_resolvent {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    z ∈ pseudospectrum A ε ↔ z ∈ spectrum ℂ A ∨
      ε⁻¹ < ‖(z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A)⁻¹‖ := by
  sorry

/-- A leading singular frame is an orthonormal collection of paired singular vectors
corresponding to the first singular values. -/
def IsLeadingSingularFrame {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin r) ℂ) (V : Matrix (Fin n) (Fin r) ℂ) : Prop :=
  let S := Matrix.diagonal fun j : Fin r ↦ (A.toEuclideanLin.singularValues j.val : ℂ)
  Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ A * V = U * S ∧ Aᴴ * U = V * S

/-- **Gap 2.18.** Wedin's bound on the maximum principal sine, expressed by the
directed residuals of the two orthogonal projectors. -/
theorem max_norm_sub_projection_mul_le_of_singular_gap {m n r : ℕ}
    {A B : Matrix (Fin m) (Fin n) ℂ}
    {UA UB : Matrix (Fin m) (Fin r) ℂ} {VA VB : Matrix (Fin n) (Fin r) ℂ}
    (hA : IsLeadingSingularFrame A UA VA) (hB : IsLeadingSingularFrame B UB VB)
    (hr : 0 < r) (hr' : r < min m n)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hgap₁ : A.toEuclideanLin.singularValues r ≤ a)
    (hgap₂ : a + δ ≤ B.toEuclideanLin.singularValues (r - 1)) :
    max ‖(1 - UA * UAᴴ) * UB‖ ‖(1 - VA * VAᴴ) * VB‖ ≤ ‖B - A‖ / δ := by
  sorry

end NASC
