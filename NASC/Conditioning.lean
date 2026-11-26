module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Conditioning and matrix perturbations

Local amplification, backward error, perturbations of eigenvalues and singular values,
pseudospectra and the leading singular subspaces. Singular values use Mathlib's zero-based
indexing.
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
  sorry

end NormedSpaces

section LinearSystems

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Gap 2.4.** Normwise forward error when simultaneous perturbations affect the
operator and right-hand side of a linear solve. -/
theorem norm_sub_le_of_perturbed_eq (A : E ≃L[ℝ] E) {x y db : E} {dA : E →L[ℝ] E}
    {ε a b : ℝ} (hε : 0 ≤ ε) (hdA : ‖dA‖ ≤ ε * a) (hdb : ‖db‖ ≤ ε * b)
    (hx : x ≠ 0) (hy : A y + dA y = A x + db)
    (hsmall : ε * ‖(A.symm : E →L[ℝ] E)‖ * a < 1) :
    ‖x - y‖ / ‖x‖ ≤ ε / (1 - ε * ‖(A.symm : E →L[ℝ] E)‖ * a) *
      (‖(A.symm : E →L[ℝ] E)‖ * b / ‖x‖ + ‖(A.symm : E →L[ℝ] E)‖ * a) := by
  sorry

/-- **Gap 2.5.** Rigal--Gaches sharp attained weighted normwise backward error. -/
theorem isLeast_normwiseBackwardError (A : E →L[ℝ] E) (x b : E) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h : 0 < a * ‖x‖ + c) :
    IsLeast {ε : ℝ | 0 ≤ ε ∧ ∃ dA : E →L[ℝ] E, ∃ db : E,
      (A + dA) x = b + db ∧ ‖dA‖ ≤ ε * a ∧ ‖db‖ ≤ ε * c}
      (‖b - A x‖ / (a * ‖x‖ + c)) := by
  sorry


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
  sorry

/-- Euclidean least-squares optimality, including rank-deficient designs. -/
def MinimizesLeastSquares {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin m)) (x : EuclideanSpace 𝕜 (Fin n)) : Prop :=
  ∀ y, ‖b - A.toEuclideanLin x‖ ≤ ‖b - A.toEuclideanLin y‖

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
