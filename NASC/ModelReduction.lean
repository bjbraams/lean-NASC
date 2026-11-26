module

public import NASC.Galerkin
public import NASC.Conditioning
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Approximation complexity and reduced models

Sparse-grid dimension, tractability and greedy widths, holomorphic parametric solves,
POD, residual certification, empirical interpolation, and linear system reduction.
-/

public section

noncomputable section

namespace NASC

open Set Filter Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- Sparse-grid hierarchical indices. An offset level $l_j$ has $2^{l_j}$ odd nodes. -/
def SparseGridIndex (d n : ℕ) : Type :=
  Σ l : {l : Fin d → Fin n // ∑ j, (l j).val < n}, ∀ j : Fin d, Fin (2 ^ (l.val j).val)

/-- The concrete finite indexing of the sparse-grid hierarchical nodes. -/
instance instFintypeSparseGridIndex (d n : ℕ) : Fintype (SparseGridIndex d n) :=
  inferInstanceAs (Fintype (Σ l : {l : Fin d → Fin n // ∑ j, (l j).val < n},
    ∀ j : Fin d, Fin (2 ^ (l.val j).val)))

/-- **Gap 24.2.** The sparse-grid node count is the weighted sum of the
numbers of level vectors at each total level. -/
theorem card_sparseGridIndex (d n : ℕ) (hd : 0 < d) :
    Fintype.card (SparseGridIndex d n) =
      ∑ i ∈ Finset.range n, 2 ^ i * (d - 1 + i).choose (d - 1) := by
  sorry

/-- **Gap 24.4.** Polynomial tractability is equivalent to a dimension-scaled
summability condition on the tail of the squared singular values. -/
theorem polynomialTractability_iff_summable_tail (σ : ℕ → ℕ → ℝ)
    (hpos : ∀ d j, 0 ≤ σ d j) (hmono : ∀ d, Antitone (σ d))
    (hdecay : ∀ d, Tendsto (σ d) atTop (nhds 0)) :
    (∃ C p q : ℝ, 0 < C ∧ 0 ≤ p ∧ 0 ≤ q ∧
      ∀ (d : ℕ), 0 < d → ∀ ε ∈ Ioo (0 : ℝ) 1,
        ∃ n : ℕ, σ d n ≤ ε ^ 2 ∧ (n : ℝ) ≤ C * (d : ℝ) ^ q * ε ^ (-p)) ↔
    (∃ D C p q t : ℝ, 0 < D ∧ 0 ≤ C ∧ 0 ≤ p ∧ 0 ≤ q ∧ 0 < t ∧
      ∀ d : ℕ, 0 < d →
        let m := Nat.ceil (D * (d : ℝ) ^ p)
        Summable (fun j : ℕ ↦ σ d (m + j) ^ t) ∧
          (∑' j : ℕ, σ d (m + j) ^ t) ≤ C * (d : ℝ) ^ q) := by
  sorry

/-- Kolmogorov width over finite-dimensional linear subspaces. Nonempty compact
input sets give bounded errors for every candidate subspace. -/
def kolmogorovWidth {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Set H) (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ Module.finrank ℝ V ≤ n ∧
    d = sSup ((bestApproximationError (V : Set H)) '' K)}

/-- **Gap 24.6.** The Hilbert-space weak greedy error is bounded by the geometric
mean of the initial and optimal $n$-width errors after $2n$ selections. -/
theorem weakGreedyError_two_mul_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : Set H) (hK : IsCompact K) (hK₀ : K.Nonempty)
    (g : ℕ → H) (hg : ∀ n, g n ∈ K) {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) 1) :
    let V := fun n ↦ Submodule.span ℝ (range (fun j : Fin n ↦ g j.val))
    let err := fun n ↦ sSup ((bestApproximationError (V n : Set H)) '' K)
    (∀ n, γ * err n ≤ bestApproximationError (V n : Set H) (g n)) →
    ∀ n : ℕ, 0 < n → err (2 * n) ≤
      γ⁻¹ * Real.sqrt (2 * kolmogorovWidth K 0 * kolmogorovWidth K n) := by
  sorry

/-- **Gap 24.7.** Affine parametric solution maps are holomorphic on the
Neumann region, where the convergent operator series represents the solution. -/
theorem exists_analyticOnNhd_parametric_inverse {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E ≃L[ℂ] E) (B : X →L[ℂ] (E →L[ℂ] E)) (f : E) :
    let S := {x : X | ‖(A.symm : E →L[ℂ] E).comp (B x)‖ < 1}
    ∃ u : X → E, AnalyticOnNhd ℂ u S ∧ ∀ x ∈ S,
      A (u x) + B x (u x) = f ∧ (∀ v, A v + B x v = f → v = u x) ∧
      u x = ∑' j : ℕ, ((-(A.symm : E →L[ℂ] E).comp (B x)) ^ j) (A.symm f) := by
  sorry

/-- **Gap 24.8.** POD in transformed energy coordinates minimizes the sum of squared
snapshot projection defects, and the minimum is the singular-value tail. -/
theorem isLeast_pod_snapshot_error_sq {m n k : ℕ} (S : Matrix (Fin m) (Fin n) ℝ)
    (hk : k ≤ m) :
    IsLeast {e : ℝ | ∃ V : Matrix (Fin m) (Fin k) ℝ, Vᵀ * V = 1 ∧
      e = ∑ i, ∑ j, (S i j - (V * Vᵀ * S) i j) ^ 2}
      (∑ j ∈ Finset.Ico k (min m n), S.toEuclideanLin.singularValues j ^ 2) := by
  sorry

/-- **Gap 24.9.** Continuity and inf-sup bound the reduced-model error
in terms of the residual dual norm. -/
theorem residual_dualNorm_error_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hA : ‖A‖ ≤ γ) (hinf : ∀ v, β * ‖v‖ ≤ ‖A v‖)
    (u v : V) :
    ‖A u - A v‖ / γ ≤ ‖u - v‖ ∧ ‖u - v‖ ≤ ‖A u - A v‖ / β := by
  rw [← map_sub]
  exact ⟨(div_le_iff₀ hγ).2 (by
    calc
      ‖A (u - v)‖ ≤ ‖A‖ * ‖u - v‖ := A.le_opNorm _
      _ ≤ ‖u - v‖ * γ := by
        rw [mul_comm ‖u - v‖ γ]
        exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)),
    (le_div_iff₀ hβ).2 (by simpa only [mul_comm] using hinf (u - v))⟩

/-- **Gap 24.10.** Unit lower triangular empirical interpolation has operator norm
at most $2^m-1$, and reproduces the supplied empirical basis. -/
theorem exists_empiricalInterpolator {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {m : ℕ} (ρ : Fin m → C(X, ℝ)) (x : Fin m → X)
    (hnorm : ∀ j, ‖ρ j‖ ≤ 1) (hdiag : ∀ j, ρ j (x j) = 1)
    (htri : ∀ i j, i < j → ρ j (x i) = 0) :
    ∃ I : C(X, ℝ) →L[ℝ] C(X, ℝ), ‖I‖ ≤ (2 : ℝ) ^ m - 1 ∧
      (∀ j, I (ρ j) = ρ j) ∧
      ∀ f, (∀ j, I f (x j) = f (x j)) ∧ I f ∈ Submodule.span ℝ (range ρ) := by
  sorry

/-- Transfer function of real state-space matrices evaluated at a complex argument. -/
def stateSpaceTransfer {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (z : ℂ) :
    Matrix (Fin p) (Fin m) ℂ :=
  C.map Complex.ofReal * (z • 1 - A.map Complex.ofReal)⁻¹ * B.map Complex.ofReal

/-- **Gap 24.11.** The leading block of a stable balanced realization is stable
and has transfer error bounded by twice the discarded Hankel singular values. -/
theorem balancedTruncation_stable_transfer_error {r k m p : ℕ} (hk : 0 < k) (hr : 0 < r)
    (A : Matrix (Fin (r + k)) (Fin (r + k)) ℝ)
    (B : Matrix (Fin (r + k)) (Fin m) ℝ) (C : Matrix (Fin p) (Fin (r + k)) ℝ)
    (η : Fin (r + k) → ℝ) (hpos : ∀ i, 0 < η i) (hord : Antitone η)
    (hgap : η ⟨r, by omega⟩ < η ⟨r - 1, by omega⟩)
    (hstable : ∀ z ∈ spectrum ℂ (A.map Complex.ofReal), z.re < 0)
    (hP : A * Matrix.diagonal η + Matrix.diagonal η * Aᵀ + B * Bᵀ = 0)
    (hQ : Aᵀ * Matrix.diagonal η + Matrix.diagonal η * A + Cᵀ * C = 0) :
    let ix : Fin r → Fin (r + k) := Fin.castLE (by omega)
    let Aᵣ := A.submatrix ix ix
    let Bᵣ := B.submatrix ix id
    let Cᵣ := C.submatrix id ix
    (∀ z ∈ spectrum ℂ (Aᵣ.map Complex.ofReal), z.re < 0) ∧ ∀ ω : ℝ,
      ‖stateSpaceTransfer A B C (ω * Complex.I) -
        stateSpaceTransfer Aᵣ Bᵣ Cᵣ (ω * Complex.I)‖ ≤
        2 * ∑ i : Fin k, η (Fin.natAdd r i) := by
  sorry

/-- **Gap 24.12.** A right tangential interpolation condition follows when the
full resolvent response lies in the trial range and the projected pencil is invertible. -/
theorem projection_transfer_right_interpolation {n r m p : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (V W : Matrix (Fin n) (Fin r) ℂ)
    (t : Fin m → ℂ) (hM : M.det ≠ 0) (hMr : (Wᵀ * M * V).det ≠ 0)
    (hV : ∃ x : Fin r → ℂ, V *ᵥ x = M⁻¹ *ᵥ (B *ᵥ t)) :
    (C * M⁻¹ * B) *ᵥ t = (C * V * (Wᵀ * M * V)⁻¹ * Wᵀ * B) *ᵥ t := by
  sorry

end NASC
