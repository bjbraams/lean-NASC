module

public import NASC.Approximation
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Variational and mixed Galerkin methods

Banach inf-sup solvability, Fortin's criterion, quasi-optimality, Strang consistency,
duality, and saddle point problems. Bilinear forms are bundled into maps to the dual.
-/

public section

noncomputable section

namespace NASC

open Set
open scoped BigOperators InnerProductSpace

section Banach

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Gap 18.1.** The Banach--Nečas--Babuška theorem. The inf-sup condition
is written as a uniform lower bound for the map to the test-space dual. -/
theorem bijective_iff_infSup_of_reflexive [CompleteSpace V] [CompleteSpace W]
    (A : V →L[ℝ] StrongDual ℝ W)
    (hW : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ W)) :
    Function.Bijective A ↔
      (∃ α > (0 : ℝ), ∀ v, α * ‖v‖ ≤ ‖A v‖) ∧ (∀ w, (∀ v, A v w = 0) → w = 0) := by
  sorry

/-- **Gap 18.2.** A Fortin map that preserves the pairing transfers the
continuous inf-sup lower bound to the discrete trial space. -/
theorem norm_restrict_ge_of_fortin (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) (P : W →L[ℝ] Y)
    {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hA : ∀ v, α * ‖v‖ ≤ ‖A v‖)
    (hP : ∀ w, γ * ‖P w‖ ≤ ‖w‖)
    (hfortin : ∀ (v : X) (w : W), A v.val (P w).val = A v.val w) :
    ∀ v : X, γ * α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖ := by
  sorry

/-- **Gap 18.3.** Babuška quasi-optimality for a discrete solution
satisfying Galerkin orthogonality. -/
theorem norm_galerkinError_le_of_infSup (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) {α : ℝ} (hα : 0 < α)
    (hstab : ∀ v : X, α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖)
    (u : V) (uh : X) (horth : ∀ w : Y, A (u - uh.val) w.val = 0) :
    ‖u - uh.val‖ ≤ (1 + ‖A‖ / α) * bestApproximationError (X : Set V) u := by
  sorry

/-- **Gap 18.3.** The Hilbert trial-space improvement of the inf-sup
quasi-optimality factor. -/
theorem norm_galerkinError_le_of_infSup_hilbert {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ H) [X.HasOrthogonalProjection] (Y : Submodule ℝ W)
    (hn : X ≠ ⊥) {α : ℝ} (hα : 0 < α)
    (hstab : ∀ v : X, α * ‖v‖ ≤ ‖(A v.val).comp Y.subtypeL‖)
    (u : H) (uh : X) (horth : ∀ w : Y, A (u - uh.val) w.val = 0) :
    ‖u - uh.val‖ ≤ ‖A‖ / α * bestApproximationError (X : Set H) u := by
  sorry

/-- **Gap 18.4.** An inconsistent discrete form is controlled by the
approximation error and the dual norm of its consistency defect. -/
theorem norm_galerkinError_le_strang (A : V →L[ℝ] StrongDual ℝ W)
    (X : Submodule ℝ V) (Y : Submodule ℝ W) (Ah : X →L[ℝ] StrongDual ℝ Y)
    {α : ℝ} (hα : 0 < α) (hstab : ∀ v : X, α * ‖v‖ ≤ ‖Ah v‖)
    (u : V) (uh : X) (f : StrongDual ℝ W) (fh : StrongDual ℝ Y)
    (hsol : A u = f) (hsh : Ah uh = fh) (v : X) :
    ‖u - uh.val‖ ≤ (1 + ‖A‖ / α) * ‖u - v.val‖ +
      ‖fh - f.comp Y.subtypeL + (A v.val).comp Y.subtypeL - Ah v‖ / α := by
  sorry

/-- **Gap 18.13.** Energy quasi-optimality for a conforming Galerkin approximation.
The energy norm is written as the square root of the positive symmetric form. -/
theorem galerkin_energy_error_le (A : V →L[ℝ] StrongDual ℝ V)
    (hA : ∀ v w, A v w = A w v) (hpos : ∀ v, 0 ≤ A v v)
    (X : Submodule ℝ V) (u : V) (uh : X) (horth : ∀ w : X, A (u - uh.val) w.val = 0)
    (v : X) :
    Real.sqrt (A (u - uh.val) (u - uh.val)) ≤ Real.sqrt (A (u - v.val) (u - v.val)) := by
  sorry

/-- **Gap 18.14.** Aubin--Nitsche improvement from approximation of all dual
solutions for the weaker Hilbert-space norm. -/
theorem norm_weak_galerkinError_le_of_dualApproximation {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : V →L[ℝ] StrongDual ℝ V) (J : V →L[ℝ] H) (X : Submodule ℝ V)
    (e : V) (horth : ∀ v : X, A e v.val = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdual : ∀ g : H, ∃ z : V, (∀ v, A v z = inner ℝ (J v) g) ∧
      ∃ w : X, ‖z - w.val‖ ≤ δ * ‖g‖) :
    ‖J e‖ ≤ ‖A‖ * δ * ‖e‖ := by
  sorry

/-- Equations for a mixed problem in the ambient spaces. -/
def IsMixedSolution (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W)
    (f : StrongDual ℝ V) (g : StrongDual ℝ W) (u : V) (p : W) : Prop :=
  (∀ v, A u v + B v p = f v) ∧ ∀ q, B u q = g q

/-- **Gap 18.18.** Coercivity on the kernel and the constraint inf-sup condition
give unique saddle point solvability in real reflexive Banach spaces. -/
theorem existsUnique_mixedSolution_of_infSup [CompleteSpace V] [CompleteSpace W]
    (hV : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V))
    (hW : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ W))
    (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ v, B v = 0 → α * ‖v‖ ^ 2 ≤ A v v)
    (hB : ∀ q : W, β * ‖q‖ ≤ ‖(NormedSpace.inclusionInDoubleDual ℝ W q).comp B‖)
    (f : StrongDual ℝ V) (g : StrongDual ℝ W) :
    ∃! up : V × W, IsMixedSolution A B f g up.1 up.2 := by
  sorry

/-- **Gap 18.19.** Uniform discrete saddle stability yields quasi-optimality with
constants independent of the discrete subspaces. -/
theorem exists_mixed_quasiOptimal_constant
    (A : V →L[ℝ] StrongDual ℝ V) (B : V →L[ℝ] StrongDual ℝ W) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ C ≥ (0 : ℝ), ∀ (X : Submodule ℝ V) (Y : Submodule ℝ W)
      (_ : FiniteDimensional ℝ X) (_ : FiniteDimensional ℝ Y),
      (∀ v : X, (∀ q : Y, B v.val q.val = 0) → α * ‖v‖ ^ 2 ≤ A v.val v.val) →
      (∀ q : Y, β * ‖q‖ ≤ ‖(NormedSpace.inclusionInDoubleDual ℝ W q.val).comp
        (B.comp X.subtypeL)‖) →
      ∀ (u : V) (p : W) (uh : X) (ph : Y),
        (∀ v : X, A (u - uh.val) v.val + B v.val (p - ph.val) = 0) →
        (∀ q : Y, B (u - uh.val) q.val = 0) →
        ‖u - uh.val‖ + ‖p - ph.val‖ ≤ C *
          (bestApproximationError (X : Set V) u + bestApproximationError (Y : Set W) p) := by
  sorry

end Banach

/-- **Gap 18.17.** The symmetric interior penalty quadratic form controls the
broken gradient and weighted jump norm under the inverse trace bound. -/
theorem sipg_coercivity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (h : Fin n → ℝ) (hpos : ∀ i, 0 < h i) (j a : Fin n → H)
    {c G η : ℝ} (hG : 0 ≤ G) (htrace : (∑ i, h i * ‖a i‖ ^ 2) ≤ c ^ 2 * G)
    (hpen : 2 * c ^ 2 + 1 / 2 ≤ η) :
    (G + ∑ i, ‖j i‖ ^ 2 / h i) / 2 ≤
      G - 2 * (∑ i, inner ℝ (a i) (j i)) + η * ∑ i, ‖j i‖ ^ 2 / h i := by
  sorry

end NASC
