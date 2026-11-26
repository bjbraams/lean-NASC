# Numerical analysis and scientific computing — Mathlib and TauCeti coverage

This inventory follows the 24 sections and stable identifiers of the
[mathematical synopsis](SYNOPSIS.md). The [bibliography](NASC-bib.md) records the
mathematical sources. The library review uses the Mathlib and TauCeti working
revisions in the shared `~/lean-codes/.lake` for NASC.

Of the **396** entries, **6** are covered, **62** are partly covered, and
**328** have no matching theorem identified at the reviewed revisions. Each
numbered section records the relevant declarations, the scope of the match,
and the gaps for its entries.

## Source baseline

- **Mathlib** — [`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842),
  2026-11-16, tag `v4.36.0`.
- **TauCeti** — [`d91980bdc255e6e50506be147ad9bcb88eb9fcc0`](https://github.com/TauCetiProject/TauCeti/tree/d91980bdc255e6e50506be147ad9bcb88eb9fcc0),
  2026-11-19, with the Mathlib revision above.
- **Lean** — `leanprover/lean4:v4.36.0`.

Coverage is based on source inspection of `Mathlib/` followed by `TauCeti/`.
Declaration links point to the above revisions. The cited modules and their
Mathlib/TauCeti imports were scanned for admissions and added axioms. The
matches are based on declared theorem statements and their source proofs.

An entry is **covered** when its mathematical claims appear as proved results,
including direct instances and equivalent representations. It is **partly
covered** when a proved result matches a claim within the entry or a special
case of it. **Not covered** means the review identified no such result.
Definitions, analogous estimates, and results that still require an argument
to yield the claimed numerical conclusion are recorded as ingredients. In
particular, a general approximation framework contributes coverage only to
the specific assertions it supplies.

The two libraries usually index ordered spectra from zero. A finite matrix
can be represented by its linear map on Euclidean space, with its induced
operator norm, or by its entries, with a different norm. The links below
identify which interpretation is used when it affects the comparison.

## Coverage by section

- [1. Floating-point arithmetic and rounding error analysis](#1-floating-point-arithmetic-and-rounding-error-analysis) — 13 entries, 0 covered, 0 partly covered, 13 not covered.
- [2. Conditioning and matrix perturbation theory](#2-conditioning-and-matrix-perturbation-theory) — 18 entries, 3 covered, 6 partly covered, 9 not covered.
- [3. Direct methods for linear systems and least squares](#3-direct-methods-for-linear-systems-and-least-squares) — 16 entries, 0 covered, 4 partly covered, 12 not covered.
- [4. Eigenvalue and singular value computations](#4-eigenvalue-and-singular-value-computations) — 19 entries, 1 covered, 3 partly covered, 15 not covered.
- [5. Iterative methods for linear systems](#5-iterative-methods-for-linear-systems) — 18 entries, 0 covered, 3 partly covered, 15 not covered.
- [6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation](#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation) — 16 entries, 0 covered, 7 partly covered, 9 not covered.
- [7. Interval arithmetic and verified computation](#7-interval-arithmetic-and-verified-computation) — 14 entries, 0 covered, 3 partly covered, 11 not covered.
- [8. Nonlinear equations, continuation, and algorithmic differentiation](#8-nonlinear-equations-continuation-and-algorithmic-differentiation) — 16 entries, 1 covered, 1 partly covered, 14 not covered.
- [9. Numerical optimization](#9-numerical-optimization) — 17 entries, 0 covered, 3 partly covered, 14 not covered.
- [10. Polynomial and rational approximation](#10-polynomial-and-rational-approximation) — 17 entries, 0 covered, 4 partly covered, 13 not covered.
- [11. Splines, kernels and wavelets](#11-splines-kernels-and-wavelets) — 18 entries, 0 covered, 1 partly covered, 17 not covered.
- [12. Orthogonal polynomials and numerical quadrature](#12-orthogonal-polynomials-and-numerical-quadrature) — 16 entries, 0 covered, 1 partly covered, 15 not covered.
- [13. Discrete Fourier analysis and sparse recovery](#13-discrete-fourier-analysis-and-sparse-recovery) — 17 entries, 0 covered, 3 partly covered, 14 not covered.
- [14. Initial value problems: one-step and multistep methods](#14-initial-value-problems-one-step-and-multistep-methods) — 16 entries, 0 covered, 3 partly covered, 13 not covered.
- [15. Stiff problems, differential-algebraic equations, and geometric integration](#15-stiff-problems-differential-algebraic-equations-and-geometric-integration) — 17 entries, 0 covered, 1 partly covered, 16 not covered.
- [16. Finite difference methods for differential equations](#16-finite-difference-methods-for-differential-equations) — 15 entries, 0 covered, 0 partly covered, 15 not covered.
- [17. Hyperbolic conservation laws and finite volume methods](#17-hyperbolic-conservation-laws-and-finite-volume-methods) — 15 entries, 0 covered, 0 partly covered, 15 not covered.
- [18. Galerkin and finite element methods for elliptic problems](#18-galerkin-and-finite-element-methods-for-elliptic-problems) — 22 entries, 0 covered, 4 partly covered, 18 not covered.
- [19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation](#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation) — 20 entries, 1 covered, 2 partly covered, 17 not covered.
- [20. Multilevel and domain decomposition methods](#20-multilevel-and-domain-decomposition-methods) — 11 entries, 0 covered, 0 partly covered, 11 not covered.
- [21. Integral equations and boundary element methods](#21-integral-equations-and-boundary-element-methods) — 16 entries, 0 covered, 4 partly covered, 12 not covered.
- [22. Inverse problems and regularization](#22-inverse-problems-and-regularization) — 16 entries, 0 covered, 4 partly covered, 12 not covered.
- [23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations](#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations) — 16 entries, 0 covered, 3 partly covered, 13 not covered.
- [24. High-dimensional approximation, uncertainty quantification, and model reduction](#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction) — 17 entries, 0 covered, 2 partly covered, 15 not covered.

## 1. Floating-point arithmetic and rounding error analysis

[Mathematical scope](SYNOPSIS.md#1-floating-point-arithmetic-and-rounding-error-analysis).

### Mathlib

The experimental rational semantics for a binary floating-point format defines finite encodings, validity, conversion to rationals, and arithmetic operations. The format uses fixed exponent and precision parameters. The API is a starting point for the spacing and correct-rounding statements of 1.1–1.5. [`ValidFinite`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/FP/Basic.lean#L65), [`toRat`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/FP/Basic.lean#L81)

The interval evaluator in §7 also represents dyadic endpoints. It targets interval inclusion and supplies infrastructure for comparing exact and computed values. [`Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Init.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Init.lean)

### TauCeti

This section has no floating-point error theorem in the audited source.

### Open results

The format-independent relative-error theorem, Sterbenz exactness, error-free transformations, accumulated rounding factors, and algorithm-level backward errors remain open. The distinction between exact real sums and computed reduction trees matters for 1.9–1.13. The a posteriori bound in 1.9 uses the inverse relative-error model.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — None.
- **Not covered** — 1.1–1.13.

## 2. Conditioning and matrix perturbation theory

[Mathematical scope](SYNOPSIS.md#2-conditioning-and-matrix-perturbation-theory).

### Mathlib

For 2.3, the norm-small perturbation criterion follows from the normed-ring construction of a unit within inverse-norm distance of a unit. The rank-one minimum and its identification with the smallest singular value remain to be matched. The normed ring API gives a first-order inverse expansion and is useful for 2.2, whose claim is the exact relative condition number. [`add`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Ring/Units.lean#L47), [`inverse_add_norm_diff_second_order`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Ring/Units.lean#L176)

For 2.12, the row-disc inclusion holds for eigenvalues of a matrix over a normed field. Exact counting with multiplicities for a separated component and the combined row/column formulation remain open. [`eigenvalue_mem_ball`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L30)

### TauCeti

For 2.7, the ordered eigenvalues of a symmetric endomorphism satisfy the max–min form of Courant–Fischer over unit vectors in subspaces, including a witness attaining the outer supremum. The dual min–max form is obtained mathematically by negating the operator. For 2.8, the ordered Hermitian eigenvalues satisfy both index forms of Weyl's inequality and the spectral-norm perturbation bound. Positive semidefinite monotonicity is their specialization using the sign of the least eigenvalue of the perturbation. For 2.9, both interlacing inequalities hold for an arbitrary principal-submatrix embedding. The library uses decreasing indices starting at zero. [`eigenvalues_eq_iSup_iInf_re_inner`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean#L259), [`IsHermitian.eigenvalues₀_add_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Eigenvalues/Basic.lean#L207), [`IsHermitian.le_eigenvalues₀_add`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Eigenvalues/Basic.lean#L221), [`IsHermitian.abs_eigenvalues₀_sub_le_norm`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Eigenvalues/Basic.lean#L103), [`eigenvalues₀_submatrix_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Eigenvalues/Interlacing.lean#L58), [`eigenvalues₀_le_eigenvalues₀_submatrix`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Eigenvalues/Interlacing.lean#L71)

For 2.10, the spectral-norm bound holds for rectangular linear maps and the Frobenius inequality holds for matrices. The general unitarily invariant norm statement and column-deletion interlacing remain open. For 2.11, the ordered Hermitian inequality is proved. The general matching assertion for complex normal matrices remains open. [`abs_singularValues_sub_singularValues_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean#L106), [`sum_sq_singularValues_toEuclideanLin_sub_le_frobenius_norm_sub_sq`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/HoffmanWielandt.lean#L68), [`IsHermitian.sum_sq_eigenvalues₀_sub_le_frobenius_norm_sub_sq`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/HoffmanWielandt.lean#L86)

For 2.16, the Hermitian resolvent norm is the reciprocal distance to the spectrum in the Euclidean operator norm, which gives the disc description for that special case. For 2.17, the interval/exterior gap gives the directed sine bound with numerator the whole perturbation in every unitarily invariant seminorm. The residual theorem applied with the orthonormal frame and its compressed first operator gives the sharper numerator. For the two norms in the synopsis, a frame identifies the directed sine map with the diagonal principal-sine matrix up to isometries and zero padding. [`l2_opNorm_inv_sub_smul_one`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Resolvent/Basic.lean#L140), [`mul_map_starProjection_comp_le_map_sylvester_apply`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Basic.lean#L89), [`mul_map_starProjection_comp_starProjection_le_map_sub`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Basic.lean#L135), [`TauCeti/Analysis/InnerProductSpace/Projection/PrincipalAngle.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Projection/PrincipalAngle.lean)

### Open results

The available singular-subspace perturbation results for 2.18 use a gap in the squared Gram spectrum and a numerator with a factor involving both matrix norms. The Yu–Wang–Samworth bound has a different gap and scaling. These are ingredients for Wedin's leading singular-subspace bound. Sharp linear-system and least-squares condition numbers, normwise and componentwise backward errors, Bauer–Fike, and the pseudospectral perturbation and connected-component descriptions are other targets. [`mul_norm_sinThetaMap_rightSingularSubspace_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/SingularSubspace/Perturbation.lean#L45), [`mul_norm_sinThetaMap_leftSingularSubspace_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/SingularSubspace/Perturbation.lean#L83), [`TauCeti/Analysis/InnerProductSpace/YuWangSamworth/SingularVectors.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/YuWangSamworth/SingularVectors.lean)

**Synopsis entries.**

- **Covered** — 2.8–2.9, 2.17.
- **Partly covered** — 2.3, 2.7, 2.10–2.12, 2.16.
- **Not covered** — 2.1–2.2, 2.4–2.6, 2.13–2.15, 2.18.

## 3. Direct methods for linear systems and least squares

[Mathematical scope](SYNOPSIS.md#3-direct-methods-for-linear-systems-and-least-squares).

### Mathlib

Positive matrices have an LDL factorization in terms of Gram–Schmidt, and projection onto a complete inner-product subspace gives the closest vector. These are the basic exact-arithmetic constructions for Cholesky and least squares. Matrix inversion, determinant products and the block elimination identities of the Schur complement support LU. [`Mathlib/Analysis/Matrix/LDL.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/LDL.lean), [`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean), [`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean)

### TauCeti

For 3.7, a real positive-definite matrix has a lower triangular Cholesky factor with positive diagonal, with reconstruction and injectivity of the factorization. The complex LDL result gives an upper triangular factor with positive diagonal in the adjoint-product convention, which gives the existence assertion in 3.7. For 3.9, the general linear group API gives a unitary/upper-triangular factorization for square invertible matrices. Rectangular and rank-deficient QR, and its normalization and uniqueness as a reduced factorization, extend beyond that statement. [`cholesky`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/Cholesky/Basic.lean#L92), [`cholesky_mul_transpose`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/Cholesky/Basic.lean#L106), [`cholesky_injective`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/Cholesky/Basic.lean#L145), [`Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/LDL.lean#L78), [`exists_mem_upperTriangularGroup_toUnits_mul_eq`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/QR.lean#L47)

For 3.11, the projection theorem gives the unique closest point in the range of the finite-dimensional map, hence a fitted value for the least-squares problem. The normal equations and the reduced-QR solution formula require additional development. For 3.12, the Moore–Penrose API proves existence and uniqueness for the four Penrose identities. Its construction expands in the right singular basis with inverse squared singular values applied to inner products with the images of that basis. It also gives the involution and adjoint identities. The least-norm characterization is additional. [`moorePenroseInverse_apply`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L216), [`isMoorePenroseInverse_moorePenroseInverse`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L231), [`isMoorePenroseInverse_iff_eq_moorePenroseInverse`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L268), [`moorePenroseInverse_moorePenroseInverse`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L291), [`moorePenroseInverse_adjoint`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L298)

### Open results

The pivoting theorem, growth factors, floating-point backward errors, mixed-precision recurrence, sparse fill paths and elimination tree are gaps. Algebraic row reduction provides exact row operations and pivoting for echelon form. [`TauCeti/LinearAlgebra/Matrix/Echelon/RowReduce.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/Echelon/RowReduce.lean)

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 3.7, 3.9, 3.11–3.12.
- **Not covered** — 3.1–3.6, 3.8, 3.10, 3.13–3.16.

## 4. Eigenvalue and singular value computations

[Mathematical scope](SYNOPSIS.md#4-eigenvalue-and-singular-value-computations).

### Mathlib

For 4.2, the spectral theorem provides unitary diagonalization with real eigenvalues for Hermitian matrices, including real symmetric matrices via the real instance. For 4.3, the singular values of a finite-dimensional linear map are the ordered square roots from the adjoint product, with their positive support equal to the rank. The Hessenberg API records characteristic-polynomial preservation under a similarity certificate and implements algebraic reductions for concrete matrices. It supplies ingredients for 4.8, which specifies a unitary reduction and shifted QR iteration. [`spectral_theorem`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/Spectrum.lean#L143), [`hasEigenvalue_adjoint_comp_self_sq_singularValues`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/SingularValues.lean#L137), [`card_support_singularValues`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/SingularValues.lean#L174), [`Similarity.charpoly_eq`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Hessenberg/Similarity.lean#L53), [`Mathlib/Tactic/Hessenberg/Reduce.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Tactic/Hessenberg/Reduce.lean)

### TauCeti

For 4.3, there is a unitary SVD for square matrices and an orthonormal rank-one expansion for rectangular linear maps. The Hermitian dilation and its eigenvectors are available on a product of inner-product spaces. The synopsis bundles this with rectangular full bases, both norm identities and the corresponding sorted-square assertions. For 4.12, ordered eigenvalues of a compression along an isometry satisfy the two interlacing bounds. [`exists_unitary_mul_diagonal_mul_unitary`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/SingularValues.lean#L74), [`exists_orthonormal_eq_sum_singularValues_smul_rankOne`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/SingularValues.lean#L742), [`TauCeti/Analysis/InnerProductSpace/HermitianDilation/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/HermitianDilation/Basic.lean), [`eigenvalues_le_eigenvalues_of_isometry`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean#L584), [`eigenvalues_le_eigenvalues_of_isometry'`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean#L599)

For 4.19, the scalar polynomial companion pencil has the determinant and invertibility relation. The statement in the synopsis uses block coefficients and also identifies eigenspaces and left eigenvectors. [`companionPencil`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/CompanionPencil.lean#L68), [`companionPencil_eq_mul`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/CompanionPencil.lean#L111), [`isUnit_companionPencil_iff`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/CompanionPencil.lean#L135)

### Open results

Schur form with prescribed order, the normality criterion using the Frobenius norm, QR iteration, Jacobi sweeps, Arnoldi/Lanczos recurrences and bounds, Golub–Kahan, and the nonlinear eigenvalue and Keldysh theory remain gaps. The Rayleigh–Ritz source also proves residual compression estimates for reducing subspaces, useful for bounding approximate eigenvectors. [`TauCeti/Analysis/InnerProductSpace/RayleighRitz.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/RayleighRitz.lean)

**Synopsis entries.**

- **Covered** — 4.12.
- **Partly covered** — 4.2–4.3, 4.19.
- **Not covered** — 4.1, 4.4–4.11, 4.13–4.18.

## 5. Iterative methods for linear systems

[Mathematical scope](SYNOPSIS.md#5-iterative-methods-for-linear-systems).

### Mathlib

For 5.1, the Gelfand formula proves the spectral-radius limit for powers in a complex Banach algebra. Taking the matrix algebra with an operator norm gives the corresponding norm limit in the synopsis. For 5.3, strict row or column diagonal dominance gives a nonzero determinant. Neither entry's iteration formula is supplied here. Mathlib's irreducibility predicate uses strong connectivity of the nonzero digraph. [`pow_norm_pow_one_div_tendsto_nhds_spectralRadius`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean#L139), [`det_ne_zero_of_sum_row_lt_diag`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L63), [`det_ne_zero_of_sum_col_lt_diag`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L73), [`IsIrreducible`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean#L83)

### TauCeti

For 5.2, a nonnegative irreducible real matrix has a strictly positive eigenvector at the spectral radius. Its characteristic-root multiplicity there is one. The positive, nonnegative and primitive versions and comparison inequalities have separate files. The synopsis also includes the block reducibility characterization for complex matrices and strict comparison under entrywise increase. [`IsIrreducible.exists_mulVec_eq_smul`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Irreducible.lean#L158), [`IsIrreducible.rootMultiplicity_charpoly_eq_one`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Irreducible.lean#L247), [`TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Nonnegative.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Nonnegative.lean)

### Open results

Nonsingular M-matrix characterizations, regular splitting comparisons, the Stein–Rosenberg theorem, the SOR criterion on its relaxation interval, CG, GMRES including its field-of-values bound, and MINRES remain gaps. The finite-dimensional spectral theory and Chebyshev polynomial API are reusable for the minimax polynomial bounds. [`Mathlib/RingTheory/Polynomial/Chebyshev.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Polynomial/Chebyshev.lean)

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 5.1–5.3.
- **Not covered** — 5.4–5.18.

## 6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation

[Mathematical scope](SYNOPSIS.md#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation).

### Mathlib

For 6.1, continuous functional calculus gives evaluation on a Hermitian spectral decomposition. This covers the self-adjoint diagonal case with real-valued functions on the spectrum. For 6.2, the ring exponential is available as a convergent series on the entire complete normed algebra. General Jordan-block convergence on the scalar series boundary and the Dunford contour estimate are separate. [`Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean), [`exp_eq_tsum`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L164)

### TauCeti

For 6.1–6.3, there is a finite-spectrum evaluation API, a matrix logarithm in a neighborhood of the identity, and positive semidefinite matrix square roots. For 6.4, the noncommutative Banach-algebra exponential has the insertion series as its Fréchet derivative, giving the derivative-series formula for that choice of function. The general primary-function derivative and condition number remain to be formalized. [`TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/FiniteSpectrum.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/FiniteSpectrum.lean), [`TauCeti/Analysis/Matrix/Exponential/Log.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Exponential/Log.lean), [`TauCeti/Analysis/Matrix/Sqrt.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Sqrt.lean), [`hasFDerivAt_exp`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/SpecialFunctions/Exponential.lean#L267), [`expFDeriv_apply`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/SpecialFunctions/Exponential.lean#L261), [`exp_fromBlocks_zero₂₁`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/Exponential/Block.lean#L128)

For 6.6, the general disjoint-spectrum result gives uniqueness for bounded operators via the intertwining equation. For self-adjoint operators, the Sylvester file also proves invertibility and solves the equation via the spectral data. For 6.7, the positive Sylvester equivalence gives the definite self-adjoint coefficient case after a change of sign, including a self-adjoint solution for self-adjoint data. The nonnormal stability condition and the improper-integral representations need further results. [`eq_zero_of_comp_eq_comp_of_disjoint_spectrum`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/LinearPMap/Rosenblum.lean#L114), [`TauCeti/Analysis/InnerProductSpace/Sylvester.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Sylvester.lean), [`positiveSylvesterEquiv`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Positive/Sylvester.lean#L77), [`isSelfAdjoint_positiveSylvesterEquiv_symm_iff`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Positive/Sylvester.lean#L134)

For 6.8, the operator-norm infimum over rank-bounded maps equals the corresponding singular value, and the approximation-number API proves attainment for compact Hilbert-space operators. The synopsis also requires the Frobenius-norm optimum. [`singularValue_eq_linearMap_singularValues`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean#L65), [`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Attainment.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Attainment.lean)

### Open results

Neither the matrix Padé scaling-and-squaring error theory nor the randomized range finder, Gaussian embedding and Nyström performance statements are matched. Tensor products are available, but border-rank nonclosedness, HOSVD error, tensor-train ranks, admissibility and hierarchical low-rank costs remain gaps.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 6.1–6.4, 6.6–6.8.
- **Not covered** — 6.5, 6.9–6.16.

## 7. Interval arithmetic and verified computation

[Mathematical scope](SYNOPSIS.md#7-interval-arithmetic-and-verified-computation).

### Mathlib

For 7.1–7.2, there is a generic order-interval arithmetic API, including arithmetic on endpoints and monotonicity in the interval order. The tactic inclusion API implements verified operations on interval representations, including dyadic enclosures of elementary expressions. It is evidence for enclosure of those operations and a starting point for the general expression and outward-rounding model. [`Mathlib/Algebra/Order/Interval/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Order/Interval/Basic.lean), [`Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Init.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Init.lean)

For 7.11, if the spectral radius of an algebra element is less than one, then subtracting it from the unit gives an invertible element. In the matrix setting, take the element to be the residual matrix to get invertibility of the product and hence of the two factors. The combined residual estimate for an approximate solution is a separate calculation. [`isUnit_one_sub_smul_of_lt_inv_radius`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L391)

### TauCeti

Weak elliptic problems have an existence and continuous-dependence API using coercive forms. This provides a continuous analytic framework for 7.13–7.14. [`existsUnique_isWeakSolutionDirichlet`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/DirichletProblem.lean#L407)

### Open results

Interval Newton and Krawczyk enclosures, interval-matrix interior inclusion, directed-rounding nonsingularity certificates, and the two-dimensional constructive finite-element constants remain open. General operator estimates leave the dependency overestimation problem and the interval expression semantics to be developed.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 7.1–7.2, 7.11.
- **Not covered** — 7.3–7.10, 7.12–7.14.

## 8. Nonlinear equations, continuation, and algorithmic differentiation

[Mathematical scope](SYNOPSIS.md#8-nonlinear-equations-continuation-and-algorithmic-differentiation).

### Mathlib

For 8.1, a contraction on a complete nonempty metric space has a unique fixed point, its iterates converge, and Mathlib has the a priori and a posteriori bounds. For the a posteriori estimate in terms of the preceding step, combine the library's next-step form with contraction. The estimate by the preceding iterate is the Lipschitz bound with the fixed point substituted. The closed-subset Banach-space formulation is the complete subtype instance. [`fixedPoint_unique`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Contracting.lean#L283), [`tendsto_iterate_fixedPoint`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Contracting.lean#L302), [`apriori_dist_iterate_fixedPoint_le`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Contracting.lean#L295), [`aposteriori_dist_iterate_fixedPoint_le`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Contracting.lean#L290), [`dist_le_mul`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/Contracting.lean#L246)

For 8.12, the implicit function theorem gives the local equation graph and its derivative when the relevant partial derivative is invertible. The subsection's continuation along a parametrized solution curve still needs its specific tangent normalization and coordinate switching. The intermediate value theorem and the Fréchet chain rule are ingredients for 8.3 and 8.14. [`leftFun_eq_iff_implicitFunction`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/Implicit.lean#L211), [`hasStrictFDerivAt_implicitFunction`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/Implicit.lean#L253), [`Mathlib/Topology/Order/IntermediateValue.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Order/IntermediateValue.lean), [`Mathlib/Analysis/Calculus/FDeriv/Comp.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/FDeriv/Comp.lean)

### TauCeti

The general ODE and calculus developments give reusable fixed-point and differentiability estimates. They leave the numerical Newton variants, secant and Broyden iterations, step control and differentiation programs to be developed.

### Open results

The important algorithmic targets are the Newton–Kantorovich enclosure and convergence bounds with the closed majorant ball in the domain, inexact and damped Newton, predictor–corrector continuation, and forward/reverse accumulation and its operation counts. The bisection algorithm still needs a proved interval invariant and convergence rate.

**Synopsis entries.**

- **Covered** — 8.1.
- **Partly covered** — 8.12.
- **Not covered** — 8.2–8.11, 8.13–8.16.

## 9. Numerical optimization

[Mathematical scope](SYNOPSIS.md#9-numerical-optimization).

### Mathlib

For 9.1, the vanishing Fréchet derivative of a differentiable local extremum is formalized, as is the one-dimensional positive second-derivative test. For 9.2, the equality-constrained multiplier theorem gives a nontrivial linear dependence between the objective derivative and the constraint derivatives. Under linear independence of the latter the multiplier of the objective is nonzero, so this is the equality-only part of the first-order KKT condition. The inequality signs, complementarity and constrained second-order tests are additional. [`IsLocalMin.fderiv_eq_zero`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean#L181), [`isLocalMin_of_deriv_deriv_pos`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/DerivativeTest.lean#L404), [`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/LagrangeMultipliers.lean#L107)

### TauCeti

For 9.16, positive matrix scaling has a Birkhoff projective contraction bound. The Sinkhorn source gives one-step and iteration bounds for the alternating updates, convergence of the plans given a positive diagonal scaling, and quantitative marginal error bounds. The relative-entropy minimum with prescribed positive marginals is represented by a diagonal scaling. For a marginal with zero entries, a positive scaling of an everywhere positive Gibbs kernel cannot have the specified zero row or column. The positive-scaling clause of the synopsis needs strictly positive marginals or a restriction to their supports. [`TauCeti/Data/Matrix/BirkhoffContraction.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/BirkhoffContraction.lean), [`hilbertProjectiveDist_sinkhornStep_iterate_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/Sinkhorn/Basic.lean#L214), [`tendsto_sinkhornPlan_iterate`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/Sinkhorn/Basic.lean#L483), [`abs_sum_sinkhornPlan_iterate_apply_sub_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/Sinkhorn/Rate.lean#L256), [`exists_sinkhorn_scaling`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/Scaling/Basic.lean#L974), [`relEntropy_minOn_iff_exists_isDiagonalScaling`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Matrix/Scaling/Basic.lean#L1120), [`TauCeti/MeasureTheory/OptimalTransport/Entropic/SchroedingerSystem.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/MeasureTheory/OptimalTransport/Entropic/SchroedingerSystem.lean)

The Riemannian gradient is defined with its metric pairing, derivative and norm identities. It supports 9.15. [`mgradient`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Manifold/Riemannian/Gradient/Basic.lean#L78), [`inner_mgradient`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Manifold/Riemannian/Gradient/Basic.lean#L90)

### Open results

Wolfe/Zoutendijk, quasi-Newton and trust-region convergence, gradient and proximal complexity, fixed-point iteration for maximally monotone operators, self-concordant path following, discrete transport duality and the control/Riccati assertion remain formalization targets.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 9.1–9.2, 9.16.
- **Not covered** — 9.3–9.15, 9.17.

## 10. Polynomial and rational approximation

[Mathematical scope](SYNOPSIS.md#10-polynomial-and-rational-approximation).

### Mathlib

For 10.1, uniform approximation by real polynomials on a compact interval and density of the trigonometric-polynomial span on an additive circle are proved. The finite-dimensional best-approximation claim and its degree-indexed specialization are additional. [`exists_polynomial_near_of_continuousOn`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/ContinuousMap/Weierstrass.lean#L111), [`span_fourier_closure_eq_top`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L243)

For 10.4, the Chebyshev leading coefficient, alternating values at extrema, and sharp leading-coefficient inequality on the unit ball of the uniform norm are available. The equality theorem in the extremal file for the leading coefficient is stated in degrees at least two. For 10.5, the evaluation, degree and uniqueness of the Lagrange interpolant hold over a field. For 10.12, the normalized second barycentric formula with arbitrary distinct nodes and the nonzero denominator are proved. The derivative remainder and the explicit Chebyshev-node simplification need further proofs. [`leadingCoeff_T`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Polynomial/Chebyshev.lean#L222), [`eval_T_real_node`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean#L63), [`leadingCoeff_le_of_forall_abs_le_one`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean#L201), [`leadingCoeff_eq_iff_of_forall_abs_le_one`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean#L220), [`eval_interpolate_at_node`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean#L318), [`degree_interpolate_lt`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean#L335), [`eq_interpolate`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean#L361), [`eval_interpolate_not_at_node'`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean#L693), [`sum_nodalWeight_mul_inv_sub_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean#L686)

### TauCeti

Hermite interpolation gives existence and uniqueness for specified jets at finitely many distinct nodes. The weighted Chebyshev development provides orthogonal expansions and Parseval in weighted $L^2$. These are ingredients for the rational interpolation and Chebyshev approximation sections. [`TauCeti/LinearAlgebra/HermiteInterpolation.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/LinearAlgebra/HermiteInterpolation.lean), [`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean)

### Open results

The general Haar-space and equioscillation theorems, Lebesgue-constant growth, Jackson and inverse estimates, Bernstein-ellipse convergence and the Padé and rational approximation theorems remain open. The polynomial extremal API also provides endpoint derivative bounds, related to the inverse-estimate discussion. [`eval_iterate_derivative_le_of_forall_abs_le_one`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean#L283)

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 10.1, 10.4–10.5, 10.12.
- **Not covered** — 10.2–10.3, 10.6–10.11, 10.13–10.17.

## 11. Splines, kernels and wavelets

[Mathematical scope](SYNOPSIS.md#11-splines-kernels-and-wavelets).

### Mathlib

Mathlib supplies reproducing-kernel Hilbert spaces with bounded scalar evaluation and canonical reproducing kernels. This supports the native-space and power-function constructions. [`Mathlib/Analysis/InnerProductSpace/Reproducing.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Reproducing.lean)

### TauCeti

For 11.9, Bochner's theorem gives a finite positive representing measure for a continuous positive-definite function on Euclidean space, with uniqueness, and the integrable positive-definite case has a nonnegative Fourier transform. The library uses positive definite for the nonstrict condition. It also supplies Gaussian examples and Schoenberg kernels. The strict condition on pairwise distinct sites, including the open-support implication and the full strict integrable characterization, is additional. [`bochner`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Bochner/BochnerTheorem.lean#L243), [`TauCeti/Analysis/Bochner/Fourier/Nonneg.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Bochner/Fourier/Nonneg.lean), [`TauCeti/Analysis/Bochner/Gaussian/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Bochner/Gaussian/Basic.lean), [`TauCeti/Analysis/PositiveDefinite/Kernel/Schoenberg.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PositiveDefinite/Kernel/Schoenberg.lean)

The library develops Besov spaces through Littlewood–Paley decompositions and has a Haar basis development for $L^p$. These provide pieces of the wavelet setting. [`TauCeti/Analysis/FunctionalSpaces/BesovSpace/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/FunctionalSpaces/BesovSpace/Basic.lean), [`TauCeti/MeasureTheory/Function/Lp/HaarBasis/Unconditional.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/MeasureTheory/Function/Lp/HaarBasis/Unconditional.lean)

### Open results

Spline interpolation, the Curry–Schoenberg and Schoenberg–Whitney theorems, interpolation and quasi-interpolation estimates, Wendland functions, conditionally positive-definite interpolation, power-function estimates, and Daubechies and nonlinear wavelet approximation remain open.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 11.9.
- **Not covered** — 11.1–11.8, 11.10–11.18.

## 12. Orthogonal polynomials and numerical quadrature

[Mathematical scope](SYNOPSIS.md#12-orthogonal-polynomials-and-numerical-quadrature).

### Mathlib

Chebyshev orthogonality and the Rodrigues-style definition of shifted Legendre polynomials supply examples for the general orthogonal polynomial theory. The composite trapezoidal rule has the rigorous second-derivative supremum error bound and an integral-error derivation. The Newton–Cotes derivative-at-an-interior-point error in 12.11 and the analytic estimates in 12.14 have different conclusions. [`Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean), [`shiftedLegendre`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean#L40), [`trapezoidal_error_le_of_c2`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean#L252)

### TauCeti

For 12.12, Euler–Maclaurin on integer endpoints gives the endpoint corrections and a remainder in integral form with a periodic Bernoulli function. The synopsis uses an arbitrary mesh and a derivative-at-an-interior-point remainder plus a periodic error bound. The library also supplies weighted orthogonal bases and the Chebyshev weighted measure. [`sum_Icc_eq_eulerMaclaurin`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Asymptotics/Sum/EulerMaclaurin.lean#L219), [`TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean), [`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Measure.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Measure.lean)

### Open results

The Hankel determinant criterion, Favard, zeros and interlacing for general orthogonal polynomials, Christoffel–Darboux, Gauss and related rules including the Golub–Welsch computation, Peano kernels, Romberg, and exponential quadrature estimates are the main missing results.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 12.12.
- **Not covered** — 12.1–12.11, 12.13–12.16.

## 13. Discrete Fourier analysis and sparse recovery

[Mathematical scope](SYNOPSIS.md#13-discrete-fourier-analysis-and-sparse-recovery).

### Mathlib

For 13.1, finite character orthogonality and the cyclic DFT and its inverse are available as linear maps on $\mathbb Z/N\mathbb Z$. The synopsis packages these as matrix identities and unitarity with Parseval normalization. For 13.3, circulants are closed under multiplication and commute, including the integer-modulo-index convention. The simultaneous Fourier eigenbasis and the explicit eigenvalues are additional. [`Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean), [`dft_apply`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/ZMod.lean#L106), [`invDFT_apply`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/ZMod.lean#L114), [`dft_dft`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/ZMod.lean#L176), [`Fin.circulant_mul`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Circulant.lean#L123), [`Fin.circulant_mul_comm`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Circulant.lean#L140)

For 13.7, Poisson summation gives the pointwise periodization/Fourier-series identity under summability on compact sets of translating norms and summability of the Fourier coefficients. Rescaling converts the normalized Fourier convention to period $2\pi$. The full statement of 13.7 also specifies absolute and uniform convergence on the whole line. Continuous Fourier convolution and inversion give ingredients for 13.2 and 13.8. [`Real.tsum_eq_tsum_fourier`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/PoissonSummation.lean#L98), [`fourier_mul_convolution_eq`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/Convolution.lean#L120), [`Mathlib/Analysis/Fourier/Inversion.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/Inversion.lean)

### TauCeti

The cyclic DFT has a divisibility and frequency-restriction API and Poisson summation extends to Euclidean lattices for Schwartz functions. The first result is a tool for algebraic frequency aliasing, while 13.5 concerns sampled values of a continuous function with summable Fourier coefficients. [`dft_comp_natCast_val`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Fourier/ZMod.lean#L78), [`tsum_eq_tsum_dual_fourier`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Fourier/PoissonSummation.lean#L307)

### Open results

The cyclic convolution and shift formulas, FFT factorization and operation count, aliasing and trigonometric-interpolation estimates, Shannon reconstruction, the nonequispaced FFT and Prony error and reconstruction theory remain targets. The Prony Hankel factorization uses a Vandermonde matrix with rows indexed by sample exponents. No one of the compressed-sensing recovery or measurement-complexity results is recorded here.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 13.1, 13.3, 13.7.
- **Not covered** — 13.2, 13.4–13.6, 13.8–13.17.

## 14. Initial value problems: one-step and multistep methods

[Mathematical scope](SYNOPSIS.md#14-initial-value-problems-one-step-and-multistep-methods).

### Mathlib

For 14.1, the local Picard–Lindelöf API treats closed time intervals and state balls, with uniqueness for trajectories on intervals. It proceeds by contraction in a function space. The Euler-polygon convergence statement is extra. For 14.2, the library proves discrete Grönwall bounds in recurrence form, including the general product with an additive forcing. For 14.3, the two approximate-trajectory bound uses right derivatives, a time-dependent set containing both trajectories, and the standard exponential expression. Taking one approximate solution to have zero defect gives the first estimate in the synopsis. The one-sided scalar-product version is additional. [`exists_eq_forall_mem_Icc_hasDerivWithinAt`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/ExistUnique.lean#L57), [`ODE_solution_unique_of_mem_Icc`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/ExistUnique.lean#L252), [`discrete_gronwall_prod_general`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/DiscreteGronwall.lean#L51), [`discrete_gronwall`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/DiscreteGronwall.lean#L80), [`dist_le_of_approx_trajectories_ODE_of_mem`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/Gronwall.lean#L162), [`gronwallBound_of_K_ne_0`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/ODE/Gronwall.lean#L49)

### TauCeti

For 14.1, globally Lipschitz fields with suitable time continuity have a global solution API and uniqueness. For 14.2, the continuous bound is available with a constant leading term and constant coefficient on an interval. The synopsis also allows an integrable coefficient and a nondecreasing leading function. [`globalSolution`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/ODE/GlobalSolution.lean#L208), [`hasDerivAt_globalSolution`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/ODE/GlobalSolution.lean#L230), [`eq_globalSolution`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/ODE/GlobalSolution.lean#L248), [`le_mul_exp_of_le_add_mul_integral`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/ODE/Gronwall.lean#L75)

### Open results

One-step error accumulation, Runge–Kutta stage equations and rooted-tree order conditions, order barriers, collocation and the Dahlquist equivalence theorem, BDF zero-stability, extrapolation and B-series remain gaps. The discrete and continuous Grönwall results are reusable in stability and global error estimates.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 14.1–14.3.
- **Not covered** — 14.4–14.16.

## 15. Stiff problems, differential-algebraic equations, and geometric integration

[Mathematical scope](SYNOPSIS.md#15-stiff-problems-differential-algebraic-equations-and-geometric-integration).

### Mathlib

The normed-algebra exponential and matrix inverse are available. They are supporting ingredients for the stability-function and exponential-integrator formulas. [`Mathlib/Analysis/Normed/Algebra/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/Exponential.lean), [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean)

### TauCeti

For 15.12, Hamiltonian flows on symplectic vector spaces preserve the symplectic form on tangent vectors for a globally Lipschitz Hamiltonian vector field and a twice continuously differentiable Hamiltonian. These give a global smooth case of the time-map theorem. The Lie-group Trotter product limit and exponential derivative results support the splitting analysis in 15.17. [`apply_fderiv_hamiltonianFlow`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Symplectic/Hamiltonian/Flow.lean#L139), [`TauCeti/Geometry/Symplectic/Hamiltonian/TimeDependent.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Symplectic/Hamiltonian/TimeDependent.lean), [`tendsto_lieExp_smul_mul_lieExp_smul_pow`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Lie/Exponential/Trotter.lean#L122)

### Open results

The A-, L-, B- and algebraic-stability comparisons, the Dahlquist and Ehle barriers, DAE index and method results, the finite-step splitting order and commutator expansion, preservation by numerical steps, and long-time modified Hamiltonian estimates remain open.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 15.12.
- **Not covered** — 15.1–15.11, 15.13–15.17.

## 16. Finite difference methods for differential equations

[Mathematical scope](SYNOPSIS.md#16-finite-difference-methods-for-differential-equations).

### Mathlib

The matrix and Banach-space APIs supply relevant ingredients for stability and consistency. In particular, the spectral theorem, spectral-radius formula and norm control of powers are available; the hypothesis in 16.12 is dissipativity of the underlying operator, and the main estimate involves rational functions on a half-plane. [`spectral_theorem`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/Spectrum.lean#L143), [`pow_norm_pow_one_div_tendsto_nhds_spectralRadius`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean#L139)

### TauCeti

Abstract semigroup resolvent power bounds and numerical-range estimates under self-adjoint hypotheses provide context for the stability tools. TauCeti has viscosity sub- and supersolution predicates and continuous weak-solution bridges for the Monge–Ampère equation. This supplies an example of the viscosity notion used in 16.15. [`TauCeti/Analysis/Semigroups/Resolvent/PowerBounds.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Semigroups/Resolvent/PowerBounds.lean), [`isMongeAmpereViscositySolution_of_mongeAmpereMeasure_eq`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Convex/MongeAmpere/Viscosity.lean#L383)

### Open results

The discrete maximum principle and convergence on grids, Lax–Richtmyer equivalence, Fourier amplification and CFL analysis, the Kreiss bound, numerical positivity and the Barles–Souganidis scheme-convergence theorem are missing. They require explicit grid or scheme operators and their approximation hypotheses.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — None.
- **Not covered** — 16.1–16.15.

## 17. Hyperbolic conservation laws and finite volume methods

[Mathematical scope](SYNOPSIS.md#17-hyperbolic-conservation-laws-and-finite-volume-methods).

### Mathlib

The library has Bochner integration, distributions and functions of bounded variation. These provide objects for weak formulations and $L^1$ estimates. [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean), [`Mathlib/Analysis/Distribution/Distribution.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Distribution/Distribution.lean), [`Mathlib/Analysis/BoundedVariation.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/BoundedVariation.lean)

### TauCeti

TauCeti develops distributional derivatives of functions of bounded variation and smooth approximation with convergence in $L^1$ and convergence of total variations. These are useful for compactness and estimates on scalar solutions. [`TauCeti/Analysis/BoundedVariation/WeakDerivative.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/BoundedVariation/WeakDerivative.lean), [`exists_contDiff_hasCompactSupport_strict_approximation`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/BoundedVariation/Approximation.lean#L125)

### Open results

Weak solutions and Rankine–Hugoniot, entropy admissibility and Kružkov well-posedness, the scalar and system Riemann results, and front tracking remain to be formalized. The numerical gaps include conservative consistency, TVD and monotone schemes, error bounds and order barriers, and discrete entropy fluxes.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — None.
- **Not covered** — 17.1–17.15.

## 18. Galerkin and finite element methods for elliptic problems

[Mathematical scope](SYNOPSIS.md#18-galerkin-and-finite-element-methods-for-elliptic-problems).

### Mathlib

For 18.1, the Lax–Milgram construction gives the continuous linear equivalence associated to a coercive bilinear form on a real Hilbert space, including the inverse bound. The Banach-space inf-sup characterization is additional. For 18.3, the orthogonal projection API matches the Hilbert-inner-product special case of the Galerkin solution and its best-approximation property. [`Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean), [`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean)

### TauCeti

For 18.1, the coercivity and compatibility developments extend solvability to weak elliptic problems and to compact perturbations under Gårding hypotheses. For 18.5, the homogeneous Dirichlet Poincaré inequality is available on domains contained in a slab or ball. The mean-subtracted inequality across the stated $p$ range and the full convex-domain constants are additional. [`existsUnique_isWeakSolutionDirichlet_of_subset_slab`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/DirichletProblem.lean#L768), [`existsUnique_forall_apply_eq_of_garding`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Variational/Compatibility.lean#L196), [`W1p.norm_value_le_mul_norm_gradient_of_subset_slab`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean#L102), [`W1p.norm_value_le_mul_norm_gradient_of_subset_ball`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean#L122)

For 18.6, chartwise bounded traces recover the zero-trace subspace of $W^{1,p}$ on a Lipschitz domain. There are also $W^{1,p}$ and higher integer-order Sobolev embedding results. The full trace and multiplicative estimates in 18.6 require more. The kernel of the value trace alone differs from $W^{s,p}_0$ at sufficiently high $s$, since closure of compactly supported smooth functions then also forces derivative traces to vanish. [`W1p.lipschitzChartTrace`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/LipschitzDomain/Trace/Basic.lean#L63), [`W1p.norm_lipschitzChartTrace_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/LipschitzDomain/Trace/Basic.lean#L84), [`W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/LipschitzDomain/Trace/Kernel.lean#L208), [`Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/LipschitzDomain/Wkp/Embedding.lean#L162)

For 18.7, weak solutions and Hessian regularity have developed APIs, including local constant-coefficient estimates and flat-boundary estimates. Those results provide analytic ingredients for the global convex and polygonal boundary value statement. [`TauCeti/Analysis/PDE/Regularity/Hessian/HalfSpace/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Regularity/Hessian/HalfSpace/Basic.lean), [`TauCeti/Analysis/PDE/Regularity/ConstantCoefficientDecay.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Regularity/ConstantCoefficientDecay.lean)

### Open results

Discrete inf-sup and Fortin criteria, Strang bounds, unisolvence and Bramble–Hilbert estimates, interpolation and inverse estimates on meshes, and the method-specific convergence results remain targets. These include the mixed and nonconforming elements, inf-sup stable Stokes pairs, and commuting finite-element de Rham projections.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 18.1, 18.3, 18.5–18.6.
- **Not covered** — 18.2, 18.4, 18.7–18.22.

## 19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation

[Mathematical scope](SYNOPSIS.md#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation).

### Mathlib

For the Fourier estimates in 19.6, the functions on the additive circle have a Fourier Hilbert basis, with an $L^2$ series and Parseval identity. The basis expansion gives ingredients for the inverse, projection and interpolation bounds, whose frequency cutoffs and error constants are specific to numerical approximation. [`fourierBasis`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L409), [`fourierBasis_repr`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L421), [`hasSum_sq_fourierCoeff`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L438)

### TauCeti

For 19.1, there are the continuous representative and integration by parts on the evolution space, weak existence with arbitrary initial value for a measurable bounded Gårding form on a Gelfand triple, uniqueness, and the energy estimate. The trace is surjective by the existence result with arbitrary initial value. Setting the Gårding shift to zero gives the coercive estimate in the synopsis, and the Dirichlet problem supplies the heat-equation instance. For 19.2, existence and uniqueness of a finite-dimensional autonomous Galerkin solution with continuous forcing are proved via the mass operator and global ODE theory. Its mesh-dependent Ritz projection and error estimates are additional. [`toContinuousMap`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/EvolutionSpace/Basic.lean#L344), [`TauCeti/Analysis/Sobolev/EvolutionSpace/IntegrationByParts.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Sobolev/EvolutionSpace/IntegrationByParts.lean), [`exists_hasWeakLineDerivOn_gelfandDual`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Parabolic/Existence.lean#L651), [`HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Parabolic/EnergyEstimate.lean#L128), [`HasWeakLineDerivOn.eqOn_of_gelfandDual`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Parabolic/EnergyEstimate.lean#L238), [`TauCeti/Analysis/PDE/Parabolic/DirichletProblem.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Parabolic/DirichletProblem.lean), [`existsUnique_galerkinSolution`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Parabolic/Galerkin.lean#L97)

For 19.13, the compact solution-operator construction relates the coercive form eigenproblem to reciprocal operator eigenvalues, and the Dirichlet spectrum has a Hilbert basis and a min–max theorem. The abstract synopsis formulates the variational identities for a general pivot inner product and compact solution map. The abstract Gamma-convergence API supplies ingredients for 19.20. [`hasEigenvalue_formSolutionOperator_iff`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Variational/Spectrum.lean#L421), [`exists_hilbertBasis_dirichletEigenvalue`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Spectrum/MinMax.lean#L191), [`isLeast_dirichletEigenvalue`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/PDE/Spectrum/MinMax.lean#L209), [`TauCeti/Topology/Semicontinuity/GammaConvergence.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Topology/Semicontinuity/GammaConvergence.lean)

### Open results

The full Galerkin discretization and error bounds, spectral polynomial rates, approximate eigenspaces and absence of spectral pollution, and the a posteriori and adaptive finite-element results require discretization-specific infrastructure. The present abstract parabolic results are suitable starting points for the time-dependent finite-element theory.

**Synopsis entries.**

- **Covered** — 19.1.
- **Partly covered** — 19.2, 19.13.
- **Not covered** — 19.3–19.12, 19.14–19.20.

## 20. Multilevel and domain decomposition methods

[Mathematical scope](SYNOPSIS.md#20-multilevel-and-domain-decomposition-methods).

### Mathlib

Orthogonal projection, Hermitian spectral analysis and Schur-complement identities are available. In particular, projections and their norm identities support the energy-norm formulation of coarse-grid corrections. [`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean), [`spectral_theorem`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/Spectrum.lean#L143), [`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean)

### TauCeti

TauCeti adds matrix Schur-complement norm and positivity infrastructure. Its variational eigenvalue and operator norm results are useful for analyzing the simultaneous subspace corrections. [`TauCeti/Analysis/Matrix/SchurComplement.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Matrix/SchurComplement.lean), [`eigenvalues_eq_iSup_iInf_re_inner`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean#L259)

### Open results

The smoothing and approximation framework, two-grid, multigrid cycle convergence and complexity, the Xu–Zikatanov identity, additive and multiplicative Schwarz bounds, and the coarse-space and condition-number analyses for FETI-DP and BDDC remain gaps.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — None.
- **Not covered** — 20.1–20.11.

## 21. Integral equations and boundary element methods

[Mathematical scope](SYNOPSIS.md#21-integral-equations-and-boundary-element-methods).

### Mathlib

For 21.1, the Fredholm alternative for compact continuous linear endomorphisms characterizes nonzero spectral values as eigenvalues. The API also gives compactness of the identity exactly in finite dimension over locally compact normed fields. For 21.16, the latter fact and composition of compact maps are ingredients for excluding a bounded inverse on the range. For 21.3, the geometric series in a complete normed ring sums to the inverse of one minus the argument. The normed-ring unit API supplies inversion and perturbation identities. The entries also ask for an explicit perturbed solution bound and the converse on different Banach spaces. [`hasEigenvalue_or_mem_resolventSet`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean#L165), [`hasEigenvalue_iff_mem_spectrum`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean#L222), [`isCompactOperator_id_iff_finiteDimensional`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Operator/Compact/FiniteDimension.lean#L29), [`hasSum_geometric_of_norm_lt_one`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecificLimits/Normed.lean#L476), [`inverse_one_sub`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Ring/Units.lean#L97), [`inverse_add_nth_order`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Ring/Units.lean#L129)

### TauCeti

For 21.1, Riesz theory includes finite-dimensional kernels, closed ranges, countability and the only possible spectral accumulation at zero, while continuous and weakly singular kernel discretizations use more specific hypotheses. For 21.2, the index-zero compact perturbation theorem and dual Fredholm theory give the functional-analytic form with the continuous transpose. The assertion for arbitrary normed dual systems uses a more general pairing. [`IsCompactOperator.finiteDimensional_ker_one_sub`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean#L97), [`IsCompactOperator.isClosed_range_one_sub`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean#L190), [`countable_spectrum`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Compact/Spectrum.lean#L135), [`eq_zero_of_accPt_spectrum`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Compact/Spectrum.lean#L145), [`isFredholm_one_sub`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Fredholm/CompactPerturbation.lean#L103), [`TauCeti/Analysis/Fredholm/Transpose.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Fredholm/Transpose.lean)

For 21.3, the resolvent API has a Neumann expansion and perturbation bounds. The normed-ring development gives the sharp inverse norm bound for a perturbation of the unit and a nearby invertible element. For 21.15, coercive forms plus compact perturbations have a compatibility and existence/uniqueness result, giving the continuous variational part for such forms. The boundary-specific discrete quasi-optimality result needs further work. [`norm_inverse_one_sub_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Ring/Units.lean#L54), [`norm_inverse_add_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Ring/Units.lean#L63), [`hasSum_resolvent`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Resolvent/NeumannSeries.lean#L42), [`ContinuousLinearMap.norm_resolvent_vadd_le`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/Normed/Operator/Resolvent/Perturbation.lean#L95), [`existsUnique_forall_apply_eq_of_garding`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/Variational/Compatibility.lean#L196)

### Open results

The general projection and iterated Galerkin bounds, collectively compact approximation, Nyström and Volterra collocation, and layer-potential jumps, trace-space mapping and boundary-element error results are the main missing pieces. The abstract Fredholm API is useful for these second-kind and variational equations.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 21.1–21.3, 21.15.
- **Not covered** — 21.4–21.14, 21.16.

## 22. Inverse problems and regularization

[Mathematical scope](SYNOPSIS.md#22-inverse-problems-and-regularization).

### Mathlib

For 22.2, finite-dimensional singular values and Hilbert space adjoints support the singular-system discussion. For 22.12, Mathlib gives almost-everywhere absolute continuity of conditional posteriors with a common dominating measure, and a Bayes formula stated in terms of the likelihood kernel's Radon–Nikodym derivative with respect to the output law. In the additive-noise setting the normalization is the output density. At a prescribed observation the formula requires a finite positive normalization, and the conditional law is determined up to output-law null sets. [`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/SingularValues.lean), [`absolutelyContinuous_posterior`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Kernel/Posterior.lean#L158), [`rnDeriv_posterior`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Kernel/Posterior.lean#L266), [`posterior_eq_withDensity`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Kernel/Posterior.lean#L285)

### TauCeti

For 22.2, the compact Hilbert-space singular expansion is a sum of rank-one maps with orthonormal vectors and coefficients the approximation numbers. The synopsis bundles this with the kernel projection and range identities. For 22.4, the Moore–Penrose inverse is constructed for finite-dimensional inner-product spaces in singular coordinates. The closed possibly unbounded operator with its maximal domain and the singular-series formula need further results. [`IsCompactOperator.exists_orthonormal_hasSum_rankOne`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Schmidt.lean#L149), [`moorePenroseInverse`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L211), [`moorePenroseInverse_apply`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean#L216)

For 22.15, Gaussian conditioning yields the mean and Schur-complement covariance updates for one nonsingular linear Gaussian observation on inserting the covariance blocks. A recursive filter with prediction and update across all time steps is additional. [`gaussianCondMean_of_posDef`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean#L87), [`gaussianCondCov_of_posDef`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean#L121), [`condDistrib_multivariateGaussian`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean#L537)

### Open results

The Picard range criterion, regularization and parameter-choice estimates, Tikhonov saturation and discrepancy, Landweber and Bregman estimates remain gaps. The libraries supply the foundations for Bayesian inverse problems but leave the specific stability and MAP analysis, Cameron–Martin full-measure and compact-embedding assertions, and the 3DVAR accuracy theorem open.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 22.2, 22.4, 22.12, 22.15.
- **Not covered** — 22.1, 22.3, 22.5–22.11, 22.13–22.14, 22.16.

## 23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations

[Mathematical scope](SYNOPSIS.md#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations).

### Mathlib

For 23.1, the strong law for iid integrable variables and the iid central limit theorem in variance-one normalization give the two basic limit results. The variance-of-sum API gives the exact mean-square calculation with the centering and scaling identities. The estimator with its sample-variance consistency and Studentized confidence interval is a separate statement. For 23.3, integration against a density gives the change-of-measure identity underlying unbiasedness. The optimal change of law and the variance minimization are additional. [`strong_law_ae`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/StrongLaw.lean#L787), [`tendstoInDistribution_inv_sqrt_mul_sum`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/CentralLimitTheorem.lean#L77), [`IndepFun.variance_sum`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Moments/Variance.lean#L424), [`variance_const_mul`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Moments/Variance.lean#L207), [`integral_withDensity_eq_integral_smul₀`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean#L296)

Markov kernels, product laws and irreducibility support the Monte Carlo setting. [`Mathlib/Probability/Kernel/Irreducible.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Kernel/Irreducible.lean)

### TauCeti

For 23.13, geometric Brownian motion has a lognormal law and real power-moment identities from which the exact second moment is read. The numerical theta-method recursion and its stability region are additional. An Itô integral for Brownian motion is available as stochastic integration infrastructure. [`integral_rpow_geometricBrownianMotion`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/BrownianMotion/Geometric/Basic.lean#L231), [`TauCeti/Probability/BrownianMotion/Integral/Ito/Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/BrownianMotion/Integral/Ito/Basic.lean)

### Open results

Control-variates optimality, Metropolis–Hastings, QMC discrepancy and lattice theory, the multilevel Monte Carlo complexity theorem, general strong SDE well-posedness and the Itô–Taylor and numerical convergence results remain gaps. Langevin discretization bias, particle error uniform in time, and numerical SPDE errors also remain open.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 23.1, 23.3, 23.13.
- **Not covered** — 23.2, 23.4–23.12, 23.14–23.16.

## 24. High-dimensional approximation, uncertainty quantification, and model reduction

[Mathematical scope](SYNOPSIS.md#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction).

### Mathlib

For 24.13, Gaussian measures on real normed spaces are defined by linear images, and Fernique's exponential integrability theorem applies in the separable Banach setting. Gaussian measures on Euclidean spaces are available with prescribed covariance, including degenerate cases through the positive semidefinite matrix interface. This leaves the general trace-class covariance characterization and equivalence and shift formulas in infinite dimension. [`isGaussian_iff_charFunDual_eq`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Distributions/Gaussian/Basic.lean#L170), [`IsGaussian.exists_integrable_exp_sq`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Distributions/Gaussian/Fernique.lean#L162), [`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Probability/Distributions/Gaussian/Multivariate.lean)

### TauCeti

For 24.15, the normalized probabilists' Hermite polynomials on finite products of real standard Gaussian measures form a Hilbert basis. The representation has coefficient formulas and Parseval, and the arbitrary-Gaussian-vector pullback gives a convergent expansion. The synopsis records the unnormalized factorial conventions and adds the explicit mean, variance and finite-projection assertions. [`gaussianHermitePiBasis`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean#L53), [`coeFn_gaussianHermitePiBasis`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean#L70), [`gaussianHermitePiBasis_repr_apply`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Parseval.lean#L69), [`hasSum_gaussianVectorHermite`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Pullback.lean#L116)

Approximation numbers and weighted inner-product machinery give ingredients for POD and other model reduction. The MLP development includes ReLU activation and network maps, which supply objects for the network approximation theorem. [`TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Attainment.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Attainment.lean), [`TauCeti/Geometry/Neuromanifold/Activation.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Neuromanifold/Activation.lean), [`TauCeti/Geometry/Neuromanifold/MLP/Map.lean`](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Geometry/Neuromanifold/MLP/Map.lean)

### Open results

The sparse-grid and tractability theory, weak greedy width bounds, parametric elliptic approximability, POD and empirical interpolation, balanced truncation and transfer-function interpolation remain open. Compact covariance operators, spectral expansions and Gaussian products support Karhunen–Loève and stochastic Galerkin. The numerical error estimates and the stated deep ReLU approximation rates require additional theorems.

**Synopsis entries.**

- **Covered** — None.
- **Partly covered** — 24.13, 24.15.
- **Not covered** — 24.1–24.12, 24.14, 24.16–24.17.

## Principal gaps

- **Finite-precision contract and verified computation.** The arithmetic
  model in §1 and exact interval operations in §7 are common prerequisites
  for error-free transforms, residual tests, and backward-error proofs for
  factorizations and iterative refinement in §§2–3.
- **Exact numerical linear algebra.** The spectral and projection results
  in §§2–6 give a basis for CG and GMRES, perturbation of singular subspaces,
  and orthogonality and residual relations for Krylov eigenvalue methods.
  Several of these targets require only finite-dimensional exact arithmetic.
- **Approximation and quadrature.** The interpolation and orthogonality
  APIs provide starting points for the Lagrange remainder, positive
  quadrature, and the Jacobi-matrix treatment of Gauss nodes and weights
  in §§10–12. In §13, finite character orthogonality and the DFT can support
  cyclic convolution, Fourier-matrix diagonalization, and FFT correctness.
- **Differential and integral discretizations.** Abstract continuous
  well-posedness in §§14, 18–19, and 21 can be reused once the discrete
  operators and comparison maps are in place. These include time-stepping
  schemes, grids and finite-element spaces, projections for second-kind
  equations, and the ingredients of adaptive convergence.
- **Inverse problems and stochastic approximation.** The compact spectral
  and probability APIs support regularization, randomized integration,
  Gaussian-series methods, and numerical SDE analysis. The error and
  complexity statements depend on the corresponding estimators, schemes,
  and regularization or discretization parameters in §§22–24.
