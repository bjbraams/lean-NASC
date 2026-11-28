# lean-NASC code review — 27 November 2026

This review covers the Lean library `NASC/` (34 files, 8352 lines, 548 declarations, about 245
`sorry`) in the working tree at commit 8efdbf7. It follows [AGENTS.md](AGENTS.md) and the
shared rules, and answers the owner's standing questions. No Lean source was edited. The
detailed findings, with file:line references, the checks run and the proposed fixes, are in four
parts:

- [review/code/part1.md](review/code/part1.md): FloatingPoint, Conditioning, DirectMethods,
  EigenvalueMethods, IterativeMethods.
- [review/code/part2.md](review/code/part2.md): VerifiedComputation, NonlinearEquations,
  Optimization, MatrixFunctions, LowRankApproximation, Approximation.
- [review/code/part3.md](review/code/part3.md): DiscreteFourier, Quadrature, SplinesAndKernels,
  Wavelets, SparseRecovery, InitialValueProblems, StiffAndGeometric, FiniteDifferences,
  ConservationLaws, NeuralApproximation, GaussianApproximation.
- [review/code/part4.md](review/code/part4.md): Galerkin, FiniteElements, TimeDependentGalerkin,
  VariationalEigenproblems, Multilevel, IntegralEquations, BoundaryElements, Regularization,
  BayesianInverseProblems, MonteCarlo, StochasticEquations, ModelReduction.

Finding IDs are `<part>-<kind><n>`: G generality, H hypotheses (including false or vacuous
statements), N names, D documentation, S namespaces, modules and organization, P proofs and
reuse. Each finding says whether it was checked in Lean (scratch files elaborated against the
current oleans, in `review/code/work/`), checked numerically, or judged by reading.

## Method

Checks against the existing oleans (all newer than their sources): `#print axioms` on every
proved theorem, `#lint only docBlame unusedArguments synTaut simpNF`, `#min_imports`, small
counterexamples in Lean, and numerical tests in python of the statements that looked risky.
Every complete proof depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Answers to the questions

**Most general appropriate setting?** Mostly adequate for an early library, with recurring
narrowness: matrix statements fixed to `ℂ` where `RCLike 𝕜` works (1-G2, 2-G1, 3-G1), a
derivative result over `ℝ` that proves verbatim over any nontrivially normed field (1-G1), an
eigenvector theorem that needs neither an inner product nor `ℝ` (4-G1), regularization limits
that need only normed spaces and any filter (4-G2), boxes fixed to `Fin n` (2-G3).

**Hypotheses appropriate?** Four statements are false or almost certainly unprovable as
written, and several are vacuous or trivial:

- 1-H1 `abs_kahanAccumulator_sub_sum_le` (FloatingPoint:649) is false: under the standard model
  alone the first-order error coefficient exceeds 2 (it is 8/3 at `xs = [1, 1, 1]`; the worst
  case is 3), so no constant works as
  `u → 0`; it needs correct rounding to nearest in a format.
- 3-H1 `completeSpline_derivative_error_le` (SplinesAndKernels:150) is false for `n = 0`
  (counterexample proved in Lean); add `0 < n`.
- 4-H1 `norm_twoLevel_sq_eq_coarseOptimization` (Multilevel:75) is false when the coarse space
  is `⊤` (left side 0, right side 1, from `1 - 1/0 = 1`); add `V ≠ ⊤`.
- 3-H3 `exists_uniformLimit_of_monotoneScheme` (FiniteDifferences:261) allows a non-local
  operator `F`; the Barles–Souganidis argument needs locality (judged by reading).
- 3-H2 `ContDiff ℝ ⊤` means analytic at this Mathlib pin (`⊤ = ω`), not smooth. It appears in
  `cfl_of_threePoint_convergence` (FiniteDifferences:175), where the standard proof no longer
  applies, in both viscosity definitions, in Barles–Souganidis and in Micchelli (also 2-N5).
  Use `∞`.
- Trivial or vacuous: 4-H2 `exists_raviartThomas_div_eq` (take `v = 0`; require `q` homogeneous
  of degree `k`); 2-H2 `sum_reverseWork_le` (a fact about the cost table, not the sweep); 1-H4
  bidiagonalization and 1-H5 Hessenberg reduction (corollaries of SVD and Schur without the
  algorithmic content); 4-H3 `ritz_parabolic_error_le` (an abstract energy estimate in which
  `u` and `Ru` play no role); 4-H4 the Schwarz condition bound (a five-line corollary).
- Degenerate cases: 2-H1 `HasTensorRankLE`/`HasTensorTrain` wrong for `d = 0`.
- Incomplete definitions: 3-H7 `IsWeakConservationLaw` lacks measurability (it weakens mainly
  the semigroup theorem); `IsScalarStrongSDESolution` lacks drift integrability (harmless for
  23.9–23.12 under linear growth and continuous paths, 4-H8).
- Already resolved: 1-H2 `fastTwoSum_add` now carries `radix ≤ 3`, which exhaustive search shows
  is necessary. 1-H3 `add_mem_numbers_of_abs_lt` is admitted but true, with a short proof once
  `format_extrema` is proved.
- Redundant hypotheses: about 50, listed in 1-H6–H12, 2-H3–H9, 3-H4–H6, 3-H8, 4-H5–H7
  (examples: `0 < a` and `hr` in Wedin, which also excludes the exact-rank case; the
  continuity hypothesis in the scalar interval Newton results; the row-sum hypothesis of
  `shuOsher_nonneg`; the support hypothesis of Schoenberg–Whitney; `hε` in the pseudospectrum
  theorems).

**Mathlib naming?** Capitalization and underscores are consistent. The recurring defects are
lowerCamel segments that name no definition (1-N1, 4-N1; e.g. the forward and reverse mode
theorems refer to an `evalProgram` that does not exist, 2-N1), names that do not describe the
statement or bundle conjunctions (1-N2, 2-N3, 3-N1, 4-N2), and a future clash:
`NASC.companionPencil` and `det_companionPencil` become `TauCeti.companionPencil` on renaming
(1-N3).

**Formal docstrings, and appropriate?** Every declaration has a docstring except 18 inductive
constructors (1-D4, 2-D5, 3-D6). Inaccurate docstrings: `LipschitzOnEnclosures` (2-D1),
`HasTensorRankLE` at `d = 0` (2-D2), the upwind error bound ("smooth positive speed" for a
constant unit speed, 3-D1), the stability function (invertibility of the wrong matrix, 3-D2),
Ritz, POD, Falk and `newtonSingleLayer` (4-D1), and several that claim more than the statement
(1-D2, 3-D5). "Gap N.M" labels point at catalogue numbers, one of them non-existent (2-D3,
3-D4).

**Namespaces?** Everything is under `NASC`, with dot-notation namespaces for structures
(`FloatingPointFormat`, `SumTree`, `RungeKuttaTableau`, `IntervalExpr`, ...). Minor
placements in 1-S3 and 4-S3; general helpers made `private` (3-S3).

**Every file a module?** Yes: all 34 files start with `module`, use `public import` and
`public section`. But no definition is `@[expose]`d and almost none has a `_def`, `_iff` or
`_apply` lemma, so importers cannot unfold them (`rfl`, `simp [jordanBlock]`,
`simp [IntervalExpr.eval]` fail in another module; verified). This already affects users such as
`bestApproximationError` in four files (2-S1, 1-S1, 3-S2, 4-S2). This is the most important
library-wide fix.

**Module docstrings?** All 34 files have one; they list topics but not the main results or the
notation (1-D1, 2-D6, 3-D3, 4-D3), and some omit topics the file covers.

**Long proofs?** None is over about 50 lines. Candidates for shortening: the 28-line
`l2_opNorm_unitary_mul_mul_conjTranspose` (two lines with the `CStarRing` unitary-norm lemmas,
1-P1), Bauer–Fike (1-P5), `IsGaussRule.roots_and_weights` (3-P3), two proofs in part 2 (2-P5).

**Mathlib or TauCeti replacements?**

- Duplicates of proved library results: `exists_optimal_transport_and_potentials` duplicates
  TauCeti's `exists_cost_eq_finiteDualValue` (2-P1); `bestApproximationError` is
  `Metric.infDist` (2-P2); circulants, Fourier coefficients and `Monic.as_sum` are in Mathlib
  (3-P1); `rodriguesLegendre` should come from `Polynomial.shiftedLegendre`, Metropolis–Hastings
  from `Kernel.IsReversible` (4-P2); `Matrix.IsUpperHessenberg` replaces a hand-written condition
  (1-S2).
- Proof reuse: TauCeti's unitarily invariant seminorms and Fan dominance for Mirsky (1-P2);
  TauCeti's SVD, Cholesky, block LDU, Cauchy interlacing and Hoffman–Wielandt (1-P3);
  `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` for the weighted Cauchy–Schwarz written twice
  (4-P1); Mathlib's strong law and CLT for 23.1 (4-P2).
- Statements provable now with short routes: 3-P2 (two already proved in scratch, including
  `tadmor_cell_entropy_le` and `monotoneUpdate_entropy_inequality`), 4-P3.

**Excessively long files?** None. The longest is FloatingPoint (822 lines); it mixes format
theory with the summation algorithms and would split naturally if it grows (1-S4).

**File organization?** The NASC imports are mostly unnecessary: by `#min_imports` and grep,
most files import NASC modules they never use, creating artificial rebuild chains (for example
Regularization → BayesianInverseProblems → MonteCarlo → StochasticEquations, and
ConservationLaws rebuilding on changes to Quadrature or VerifiedComputation) (2-S2, 3-S1, 4-S1).
Topic-free calculus, polynomial and approximation helpers should move to a support file
(2-S3, 2-S4, 3-S4).

**Repeated proof fragments?** The program semantics written three times as `let`s (2-P3), the
binary-operator cases of `IntervalExpr` (2-P4), repeated fragments in FloatingPoint (1-P4),
local repetition in part 3 (3-P4) and part 4 (4-P3).

## Priorities

1. Fix the false statements 1-H1, 3-H1, 4-H1, and resolve 3-H2 (`⊤` → `∞`) and 3-H3.
2. Expose definitions or add defining lemmas throughout (2-S1 and companions).
3. Replace the duplicates of library results (2-P1, 2-P2, 3-P1, 4-P2) and remove the unused
   NASC imports.
4. Strengthen the trivial or vacuous statements (4-H2, 2-H2, 1-H4, 1-H5, 4-H3) and complete the
   definitions 3-H7 and the SDE solution predicate.
5. Drop redundant hypotheses, generalize the narrow statements, correct the inaccurate
   docstrings and add main-results lists to the module docstrings.

Files needing the most work: FloatingPoint, EigenvalueMethods, NonlinearEquations,
LowRankApproximation, FiniteDifferences, SplinesAndKernels, ConservationLaws, Multilevel,
FiniteElements and TimeDependentGalerkin.
