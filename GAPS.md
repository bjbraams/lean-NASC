# Principal gaps in numerical analysis and scientific computing

The [mathematical synopsis](SYNOPSIS.md) gives 397 numbered entries in 24
sections and a [guide to their sources](SYNOPSIS.md#reference-guide). The
[coverage inventory](STRUCTURE.md) records the relevant Mathlib and TauCeti
declarations and the hypotheses at which they apply. The
[bibliography](NASC-bib.md) gives the full source details.

This catalogue selects **304 principal statements and theorem families**
across the 24 sections. Of these, **261** have no matching proved
result identified in the two libraries and **43** have partial coverage at
the level of the synopsis entry. The selection emphasizes the main numerical
methods, the estimates that explain their behavior, and results on which
other numerical guarantees depend. Counts refer to numbered entries. A
single entry may contain several related conclusions.

Identifiers and cross-references retain their synopsis meaning. For
example, **5.18** is statement 18 of section 5. Statements carry enough
context to identify the numerical problem and its hypotheses. Follow the
section links for background results cited by number. Each *Assessment*
describes the missing mathematical content and its relation to known
results. The **54** *Scope* notes identify the selected part of a
broader synopsis entry. The **15** *Argument* notes sketch comparatively
short derivations from the cited facts or other selected results.
Each entry ends with a *Lean target* paragraph: the carriers to use at the
pinned revisions, the definitions the statement needs, its split into
Lean-statable conjuncts with every hypothesis explicit, the infrastructure it
waits for, and the declaration in `NASC/` that states it.

The short derivations are **2.1**, **2.13**, **4.6**, **5.1**, **5.18**,
**6.8**, **7.11**, **7.14**, **13.1**, **13.2**, **13.3**, **14.5**,
**16.4**, **19.18**, **24.9**.

## Source baseline

- **Mathlib** — [`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842),
  2026-11-16, tag `v4.36.0`.
- **TauCeti** — [`d91980bdc255e6e50506be147ad9bcb88eb9fcc0`](https://github.com/TauCetiProject/TauCeti/tree/d91980bdc255e6e50506be147ad9bcb88eb9fcc0),
  2026-11-19, with the Mathlib revision above.
- **Lean** — `leanprover/lean4:v4.36.0`.

## Where the largest gaps lie

The library coverage and the selected statements point to four groups of
closely related targets.

- Floating-point arithmetic and verified computation need real-valued
  semantics for finite formats, roundoff and backward-error bounds, and
  numerical existence and enclosure certificates. Dyadic interval bounds,
  norm inequalities and fixed-point theorems supply starting points.
- Numerical linear algebra, optimization and approximation need estimates
  about particular factorizations, recurrences and approximation operators.
  Singular values, spectral variation, compact-operator theory and scalar
  polynomial approximation already supply much of the surrounding analysis.
- Numerical differential and integral equations need concrete discrete
  schemes, stability and convergence proofs, regularity and interpolation
  estimates, and computable error bounds. Continuous existence theory,
  Sobolev results and projection theory support these targets.
- Inverse problems, stochastic computation and model reduction need
  quantitative regularization, estimator and time-step analysis, and bounds
  on approximation complexity. Hilbert-space spectral theory, probability
  limits, Gaussian laws and conditional distributions provide ingredients.

## Contents

- [1. Floating-point arithmetic and rounding error analysis](#1-floating-point-arithmetic-and-rounding-error-analysis) — 11 selected.
- [2. Conditioning and matrix perturbation theory](#2-conditioning-and-matrix-perturbation-theory) — 13 selected.
- [3. Direct methods for linear systems and least squares](#3-direct-methods-for-linear-systems-and-least-squares) — 12 selected.
- [4. Eigenvalue and singular value computations](#4-eigenvalue-and-singular-value-computations) — 14 selected.
- [5. Iterative methods for linear systems](#5-iterative-methods-for-linear-systems) — 13 selected.
- [6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation](#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation) — 13 selected.
- [7. Interval arithmetic and verified computation](#7-interval-arithmetic-and-verified-computation) — 11 selected.
- [8. Nonlinear equations, continuation, and algorithmic differentiation](#8-nonlinear-equations-continuation-and-algorithmic-differentiation) — 11 selected.
- [9. Numerical optimization](#9-numerical-optimization) — 11 selected.
- [10. Polynomial and rational approximation](#10-polynomial-and-rational-approximation) — 12 selected.
- [11. Splines, kernels and wavelets](#11-splines-kernels-and-wavelets) — 13 selected.
- [12. Orthogonal polynomials and numerical quadrature](#12-orthogonal-polynomials-and-numerical-quadrature) — 12 selected.
- [13. Discrete Fourier analysis and sparse recovery](#13-discrete-fourier-analysis-and-sparse-recovery) — 15 selected.
- [14. Initial value problems: one-step and multistep methods](#14-initial-value-problems-one-step-and-multistep-methods) — 13 selected.
- [15. Stiff problems, differential-algebraic equations, and geometric integration](#15-stiff-problems-differential-algebraic-equations-and-geometric-integration) — 12 selected.
- [16. Finite difference methods for differential equations](#16-finite-difference-methods-for-differential-equations) — 11 selected.
- [17. Hyperbolic conservation laws and finite volume methods](#17-hyperbolic-conservation-laws-and-finite-volume-methods) — 11 selected.
- [18. Galerkin and finite element methods for elliptic problems](#18-galerkin-and-finite-element-methods-for-elliptic-problems) — 18 selected.
- [19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation](#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation) — 14 selected.
- [20. Multilevel and domain decomposition methods](#20-multilevel-and-domain-decomposition-methods) — 10 selected.
- [21. Integral equations and boundary element methods](#21-integral-equations-and-boundary-element-methods) — 13 selected.
- [22. Inverse problems and regularization](#22-inverse-problems-and-regularization) — 13 selected.
- [23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations](#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations) — 13 selected.
- [24. High-dimensional approximation, uncertainty quantification, and model reduction](#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction) — 15 selected.

## Conventions

Throughout, $\mathbb K$ denotes $\mathbb R$ or $\mathbb C$. Vectors are
columns, $A^*$ is the conjugate transpose of a matrix $A$ (the transpose
$A^\top$ when $\mathbb K=\mathbb R$), and $I$ is the identity matrix of the
appropriate order. For $1\le p\le\infty$, $\|\cdot\|_p$ is the vector
$p$-norm and also the matrix norm it induces, and $\|\cdot\|_F$ is the
Frobenius norm. For an invertible matrix $A$ and a given norm,
$\kappa(A)=\|A\|\,\|A^{-1}\|$, written $\kappa_2(A)$ for the $2$-norm. The
singular values of a matrix are $\sigma_1\ge\sigma_2\ge\cdots\ge0$. The
spectrum of a square matrix $A$ is $\Lambda(A)$ and its spectral radius is
$\rho(A)=\max\{|\lambda|:\lambda\in\Lambda(A)\}$. Unless a section says
otherwise, the eigenvalues of a Hermitian matrix of order $n$ are written
$\lambda_1\ge\lambda_2\ge\cdots\ge\lambda_n$. Inequalities and absolute
values between matrices, as in $|\Delta A|\le\gamma_n|L||U|$, hold entrywise.

In floating-point arithmetic, $u$ is the unit roundoff, $\mathrm{fl}(x)$ is
the rounded value of a real number $x$, and $\mathrm{fl}(\cdot)$ applied to an
expression denotes its computed value. For an integer $n\ge1$ with $nu<1$,
$$\gamma_n=\frac{nu}{1-nu}.$$

For partial differential equations, $\Omega\subset\mathbb R^d$ is a bounded
domain, Lipschitz unless stated otherwise, with boundary $\partial\Omega$.
$H^s(\Omega)$ and $W^{s,p}(\Omega)$ are the Sobolev spaces, with norm
$\|\cdot\|_{s,\Omega}$ and seminorm $|\cdot|_{s,\Omega}$ on $H^s(\Omega)$, and
$H^1_0(\Omega)$ is the closure in $H^1(\Omega)$ of the smooth functions with
compact support in $\Omega$. $\mathbb P_k$ is the space of polynomials of
total degree at most $k$ in the relevant number of variables. A mesh has mesh
size $h$, and constants written $C$ are independent of $h$ and of the
functions involved unless the statement says otherwise.

For ordinary differential equations, the initial value problem is
$y'=f(t,y)$, $y(t_0)=y_0$, and $h$ is the step size. A Runge–Kutta method
with $s$ stages has Butcher tableau $(A,b,c)$, and a linear multistep method
has generating polynomials $\rho$ and $\sigma$.

The logarithm $\log$ is natural. $\mathbb N=\{1,2,\dots\}$, and
$\mathbb N_0=\mathbb N\cup\{0\}$.

## 1. Floating-point arithmetic and rounding error analysis

[Synopsis](SYNOPSIS.md#1-floating-point-arithmetic-and-rounding-error-analysis) · [Coverage inventory](STRUCTURE.md#1-floating-point-arithmetic-and-rounding-error-analysis)

The finite-radix model, an explicit rounding map and the elementary
rounding-factor estimates underlie the later backward-error statements.

Floating-point numbers are real. A **floating-point format** is given
by a radix $\beta\ge2$, a precision $p\ge2$ and integers $e_{\min}<e_{\max}$.
For a rounding function $\circ$ (statement 1.3) the **unit roundoff** is
$u=\tfrac12\beta^{1-p}$ when $\circ$ rounds to nearest and $u=\beta^{1-p}$ when
it is a directed rounding. When a statement says that an algorithm is evaluated
**under the standard model**, every elementary operation it performs on
floating-point operands $a,b$ returns $\mathrm{fl}(a\mathbin{\mathrm{op}}b)=
(a\mathbin{\mathrm{op}}b)(1+\delta)$ with $|\delta|\le u$; by 1.5 this holds
for correctly rounded arithmetic in the absence of underflow and overflow.
Whenever $\gamma_k$ appears, $ku<1$ is assumed.

* **1.1. Floating-point numbers.** The set $\mathbb F$ of **floating-point
  numbers** of the format consists of the reals
  $$x=M\,\beta^{e-p+1},\qquad M\in\mathbb Z,\quad |M|\le\beta^p-1,\quad
  e_{\min}\le e\le e_{\max}.$$
  A nonzero $x\in\mathbb F$ is **normal** if $|x|\ge\beta^{e_{\min}}$ and
  **subnormal** if $|x|<\beta^{e_{\min}}$. With the exponent chosen minimal, a
  normal number has $\beta^{p-1}\le|M|<\beta^p$, and a subnormal number has
  $e=e_{\min}$ and $|M|\le\beta^{p-1}-1$. The smallest positive subnormal
  number is $\alpha=\beta^{e_{\min}-p+1}$, the smallest positive normal number
  is $\beta^{e_{\min}}$, and the largest element is
  $\Omega=(\beta-\beta^{1-p})\beta^{e_{\max}}$. Every element of $\mathbb F$
  is an integer multiple of $\alpha$, and $\mathbb F=-\mathbb F$. The
  **normal range** is $\{x\in\mathbb R:\beta^{e_{\min}}\le|x|\le\Omega\}$.

  *Assessment.* Mathlib's experimental binary encoding can support a
  fixed-format implementation. The finite-radix representation, canonical
  exponent, normal/subnormal separation and extremal values are the
  format-independent target.

  *Lean target.* Carriers at the pins: none; Mathlib's `FP.Float` is a deprecated radix-2 encoding
  without real semantics, and Lean's `Float` is opaque. The model is the real-valued format
  `NASC.FloatingPointFormat` (radix $\beta\ge2$, precision $p\ge2$, $e_{\min}\le e_{\max}$ as
  structure fields), with `value m e = m * β ^ (e - p + 1)`, the predicate `Valid m e`
  ($|m|<\beta^p$, $e_{\min}\le e\le e_{\max}$), the set `numbers : Set ℝ`, and `spacing`
  ($\alpha$), `minNormal`, `maxFinite` ($\Omega$) and `normalRange`. Conjuncts: (i) a nonzero
  element has a representation with minimal exponent, normalized ($\beta^{p-1}\le|m|$) or with
  $e=e_{\min}$ and $|m|\le\beta^{p-1}-1$; (ii) $\alpha$ and $\beta^{e_{\min}}$ are the least
  positive and least positive normal elements and $\Omega$ is the greatest element (as `IsLeast`
  and `IsGreatest` on the respective sets); (iii) every element is an integer multiple of $\alpha$;
  (iv) `numbers` is closed under negation. Pitfall: `β ^ (e - p + 1)` is a `zpow`, so the radix
  must be cast to `ℝ` before the power. All statable and elementary at the pins; 1.2–1.7 depend on
  it. NASC (`NASC/FloatingPoint/Basic.lean`): `FloatingPointFormat.exists_minimal_exponent` (i),
  `sorry`; (ii)–(iv) are the proved lemmas `FloatingPointFormat.isLeast_spacing`,
  `FloatingPointFormat.isLeast_minNormal`, `FloatingPointFormat.isGreatest_maxFinite`,
  `FloatingPointFormat.numbers_subset_range_mul_spacing` and
  `FloatingPointFormat.neg_mem_numbers_iff`.

* **1.3. Rounding and correct rounding.** For real $x$, $\mathrm{RD}(x)$ is the
  largest element of $\mathbb F\cup\{-\infty\}$ not exceeding $x$,
  $\mathrm{RU}(x)$ the smallest element of $\mathbb F\cup\{+\infty\}$ not
  less than $x$, $\mathrm{RZ}(x)$ equals $\mathrm{RD}(x)$ for $x\ge0$ and
  $\mathrm{RU}(x)$ for $x\le0$, and a **round-to-nearest** function
  $\mathrm{RN}$ satisfies $|\mathrm{RN}(x)-x|\le|t-x|$ for every
  $t\in\mathbb F$, with a tie-breaking rule (ties to even: the neighbour with
  even integral significand). Each of these functions is nondecreasing and
  fixes every element of $\mathbb F$. An operation is **correctly rounded**
  for $\circ$ if it returns $\circ$ of the exact result.

  *Assessment.* An explicit finite format permits monotonicity and exactness
  of all four rounding maps to be proved from their order and nearest-point
  definitions. These properties are used in the arithmetic and interval
  enclosure gaps.

  *Scope.* The selected claims are monotonicity of the rounding maps and
  exactness on representable values.

  *Lean target.* Carriers: `NASC.FloatingPointFormat` (see 1.1) and the predicate
  `IsRounding mode rnd` for `rnd : ℝ → EReal` and `mode : RoundingMode` (nearest, down, up, toward
  zero), where directed roundings take values in `extendedNumbers`, that is $\mathbb
  F\cup\{\pm\infty\}$ inside `EReal`, so that overflow needs no junk value, and the nearest
  rounding takes finite values with an arbitrary tie rule. Conjuncts: `Monotone rnd` and
  `rnd x = x` for `x ∈ numbers`. A separate existence statement (each mode admits a rounding
  function, and the directed ones are unique) is also needed for later entries to be non-vacuous.
  Statable and provable at the pins. NASC: `FloatingPointFormat.IsRounding.monotone` and
  `FloatingPointFormat.IsRounding.apply_coe_of_mem` (`NASC/FloatingPoint/Basic.lean`), proved; the
  existence statement is not stated.

* **1.4. Relative error of rounding.** Let $x$ lie in the normal range. Then
  $\circ(x)=x(1+\delta)$ with $|\delta|<u$, for $\circ$ rounding to nearest
  (any tie rule) as well as for $\circ\in\{\mathrm{RD},\mathrm{RU},
  \mathrm{RZ}\}$ with the respective $u$. For rounding to nearest the sharper
  bound
  $$|\delta|\le\frac{u}{1+u}$$
  holds.

  *Assessment.* Dyadic enclosure is available in Mathlib. The numerical
  statement needs the exact normal-binade spacing and an analysis of both
  nearest and directed rounding.

  *Scope.* The selected estimate is the relative error in the normal range
  under nearest and directed rounding.

  *Lean target.* Carriers: `NASC.FloatingPointFormat` with `IsRounding`, `normalRange` and
  `unitRoundoff mode` ($\tfrac12\beta^{1-p}$ for nearest, $\beta^{1-p}$ otherwise). For
  `x ∈ normalRange` the rounded value is finite, so the conclusion is stated as
  `∃ y δ : ℝ, rnd x = y ∧ y = x * (1 + δ) ∧ |δ| < u`, with the extra conjunct `|δ| ≤ u / (1 + u)`
  for `mode = .nearest`, and a separate theorem for attainment at $x=1+u$ under nearest rounding
  (it requires $1+u$ to be a midpoint, true for every radix since $1\le1+u<\beta$). Pitfall: phrase
  the relative error by an existential $\delta$, not by `(rnd x - x) / x`, to avoid `x / 0` at
  $x=0$, which lies outside the normal range but not outside the type. Statable at the pins;
  depends on 1.1–1.3. NASC: `FloatingPointFormat.IsRounding.exists_eq_mul_one_add`
  (`NASC/FloatingPoint/Basic.lean`; it also states the inverse form of 1.5), `sorry`.

* **1.5. Standard model.** Let $a,b\in\mathbb F$, let
  $\mathrm{op}\in\{+,-,\times,\div\}$ (with $b\ne0$ for division), and let
  the operation be correctly rounded for
  $\circ\in\{\mathrm{RN},\mathrm{RD},\mathrm{RU},\mathrm{RZ}\}$. If
  $a\mathbin{\mathrm{op}}b$ lies in the normal range, then
  $$\circ(a\mathbin{\mathrm{op}}b)=(a\mathbin{\mathrm{op}}b)(1+\varepsilon_1)
  =\frac{a\mathbin{\mathrm{op}}b}{1+\varepsilon_2},\qquad
  |\varepsilon_1|,|\varepsilon_2|\le u,$$
  and for rounding to nearest $|\varepsilon_1|\le u/(1+u)$. The same holds for
  the square root $\circ(\sqrt a)$, $a>0$, and for the fused multiply-add
  $\circ(ab+c)$, $c\in\mathbb F$, whenever the exact result lies in the
  normal range. Sums do not
  suffer from underflow: if $a,b\in\mathbb F$ and $|a\pm b|<\beta^{e_{\min}}$,
  then $a\pm b\in\mathbb F$, so $\circ(a\pm b)=a\pm b$ for every rounding
  function. Hence the model for $\pm$ holds whenever $|a\pm b|\le\Omega$.

  *Assessment.* The arithmetic model must specify an exact real operation and
  its rounded result. Closure of floating-point addition in the subnormal
  range uses the common lattice spacing.

  *Lean target.* Carriers: as in 1.4. Conjuncts: (i) the two relative-error representations of 1.4
  for `rnd (a op b)` with `op` each of `+ - * /` (with `b ≠ 0`), `Real.sqrt a` ($a>0$) and
  `a * b + c`, under the hypothesis that the exact result lies in `normalRange`; (ii) Hauser's
  lemma: `a, b ∈ numbers` and `|a + b| < minNormal` imply `a + b ∈ numbers`, hence
  `rnd (a + b) = a + b` by 1.3; (iii) the model for $\pm$ whenever `|a ± b| ≤ maxFinite`. Conjunct
  (i) is 1.4 applied to the exact result, so the substance is (ii), which uses that every element
  is a multiple of $\alpha$ (1.1). Statable at the pins. NASC: (i) is in
  `FloatingPointFormat.IsRounding.exists_eq_mul_one_add`, `sorry`; (ii) is
  `FloatingPointFormat.add_mem_numbers_of_abs_lt`, proved; (iii) is not stated.

* **1.6. Sterbenz lemma.** If $x,y\in\mathbb F$ satisfy $y/2\le x\le2y$, then
  $x-y\in\mathbb F$; hence $\circ(x-y)=x-y$ for every rounding function.

  *Assessment.* Exact subtraction of nearby numbers is specific to the format
  with its subnormal range. Integer divisibility and the exponent bounds give
  a route to the representability result.

  *Lean target.* Carriers: `NASC.FloatingPointFormat.numbers`. Statement: `x, y ∈ numbers`,
  `y / 2 ≤ x`, `x ≤ 2 * y` imply `x - y ∈ numbers`; the hypotheses force $x,y\ge0$, so no sign
  hypothesis is needed, and the subnormal range is part of `numbers`, which the lemma requires (it
  fails for formats with flush-to-zero). The corollary `rnd (x - y) = x - y` for every rounding is
  then 1.3. Statable and elementary at the pins. NASC:
  `FloatingPointFormat.sub_mem_numbers_of_half_le_of_le_two_mul`, `sorry`.

* **1.7. Error-free transformations.** Let arithmetic be correctly rounded
  to nearest, and write $\mathrm{RN}$ for the rounded operations.
  - **Fast2Sum.** Let $\beta\le3$, let $a,b\in\mathbb F$ with the exponent of
    $a$ at least that of $b$ (for instance $|a|\ge|b|$), and suppose
    $\mathrm{RN}(a+b)$ does not overflow. Put $s=\mathrm{RN}(a+b)$,
    $z=\mathrm{RN}(s-a)$ and $t=\mathrm{RN}(b-z)$. Then $s+t=a+b$ exactly.
  - **2Sum.** For $a,b\in\mathbb F$ put $s=\mathrm{RN}(a+b)$,
    $a'=\mathrm{RN}(s-b)$, $b'=\mathrm{RN}(s-a')$,
    $\delta_a=\mathrm{RN}(a-a')$, $\delta_b=\mathrm{RN}(b-b')$ and
    $t=\mathrm{RN}(\delta_a+\delta_b)$. In any radix, if $a$ and $b$ are
    normal and none of the six operations underflows or overflows, then
    $s+t=a+b$ exactly. For
    $\beta=2$ the hypothesis on underflow is not needed.
  - **2MultFMA.** Let $x_1,x_2\in\mathbb F$ have exponents $e_1,e_2$ with
    $e_1+e_2\ge e_{\min}+p-1$, and assume no overflow. Put
    $r_1=\mathrm{RN}(x_1x_2)$ and $r_2=\mathrm{RN}(x_1x_2-r_1)$, the latter
    computed by one fused multiply-add. Then $r_1+r_2=x_1x_2$ exactly.

  *Assessment.* The error-free decompositions require the actual sequence of
  rounded operations and the no-overflow conditions. The fused multiply-add
  contract is essential to the product residual.

  *Lean target.* Carriers: `NASC.FloatingPointFormat` and the structure `Nearest`, a real-valued map
  `round : ℝ → ℝ` satisfying `IsRounding .nearest`; the algorithms are the definitions
  `fastTwoSum rnd a b` and `twoSum rnd a b : ℝ × ℝ` (the sequences of rounded operations), and
  2MultFMA is the definition
  `twoMultFMA rnd x₁ x₂ = (rnd (x₁ * x₂), rnd (x₁ * x₂ - rnd (x₁ * x₂)))`. Three theorems: (i)
  Fast2Sum, with `F.radix ≤ 3`, `a, b ∈ numbers`, the exponent condition (the sufficient form
  `|b| ≤ |a|` is the usual hypothesis), and no overflow `|a + b| ≤ maxFinite` (with a real-valued
  `round`, overflow must be an explicit hypothesis, since a nearest point in $\mathbb F$ always
  exists); (ii) 2Sum in any radix, with every intermediate exact result of absolute value at most
  $\Omega$ and, for $\beta\ne2$, zero or normal; (iii) 2MultFMA, with representations `Valid m₁ e₁`,
  `Valid m₂ e₂`, `e₁ + e₂ ≥ emin + p - 1` and no overflow. Statable at the pins; depends on 1.1–1.6.
  NASC: `FloatingPointFormat.fastTwoSum_add`, `FloatingPointFormat.twoSum_add` and
  `FloatingPointFormat.twoMultFMA_add`, all `sorry`.

* **1.8. Accumulated rounding factors.** If $\delta_1,\dots,\delta_n$ are
  reals with $|\delta_i|\le u$, $\rho_i\in\{1,-1\}$ and $nu<1$, then
  $$\prod_{i=1}^n(1+\delta_i)^{\rho_i}=1+\theta_n,\qquad
  |\theta_n|\le\gamma_n=\frac{nu}{1-nu}.$$
  Write $\theta_k$ for any real with $|\theta_k|\le\gamma_k$. Then
  $(1+\theta_k)(1+\theta_j)=1+\theta_{k+j}$, and
  $(1+\theta_k)/(1+\theta_j)=1+\theta_{k+j}$ if $j\le k$ and
  $1+\theta_{k+2j}$ if $j>k$; moreover
  $$\gamma_k\gamma_j\le\gamma_{\min(k,j)},\quad i\gamma_k\le\gamma_{ik},\quad
  \gamma_k+u\le\gamma_{k+1},\quad
  \gamma_k+\gamma_j+\gamma_k\gamma_j\le\gamma_{k+j},$$
  whenever the indices that occur satisfy (index)$\cdot u<1$, with the
  additional condition $\max(k,j)u\le\tfrac12$ for the first inequality. If
  $nu<0.01$, then $\prod_{i=1}^n(1+\delta_i)=1+\eta_n$ with
  $|\eta_n|\le1.01\,nu$.

  *Assessment.* Finite products are available in Mathlib. The reusable
  numerical estimates are the uniform bound for signed products and the rules
  for composing the rounding factors with their stated index restrictions.

  *Lean target.* Carriers: none upstream. The format-free model is the predicate
  `NASC.HasRelativeError u x y` ($\exists\delta$, $|\delta|\le u$, $y=x(1+\delta)$) and
  `NASC.roundingGamma u n` $=nu/(1-nu)$. Conjuncts: (i) for `δ : Fin n → ℝ` with `|δ i| ≤ u` and
  signs `ρ : Fin n → ℤ` in $\{\pm1\}$, `∏ i, (1 + δ i) ^ ρ i` is `1 + θ` with
  `|θ| ≤ roundingGamma u n`; (ii) the composition rules for products and quotients of
  $(1+\theta_k)$; (iii) the four inequalities between the $\gamma_k$ with their index hypotheses;
  (iv) the bound $1.01nu$ for `n * u ≤ 0.01`. Hypotheses `0 ≤ u` and `n * u < 1` are essential: at
  `n * u = 1`, `roundingGamma` is the junk value `x / 0 = 0` and (i) would be false. Statable at
  the pins with `zpow`. NASC: `hasRelativeError_prod_zpow` (i) and `roundingGamma_add_add_mul_le`
  (part of (ii)) (`NASC/FloatingPoint/RoundingError.lean`), both proved; the quotient rule with
  index $k+2j$, the product and $\min$ inequalities of (iii) and (iv) are not stated.

* **1.9. Summation.** Let $x_1,\dots,x_n\in\mathbb F$ and
  $S_n=\sum_ix_i$. Consider any summation scheme that, starting from the set
  $\{x_1,\dots,x_n\}$, repeatedly removes two members and inserts their
  computed sum, so that $n-1$ additions are performed (recursive summation in
  any order, pairwise summation and insertion are of this form). Under the
  standard model, with $\widehat T_i$ the result of the $i$-th addition, the
  computed sum $\widehat S_n$ has the representation
  $\widehat S_n=\sum_ix_i(1+\varepsilon_i)$ with
  $|\varepsilon_i|\le\gamma_{n-1}$, so
  $|S_n-\widehat S_n|\le\gamma_{n-1}\sum_i|x_i|$. If each addition also
  satisfies the inverse relative-error model of 1.5, then
  $|S_n-\widehat S_n|\le u\sum_{i=1}^{n-1}|\widehat T_i|.$
  For pairwise summation with
  $n=2^r$ the bound is $\gamma_r\sum_i|x_i|$. If the arithmetic is correctly
  rounded to nearest and no overflow occurs, recursive summation satisfies the
  sharper bound
  $$|S_n-\widehat S_n|\le(n-1)u\sum_{i=1}^n|x_i|\qquad\text{for all }n.$$

  *Assessment.* Exact finite sums and trees provide the algebraic setting. The
  bound depends on how evaluation assigns a rounding factor to each path from
  an input to the output.

  *Lean target.* Carriers: the inductive type `NASC.SumTree ι` of binary summation trees (leaves,
  branches), with `leaves`, `depth`, `eval rnd x` (one rounding per branch) and the predicates
  `HasStableEvaluation rnd x u` and `HasInverseRelativeError rnd x u` (the two standard models at
  every branch). A summation scheme of the statement is a tree whose `leaves` list is a permutation
  of the index list. Conjuncts: (i) `|t.eval rnd x - Σ| ≤ roundingGamma u (n - 1) * Σ |x i|` for
  $n$ leaves (the bound by `roundingGamma u t.depth` implies it, since the depth is less than the
  number of leaves); (ii) the a posteriori bound by `u` times the sum of the computed node values;
  (iii) the pairwise bound for $n=2^r$ as the depth bound for the balanced tree; (iv) Rump's bound
  $(n-1)u\sum|x_i|$, which needs the format and a nearest rounding (`FloatingPointFormat.Nearest`,
  no overflow) and holds for recursive summation, a left comb tree. Statable at the pins. NASC:
  `SumTree.abs_eval_sub_sum_le` (depth form) and `SumTree.abs_eval_sub_sum_le_computed`, both
  proved; (iv) is not stated.

* **1.10. Inner products and matrix products.** Let $x,y\in\mathbb F^n$ and
  let $\mathrm{fl}(x^\top y)$ be computed under the standard model with the
  additions in any order. Then
  $$\mathrm{fl}(x^\top y)=(x+\Delta x)^\top y=x^\top(y+\Delta y),\qquad
  |\Delta x|\le\gamma_n|x|,\quad|\Delta y|\le\gamma_n|y|,$$
  so $|x^\top y-\mathrm{fl}(x^\top y)|\le\gamma_n|x|^\top|y|$; inequalities
  and absolute values of vectors and matrices are componentwise. For
  $A\in\mathbb F^{m\times n}$ the computed $\hat y$ of $y=Ax$ satisfies
  $\hat y=(A+\Delta A)x$ with $|\Delta A|\le\gamma_n|A|$. For
  $B\in\mathbb F^{n\times q}$, the computed product $\widehat C$ of $C=AB$
  formed by inner products has $j$-th column $(A+\Delta A_j)b_j$ with
  $|\Delta A_j|\le\gamma_n|A|$, hence
  $$|C-\widehat C|\le\gamma_n|A||B|,$$
  and $\|C-\widehat C\|\le\gamma_n\|A\|\|B\|$ for the $1$-, $\infty$- and
  Frobenius norms. With correct rounding to nearest and neither underflow nor
  overflow, $\gamma_n$ in the inner product bound can be replaced by $nu$ for
  every $n$.

  *Assessment.* Mathlib has exact products and operator norms. The missing
  result links a specified rounded accumulation to entrywise perturbations,
  with the separate rounding-to-nearest improvement.

  *Lean target.* Carriers: `NASC.SumTree`, `NASC.HasRelativeError`, `NASC.roundingGamma` (see
  1.8–1.9); Mathlib's `Matrix`, `dotProduct` and `Matrix.mulVec`, and the matrix norms as local
  instances: `Matrix.linftyOpNormedAddCommGroup`, `Matrix.frobeniusNormedAddCommGroup`, and the
  $1$-norm via `Matrix.linfty_opNorm_def` on the transpose. Conjuncts: (i) the computed inner
  product (products rounded, sum evaluated on any tree with the leaves a permutation of `Fin n`)
  equals `∑ i, (x i + dx i) * y i` with `|dx i| ≤ roundingGamma u n * |x i|`; (ii) the
  matrix–vector and matrix–matrix forms entrywise; (iii) the three normwise bounds; (iv) the bound
  with $nu$ in place of $\gamma_n$, which needs the format and nearest rounding and holds for all
  $n$. Hypotheses `0 ≤ u`, `n * u < 1`. Statable at the pins. NASC:
  `SumTree.exists_dotProduct_eq_sum_mul_perturbed` (i) and `SumTree.abs_mul_apply_sub_eval_le`
  (entrywise product) (`NASC/FloatingPoint/RoundingError.lean`), proved; (iii)–(iv) not stated.

* **1.12. Compensated summation.** Let $x_1,\dots,x_n\in\mathbb F$ and
  $S_n=\sum_ix_i$.
  - **Kahan's compensated summation** ($s=e=0$; for $i=1,\dots,n$:
    $t=s$, $y=x_i+e$, $s=t+y$, $e=(t-s)+y$, each operation rounded) satisfies,
    when the arithmetic is correctly rounded to nearest and no operation
    overflows,
    $$\widehat S_n=\sum_{i=1}^n(1+\mu_i)x_i,\qquad
    |\mu_i|\le2u+O(nu^2),$$
    with an implied constant independent of $n$, $u$, the format and the data. So
    $|S_n-\widehat S_n|\le(2u+O(nu^2))\sum_i|x_i|$.
  - **Cascaded summation.** With correct rounding to nearest, let
    $s=x_1$, $e=0$, and for $i=2,\dots,n$ let $(s,e_i)$ be the output of 2Sum
    (1.7) applied to $(s,x_i)$ and $e=\mathrm{RN}(e+e_i)$; return
    $\sigma=\mathrm{RN}(s+e)$. If $nu<1$ and no overflow occurs, then, even
    with underflow,
    $$|\sigma-S_n|\le u|S_n|+\gamma_{n-1}^2\sum_{i=1}^n|x_i|.$$
  - **Doubly compensated summation.** With correct rounding to nearest, if
    $|x_1|\ge|x_2|\ge\cdots\ge|x_n|$ and $n\le\beta^{p-3}$, Priest's doubly
    compensated sum $s_n$ satisfies $|s_n-S_n|\le2u|S_n|$.

  *Assessment.* The two-word accumulator and the computed correction must be
  represented explicitly. The quantitative error bounds depend on cancellation
  in those recurrences.

  *Lean target.* Carriers: `NASC.FloatingPointFormat` with `Nearest`, and the recursion
  `NASC.kahanAccumulator rnd xs` (a fold of `kahanStep`) on a list. Conjuncts: (i) Kahan: there is
  an absolute constant $C>0$, quantified before the format, the rounding and the data (an
  `O`-statement with hidden dependence on $n$ would be weaker than the source), such that for
  summands in `numbers`, no overflow at any of the four roundings of each step (`kahanStepArgs`)
  and `n * u ≤ 1/2` with `u = F.unitRoundoff .nearest`, $|\widehat
  S_n-S_n|\le(2u+Cnu^2)\sum|x_i|$; the standard model at the four operations of a step does not
  suffice (for $x=(1,1)$ it allows $\widehat S_2=2+5u+O(u^2)$); (ii) cascaded summation, with
  `FloatingPointFormat.Nearest`, the 2Sum outputs of 1.7, `n * u < 1` and no overflow, valid with
  underflow; (iii) Priest, with sorted magnitudes and `n ≤ β ^ (p - 3)`. (ii) depends on 1.7 and
  (iii) on Fast2Sum (1.7); both need the format. Statable at the pins; Priest's proof is long. NASC:
  `abs_kahanAccumulator_sub_sum_le` (`NASC/FloatingPoint/RoundingError.lean`), `sorry`; (ii) and
  (iii) not stated.

* **1.13. Triangular systems.** Let $T\in\mathbb F^{n\times n}$ be
  nonsingular and triangular and $b\in\mathbb F^n$. The solution of $Tx=b$
  computed by substitution under the standard model, with the inner sums in any
  order, satisfies
  $$(T+\Delta T)\hat x=b,\qquad|\Delta T|\le\gamma_n|T|.$$
  Consequently
  $$\frac{\|x-\hat x\|_\infty}{\|x\|_\infty}\le
  \frac{\mathop{\mathrm{cond}}(T,x)\,\gamma_n}{1-\mathop{\mathrm{cond}}(T)\,
  \gamma_n},\qquad
  \mathop{\mathrm{cond}}(T,x)=\frac{\|\,|T^{-1}||T||x|\,\|_\infty}
  {\|x\|_\infty},\quad
  \mathop{\mathrm{cond}}(T)=\|\,|T^{-1}||T|\,\|_\infty,$$
  provided $x\ne0$ and $\mathop{\mathrm{cond}}(T)\gamma_n<1$.

  *Assessment.* The exact triangular inverse theory gives the algebraic
  background. The backward-error certificate must be derived from the order of
  arithmetic in forward or backward substitution.

  *Lean target.* Carriers: Mathlib's `Matrix`, `Matrix.mulVec` and `Matrix.BlockTriangular` (or the
  hypothesis `∀ i j, i < j → T i j = 0`), and `NASC.SumTree` with `NASC.HasRelativeError` for each
  rounded operation of a row. The predicate `IsRoundedForwardSubstitution T b x rnd u` records the
  rounded operations, with any summation order in each row. Conjuncts: (i) `∃ E, (T + E) *ᵥ x = b`
  with `|E i j| ≤ roundingGamma u n * |T i j|`; (ii) the forward error bound in the $\infty$-norm
  under `x ≠ 0` and $\mathrm{cond}(T)\gamma_n<1$, with $\mathrm{cond}(T,x)$ and $\mathrm{cond}(T)$
  defined through the entrywise absolute value of `T⁻¹`; (iii) the same for back substitution
  (reverse the index order). Hypotheses `0 ≤ u`, `n * u < 1`, nonzero diagonal. Pitfall: `T⁻¹` is
  the junk value `0` for singular `T`, so the nonzero diagonal must stay a hypothesis of (ii). (ii)
  follows from (i) and 2.6. Statable at the pins. NASC:
  `IsRoundedForwardSubstitution.exists_add_mulVec_eq` (`NASC/FloatingPoint/RoundingError.lean`),
  proved; (ii) and (iii) not stated.

## 2. Conditioning and matrix perturbation theory

[Synopsis](SYNOPSIS.md#2-conditioning-and-matrix-perturbation-theory) · [Coverage inventory](STRUCTURE.md#2-conditioning-and-matrix-perturbation-theory)

The matrix norm and eigenvalue conventions are those of the synopsis. A norm
on matrices in the perturbation statements is induced by the indicated vector
norm unless the statement specifies another norm.

A norm on
$\mathbb K^n$ is arbitrary unless marked, and a matrix norm written with the
same symbol is the induced norm. Inequalities and absolute values of vectors
and matrices are componentwise. The left eigenvectors of $A$ for $\lambda$
are the nonzero $y$ with $y^*A=\lambda y^*$. The Kreiss matrix theorem is in
section 16 and the Eckart–Young theorem in section 6.

* **2.1. Condition number of a map.** Let $X,Y$ be finite-dimensional normed
  spaces, $U\subseteq X$ open, $f:U\to Y$ and $x\in U$. The **absolute** and
  **relative condition numbers** of $f$ at $x$ are
  $$\hat\kappa(x)=\lim_{\delta\to0}\ \sup_{0<\|h\|\le\delta}
  \frac{\|f(x+h)-f(x)\|}{\|h\|},\qquad
  \kappa(x)=\lim_{\delta\to0}\ \sup_{0<\|h\|\le\delta}
  \frac{\|f(x+h)-f(x)\|/\|f(x)\|}{\|h\|/\|x\|},$$
  the second for $x\ne0$ and $f(x)\ne0$; the limits exist in $[0,\infty]$
  because the suprema decrease with $\delta$. If $f$ is Fréchet
  differentiable at $x$ with derivative $f'(x)$, then
  $$\hat\kappa(x)=\|f'(x)\|,\qquad\kappa(x)=\frac{\|f'(x)\|\,\|x\|}{\|f(x)\|},$$
  where $\|f'(x)\|$ is the operator norm induced by the norms on $X$ and $Y$.

  *Assessment.* Fréchet differentiation and the continuous linear operator
  norm are available. The condition number is the exact limiting amplification
  for arbitrary small admissible changes of the input.

  *Argument.* Write the increment as the Fréchet derivative applied to the
  perturbation plus a remainder that is uniformly small relative to the
  perturbation on shrinking balls. The derivative norm supplies the upper
  bound. For the reverse bound, take a norming direction or a sequence of unit
  directions approaching the derivative norm and scale by the radius of the
  perturbation ball.

  *Lean target.* Carriers: Mathlib's `HasFDerivAt f D x` with `D : E →L[ℝ] F` and its operator
  norm, for real normed spaces (finite dimension is not needed). New definition: the absolute
  condition number as an extended real,
  `⨅ δ > 0, ⨆ (y ∈ s, y ≠ x, ‖y - x‖ ≤ δ), ENNReal.ofReal (‖f y - f x‖ / ‖y - x‖)` over a domain
  `s`, and the relative one with the factor $\|x\|/\|f(x)\|$. Conjuncts: (i) for `s ∈ nhds x`, the
  absolute condition number is `ENNReal.ofReal ‖D‖`; (ii) for `x ≠ 0` and `f x ≠ 0`, the relative
  one is `ENNReal.ofReal (‖D‖ * ‖x‖ / ‖f x‖)`. Pitfalls: a real-valued `⨆` would be `0` on an
  unbounded set; the field must be nontrivially normed for the lower bound (over `ℝ`, scaling a
  norming direction). Statable at the pins; 2.2 is (i) for inversion. NASC:
  `NASC.absoluteConditionNumber` and `HasFDerivAt.absoluteConditionNumber_eq` (i), over any
  nontrivially normed field, proved; (ii) not stated.

* **2.3. Distance to singularity.** Let $A\in\mathbb K^{n\times n}$ be
  nonsingular. Then (Gastinel–Kahan)
  $$\min\Bigl\{\frac{\|\Delta A\|}{\|A\|}:A+\Delta A\text{ singular}\Bigr\}
  =\frac1{\kappa(A)},$$
  and the minimum is attained by a matrix $\Delta A$ of rank one. In the
  $2$-norm the minimum of $\|\Delta A\|_2$ is $\sigma_n(A)$.

  *Assessment.* Partly covered. Mathlib gives invertibility within the
  inverse-norm radius of an invertible element. The extremal rank-one
  perturbation and its matrix-norm interpretation are the selected gap.

  *Scope.* The selected claim is attainment of the distance by a rank-one
  perturbation and its expression in singular-value form for the Euclidean
  norm.

  *Lean target.* Carriers: Mathlib's `Matrix.det`, `Matrix.rank`, `Matrix.toEuclideanLin` and
  `LinearMap.singularValues` (zero-indexed, so $\sigma_n$ is index `n - 1`), with the Euclidean
  operator norm from `open scoped Matrix.Norms.L2Operator`; for a general induced norm, the operator
  norm of `Matrix.toLin'` between normed spaces `(Fin n → 𝕜)` with arbitrary norms. Conjuncts: (i)
  for invertible `A` and an induced norm, the least `‖ΔA‖` with `A + ΔA` singular equals `‖A⁻¹‖⁻¹`,
  attained at a rank-one `ΔA` (use `exists_dual_vector` for the norming functional); (ii) in the
  Euclidean norm, this least value is `singularValues (n - 1)`. Dimension $n\ge1$ is needed (write
  the index type as `Fin (n + 1)`). Pitfall: `Ring.inverse` of a singular matrix is `0`, so
  invertibility must be a hypothesis. Statable at the pins. NASC:
  `exists_rank_one_isLeast_norm_det_add_eq_zero` (Euclidean case, over `RCLike 𝕜`), `sorry`; the
  general-norm form (i) is not stated.

* **2.4. Perturbation of linear systems.** Let $A\in\mathbb R^{n\times n}$
  be nonsingular, $Ax=b$ with $x\ne0$, let $E\in\mathbb R^{n\times n}$,
  $f\in\mathbb R^n$ and $\varepsilon\ge0$ with
  $\varepsilon\|A^{-1}\|\,\|E\|<1$, and let $(A+\Delta A)y=b+\Delta b$ with
  $\|\Delta A\|\le\varepsilon\|E\|$ and $\|\Delta b\|\le\varepsilon\|f\|$. Then
  $$\frac{\|x-y\|}{\|x\|}\le\frac{\varepsilon}{1-\varepsilon\|A^{-1}\|\,\|E\|}
  \Bigl(\frac{\|A^{-1}\|\,\|f\|}{\|x\|}+\|A^{-1}\|\,\|E\|\Bigr),$$
  and the corresponding condition number
  $$\kappa_{E,f}(A,x)=\lim_{\varepsilon\to0}\sup\Bigl\{\frac{\|\Delta x\|}
  {\varepsilon\|x\|}:(A+\Delta A)(x+\Delta x)=b+\Delta b,\
  \|\Delta A\|\le\varepsilon\|E\|,\ \|\Delta b\|\le\varepsilon\|f\|\Bigr\}$$
  equals $\|A^{-1}\|\,\|f\|/\|x\|+\|A^{-1}\|\,\|E\|$. For $E=A$, $f=b$ one has
  $\kappa(A)\le\kappa_{A,b}(A,x)\le2\kappa(A)$, and if $\varepsilon\kappa(A)<1$
  then $\|x-y\|/\|x\|\le2\varepsilon\kappa(A)/(1-\varepsilon\kappa(A))$.

  *Assessment.* The inverse perturbation lemmas give a starting point for the
  upper bound. The sharp first-order worst case requires constructing
  simultaneous perturbations at the prescribed matrix and right-hand-side
  scales.

  *Lean target.* Carriers: a real finite-dimensional normed space `E`, `A : E ≃L[ℝ] E`,
  perturbations `dA : E →L[ℝ] E`, `db : E`, with operator norms. Conjuncts: (i) the forward bound
  under `x ≠ 0`, `0 ≤ ε`, `‖dA‖ ≤ ε * a`, `‖db‖ ≤ ε * b` and `ε * ‖A⁻¹‖ * a < 1`; (ii) the
  condition number as the limit, as `ε → 0⁺`, of the supremum of `‖y - x‖ / (ε * ‖x‖)` over the
  admissible perturbations, equal to `‖A⁻¹‖ * b / ‖x‖ + ‖A⁻¹‖ * a`; (iii) the bounds
  $\kappa\le\kappa_{A,b}\le2\kappa$ and the $2\varepsilon\kappa/(1-\varepsilon\kappa)$ bound. The
  supremum in (ii) is over a bounded set only for small $\varepsilon$; state it as an `ℝ≥0∞`-valued
  `⨆` or restrict to $\varepsilon\|A^{-1}\|a<1$ to avoid the junk value of a real `sSup`. Statable
  at the pins with `exists_dual_vector`. NASC, over `RCLike 𝕜`: `norm_sub_le_of_perturbed_eq` (i),
  proved; `tendsto_sSup_norm_sub_div_of_perturbation` (ii), `sorry`, which uses a real `sSup` over a
  set that is unbounded for large $\varepsilon$ (harmless in the limit, but the `ℝ≥0∞` form is
  safer); (iii) not stated.

* **2.5. Normwise backward error (Rigal–Gaches).** Let $A\in\mathbb
  R^{n\times n}$, $b,y\in\mathbb R^n$, $E\in\mathbb R^{n\times n}$ and
  $f\in\mathbb R^n$ with $\|E\|\,\|y\|+\|f\|>0$, and put $r=b-Ay$. Then
  $$\eta_{E,f}(y):=\min\{\varepsilon:(A+\Delta A)y=b+\Delta b,\
  \|\Delta A\|\le\varepsilon\|E\|,\ \|\Delta b\|\le\varepsilon\|f\|\}
  =\frac{\|r\|}{\|E\|\,\|y\|+\|f\|}.$$

  *Assessment.* The result identifies a computable residual quotient with a
  minimum over perturbations. A rank-one norming construction realizes the
  bound.

  *Lean target.* Carriers: as in 2.4, without invertibility: `A : E →L[ℝ] E`. Statement: under
  `0 ≤ a`, `0 ≤ c` and `0 < a * ‖y‖ + c`, the value `‖b - A y‖ / (a * ‖y‖ + c)` is `IsLeast` of the
  set of `ε ≥ 0` admitting `dA`, `db` with `(A + dA) y = b + db`, `‖dA‖ ≤ ε * a`, `‖db‖ ≤ ε * c`.
  Here $a=\|E\|$ and $c=\|f\|$ are numbers, which is the generality of the source. The
  nondegeneracy hypothesis cannot be dropped: otherwise the quotient is the junk value $0$ although
  the set may be empty. Statable at the pins. NASC: `isLeast_normwiseBackwardError`, proved.

* **2.6. Componentwise backward error and perturbation (Oettli–Prager,
  Skeel).** Let $A\in\mathbb R^{n\times n}$, $b,y\in\mathbb R^n$, and let
  $E\ge0$ and $f\ge0$ be a matrix and a vector with nonnegative entries; put
  $r=b-Ay$. Then
  $$\omega_{E,f}(y):=\min\{\varepsilon:(A+\Delta A)y=b+\Delta b,\
  |\Delta A|\le\varepsilon E,\ |\Delta b|\le\varepsilon f\}
  =\max_i\frac{|r_i|}{(E|y|+f)_i},$$
  with $0/0$ read as $0$ and $\xi/0$ as $\infty$ for $\xi\ne0$ (the minimum
  over the empty set being $\infty$). If $A$ is nonsingular, $Ax=b$ with
  $x\ne0$, $(A+\Delta A)y=b+\Delta b$ with $|\Delta A|\le\varepsilon E$,
  $|\Delta b|\le\varepsilon f$, and $\varepsilon\|\,|A^{-1}|E\,\|<1$ for an
  absolute norm (one with $\|\,|z|\,\|=\|z\|$), then
  $$\frac{\|x-y\|}{\|x\|}\le\frac{\varepsilon}{1-\varepsilon\|\,|A^{-1}|E\,\|}
  \cdot\frac{\|\,|A^{-1}|E|x|+|A^{-1}|f\,\|}{\|x\|}.$$
  For the $\infty$-norm the bound is attainable to first order in
  $\varepsilon$, and
  $$\lim_{\varepsilon\to0}\sup\Bigl\{\frac{\|\Delta x\|_\infty}
  {\varepsilon\|x\|_\infty}:(A+\Delta A)(x+\Delta x)=b+\Delta b,\
  |\Delta A|\le\varepsilon E,\ |\Delta b|\le\varepsilon f\Bigr\}
  =\frac{\|\,|A^{-1}|E|x|+|A^{-1}|f\,\|_\infty}{\|x\|_\infty}.$$
  For $E=|A|$ and $f=|b|$ this is Skeel's condition number
  $\mathop{\mathrm{cond}}(A,x)=\|\,|A^{-1}||A||x|\,\|_\infty/
  \|x\|_\infty$ up to a factor at most $2$.

  *Assessment.* The signed perturbation constraints and handling of zero
  denominators are part of the statement. The exact componentwise optimum and
  the first-order worst-case analysis need more than normwise inversion
  bounds.

  *Lean target.* Carriers: Mathlib's `Matrix (Fin m) (Fin n) ℝ`, `Matrix.mulVec`, entrywise
  absolute values as functions, and `ℝ≥0∞`. Conjuncts: (i) feasibility at level $\varepsilon\ge0$
  is equivalent to $|r_i|\le\varepsilon(E|y|+f)_i$ for all $i$ (no division, so zero budgets need
  no convention); (ii) the backward error as an `ℝ≥0∞`-valued `sInf` equals
  `⨆ i, ofReal |r i| / ofReal ((E *ᵥ |y|) i + f i)`, where `ℝ≥0∞` division gives $\xi/0=\infty$ for
  $\xi\ne0$ and $0/0=0$ exactly as in the source; (iii) the forward bound for an absolute norm
  (state it for the $\infty$-norm `‖·‖` on `Fin n → ℝ`, which is absolute; general absolute norms
  need a new predicate `∀ z, ‖|z|‖ = ‖z‖`); (iv) the condition number as a limit equal to
  $\|\,|A^{-1}|E|x|+|A^{-1}|f\|_\infty/\|x\|_\infty$, under `A` invertible and `x ≠ 0`; (v) the
  comparison with Skeel's $\mathrm{cond}(A,x)$. Statable at the pins. NASC:
  `exists_componentwisePerturbation_iff` (i) and, with the `ℝ≥0∞`-valued definition
  `componentwiseBackwardError` (an `sInf`, `⊤` on an empty feasible set),
  `componentwiseBackwardError_eq` (ii), both `sorry`; (iii)–(v) not stated.

* **2.10. Perturbation of singular values.** Let
  $A,B\in\mathbb C^{m\times n}$.
  - (Mirsky) For every unitarily invariant norm $\|\cdot\|$ on
    $\mathbb C^{m\times n}$ (one with $\|UXV\|=\|X\|$ for all unitary $U,V$),
    $\|A-B\|\ge\|\Sigma(A)-\Sigma(B)\|$, where $\Sigma(\cdot)$ is the
    $m\times n$ diagonal matrix of the singular values in decreasing order.
  - (Interlacing) If $\hat A$ is $A$ with one column deleted and $m\ge n$,
    then $\sigma_1(A)\ge\sigma_1(\hat A)\ge\sigma_2(A)\ge\cdots\ge
    \sigma_{n-1}(\hat A)\ge\sigma_n(A)$; if $m<n$, then
    $\sigma_1(A)\ge\sigma_1(\hat A)\ge\cdots\ge\sigma_m(A)\ge
    \sigma_m(\hat A)\ge0$.

  *Assessment.* Partly covered. TauCeti proves spectral- and Frobenius-norm
  perturbation bounds. The general unitarily invariant norm comparison and
  singular interlacing after column deletion are the selected assertions.

  *Scope.* The selected claims are Mirsky's inequality for every unitarily
  invariant norm and interlacing under column deletion.

  *Lean target.* Carriers: Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin A`
  (zero-indexed, zero past the dimension), TauCeti's `TauCeti.UnitarilyInvariantSeminorm 𝕜 E F` on
  linear maps between finite-dimensional inner product spaces with its gauge representation and Fan
  dominance (`TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`), and `LinearMap.kyFanSum`.
  Conjuncts: (i) Mirsky: for every unitarily invariant seminorm `N`, `N (D_A - D_B) ≤ N (A - B)`,
  where `D_A` is the rectangular diagonal of singular values in a fixed pair of orthonormal bases;
  with Fan dominance this reduces to the singular-value Lidskii inequality, the Ky Fan sums of
  $|\sigma_i(A)-\sigma_i(B)|$ being at most those of $A-B$; (ii) interlacing for `A.submatrix id e`
  with `e : Fin n ↪ Fin (n + 1)`: `σ (i + 1) A ≤ σ i (A.submatrix id e) ≤ σ i A` for all `i : ℕ`,
  which covers both cases $m\ge n$ and $m<n$ thanks to the zero extension. Statable at the pins;
  (ii) follows from Cauchy interlacing (2.9, TauCeti) applied to $A^*A$. NASC:
  `seminorm_singularValueDiagonal_sub_le` (for `N : TauCeti.UnitarilyInvariantSeminorm 𝕜` on the
  Euclidean operators `toEuclideanLin`, `RCLike 𝕜`) and `singularValues_submatrix_interlace`, both
  `sorry`.

* **2.11. Hoffman–Wielandt theorem.** Let $A,E\in\mathbb C^{n\times n}$ with
  $A$ and $A+E$ normal, with eigenvalues $\lambda_1,\dots,\lambda_n$ and
  $\hat\lambda_1,\dots,\hat\lambda_n$ in some order. Then there is a
  permutation $\pi$ of $\{1,\dots,n\}$ with
  $$\Bigl(\sum_{i=1}^n|\hat\lambda_{\pi(i)}-\lambda_i|^2\Bigr)^{1/2}\le
  \|E\|_F.$$

  *Assessment.* Partly covered. TauCeti gives the ordered Hermitian
  inequality. Matching the eigenvalues of two normal matrices by a permutation
  requires the complex spectral setting and a matching argument.

  *Scope.* The target is the matching bound for two complex normal matrices.

  *Lean target.* Carriers: Mathlib's `IsStarNormal` on `Matrix (Fin n) (Fin n) ℂ`,
  `Matrix.charpoly` and `Polynomial.roots` (a multiset, so the eigenvalues are listed with
  algebraic multiplicity by `α : Fin n → ℂ` with
  `Multiset.ofList (List.ofFn α) = A.charpoly.roots`), `Equiv.Perm (Fin n)`, and the Frobenius norm
  (local instance `Matrix.frobeniusNormedAddCommGroup`, or the explicit double sum). Statement:
  `∃ e : Equiv.Perm (Fin n), ∑ i, ‖α i - β (e i)‖ ^ 2 ≤ ‖A - B‖_F ^ 2`. The standard proof uses
  Birkhoff's theorem on doubly stochastic matrices, which Mathlib has (`doublyStochastic` and its
  extreme points), and the unitary diagonalization of normal matrices. A non-normal counterexample
  makes a useful negative control. Statable at the pins. NASC:
  `exists_perm_sum_norm_sq_le_of_isStarNormal`, `sorry`.

* **2.12. Gershgorin theorem.** Let $A=(a_{ij})\in\mathbb C^{n\times n}$ and
  $R_i=\{z\in\mathbb C:|z-a_{ii}|\le\sum_{j\ne i}|a_{ij}|\}$. Every
  eigenvalue of $A$ lies in $\bigcup_{i=1}^nR_i$. If $I\subseteq\{1,\dots,n\}$
  has $k$ elements and $\bigcup_{i\in I}R_i$ is disjoint from
  $\bigcup_{i\notin I}R_i$, then $\bigcup_{i\in I}R_i$ contains exactly $k$
  eigenvalues of $A$, counted with algebraic multiplicity. The same holds
  with column sums in place of row sums.

  *Assessment.* Partly covered. Mathlib proves the row-disc inclusion. The
  selected counting theorem requires tracking algebraic multiplicities across
  separated unions of discs.

  *Scope.* The target is the separated-component count with algebraic
  multiplicity, and the column form of the inclusion.

  *Lean target.* Carriers: Mathlib's `Matrix.eigenvalue_mem_ball` (inclusion, over a normed field),
  `Matrix.charpoly` with `Polynomial.roots` for multiplicities, and `Metric.closedBall`. New
  definition: the row disc `gershgorinDisc A i`. Conjuncts: (i) for `I : Finset (Fin n)` with the
  union over `I` disjoint from the union over the complement, the number of roots of `A.charpoly`
  in the first union, counted in the multiset, is `I.card`; (ii) the column form of the inclusion
  and of (i), by transposition (`Matrix.charpoly_transpose`). The proof of (i) follows the root
  count along $t\mapsto D+t(A-D)$, $D$ the diagonal of $A$: the count of roots in the closed union
  is locally constant in $t$ because no root crosses the gap between the two unions. Either
  continuity of the roots of a monic polynomial in its coefficients or TauCeti's argument principle
  (`TauCeti.argumentPrinciple_windingNumber`, on a cycle separating the two unions) gives the local
  constancy; the cycle construction around a finite union of discs is the infrastructure to build.
  NASC: `card_roots_filter_mem_gershgorinDiscs`, `sorry`.

* **2.13. Bauer–Fike theorem.** Let $A=S\Lambda S^{-1}\in\mathbb C^{n\times
  n}$ with $\Lambda=\mathrm{diag}(\lambda_1,\dots,\lambda_n)$, let
  $E\in\mathbb C^{n\times n}$, and let $\|\cdot\|$ be a matrix norm with
  $\|D\|=\max_i|d_i|$ for every diagonal $D=\mathrm{diag}(d_1,\dots,d_n)$
  (for instance an induced $p$-norm). Then every eigenvalue $\mu$ of $A+E$
  satisfies
  $$\min_i|\mu-\lambda_i|\le\|S\|\,\|S^{-1}\|\,\|E\|.$$
  If $A$ is normal, then $\min_i|\mu-\lambda_i|\le\|E\|_2$.

  *Assessment.* The nonsingular resolvent and matrix norm infrastructure are
  available. The gap is the perturbation bound for a general diagonalizable
  matrix with its eigenvector condition number.

  *Argument.* If $\mu\notin\Lambda(A)$, then $1$ is an eigenvalue of $(\mu
  I-\Lambda)^{-1}S^{-1}ES$, as follows by applying $S^{-1}$ to an eigenvector
  of $A+E$. The spectral radius is bounded by the matrix norm. Use
  submultiplicativity and the diagonal norm assumption to get the estimate. In
  the normal case use a unitary $S$ and the Euclidean operator norm.

  *Lean target.* Carriers: Mathlib's `spectrum ℂ`, `Matrix.diagonal`, units of the matrix ring for
  `S`, and the Euclidean operator norm (`Matrix.Norms.L2Operator`) or the $\infty$-norm instance.
  Conjuncts: (i) for `A = S * diagonal λ * S⁻¹` and `μ ∈ spectrum ℂ (A + E)`,
  `∃ i, ‖μ - λ i‖ ≤ ‖S‖ * ‖S⁻¹‖ * ‖E‖` for every submultiplicative matrix norm with
  `‖diagonal d‖ = sup ‖d i‖` (a new hypothesis on the norm, satisfied by the induced $p$-norms);
  (ii) for normal `A`, `∃ i, ‖μ - λ i‖ ≤ ‖E‖` in the Euclidean norm. The empty case `n = 0` is
  vacuous since the spectrum is empty. Statable at the pins. NASC:
  `exists_norm_sub_eigenvalue_le_of_diagonalization` (Euclidean norm), proved; (ii) and the general
  norm are not stated.

* **2.14. Condition number of a simple eigenvalue.** Let
  $A\in\mathbb C^{n\times n}$, let $\lambda$ be an algebraically simple
  eigenvalue with right eigenvector $x$ and left eigenvector $y$. Then
  $y^*x\ne0$. For every $E\in\mathbb C^{n\times n}$ there are
  $\varepsilon_0>0$ and an analytic function $\lambda(\varepsilon)$ on
  $|\varepsilon|<\varepsilon_0$ with $\lambda(0)=\lambda$ such that
  $\lambda(\varepsilon)$ is a simple eigenvalue of $A+\varepsilon E$ and
  $$\lambda'(0)=\frac{y^*Ex}{y^*x}.$$
  Hence $\sup_{\|E\|_2\le1}|\lambda'(0)|=\|x\|_2\|y\|_2/|y^*x|$, the
  **condition number** of $\lambda$, attained at
  $E=yx^*/(\|x\|_2\|y\|_2)$. It is at least $1$, and it equals $1$ when $A$
  is normal.

  *Assessment.* Not covered. Mathlib has eigenvalues, characteristic polynomials and an
  implicit function theorem, and TauCeti's eigenvalue perturbation bounds concern
  Hermitian matrices. The analytic branch of a simple eigenvalue under a
  non-Hermitian perturbation, the left-right eigenvector formula for its derivative and
  the attained worst case over unit perturbations are missing.

  *Lean target.* Carriers: Mathlib's `Module.End.HasEigenvalue`, `Polynomial.rootMultiplicity` of
  `Matrix.charpoly` for algebraic simplicity, `Matrix.mulVec` and `Matrix.vecMul` for right and
  left eigenvectors, and Mathlib's analytic implicit function theorem
  (`HasStrictFDerivAt.implicitFunction`) or the simple root of an analytic family of polynomials.
  Conjuncts: (i) for an algebraically simple eigenvalue, `star y ⬝ᵥ x ≠ 0`; (ii) for each `E` there
  are `ε₀ > 0` and a function `λ` analytic on the ball, with `λ 0 = λ₀`, each `λ ε` a simple root
  of `(A + ε • E).charpoly`, and `HasDerivAt λ ((star y ⬝ᵥ E *ᵥ x) / (star y ⬝ᵥ x)) 0`; (iii) the
  supremum of the derivative over `‖E‖ ≤ 1` (Euclidean operator norm) is
  `‖x‖ * ‖y‖ / ‖star y ⬝ᵥ x‖`, attained at the rank-one `E`; (iv) this is at least `1`, with
  equality for normal `A`. The supremum is over a compact set, so a real `sSup` is safe once
  boundedness is shown. Statable at the pins. NASC: not stated.

* **2.15. Perturbation of least squares problems.** Let
  $A\in\mathbb R^{m\times n}$, $m\ge n$, have rank $n$, let $b\in\mathbb R^m$,
  and let $x$ minimize $\|b-Ax\|_2$, with $r=b-Ax$ and $x\ne0$. Let
  $\|\Delta A\|_2\le\varepsilon\|A\|_2$, $\|\Delta b\|_2\le\varepsilon\|b\|_2$
  and $\kappa_2(A)\varepsilon<1$, where $\kappa_2(A)=\sigma_1(A)/\sigma_n(A)$.
  Then $A+\Delta A$ has rank $n$, and if $y$ minimizes
  $\|(b+\Delta b)-(A+\Delta A)y\|_2$ and $s=b+\Delta b-(A+\Delta A)y$, then
  $$\frac{\|x-y\|_2}{\|x\|_2}\le\frac{\kappa_2(A)\varepsilon}
  {1-\kappa_2(A)\varepsilon}\Bigl(2+(\kappa_2(A)+1)
  \frac{\|r\|_2}{\|A\|_2\|x\|_2}\Bigr),\qquad
  \frac{\|r-s\|_2}{\|b\|_2}\le(1+2\kappa_2(A))\varepsilon.$$
  The factor $\kappa_2(A)^2$ multiplying $\|r\|_2$ is genuine: for
  $0<\delta<\eta<1$, $A=\begin{pmatrix}1&0\\0&\eta\\0&0\end{pmatrix}$,
  $b=(1,0,1)^\top$, $\Delta b=0$ and $\Delta A=\delta\,e_3e_2^\top$, one has
  $\kappa_2(A)=1/\eta$, $\|A\|_2=1$, $\varepsilon=\delta$,
  $\kappa_2(A)\varepsilon=\delta/\eta<1$, $x=(1,0)^\top$, $\|r\|_2=1$ and
  $y=(1,\delta/(\eta^2+\delta^2))^\top$, so
  $$\frac{\|x-y\|_2}{\|x\|_2}=\frac{\delta}{\eta^2+\delta^2}
  \ge\tfrac12\kappa_2(A)^2\frac{\|\Delta A\|_2}{\|A\|_2}.$$

  *Assessment.* Finite-dimensional orthogonal projection and singular values
  support the linearization. The coefficient and residual perturbations and
  their dependence on the least-squares geometry remain to be formalized.

  *Lean target.* Carriers: Mathlib's `Matrix.toEuclideanLin`, `LinearMap.singularValues`, the
  Euclidean operator norm, and `EuclideanSpace ℝ (Fin m)`. New definition: least-squares minimizer
  `MinimizesLeastSquares A b x` ($\forall y$, $\|b-Ax\|\le\|b-Ay\|$). Conjuncts, under
  `Function.Injective A.toEuclideanLin` (full column rank, $n\ge1$), `x ≠ 0`, `b ≠ 0`, `0 ≤ ε`, the
  two perturbation bounds and `κ * ε < 1` with `κ = ‖A‖ / σ_{n-1}`: (i) `A + ΔA` has full column
  rank; (ii) the solution bound; (iii) the residual bound; (iv) the example (a `decide`/`norm_num`
  computation at concrete $\eta,\delta$, or a symbolic one). Pitfall: `σ_{n-1} > 0` follows from
  injectivity; without it `κ` is the junk `‖A‖ / 0 = 0`. Depends on 2.10 (Weyl) and on the normal
  equations of 3.11. NASC: `MinimizesLeastSquares.injective_and_norm_sub_div_le` (i)–(iii),
  `sorry`.

* **2.16. Pseudospectra.** Let $A\in\mathbb C^{N\times N}$, $\varepsilon>0$,
  and let $\|(z-A)^{-1}\|=\infty$ for $z\in\Lambda(A)$. The following
  conditions on $z\in\mathbb C$ are equivalent, and the set
  $\Lambda_\varepsilon(A)$ of such $z$ is the **$\varepsilon$-pseudospectrum**:
  (i) $\|(z-A)^{-1}\|>\varepsilon^{-1}$; (ii) $z\in\Lambda(A+E)$ for some
  $E$ with $\|E\|<\varepsilon$; (iii) $\|(z-A)v\|<\varepsilon$ for some $v$
  with $\|v\|=1$. In the $2$-norm they are also equivalent to
  $\sigma_N(z-A)<\varepsilon$. For every norm,
  $\Lambda(A)+\Delta_\varepsilon\subseteq\Lambda_\varepsilon(A)$, where
  $\Delta_\varepsilon$ is the open disc of radius $\varepsilon$ about $0$. In
  the $2$-norm, if $A=V\Lambda V^{-1}$ is diagonalizable, then
  $$\Lambda(A)+\Delta_\varepsilon\subseteq\Lambda_\varepsilon(A)\subseteq
  \Lambda(A)+\Delta_{\varepsilon\kappa_2(V)},$$
  and $\Lambda_\varepsilon(A)=\Lambda(A)+\Delta_\varepsilon$ for all
  $\varepsilon>0$ if and only if $A$ is normal. Each
  $\Lambda_\varepsilon(A)$ is nonempty, open and bounded, and has at most $N$
  connected components, each containing an eigenvalue of $A$.

  *Assessment.* Partly covered. TauCeti gives the Euclidean resolvent norm of
  a Hermitian matrix. The selected statements link a general matrix's
  resolvent, perturbation spectrum and smallest singular value, and give the
  component bound.

  *Scope.* The selected parts are the perturbation and resolvent descriptions
  for general matrices, the component count, and the nonnormal resolvent
  estimates.

  *Lean target.* Carriers: Mathlib's `spectrum ℂ`, `Matrix.toEuclideanLin`,
  `LinearMap.singularValues`, `connectedComponentIn`, `IsOpen`, `Bornology.IsBounded`; TauCeti's
  `Matrix.IsHermitian.l2_opNorm_inv_sub_smul_one` for the Hermitian case. New definition: the open
  pseudospectrum, defined by the residual form (iii), `{z | ∃ v, ‖v‖ = 1 ∧ ‖z • v - A v‖ < ε}`,
  which avoids the junk inverse at eigenvalues. Conjuncts: (i) equivalence with (ii) and, in the
  Euclidean norm, with `singularValues (N - 1) (z • 1 - A) < ε`; (ii) the resolvent form stated as
  `z ∈ spectrum ℂ A ∨ ε⁻¹ < ‖(z • 1 - A)⁻¹‖` (the matrix inverse at an eigenvalue is `0`); (iii)
  $\Lambda+\Delta_\varepsilon\subseteq\Lambda_\varepsilon$ for every induced norm; (iv) the
  Bauer–Fike inclusion for diagonalizable `A`; (v) equality for all $\varepsilon$ iff
  `IsStarNormal A`; (vi) nonempty, open, bounded, every connected component meets `spectrum ℂ A`.
  Dimension $N\ge1$ for nonemptiness. (vi) needs subharmonicity of $\log\|(z-A)^{-1}\|$ or the
  maximum principle for the resolvent, which Mathlib has for holomorphic Banach-valued maps
  (`Complex.norm_le_of_forall_mem_frontier_norm_le`). (iv) depends on 2.13. NASC: `pseudospectrum`
  with its unfolding lemma `mem_pseudospectrum_iff` and `pseudospectrum_eq_empty_of_nonpos`,
  proved; `mem_pseudospectrum_iff_exists_mem_spectrum_add` and
  `mem_pseudospectrum_iff_singularValues_lt` (i), `mem_pseudospectrum_iff_resolvent` (ii) and
  `connectedComponentIn_pseudospectrum_inter_spectrum_nonempty` (vi), `sorry`; (iii)–(v) not
  stated.

* **2.18. Wedin's singular subspace bound.** Let $A,B\in\mathbb C^{m\times n}$
  and let $1\le r<\min(m,n)$. Write $U_A,V_A$ and $U_B,V_B$ for orthonormal
  bases of their leading $r$ left and right singular subspaces, respectively,
  chosen from singular value decompositions. Suppose that
  $\sigma_{r+1}(A)\le a$ and $\sigma_r(B)\ge a+\delta$ with $a,\delta>0$.
  For $\Theta_U$ and $\Theta_V$ the diagonal matrices of principal angles
  between the corresponding left and right subspaces,
  $$\max\{\|\sin\Theta_U\|_2,\|\sin\Theta_V\|_2\}
  \le\frac{\|B-A\|_2}{\delta}.$$

  *Assessment.* TauCeti controls singular subspaces through the squared Gram
  spectrum and supplies related perturbation inequalities. The required
  estimate uses a gap between singular values themselves and has numerator
  exactly the perturbation norm.

  *Lean target.* Carriers: Mathlib's `LinearMap.singularValues` and the Euclidean operator norm;
  TauCeti's singular-subspace perturbation bounds
  (`LinearMap.mul_norm_sinThetaMap_rightSingularSubspace_le` and the left version) and the
  Davis–Kahan residual theorem
  (`TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_le_map_sylvester_apply`),
  applied to the Hermitian dilation $\begin{pmatrix}0&A\\A^*&0\end{pmatrix}$. New definition: a
  leading singular frame `(U, V)` of rank `r` ($U^*U=V^*V=I_r$, $AV=U\Sigma_r$, $A^*U=V\Sigma_r$).
  Statement, with `0 < r < min m n`, `0 < a`, `0 < δ`, `σ_r(A) ≤ a` and `a + δ ≤ σ_{r-1}(B)` in
  zero-based indexing: `max ‖(1 - U_A U_Aᴴ) U_B‖ ‖(1 - V_A V_Aᴴ) V_B‖ ≤ ‖B - A‖ / δ`, the sines of
  the principal angles being the norms of these projector residuals. Pitfall: the zero-based shift
  makes $\sigma_{r+1}$ index `r` and $\sigma_r$ index `r - 1`. Statable at the pins via the
  dilation. NASC: `max_norm_sub_projection_mul_le_of_singular_gap`, `sorry`, without the
  hypotheses `0 < r` and `0 < a` (`a = 0` is the exact rank-`r` case).

## 3. Direct methods for linear systems and least squares

[Synopsis](SYNOPSIS.md#3-direct-methods-for-linear-systems-and-least-squares) · [Coverage inventory](STRUCTURE.md#3-direct-methods-for-linear-systems-and-least-squares)

These gaps concern exact triangular and orthogonal factorizations, their
rounded implementations, least-squares solves, and the combinatorial structure
of sparse elimination.

Rounding error
statements use the standard model of floating-point arithmetic of section 1,
with unit roundoff $u$ and $\gamma_k=ku/(1-ku)$ for $ku<1$; hatted quantities
are the computed ones, and $|M|$ and inequalities between matrices are
entrywise. Such statements are for real data, as in the sources, and they
assume no underflow or overflow. For $A\in\mathbb K^{n\times n}$, $A_k$ is the
leading principal submatrix $A(1{:}k,1{:}k)$. An **LU factorization** of
$A$ is $A=LU$ with $L$ unit lower triangular and $U$ upper triangular. The
perturbation theory of linear systems and least squares problems is in
section 2.

### Gaussian elimination

* **3.1. Existence and uniqueness of the LU factorization.** A matrix
  $A\in\mathbb K^{n\times n}$ has a unique LU factorization if and only if
  $A_k$ is nonsingular for $k=1,\dots,n-1$. In that case
  $$\det A_k=u_{11}u_{22}\cdots u_{kk},\qquad k=1,\dots,n,$$
  so that $u_{kk}=\det A_k/\det A_{k-1}$ for $k\ge2$. If $A_k$ is singular
  for some $k\le n-1$, an LU factorization may exist, but it is then not
  unique. Gaussian elimination without pivoting runs to completion (meets
  no zero pivot in its first $n-1$ stages) exactly when $A_k$ is nonsingular
  for $k=1,\dots,n-1$, and it then computes this factorization.

  *Assessment.* Schur complements and exact elimination support induction on
  leading principal blocks. The factorization theorem includes the converse
  uniqueness criterion and the permitted singular final pivot.

  *Lean target.* Carriers: Mathlib's `Matrix.det`, `Matrix.submatrix` with `Fin.castLE` for the
  leading block $A_k$, `Matrix.IsUpperTriangular`, `Matrix.BlockTriangular`,
  `Matrix.det_of_isUpperTriangular`, and the Schur-complement determinant
  `Matrix.det_fromBlocks₁₁`. New definition: `IsLU A L U` ($L$ unit lower triangular, $U$ upper
  triangular, $A=LU$) over a commutative ring. Conjuncts: (i) `∃! LU` iff `det A_k ≠ 0` for all
  `k < n` (the last block may be singular); (ii) for any LU factorization,
  `det A_k = ∏ i < k, U i i`; (iii) a singular proper leading block with an LU factorization implies
  non-uniqueness; (iv) elimination without pivoting meets no zero pivot in its first $n-1$ stages
  iff the same minors are nonzero, for an explicit recursive definition of elimination (new).
  Statable at the pins over any field; $n=0,1$ are boundary cases where every matrix has a unique
  LU. NASC: `IsLU`, `existsUnique_isLU_iff` (i, over a field), `sorry`; `IsLU.det_submatrix_castLE`
  (ii, over a commutative ring) and `IsLU.det_eq`, proved; (iii) and (iv) not stated.

* **3.2. Partial pivoting.** In **Gaussian elimination with partial
  pivoting** (GEPP), stage $k$ first interchanges row $k$ of the current
  matrix with a row $r\ge k$ for which $|a^{(k)}_{rk}|=\max_{i\ge k}
  |a^{(k)}_{ik}|$, and then eliminates below the diagonal in column $k$.
  Every $A\in\mathbb K^{n\times n}$, singular or not, has a factorization
  $$PA=LU$$
  with $P$ a permutation matrix, $L$ unit lower triangular with
  $|l_{ij}|\le1$ for all $i>j$, and $U$ upper triangular; $U$ is nonsingular
  if and only if $A$ is. If $A$ is nonsingular, every pivot of GEPP is
  nonzero and GEPP computes such a factorization, performing the same
  operations as Gaussian elimination without pivoting applied to $PA$.

  *Assessment.* TauCeti supplies exact row reduction. The numerical theorem
  specifies the partial pivot rule, bounds every multiplier and constructs the
  global permutation and both triangular factors.

  *Lean target.* Carriers: Mathlib's `Equiv.Perm (Fin n)` with `Matrix.submatrix σ id` for $PA$ (or
  `Equiv.Perm.permMatrix`), Mathlib's echelon decomposition certificates (`Echelon.Decomposition`),
  and TauCeti's exact row reduction as a model of the pivoting loop. New definitions: the
  elimination step with partial pivoting (`partialPivotStep`) and the predicate that a sequence of
  reduced matrices arises from GEPP. Conjuncts: (i) every square matrix over `𝕜` (`RCLike`) has
  `P`, `L`, `U` with `PA = LU`, `L` unit lower triangular with `‖L i j‖ ≤ 1`, `U` upper triangular;
  (ii) `U` invertible iff `A` is; (iii) for invertible `A`, GEPP meets no zero pivot and produces
  such factors, and coincides with elimination without pivoting on `PA`. Ties in the pivot choice
  make the factorization non-unique, so (iii) is stated for every admissible pivot sequence.
  Statable at the pins. NASC: `exists_isLU_permuted_norm_le_one` (i), `sorry`; (ii) follows from
  the proved `IsLU.det_eq` with `Matrix.det_permute`; (iii) not stated.

* **3.3. Backward error of LU factorization.** Let $A\in\mathbb R^{m\times n}$
  with $m\ge n$ and $nu<1$. If Gaussian elimination runs to completion on $A$,
  the computed factors $\widehat L\in\mathbb R^{m\times n}$ and
  $\widehat U\in\mathbb R^{n\times n}$ satisfy
  $$\widehat L\widehat U=A+\Delta A,\qquad
  |\Delta A|\le\gamma_n|\widehat L||\widehat U| .$$
  If $m=n$ and the systems $\widehat Ly=b$ and $\widehat Ux=y$ are then solved
  by substitution, the computed solution $\widehat x$ of $Ax=b$ satisfies
  $$(A+\Delta A)\widehat x=b,\qquad |\Delta A|\le(3\gamma_n+\gamma_n^2)|\widehat L||\widehat U| .$$
  If in addition $\widehat L\ge0$ and $\widehat U\ge0$ entrywise and
  $nu<\tfrac12$, then $|\widehat L||\widehat U|\le(1-\gamma_n)^{-1}|A|$, so that
  $|\Delta A|\le(3\gamma_n+\gamma_n^2)(1-\gamma_n)^{-1}|A|$. With pivoting, these bounds
  hold with $A$ replaced by the permuted matrix $PA$ (or $PAQ$) that is
  eliminated without interchanges.

  *Assessment.* The factorization and substitution identities must be joined
  with the scalar rounding model. This gives separate certificates for the
  computed factors and for the computed solution.

  *Lean target.* Carriers: `NASC.HasRelativeError`, `NASC.roundingGamma`, `NASC.SumTree` (section 1
  model), Mathlib's `Matrix`. New definition: a rounded Doolittle elimination predicate
  `IsRoundedElimination` on `A : Matrix (Fin m) (Fin n) ℝ` with `n ≤ m` and computed factors
  `L̂ : Matrix (Fin m) (Fin n) ℝ`, `Û : Matrix (Fin n) (Fin n) ℝ`, each entry obtained by a rounded
  inner product (any order) and, for $\widehat L$, a rounded division. Conjuncts: (i)
  `|L̂ * Û - A| ≤ roundingGamma u n * (|L̂| * |Û|)` entrywise; (ii) for `m = n`, the solve by the
  two substitutions of 1.13 has `|ΔA| ≤ (3 * γₙ + γₙ ^ 2) * (|L̂| * |Û|)` with
  `γₙ = roundingGamma u n` (the printed $2\gamma_n$ fails for $n\ge4$; reference guide of 3.3);
  (iii) the nonnegative-factor bound under `n * u < 1/2`. Hypotheses `0 ≤ u`, `n * u < 1`,
  nonzero computed pivots. Depends on 1.8–1.10 and 1.13 (the back-substitution case of 1.13 is
  needed). NASC: `IsRoundedElimination`, `IsRoundedElimination.abs_residual_le` (i), `sorry`;
  (ii)–(iii) not stated.

* **3.5. Growth under partial pivoting.** For GEPP on any nonzero
  $A\in\mathbb K^{n\times n}$, $\rho_n\le2^{n-1}$, and $|u_{ij}|\le2^{i-1}
  \max_{k\le i}|a_{kj}|$ for the matrix $PA=(a_{kj})$ that is eliminated.
  The bound $2^{n-1}$ is attained for every $n$: for the matrix with
  $a_{ii}=1$, $a_{ij}=-1$ for $i>j$, $a_{in}=1$ for all $i$, and all other
  entries $0$, partial pivoting with ties broken in favour of the smallest
  row index makes no interchanges, and $u_{in}=2^{i-1}$, so
  $\rho_n=|u_{nn}|=2^{n-1}$.

  *Assessment.* The bound needs a recurrence for the entries of the reduced
  matrices and a tie rule for the sharp example. Algebraic elimination alone
  does not encode these choices.

  *Lean target.* Carriers: the exact GEPP model of 3.2 (`partialPivotStep`,
  `IsPartialPivotElimination`) over `𝕜` (`RCLike`). Conjuncts: (i) each reduced entry is at most
  twice the maximal entry of the previous reduced matrix, hence $\rho_n\le2^{n-1}$ (state $\rho_n$
  as a ratio of maxima over `Finset.univ.sup'`, with `A ≠ 0` so the denominator is positive); (ii)
  the row bound $|u_{ij}|\le2^{i-1}\max_{k\le i}|a_{kj}|$ for the permuted matrix; (iii) for the
  explicit Wilkinson matrix and ties broken towards the smallest row index, no interchange occurs
  and $u_{in}=2^{i-1}$, so $\rho_n=2^{n-1}$ (an explicit computation, by induction on `n`).
  Statable at the pins. NASC: `IsPartialPivotElimination.norm_entry_le_two_pow` (the stage bound in
  (i)), proved; (ii) and (iii) not stated.

* **3.6. No growth for diagonally dominant and positive definite matrices.**
  - Let $A\in\mathbb R^{n\times n}$ be nonsingular and **diagonally dominant
    by rows**, $|a_{ii}|\ge\sum_{j\ne i}|a_{ij}|$ for all $i$, or by columns
    (that is, $A^\top$ is diagonally dominant by rows). Then $A$ has an LU
    factorization, and Gaussian elimination without pivoting has
    $\rho_n\le2$. If $A$ is diagonally dominant by columns, then
    $|l_{ij}|\le1$, so GEPP (with ties broken in favour of the current row)
    makes no interchanges.
  - If $A\in\mathbb R^{n\times n}$ is symmetric positive definite, then
    every reduced matrix of Gaussian elimination without pivoting has a
    symmetric positive definite trailing block, and $\rho_n=1$.

  *Assessment.* Not covered. Mathlib proves nonsingularity of strictly diagonally
  dominant matrices and the Schur-complement identities, and TauCeti the exact Cholesky
  factor. The invariance of (weak) diagonal dominance and of positive definiteness under
  an elimination step, and the resulting growth bounds, are missing.

  *Lean target.* Carriers: Mathlib's `Matrix.PosDef`, the diagonal dominance hypothesis as an
  explicit inequality (Mathlib's `Matrix.det_ne_zero_of_sum_row_lt_diag` covers strict dominance
  only), and the exact elimination of 3.1 with the growth factor of 3.4–3.5. Conjuncts: (i) a
  nonsingular matrix diagonally dominant by rows or by columns has nonzero proper leading minors,
  hence an LU factorization (3.1), and every reduced matrix of elimination without pivoting is
  again diagonally dominant with entries at most twice the maximal entry, so $\rho_n\le2$; (ii)
  column dominance gives `‖L i j‖ ≤ 1`, so GEPP with ties towards the current row makes no
  interchange; (iii) for `A.PosDef`, every trailing block of a reduced matrix is a Schur
  complement, hence `PosDef` (Mathlib's Schur-complement criterion `Matrix.PosDef.fromBlocks₁₁`),
  and the maximal modulus entry of a positive definite matrix lies on the diagonal, whose entries
  do not increase, so $\rho_n=1$. Nonsingularity cannot be dropped in (i) (the zero matrix is
  weakly dominant). Statable at the pins. NASC: not stated.

### Cholesky and QR factorization

* **3.8. Backward stability of Cholesky factorization.** Let
  $A\in\mathbb R^{n\times n}$ be symmetric and $(n+1)u<1$.
  - Let $A$ be positive definite. If the Cholesky factorization runs to
    completion (every square root has a positive argument), the computed
    factor satisfies
    $$\widehat R^\top\widehat R=A+\Delta A,\qquad
    |\Delta A|\le\gamma_{n+1}|\widehat R^\top||\widehat R| ,$$
    and the computed solution of $Ax=b$ by the two triangular solves
    satisfies $(A+\Delta A)\widehat x=b$ with $|\Delta A|\le(3\gamma_{n+1}
    +\gamma_{n+1}^2)|\widehat R^\top||\widehat R|$. If also $n\gamma_{n+1}<1$, this
    $\Delta A$ satisfies
    $$\|\Delta A\|_2\le n(3\gamma_{n+1}+\gamma_{n+1}^2)(1-n\gamma_{n+1})^{-1}\|A\|_2 .$$
  - Let $A$ have positive diagonal entries, let $(n+1)u<\tfrac12$ (that is,
    $\gamma_{n+1}<1$), and write $A=DHD$ with $D=\mathop{\mathrm{diag}}(A)^{1/2}$, so that $H$ is
    symmetric with unit diagonal. If $\lambda_{\min}(H)>n\gamma_{n+1}/(1-\gamma_{n+1})$, then $A$ is
    positive definite and the Cholesky factorization runs to completion and gives a nonsingular
    $\widehat R$. If $\lambda_{\min}(H)\le-n\gamma_{n+1}/(1-\gamma_{n+1})$, it fails: some square
    root has a nonpositive argument.

  *Assessment.* TauCeti constructs the exact Cholesky factor. The rounded
  recursion must account for breakdown and establish the componentwise
  backward error upon completion.

  *Lean target.* Carriers: section 1 model as in 3.3; Mathlib's `Matrix.PosDef`,
  `Matrix.IsHermitian.eigenvalues₀` and the Euclidean operator norm; TauCeti's exact factor
  `TauCeti.cholesky` (real, lower triangular with positive diagonal) for comparison. New
  definition: a rounded Cholesky recursion `IsRoundedCholesky A R u`, including the event of
  completion (every square-root argument positive). Conjuncts: (i) for `A.PosDef`, completion gives
  `|R̂ᵀ * R̂ - A| ≤ roundingGamma u (n + 1) * (|R̂ᵀ| * |R̂|)`; (ii) the solve bound with
  $3\gamma_{n+1}+\gamma_{n+1}^2$; (iii) the 2-norm bound under `n * roundingGamma u (n + 1) < 1`; (iv) for
  symmetric `A` with positive diagonal and `(n + 1) * u < 1 / 2`, $H=D^{-1}AD^{-1}$: if
  $\lambda_{\min}(H)>n\gamma_{n+1}/(1-\gamma_{n+1})$ the recursion completes with nonsingular
  $\widehat R$; if $\lambda_{\min}(H)\le-n\gamma_{n+1}/(1-\gamma_{n+1})$ it does not complete.
  Pitfall: `Real.sqrt` of a negative argument is `0`, so completion must be an explicit positivity
  condition in the predicate, not inferred from the output. Use `eigenvalues₀` with index `n - 1`
  for $\lambda_{\min}$ ($n\ge1$). Depends on 1.8–1.10, 1.13 and 3.3. NASC: `IsRoundedCholesky`,
  `IsRoundedCholesky.abs_residual_le` (i), `sorry`; (ii)–(iv) not stated.

* **3.9. QR factorization.** Let $A\in\mathbb K^{m\times n}$ with $m\ge n$.
  There is a unitary $Q\in\mathbb K^{m\times m}$ and an upper trapezoidal
  $R\in\mathbb K^{m\times n}$ with $A=QR$ (a **full QR factorization**);
  keeping the first $n$ columns of $Q$ and the first $n$ rows of $R$ gives a
  **reduced QR factorization** $A=Q_1R_1$ with $Q_1^*Q_1=I_n$ and $R_1$
  upper triangular. If $A$ has full column rank, the reduced QR
  factorization with positive real diagonal entries of $R_1$ is unique, the
  columns of $Q_1$ span $\mathop{\mathrm{range}}(A)$, and $R_1^*R_1$ is the
  Cholesky factorization of $A^*A$.

  *Assessment.* Partly covered. TauCeti has unitary triangular factorization
  for invertible square matrices. The general rectangular or rank-deficient
  statement and the full-column-rank reduced normalization are the focus.

  *Scope.* The target includes full and reduced factorizations for rectangular
  matrices, including deficient rank in the full factorization, and the
  positive-diagonal uniqueness assertion.

  *Lean target.* Carriers: Mathlib's `unitary (Matrix (Fin m) (Fin m) 𝕜)`,
  `Matrix.IsUpperTriangular` (for the square part), `Matrix.toEuclideanLin`, `LinearMap.range`,
  `Matrix.PosDef`; TauCeti's
  `Matrix.GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq` for the square
  invertible case and `Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq` for the
  Cholesky link. New definition: upper trapezoidal for a rectangular matrix
  (`∀ i j, j < i → R i j = 0` with `Fin m` and `Fin n` compared through their values). Conjuncts:
  (i) for `n ≤ m`, `∃ Q ∈ unitary, ∃ R` upper trapezoidal, `A = Q * R` (rank deficiency allowed);
  (ii) the reduced form with `Q₁ᴴ * Q₁ = 1`; (iii) at full column rank, uniqueness of the reduced
  factorization with `0 < re (R₁ i i)` and real diagonal, `range Q₁ = range A`, and `R₁ᴴ R₁` the
  Cholesky factorization of `Aᴴ A`. Statable at the pins (Gram–Schmidt via Mathlib's `gramSchmidt`,
  or Householder). NASC: `exists_unitary_mul_upperTrapezoidal` (i, for any shape, without
  `n ≤ m`) and `existsUnique_thinQR` (iii), `sorry`.

* **3.10. Backward stability of Householder QR.** There is a small integer
  constant $c$, independent of $m$ and $n$, with the following property. Let
  $A\in\mathbb R^{m\times n}$, $m\ge n$, write
  $\tilde\gamma_{m}=cmu/(1-cmu)$, and assume $mn\tilde\gamma_{m}<1/2$.
  If $\widehat R$ is the computed upper trapezoidal factor of the Householder
  QR algorithm, there is an orthogonal $Q\in\mathbb R^{m\times m}$ with
  $$A+\Delta A=Q\widehat R,\qquad
  \|\Delta A\|_F\le n\tilde\gamma_{m}\|A\|_F,\qquad
  |\Delta A|\le mn\tilde\gamma_{m}G|A| ,$$
  for some $G\ge0$ with $\|G\|_F=1$.
  Here $Q$ is the product of the Householder matrices that the exact
  algorithm would apply to the successive computed reduced matrices.

  *Assessment.* Exact QR and norm preservation by reflectors are ingredients.
  The backward error must compare the computed triangular data with a product
  of exact unitary reflectors.

  *Lean target.* Carriers: section 1 model; Mathlib's `Matrix.frobeniusNormedAddCommGroup`,
  `Matrix.orthogonalGroup`; the reflection `I - 2vvᵀ/vᵀv` as Mathlib's `Submodule.reflection` on
  `EuclideanSpace ℝ (Fin m)` or a matrix-level definition. New definitions: the computed
  Householder vector and the rounded application of a reflector (Higham's model (18.3): the
  computed vector is within $\tilde\gamma_m$ of the exact one). Conjuncts: (i) a sequence of $r$
  rounded reflector applications to `A` gives `Q.transpose * (A + ΔA)` with
  `‖ΔA‖_F ≤ r * γ̃ * ‖A‖_F` and `|ΔA| ≤ m * r * γ̃ * G * |A|`, `‖G‖_F = 1`, under
  `m * r * γ̃ < 1/2`; (ii) the QR theorem as (i) with $r=n$ and the zeroed entries set to zero. The
  constant $c$ is existential and must be fixed before $m$, $n$, $u$. The rounding model of a
  reflector application is the main design decision; the exact reflector algebra is elementary.
  Depends on 1.8 and 1.10. NASC: `exists_orthogonal_mul_of_householder_step_bound` (accumulation
  step of (i)), `sorry`.

### Linear least squares

* **3.11. Least squares and the normal equations.** Let $A\in\mathbb
  K^{m\times n}$ and $b\in\mathbb K^m$. The problem
  $\min_{x\in\mathbb K^n}\|b-Ax\|_2$ has at least one solution. A vector $x$
  is a solution if and only if the residual $r=b-Ax$ is orthogonal to
  $\mathop{\mathrm{range}}(A)$, that is, if and only if $x$ solves the
  **normal equations**
  $$A^*Ax=A^*b,$$
  and if and only if $Ax=Pb$ with $P$ the orthogonal projector onto
  $\mathop{\mathrm{range}}(A)$. All solutions have the same $Ax$ and the
  same residual. The solution is unique if and only if $A$ has full column
  rank; then $x=R_1^{-1}Q_1^*b$ for the reduced QR factorization of 3.9.

  *Assessment.* Partly covered. Orthogonal projection supplies the closest
  point in the range of a finite-dimensional map. The selected assertions
  connect that fitted value to the normal equations and the reduced-QR
  solution.

  *Scope.* The targets are the matrix normal equations and the
  full-column-rank QR solve. The projection description fixes the fitted value
  in both formulations.

  *Lean target.* Carriers: Mathlib's `Matrix.toEuclideanLin`, `LinearMap.range`,
  `Submodule.starProjection` (orthogonal projection) and its closest-point characterization,
  `Matrix.conjTranspose`. Definition: `MinimizesLeastSquares A b x` (see 2.15). Conjuncts: (i)
  existence of a minimizer; (ii) `MinimizesLeastSquares A b x ↔ Aᴴ *ᵥ A *ᵥ x = Aᴴ *ᵥ b` ↔ residual
  orthogonal to the range ↔ `A x = P b`; (iii) all minimizers have the same `A x`; (iv) uniqueness
  iff injectivity; (v) the QR solve. Statable and provable at the pins. NASC:
  `minimizesLeastSquares_iff_normalEquation` (ii, normal equations) and
  `minimizesLeastSquares_iff_of_thinQR` (v), proved; (i), (iii), (iv) not stated.

### Iterative refinement

* **3.14. Iterative refinement.** Let $A\in\mathbb R^{n\times n}$ be
  nonsingular, $b\in\mathbb R^n$, and $x=A^{-1}b$. Let $\bar u\le u$ be the
  unit roundoff of the precision in which residuals are formed, with
  $\bar\gamma_k=k\bar u/(1-k\bar u)$ and $(n+1)\bar u<1$. Starting from
  $x_1\in\mathbb R^n$, iterative refinement computes, for $i=1,2,\dots$,
  $r_i$, $d_i$ and $x_{i+1}$ such that
  $$r_i=s_i+f_i,\quad s_i=b-Ax_i+\Delta s_i,\quad
  |\Delta s_i|\le\bar\gamma_{n+1}(|b|+|A||x_i|),\quad |f_i|\le u|s_i|;$$
  $$(A+\Delta A_i)d_i=r_i,\qquad \theta_i:=\|A^{-1}\Delta A_i\|_\infty<1;$$
  $$x_{i+1}=x_i+d_i+\Delta x_i,\qquad |\Delta x_i|\le u|x_i+d_i| .$$
  Define $F_i$ by $(A+\Delta A_i)^{-1}=(I+F_i)A^{-1}$, so that
  $\|F_i\|_\infty\le\theta_i/(1-\theta_i)$. Then
  $$|x_{i+1}-x|\le G_i|x_i-x|+g_i,$$
  $$G_i=(1+u)|F_i|+2uI+(1+u)\bigl(u+(1+u)\bar\gamma_{n+1}\bigr)
  (I+|F_i|)|A^{-1}||A|,$$
  $$g_i=2(1+u)^2\bar\gamma_{n+1}(I+|F_i|)|A^{-1}||A||x|+u|x| .$$
  Consequently, if $\|G_i\|_\infty\le q<1$ and $\|g_i\|_\infty\le g$ for all
  $i$, then
  $$\limsup_{i\to\infty}\|x_i-x\|_\infty\le\frac{g}{1-q}.$$

  *Assessment.* The task is to combine residual evaluation, solve
  perturbations and the rounded update in a single componentwise recurrence.
  Exact inverse perturbation estimates are useful for bounding the correction
  error.

  *Lean target.* Carriers: Mathlib's `Matrix`, `Matrix.mulVec`, entrywise absolute values, the
  $\infty$-norm instance `Matrix.linftyOpNormedAddCommGroup`, `Filter.limsup`. New definition: an
  iterative refinement trace, a sequence `x : ℕ → (Fin n → ℝ)` with witnesses `s i`, `f i`, `ΔA i`,
  `Δx i` satisfying the hypotheses of the statement (residual model with $\bar u$, solver model
  with $\theta_i<1$, update model with $u$). Conjuncts: (i) the componentwise recurrence
  `|x (i+1) - x| ≤ G i * |x i - x| + g i` with the explicit $G_i,g_i$ (entrywise, as
  `Matrix.mulVec` of nonnegative matrices); (ii) the abstract `limsup` consequence in any normed
  space under `‖G_i‖ ≤ q < 1` and `‖g_i‖ ≤ g`. Pitfall: `limsup` of a real sequence that is not
  bounded above is a junk value; (ii) must first prove boundedness (from the contraction) or be
  stated in `ℝ≥0∞`. Also $F_i$ is defined by an inverse, so `A + ΔA i` must be shown invertible
  from $\theta_i<1$ before `F_i` is used. Depends on 1.8 and 1.10. NASC:
  `limsup_le_div_one_sub_of_le_mul_add` (ii) for a real sequence and its norm corollary
  `limsup_norm_le_of_refinement_bound`, both proved; (i) not stated.

### Sparse elimination

* **3.15. Elimination graphs and the fill path theorem.** Let $A\in\mathbb
  K^{n\times n}$ have nonzero diagonal and symmetric nonzero pattern, and let
  $G$ be its **graph**: vertices $1,\dots,n$, and an edge $\{i,j\}$ for
  $i\ne j$ whenever $a_{ij}\ne0$. Eliminating vertex $v$ from a graph means
  deleting $v$ and joining every two remaining neighbours of $v$ by an edge.
  Eliminating $1,2,\dots,n$ in turn from $G$, and keeping all edges ever
  created, gives the **filled graph** $G^+$; its edges not in $G$ are the
  **fill**. Then:
  - $\{i,j\}$ is an edge of $G^+$ if and only if $G$ contains a path from
    $i$ to $j$ all of whose interior vertices are numbered less than
    $\min(i,j)$ (Rose–Tarjan–Lueker).
  - If $A$ is Hermitian positive definite with Cholesky factor $L=R^*$, then
    for $i>j$, $l_{ij}\ne0$ implies that $\{i,j\}$ is an edge of $G^+$. The
    converse holds when no exact numerical cancellation occurs, so $G^+$ is
    the structural nonzero pattern of $L+L^*$.
  - In particular, if $l_{ji}\ne0$ and $l_{ki}\ne0$ with $i<j<k$, then
    $\{j,k\}$ is an edge of $G^+$ (Parter).

  *Assessment.* Mathlib graph connectivity and path operations can be reused.
  The gap is the elimination-graph fill criterion and its link to the possible
  nonzero positions in a factor.

  *Lean target.* Carriers: Mathlib's `SimpleGraph (Fin n)`, `SimpleGraph.Walk` with `Walk.support`,
  and `SimpleGraph.fromRel`; for the pattern statements, `Matrix.PosDef` and TauCeti's Cholesky
  factor (real case) or the complex upper factor of
  `Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq`. New definitions: vertex
  elimination `eliminateVertex G v` (delete `v`, make its neighbourhood a clique; keeping `v`
  isolated keeps the vertex type fixed), the filled graph after eliminating `0, …, n-1` while
  keeping all edges, and the graph of a matrix. Conjuncts: (i) the fill path theorem: `i ≠ j`
  adjacent in the filled graph iff there is a walk from `i` to `j` whose interior support lies
  below `min i j`; (ii) for positive definite `A` with Cholesky factor `L`, `L i j ≠ 0` with
  `i > j` implies adjacency in the filled graph; (iii) the converse for generic values, stated as:
  for the pattern of `A`, there is a positive definite matrix with that pattern whose factor has
  exactly the filled pattern (the source's "no cancellation" convention has no direct formal
  meaning); (iv) Parter's lemma, a corollary of (i). Statable at the pins; (i) is purely
  combinatorial. Related owner: the PerfectAndChordalGraphs roadmap (perfect elimination
  orderings). NASC: `eliminateVertex`, `eliminateVertices` and
  `eliminateVertices_adj_iff_exists_walk` (i, for an arbitrary list of eliminated vertices),
  `sorry`; (ii)–(iv) not stated.

* **3.16. Elimination tree.** In the setting of 3.15, the **parent** of a
  vertex $j<n$ is the least $i>j$ with $\{i,j\}$ an edge of $G^+$, if there
  is one; otherwise $j$ is a root. The resulting forest $T$ on
  $\{1,\dots,n\}$ is the **elimination tree** (by convention, even when it is
  a forest). Every vertex is numbered less than its parent. Moreover:
  - if $\{i,k\}$ is an edge of $G^+$ with $i<k$, then $k$ is an ancestor of
    $i$ in $T$; in particular, if $a_{ki}\ne0$ with $i<k$, then $i$ is a
    descendant of $k$ (Liu);
  - for each $k$, the set $\{k\}\cup\{j<k:\{j,k\}\text{ is an edge of }
    G^+\}$, the structure of row $k$ of $L$, is the vertex set of the
    **row subtree**: the union of the paths in $T$ from each $i<k$ with
    $a_{ki}\ne0$ up to $k$;
  - if $P$ is the permutation matrix of a postordering of $T$, the filled
    graphs of $A$ and of $PAP^\top$ are isomorphic, and their elimination
    trees are isomorphic, so the two Cholesky factorizations have the same
    numbers of structural nonzeros and the same operation counts.

  *Assessment.* Not covered. Mathlib's simple graphs, walks and relation closures supply
  the language, and the PerfectAndChordalGraphs roadmap owns perfect elimination
  orderings. The elimination tree, Liu's ancestor theorem, the row subtrees and the
  invariance of fill under postordering are missing.

  *Lean target.* Carriers: as in 3.15 (`SimpleGraph (Fin n)`, the filled graph), with Mathlib's
  order on `Fin n`. New definitions: the parent function `parent : Fin n → Option (Fin n)` (least
  larger neighbour in the filled graph, via `Finset.min` on the filtered neighbour set), the
  ancestor relation as the transitive closure `Relation.TransGen` of the parent relation, and the
  row subtree of `k`. Conjuncts: (i) `parent j = some i → j < i`; (ii) Liu: an edge `{i, k}` of the
  filled graph with `i < k` makes `k` an ancestor of `i`; (iii) the row structure
  `{k} ∪ {j < k | adjacent j k}` equals the union of the tree paths from each `i < k` with
  `A k i ≠ 0` up to `k`; (iv) for a postordering permutation `σ` of the forest, the filled graph of
  the permuted matrix is the image of the filled graph under `σ`, and so are the elimination trees
  (graph isomorphisms `SimpleGraph.Iso`), giving equal fill counts. Statable at the pins; depends
  on 3.15 (i). NASC: not stated.

## 4. Eigenvalue and singular value computations

[Synopsis](SYNOPSIS.md#4-eigenvalue-and-singular-value-computations) · [Coverage inventory](STRUCTURE.md#4-eigenvalue-and-singular-value-computations)

Hermitian and normal spectral decomposition, singular-value theory and
compression interlacing provide the analytic framework. The selected
statements concern normal forms beyond that framework, actual iterations, and
the nonlinear eigenvalue problem.

A matrix $H=(h_{ij})$ is **upper Hessenberg** if $h_{ij}=0$ for $i>j+1$, and
an upper Hessenberg matrix is **unreduced** if $h_{i+1,i}\ne0$ for all $i$.
A **phase matrix** is a diagonal unitary matrix. For a matrix that need not
be Hermitian, an ordering of its eigenvalues is stated where it is used.
Statements on rounding errors use the standard model 1.5; there
$O(u)$ means a quantity bounded by $c_n u$ for all sufficiently small $u$,
with $c_n$ depending only on the dimension.

Common carriers at the pins for this section: square matrices
`Matrix (Fin n) (Fin n) 𝕜` with `[RCLike 𝕜]`, `Matrix.unitaryGroup` (or
`unitary (Matrix _ _ 𝕜)`) and `Matrix.orthogonalGroup`, the predicates
`Matrix.IsUpperTriangular`, `Matrix.BlockTriangular` and
`Matrix.IsUpperHessenberg`, `Matrix.IsHermitian` with
`Matrix.IsHermitian.eigenvalues₀` (antitone, `0`-indexed), `Matrix.charpoly`
with `Polynomial.roots`, `Matrix.toEuclideanLin` on `EuclideanSpace 𝕜 (Fin n)`,
and the Euclidean operator norm from `open scoped Matrix.Norms.L2Operator`.
Mathlib's eigenvalues are `0`-indexed in decreasing order, so $\lambda_1$ of
the synopsis is `eigenvalues₀ 0`; every statement with $n\ge1$ or $n\ge3$
indexes over `Fin (n + 1)` or `Fin (n + 3)` to keep the indices in range.

### Unitary normal forms

* **4.1. Schur decomposition.** For every $A\in\mathbb C^{n\times n}$ and
  every ordering $\lambda_1,\dots,\lambda_n$ of its eigenvalues, counted with
  algebraic multiplicity, there is a unitary $U$ such that $U^*AU=T$ is upper
  triangular with $t_{ii}=\lambda_i$. If $A$ is real and all its eigenvalues
  are real, $U$ can be taken real orthogonal. For every
  $A\in\mathbb R^{n\times n}$ there is a real orthogonal $Q$ such that
  $Q^\top AQ$ is block upper triangular with diagonal blocks of order $1$ or
  $2$, where each $2\times2$ diagonal block has a pair of non-real complex
  conjugate eigenvalues (the **real Schur form**); the diagonal blocks can be
  arranged in any prescribed order.

  *Assessment.* The Hermitian and normal diagonalizations treat special
  normal classes. General Schur forms require unitary triangularization with
  chosen eigenvalue order and real invariant blocks of dimension one or two.

  *Lean target.* Carriers at the pins: `Matrix.IsUpperTriangular`,
  `unitary (Matrix (Fin n) (Fin n) ℂ)`, `Matrix.orthogonalGroup`,
  `Matrix.charpoly`, `Polynomial.roots`, `Matrix.BlockTriangular`. The order
  of the eigenvalues is a function `eigs : Fin n → ℂ` with
  `Multiset.ofList (List.ofFn eigs) = A.charpoly.roots`; for real $A$ the
  roots are those of `(A.map (algebraMap ℝ ℂ)).charpoly`. The real Schur form
  needs one new predicate: `IsRealSchurForm T b`, for `T : Matrix (Fin n) (Fin n) ℝ`
  and a monotone block map `b : Fin n → Fin k`, saying that `T.BlockTriangular b`,
  every fibre of `b` has one or two elements, and the `2 × 2` diagonal blocks
  have characteristic polynomials without real roots; the prescribed order is
  a list of the blocks' complex eigenvalue multisets. Conjuncts: (i) the
  complex ordered form; (ii) real orthogonal $U$ when the characteristic
  polynomial splits over $\mathbb R$; (iii) existence of the real Schur form
  with a prescribed order of the blocks. Pitfall: the diagonal must be
  matched to `eigs` entrywise, not as a multiset, to express the order; for
  $n=0$ all conjuncts are trivial. Everything is statable at the pins; (iii)
  depends on the block predicate. NASC: `NASC.exists_schur_of_roots`
  (EigenvalueMethods.lean) states (i), `sorry`.

* **4.3. Singular value decomposition.** For every
  $A\in\mathbb C^{m\times n}$, with $p=\min\{m,n\}$, there are unitary
  $U\in\mathbb C^{m\times m}$ and $V\in\mathbb C^{n\times n}$ such that
  $$U^*AV=\Sigma=\mathrm{diag}(\sigma_1,\dots,\sigma_p)\in\mathbb R^{m\times n},
  \qquad \sigma_1\ge\cdots\ge\sigma_p\ge0 .$$
  If $A$ is real, $U$ and $V$ can be taken real orthogonal. The **singular
  values** $\sigma_i$ are uniquely determined: $\sigma_1^2,\dots,\sigma_p^2$
  are the $p$ largest eigenvalues of $A^*A$ and of $AA^*$, and the nonzero
  singular values are the square roots of the nonzero eigenvalues of $A^*A$.
  The rank of $A$ is the number of nonzero singular values,
  $\|A\|_2=\sigma_1$, and $\|A\|_F^2=\sigma_1^2+\cdots+\sigma_p^2$. If $A$ is
  Hermitian, its singular values are the absolute values of its eigenvalues.
  If $m=n$, the Hermitian matrix
  $$H=\begin{pmatrix}0&A^*\\A&0\end{pmatrix}\in\mathbb C^{2n\times2n}$$
  satisfies
  $$H\begin{pmatrix}V&V\\U&-U\end{pmatrix}
  =\begin{pmatrix}V&V\\U&-U\end{pmatrix}
  \begin{pmatrix}\Sigma&0\\0&-\Sigma\end{pmatrix},$$
  so its eigenvalues are $\pm\sigma_1,\dots,\pm\sigma_n$.

  *Assessment.* Partly covered. Mathlib supplies ordered singular values and
  the rank identity, and TauCeti supplies the square unitary SVD, rectangular
  rank-one expansions and the Hermitian dilation. The selected assertion is
  the rectangular full factorization in orthonormal coordinates; the identity
  $\|A\|_2=\sigma_1$ and the dilation eigenvalues are short consequences.

  *Scope.* The target is the explicit rectangular factorization with ordered
  diagonal, including real orthogonal factors for real input.

  *Lean target.* Carriers at the pins: `LinearMap.singularValues` of
  `Matrix.toEuclideanLin A`, `TauCeti`'s `Matrix.exists_unitary_mul_diagonal_mul_unitary`
  for the square case and
  `LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`. The
  rectangular diagonal `Σ : Matrix (Fin m) (Fin n) ℝ` with `Σ i j = σ_i` for
  `i.val = j.val` and `0` otherwise is NASC's `singularValueDiagonal A`
  (Conditioning.lean). Conjunct: there are `U ∈ unitary (Matrix (Fin m) (Fin m) 𝕜)`
  and `V ∈ unitary (Matrix (Fin n) (Fin n) 𝕜)` with `Uᴴ * A * V` equal to the
  diagonal; over `𝕜 = ℝ`, `unitary` is the orthogonal group, so one statement
  over `RCLike 𝕜` covers both fields. Pitfall: `singularValues` is a
  function `ℕ → ℝ` that is `0` beyond the rank, so the diagonal entries
  beyond the rank are correctly zero, but indices must be compared through
  `Fin.val`. Statable at the pins; extend the orthonormal families of the
  rank-one expansion to bases with `Orthonormal.exists_orthonormalBasis_extension`.
  NASC: `NASC.exists_unitary_conjTranspose_mul_eq_singularValueDiagonal`
  (EigenvalueMethods.lean), `sorry`.

### Vector iterations

* **4.4. Power method and inverse iteration.** Let $q^{(0)}$ be a unit
  vector. The **power method** sets $q^{(k)}=Aq^{(k-1)}/\|Aq^{(k-1)}\|_2$ and
  $\nu^{(k)}=q^{(k)*}Aq^{(k)}$ for $k\ge1$.
  - Let $A\in\mathbb C^{n\times n}$ be diagonalizable, with eigenpairs
    $(\lambda_i,x_i)$, $\|x_i\|_2=1$, and
    $|\lambda_1|>|\lambda_2|\ge\cdots\ge|\lambda_n|$. Write
    $q^{(0)}=\sum_i\alpha_ix_i$ and assume $\alpha_1\ne0$. Then the iteration
    is defined for all $k$, and there are a constant $C$, depending on $A$
    and $q^{(0)}$, and scalars $\mu_k$ with $|\mu_k|=1$, such that
    $$\|\mu_kq^{(k)}-x_1\|_2\le C\,|\lambda_2/\lambda_1|^k,\qquad k\ge1,$$
    and $\nu^{(k)}\to\lambda_1$.
  - If moreover $A$ is real symmetric, $q^{(0)}$ is real, the $x_i$ are
    orthonormal, and $\cos\theta_0=|x_1^\top q^{(0)}|\ne0$, then
    $$|\lambda_1-\nu^{(k)}|\le\max_i|\lambda_1-\lambda_i|\,\tan^2\theta_0\,
    \Bigl|\frac{\lambda_2}{\lambda_1}\Bigr|^{2k},\qquad k\ge1 .$$
  - **Inverse iteration** with shift $\mu$, not an eigenvalue of $A$, is the
    power method applied to $(A-\mu I)^{-1}$, with
    $\nu^{(k)}=q^{(k)*}Aq^{(k)}$. Let $A$ be real symmetric with orthonormal
    eigenvectors $q_j$, let $\mu\in\mathbb R$ and $q^{(0)}\in\mathbb R^n$, and
    suppose there are indices $J\ne K$ with
    $|\mu-\lambda_J|<|\mu-\lambda_K|\le|\mu-\lambda_j|$ for all $j\ne J$. If
    $q_J^\top q^{(0)}\ne0$, then as $k\to\infty$, for a suitable choice of
    sign at each step,
    $$\|q^{(k)}-(\pm q_J)\|_2=O\Bigl(\Bigl|\frac{\mu-\lambda_J}{\mu-\lambda_K}
    \Bigr|^k\Bigr),\qquad
    |\nu^{(k)}-\lambda_J|=O\Bigl(\Bigl|\frac{\mu-\lambda_J}{\mu-\lambda_K}
    \Bigr|^{2k}\Bigr).$$

  *Assessment.* Spectral decomposition gives the coefficients in the
  eigenbasis. The numerical theorem determines the limiting line and
  convergence rate of normalized power and inverse iterates.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℂ (Fin (n + 1))`, an
  eigenbasis `Module.Basis (Fin (n + 1)) ℂ _` of unit vectors, and the
  normalized step NASC `powerStep A x = ‖A x‖⁻¹ • A x`. Conjuncts: (i) the
  diagonalizable bound with a phase $\mu_k$ and a constant depending on $A$ and
  $q^{(0)}$; (ii) $\nu^{(k)}\to\lambda_1$; (iii) the real symmetric bound
  with $\tan^2\theta_0$, using `Matrix.IsHermitian.eigenvalues₀` and the
  eigenvector basis `Matrix.IsHermitian.eigenvectorBasis`; (iv) inverse
  iteration with real shift and real start, stated as (i) and (iii) for
  `(A - μ • 1)⁻¹` together with the ordering hypothesis on $|\mu-\lambda_j|$.
  Hypotheses: $\alpha_1\ne0$, $\lambda_1\ne0$ and the strict gap, written
  `‖eigs i‖ ≤ q * ‖eigs 0‖` with `q < 1` for `i ≠ 0`. Pitfall:
  `powerStep` returns `0` when `A x = 0`, so the conclusion must include that
  every iterate has norm $1$; the "$\pm q_J$" of (iv) is false for a complex
  shift. Statable at the pins. NASC: `NASC.exists_phase_norm_powerStep_iterate_sub_le`
  (EigenvalueMethods.lean) states (i) in any normed space over `RCLike 𝕜` with an eigenbasis
  indexed by a finite type and a dominant index `i₀` (only that eigenvector need be a unit
  vector), with $q$ in place of $|\lambda_2/\lambda_1|$, `sorry`; (ii)–(iv) are not stated.

* **4.5. Rayleigh quotient iteration.** Let $A\in\mathbb R^{n\times n}$ be
  symmetric. The **Rayleigh quotient** of $x\ne0$ is
  $r(x)=x^\top Ax/x^\top x$; its gradient vanishes at $x\ne0$ if and only if
  $x$ is an eigenvector. If $Aq=\lambda q$ and $\|q\|_2=\|v\|_2=1$, then
  $$r(v)-\lambda=(v-q)^\top(A-\lambda I)(v-q),\qquad\text{so}\qquad
  |r(v)-\lambda|\le\|A-\lambda I\|_2\,\|v-q\|_2^2 .$$
  **Rayleigh quotient iteration** starts from a unit vector $v^{(0)}$ with
  $\lambda^{(0)}=r(v^{(0)})$, and for $k\ge1$, as long as $\lambda^{(k-1)}$
  is not an eigenvalue, solves $(A-\lambda^{(k-1)}I)w=v^{(k-1)}$ and sets
  $v^{(k)}=w/\|w\|_2$, $\lambda^{(k)}=r(v^{(k)})$. Let $\lambda_J$ be a
  simple eigenvalue with unit eigenvector $q_J$. There are $\varepsilon>0$
  and $C$, depending on $A$ and $J$, such that if
  $\|v^{(k)}-s q_J\|_2\le\varepsilon$ for a sign $s\in\{1,-1\}$ and
  $\lambda^{(k)}$ is not an eigenvalue, then
  $$\|v^{(k+1)}-s'q_J\|_2\le C\,\|v^{(k)}-sq_J\|_2^3$$
  for a sign $s'$, and by the first display
  $|\lambda^{(k+1)}-\lambda_J|\le\|A-\lambda_JI\|_2\,
  \|v^{(k+1)}-s'q_J\|_2^2$.

  *Assessment.* The Rayleigh quotient and real symmetric spectral theory are
  available. The gap relates the changing inverse shift to the angle error and
  proves the cubic local rate.

  *Lean target.* Carriers at the pins: `Matrix.IsHermitian` for real
  symmetric `A`, `Matrix.toEuclideanLin`, the inner product on
  `EuclideanSpace ℝ (Fin n)`, `Matrix.det` and `Matrix.inv`. Conjuncts: (i) the
  identity $r(v)-\lambda=(v-q)^\top(A-\lambda I)(v-q)$ for unit $v,q$ with
  $Aq=\lambda q$, and the resulting quadratic bound; (ii) the gradient
  characterization (stated with `HasFDerivAt` of the Rayleigh quotient on
  $x\ne0$); (iii) the cubic step. The simplicity of $\lambda_J$ is
  `finrank (ker (A.toEuclideanLin - λ • id)) = 1`, and the step needs
  `(A - r(v) • 1).det ≠ 0`, since `Matrix.inv` is `0` on singular matrices.
  Pitfall: the sign $s$ must be chosen before the hypothesis
  $\|v-sq_J\|\le\varepsilon$; quantify over both signs or fix $s=1$ by
  replacing $q_J$ with $sq_J$. Statable at the pins. NASC:
  `NASC.exists_norm_rayleighQuotientStep_sub_le_cube` (EigenvalueMethods.lean)
  states (iii), `sorry`.

### The QR algorithm

* **4.6. QR algorithm and simultaneous iteration.** For
  $A\in\mathbb C^{n\times n}$ the **QR algorithm** sets $A_1=A$ and, for
  $i\ge1$, factors $A_i=Q_iR_i$ with $Q_i$ unitary and $R_i$ upper triangular
  and sets $A_{i+1}=R_iQ_i$. With $P_i=Q_1\cdots Q_i$ and
  $U_i=R_i\cdots R_1$,
  $$A_{i+1}=Q_i^*A_iQ_i=P_i^*AP_i,\qquad A^i=P_iU_i,\qquad i\ge1 .$$
  If $A$ is nonsingular and every factorization is normalized so that $R$
  has positive diagonal, then $P_i$ equals the matrix $\hat Q^{(i)}$ of
  **simultaneous iteration** $\hat Q^{(0)}=I$,
  $A\hat Q^{(i-1)}=\hat Q^{(i)}\hat R^{(i)}$, and $U_i=\hat R^{(i)}\cdots
  \hat R^{(1)}$.

  *Assessment.* TauCeti has the QR factorization of an invertible matrix and
  the uniqueness of a unitary upper triangular matrix with positive diagonal.
  The gap is the identity between the sequence of QR similarities, the
  factorizations of matrix powers and simultaneous iteration.

  *Argument.* Iterating the similarity formula gives $A_{i+1}=P_i^*AP_i$. Also
  $AP_{i-1}=P_{i-1}A_i=P_iR_i$. Apply this identity inductively to $A^i$ and
  use uniqueness of the positive-diagonal QR factorization to identify the
  simultaneous iterates.

  *Lean target.* Carriers at the pins: `unitary (Matrix (Fin n) (Fin n) 𝕜)`,
  `Matrix.IsUpperTriangular`, TauCeti's
  `Matrix.GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq` and
  `Matrix.IsUpperTriangular.eq_one_of_mem_unitaryGroup`. The QR sequence is a predicate on sequences
  `B Q R : ℕ → Matrix (Fin n) (Fin n) 𝕜` (NASC's `IsQRIteration`, numbered from $0$). Conjuncts: (i)
  $P_i$, $U_i$ with $A_{i+1}=P_i^*AP_i$ and $A^i=P_iU_i$; (ii) under `A.det ≠ 0` and
  `0 < (R k i i).re` with real diagonal, equality with simultaneous iteration defined by the same
  normalization. Pitfall: the positive-diagonal condition on a complex triangular matrix must say
  that the diagonal is real positive, `0 < R k i i` in the order of `RCLike`. Statable at the pins.
  NASC: the accumulated factors `NASC.accumulatedQ` and `NASC.accumulatedR` with
  `NASC.IsQRIteration.conjTranspose_accumulatedQ_mul_self_and_mul_eq`,
  `NASC.IsQRIteration.eq_conjTranspose_mul_mul`, `NASC.IsQRIteration.mul_accumulatedQ_eq` and
  `NASC.IsQRIteration.pow_eq_mul_accumulatedR` (EigenvalueMethods.lean) state (i), proved; (ii) is
  not stated.

* **4.7. Convergence of the unshifted QR algorithm.** Let
  $A\in\mathbb C^{n\times n}$ be nonsingular with eigenvalues of distinct
  moduli, $|\lambda_1|>|\lambda_2|>\cdots>|\lambda_n|>0$. Write
  $A=XDX^{-1}$ with $D=\mathrm{diag}(\lambda_1,\dots,\lambda_n)$, and assume
  that $Y=X^{-1}$ has a factorization $Y=L_YR_Y$ with $L_Y$ unit lower
  triangular and $R_Y$ upper triangular. Then there are phase matrices $S_i$
  such that $S_{i-1}^*Q_iS_i\to I$ and
  $$S_{i-1}^*A_iS_{i-1}\to R_XDR_X^{-1}\qquad(i\to\infty),$$
  where $X=Q_XR_X$ is a QR factorization; the limit is upper triangular with
  diagonal $\lambda_1,\dots,\lambda_n$. In particular the diagonal entries of
  $A_i$ converge to $\lambda_1,\dots,\lambda_n$ in this order, and the
  entries below the diagonal converge to $0$. If $A$ is real symmetric with
  $|\lambda_1|>\cdots>|\lambda_n|$, and the orthogonal eigenvector matrix $Q$
  has nonsingular leading principal submatrices, then $A_i$ converges to
  $\mathrm{diag}(\lambda_1,\dots,\lambda_n)$, and $P_i$, with the signs of
  its columns adjusted, converges to $Q$, both with error
  $O(c^i)$, $c=\max_k|\lambda_{k+1}|/|\lambda_k|$.

  *Assessment.* The exact QR step is a similarity. Convergence requires
  tracking the column flags under repeated power iteration with the stated
  eigenvalue separation and starting basis hypotheses.

  *Lean target.* Carriers at the pins as in 4.6, with
  `Filter.Tendsto … atTop (nhds _)` in the matrix topology and
  `(Matrix (Fin n) (Fin n) ℂ)ˣ` for $X$. The hypothesis on $Y=X^{-1}$ is the
  nonvanishing of its leading principal minors,
  `(X⁻¹.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0` for every leading
  size, which is equivalent to the
  unit lower–upper factorization. Conjuncts: (i) phases with
  $S_{i-1}^*Q_iS_i\to I$; (ii) $S_{i-1}^*A_iS_{i-1}\to R_XDR_X^{-1}$; (iii)
  the real symmetric case with the rate $O(c^i)$, stated as a bound
  `‖A_i - diagonal λ‖ ≤ C * c ^ i`. Hypotheses: `StrictAnti (‖eigs ·‖)` and
  `eigs i ≠ 0`. Statable at the pins; depends on 4.6. NASC:
  `NASC.IsQRIteration.exists_tendsto_conjTranspose_mul` (EigenvalueMethods.lean)
  states (ii), `sorry`.

* **4.8. Hessenberg form and the shifted QR step.** For every
  $A\in\mathbb C^{n\times n}$ there is a unitary $Q$, a product of $\max\{n-2,0\}$
  Householder reflectors, such that $Q^*AQ$ is upper Hessenberg; if $A$ is
  Hermitian, $Q^*AQ$ is Hermitian tridiagonal. Let $H$ be unreduced upper
  Hessenberg, $k\in\mathbb C$, $H-kI=QR$ a QR factorization, and
  $H'=RQ+kI$. Then $H'=Q^*HQ$, and $H'$ is Hermitian tridiagonal if $H$ is.
  If $k$ is not an eigenvalue of $H$, then $H'$ is unreduced upper
  Hessenberg. If $k$ is an eigenvalue, then
  $$H'=\begin{pmatrix}\tilde H&*\\0&k\end{pmatrix}$$
  with $\tilde H$ unreduced upper Hessenberg of order $n-1$. For the
  **shifted QR algorithm** $A_1=A$, $A_i-k_iI=Q_iR_i$,
  $A_{i+1}=R_iQ_i+k_iI$, one has
  $$A_{i+1}=P_i^*AP_i,\qquad (A-k_1I)\cdots(A-k_iI)=P_iU_i,$$
  with $P_i$ and $U_i$ as in 4.6. **Wilkinson's theorem:** if $A$ is real
  symmetric, tridiagonal and unreduced, and each $k_i$ is an eigenvalue of
  the trailing $2\times2$ submatrix of $A_i$ nearest to $a^{(i)}_{nn}$, then
  $a^{(i)}_{n,n-1}\to0$, ultimately at least quadratically, so that $a^{(i)}_{nn}$
  converges to an eigenvalue of $A$.

  *Assessment.* Mathlib has the Hessenberg predicate and algebraic
  Hessenberg similarity certificates, and TauCeti has Householder
  reflections. The selected result requires unitary reduction and
  preservation of Hessenberg form in the shifted QR step.

  *Lean target.* Carriers at the pins: `Matrix.IsUpperHessenberg` (on a
  `SuccOrder` index type such as `Fin n`), TauCeti's
  `Matrix.one_sub_smul_vecMulVec_mem_unitary` for reflectors,
  `Matrix.IsHermitian`. "Unreduced" is the new predicate `NASC.IsUnreducedHessenberg H`: upper
  Hessenberg with nonzero subdiagonal (`isUnreducedHessenberg_iff`).
  Conjuncts: (i) unitary Hessenberg reduction, tridiagonal when Hermitian;
  (ii) the shifted step is a unitary similarity; (iii) unreduced Hessenberg is
  preserved when $k$ is not an eigenvalue (equivalently `R.det ≠ 0`); (iv) the
  deflated form when $k$ is an eigenvalue; (v) the accumulated identities of
  the shifted algorithm; (vi) Wilkinson's theorem, as
  `Tendsto (fun i ↦ A i (Fin.last _) _) atTop (nhds 0)` with an ultimate
  quadratic bound. Pitfall: for $n\le1$ the product of reflectors is empty;
  the QR factorization of a singular $H-kI$ is not unique, so (iv) holds for
  every QR factorization only when stated for all of them. Statable at the
  pins except (vi), which needs the tridiagonal QR convergence argument
  (Parlett's proof). NASC: `NASC.exists_unitary_conjTranspose_mul_upperHessenberg` states (i)
  without the Hermitian part, over `RCLike 𝕜` and with a prescribed unit first column `Q e₀ = q`,
  and `NASC.IsUnreducedHessenberg.shifted_qr_step` states (ii)–(iii) (EigenvalueMethods.lean),
  both `sorry`.

* **4.9. Implicit Q theorem.** Let $A\in\mathbb C^{n\times n}$, let
  $Q=[q_1,\dots,q_n]$ and $U=[u_1,\dots,u_n]$ be unitary, and suppose that
  $H=Q^*AQ$ and $K=U^*AU$ are both upper Hessenberg, that
  $h_{i,i-1}\ne0$ for $2\le i\le n-1$, and that $u_1=\sigma q_1$ with
  $|\sigma|=1$. Then there is a phase matrix $S$ such that $U=QS$ and
  $K=S^*HS$.

  *Assessment.* Not covered. The implicit Q theorem is the uniqueness
  statement behind implicitly shifted QR steps and the Golub–Kahan step of
  4.16; no library states it.

  *Lean target.* Carriers at the pins: `unitary (Matrix (Fin n) (Fin n) ℂ)`,
  `Matrix.IsUpperHessenberg`, the unreduced predicate of 4.8, and the columns
  `Q.col` (or `fun i ↦ Q i j`). Conjunct: if $Q^*AQ$ and $U^*AU$ are upper
  Hessenberg, $Q^*AQ$ unreduced in the stated index range, and
  $q_1=u_1$, then $u_i=d_iq_i$ with $|d_i|=1$ and the Hessenberg entries agree
  up to the phases. Pitfall: the statement must fix which index range is
  unreduced ($2\le i\le n-1$ for the conclusion on all columns); for
  $n\le1$ it is trivial. Statable at the pins. NASC: none.

* **4.10. Backward stability.** In the standard model 1.5 of floating-point
  arithmetic, Householder reduction of $A\in\mathbb C^{n\times n}$ to upper
  Hessenberg form computes $\tilde H$ for which there is an exactly unitary
  $\tilde Q$, determined by the computed reflection vectors, with
  $$\tilde Q\tilde H\tilde Q^*=A+\delta A,\qquad
  \|\delta A\|/\|A\|=O(u).$$
  If $A\in\mathbb R^{n\times n}$ is symmetric tridiagonal and is
  diagonalized by the QR algorithm with Householder reflectors or Givens
  rotations, the computed diagonal matrix $\tilde\Lambda$ and the exactly
  orthogonal $\tilde Q$ of the computed transformations satisfy
  $\tilde Q\tilde\Lambda\tilde Q^\top=A+\delta A$ with
  $\|\delta A\|/\|A\|=O(u)$. Together with Weyl's inequality (section 2),
  the computed eigenvalues of a real symmetric matrix obtained by
  tridiagonal reduction followed by the QR algorithm satisfy
  $|\tilde\lambda_j-\lambda_j|/\|A\|=O(u)$.

  *Assessment.* Exact unitary similarity provides the comparison
  transformation. The numerical claim requires a backward-error accumulation
  for the reduction and iteration.

  *Lean target.* Floating point: an abstract rounding `fl : ℝ → ℝ` (and its
  complex extension) with `|fl x − x| ≤ u * |x|` on the normal range, the
  standard model of 1.5; neither Mathlib nor TauCeti has float carriers. New
  definitions: the computed Householder reflector of a vector, and the
  computed reduction as a function of `fl`, with the exactly unitary
  $\tilde Q$ assembled from the computed reflection vectors. Conjuncts: (i)
  the Hessenberg reduction bound $\|\delta A\|\le c_n u\|A\|$ for $u\le u_0(n)$;
  (ii) the same for the symmetric tridiagonal QR algorithm run for a given
  number of steps; (iii) the eigenvalue consequence through Weyl's inequality
  (`Matrix.IsHermitian.eigenvalues₀` and TauCeti's Courant–Fischer). Pitfall:
  $O(u)$ must be written as an explicit $c_n$ and a range of $u$, and the
  number of QR steps must be part of the statement. The accumulation lemma is
  statable at the pins; (i)–(ii) need the floating-point reflector model.
  NASC: `NASC.norm_conjTranspose_mul_sub_le_of_reductions`
  (EigenvalueMethods.lean) proves the composition of two backward errors;
  (i)–(iii) are not stated.

### Rayleigh–Ritz and Krylov methods

* **4.13. Arnoldi and Lanczos relations.** Let $A\in\mathbb C^{n\times n}$
  and $b\ne0$, and let
  $\mathcal K_m=\mathrm{span}\{b,Ab,\dots,A^{m-1}b\}$ have dimension $m$.
  The **Arnoldi process** produces $Q_m=[q_1,\dots,q_m]$ with orthonormal
  columns spanning $\mathcal K_m$ such that the Krylov matrix
  $[b,Ab,\dots,A^{m-1}b]=Q_mR_m$ with $R_m$ upper triangular, and
  $H_m=Q_m^*AQ_m$ is upper Hessenberg.
  - If $\dim\mathcal K_{m+1}=m+1$, then $AQ_m=Q_{m+1}\underline H_m$ with
    $\underline H_m\in\mathbb C^{(m+1)\times m}$ upper Hessenberg whose
    leading $m\times m$ block is $H_m$. If $\dim\mathcal K_{m+1}=m$, then
    $AQ_m=Q_mH_m$, $\mathcal K_m$ is invariant under $A$, and every
    eigenvalue of $H_m$ is an eigenvalue of $A$.
  - The characteristic polynomial of $H_m$ is the unique monic polynomial $p$
    of degree $m$ that minimizes $\|p(A)b\|_2$.
  - If $A$ is Hermitian, $H_m=J_m$ is real symmetric tridiagonal, and the
    columns satisfy the three-term **Lanczos recurrence**
    $Aq_j=\beta_{j-1}q_{j-1}+\alpha_jq_j+\beta_jq_{j+1}$ for $1\le j\le m-1$,
    with $\beta_0q_0=0$ and $\alpha_j$, $\beta_j$ real.

  *Assessment.* Inner products and orthogonal bases are available. The Arnoldi
  relation requires the generated Krylov basis, the residual coefficient, and
  the tridiagonal specialization for Hermitian inputs.

  *Lean target.* Carriers at the pins: `Submodule.span` of the iterates
  `(A.toEuclideanLin ^ j) b` (NASC's `krylovSubmodule`), Gram–Schmidt
  `gramSchmidtNormed`, `Matrix.IsUpperHessenberg`, `Polynomial.Monic`,
  `Polynomial.aeval`. Conjuncts: (i) an orthonormal `Q : Matrix (Fin n) (Fin m) 𝕜`
  whose leading columns span the leading Krylov spaces, with `Qᴴ * A * Q`
  upper Hessenberg; (ii) the Arnoldi relation with the extra row, and the
  invariant case; (iii) the characteristic polynomial of $H_m$ minimizes
  `‖aeval A p *ᵥ b‖` over monic `p` of degree $m$, uniquely; (iv) the
  Hermitian three-term recurrence. Hypothesis:
  `finrank (krylovSubmodule A b m) = m`. Pitfall: $H_{m+1}$ is indexed by
  `Fin (m + 1) × Fin m` for (ii); the minimizer in (iii) is unique only under
  the dimension hypothesis. Statable at the pins; Krylov spaces and the
  Lanczos case are owned by roadmaps (see notes). NASC:
  `NASC.exists_arnoldiFrame` (EigenvalueMethods.lean) states (i), `sorry`.

* **4.14. Kaniel–Paige–Saad bound.** Let $A\in\mathbb R^{n\times n}$ be
  symmetric, $n\ge3$, with eigenvalues $\lambda_1\ge\cdots\ge\lambda_n$ and
  orthonormal eigenvectors $u_1,\dots,u_n$, and let $J_m=Q_m^\top AQ_m$ be the
  tridiagonal matrix of $m$ Lanczos steps started from a unit vector $q_1$,
  with $\dim\mathcal K_m=m$. Let $\eta_1\ge\cdots\ge\eta_m$ be the
  eigenvalues of $J_m$ and $T_{m-1}$ the Chebyshev polynomial of degree
  $m-1$. If $\cos\varphi_1=|q_1^\top u_1|\ne0$ and $\lambda_2>\lambda_n$,
  then with $\rho_1=(\lambda_1-\lambda_2)/(\lambda_2-\lambda_n)$,
  $$\lambda_1\ge\eta_1\ge\lambda_1-\frac{(\lambda_1-\lambda_n)\tan^2\varphi_1}
  {T_{m-1}(1+2\rho_1)^2}.$$
  If $\cos\varphi_n=|q_1^\top u_n|\ne0$ and $\lambda_1>\lambda_{n-1}$, then
  with $\rho_n=(\lambda_{n-1}-\lambda_n)/(\lambda_1-\lambda_{n-1})$,
  $$\lambda_n\le\eta_m\le\lambda_n+\frac{(\lambda_1-\lambda_n)\tan^2\varphi_n}
  {T_{m-1}(1+2\rho_n)^2}.$$

  *Assessment.* Compression interlacing is available, and Mathlib has the
  extremal bound of Chebyshev polynomials outside $[-1,1]$. The Ritz-value
  rate combines the Krylov polynomial with that bound and the angle of the
  starting vector.

  *Lean target.* Carriers at the pins: `Matrix.IsHermitian.eigenvalues₀` for
  `A` and for `Qᵀ * A * Q`, `Polynomial.Chebyshev.T ℝ`, the Krylov space of
  4.13. Conjuncts: (i) $\lambda_1\ge\eta_1$; (ii) the lower bound for
  $\eta_1$; (iii)–(iv) the symmetric pair for $\eta_m$, obtained from (i)–(ii)
  for $-A$. Hypotheses: `n + 3` rows (for $n\ge3$), `m + 1` Krylov dimensions
  with $T_m$, `⟪u₁, q₁⟫ ≠ 0`, and the strict inequality $\lambda_2>\lambda_n$.
  Pitfall: $\tan^2\varphi_1$ is written as $(1-c^2)/c^2$ with $c\ne0$, and the
  Chebyshev argument is at least $1$, so the denominator is at least $1$.
  Statable at the pins; depends on 4.13. NASC:
  `NASC.kaniel_paige_saad` (EigenvalueMethods.lean) states (i)–(ii),
  `sorry`.

* **4.16. Golub–Kahan bidiagonalization.** Let $A\in\mathbb C^{m\times n}$
  with $m\ge n$. There are unitary $P\in\mathbb C^{m\times m}$ and
  $Q\in\mathbb C^{n\times n}$, products of Householder reflectors, such that
  $$P^*AQ=\begin{pmatrix}J\\0\end{pmatrix}$$
  with $J\in\mathbb C^{n\times n}$ upper bidiagonal. Then $J$ and $A$ have
  the same singular values, $J^*J=Q^*A^*AQ$ is Hermitian tridiagonal, and an
  SVD $J=G\Sigma K^*$ gives the SVD
  $A=P\,\mathrm{diag}(G,I_{m-n})\begin{pmatrix}\Sigma\\0\end{pmatrix}(QK)^*$.
  If $M=J^*J$ is unreduced and $k\in\mathbb R$, a bidiagonal $J'=S^*JT$, with
  $S,T$ unitary and the first column of $T$ equal to that of the unitary
  factor of a QR factorization of $M-kI$, satisfies $J'^*J'=D^*M'D$ for a
  phase matrix $D$, where $M'$ is the result of one shifted QR step 4.8
  with shift $k$ applied to $M$.

  *Assessment.* SVD and the adjoint are ingredients, and TauCeti has
  Householder reflections. The coupled bidiagonalization recurrence must
  preserve orthogonality and give both matrix relations with the terminal
  residual.

  *Lean target.* Carriers at the pins: `unitary` matrices of sizes `m` and
  `n`, `LinearMap.singularValues`, `Matrix.fromRows` for the block
  $\begin{pmatrix}J\\0\end{pmatrix}$ after reindexing `Fin m ≃ Fin n ⊕ Fin (m - n)`.
  New predicate: upper bidiagonal, `J i j = 0` unless `j = i` or
  `j.val = i.val + 1`. Conjuncts: (i) existence of $P$, $Q$ with bidiagonal
  $J$; (ii) equal singular values; (iii) $J^*J$ Hermitian tridiagonal; (iv)
  assembly of the SVD; (v) the Golub–Reinsch step, which depends on 4.8 and
  4.9. Hypothesis: `n ≤ m`. Statable at the pins. NASC:
  `NASC.exists_unitary_conjTranspose_mul_bidiagonal` (EigenvalueMethods.lean) states (i)–(ii) for
  any shape (`Fin m × Fin (n + 1)`), with a prescribed unit first column `V e₀ = v` and
  nonnegative real diagonal and superdiagonal (the Golub–Kahan form), `sorry`.

### Nonlinear eigenvalue problems

* **4.18. Keldysh's theorem.** Let $F$ be holomorphic and regular on a
  domain $\Omega$, with finitely many eigenvalues $\lambda_1,\dots,\lambda_s$
  in $\Omega$, of partial multiplicities $m_{i,1}\ge\cdots\ge m_{i,d_i}$, and
  let $m=\sum_{i,j}m_{i,j}$. There are $V,W\in\mathbb C^{n\times m}$ whose
  columns are generalized eigenvectors of $F$ and of $F^*$ respectively, and
  a Jordan matrix $J\in\mathbb C^{m\times m}$ with a Jordan block of order
  $m_{i,j}$ for $\lambda_i$ for each $i,j$, such that
  $$F(z)^{-1}=V(zI-J)^{-1}W^*+R(z),\qquad z\in\Omega\setminus\Lambda(F),$$
  with $R$ holomorphic on $\Omega$. The columns of $V$ are complete systems
  of Jordan chains for $F$, and those of $W$ are the complete systems of
  Jordan chains for $F^*$ normalized against them. If all eigenvalues are
  simple,
  $$F(z)^{-1}=\sum_{i=1}^s\frac{v_iw_i^*}{z-\lambda_i}+R(z),$$
  with right and left eigenvectors $v_i,w_i$ normalized by
  $w_i^*F'(\lambda_i)v_i=1$.

  *Assessment.* Holomorphicity and meromorphic principal parts provide
  analytic ingredients, and TauCeti has Jordan-chain bases of nilpotent
  endomorphisms. The missing result identifies the pole terms and their
  coefficients with the normalized left and right Jordan chains of the matrix
  function.

  *Lean target.* Carriers at the pins: `F : ℂ → Matrix (Fin n) (Fin n) ℂ` with
  `AnalyticOnNhd ℂ F Ω`, `Matrix.det`, `MeromorphicAt`, and
  `Module.End.exists_jordanChainBasis` for the matrix $J$. New definitions:
  a Jordan chain of $F$ at $\lambda$ (vectors $v_0\ne0,\dots,v_{k-1}$ with
  $\sum_{j\le i}F^{(j)}(\lambda)v_{i-j}/j!=0$, via `iteratedDeriv`), partial
  multiplicities and a complete system of chains. Conjuncts: (i) the simple
  case, $F(z)^{-1}-\sum_i v_iw_i^*/(z-\lambda_i)$ holomorphic, with
  $w_i^*F'(\lambda_i)v_i=1$; (ii) the general case with $V$, $W$, $J$. Hypotheses:
  regularity (`det F` not identically zero on the connected $\Omega$),
  finitely many eigenvalues. Pitfall: `F z⁻¹` is junk `0` at eigenvalues, so
  the identity is stated on $\Omega\setminus\Lambda(F)$ with $R$ analytic on
  $\Omega$. (i) is statable at the pins; (ii) needs the theory of partial
  multiplicities (Smith-form or Gohberg–Sigal factorization), which no library
  has. NASC: `NASC.exists_analyticOnNhd_sub_inv_pole_of_simple_eigenvalue`
  (EigenvalueMethods.lean) states a local form of (i) at one eigenvalue with
  `deriv (det F) z₀ ≠ 0`, `sorry`.

* **4.19. Companion linearization.** Let
  $P(z)=\sum_{j=0}^{\ell}z^jD_j$ with $D_j\in\mathbb C^{n\times n}$ and
  $\ell\ge1$, and let $L(z)\in\mathbb C^{\ell n\times\ell n}$ be the pencil
  with first block row $(D_0,\dots,D_{\ell-2},D_{\ell-1}+zD_\ell)$ (the single
  block $D_0+zD_1$ when $\ell=1$) and,
  for $2\le j\le\ell$, block row $j$ equal to $-zI_n$ in block column $j-1$,
  $I_n$ in block column $j$, and $0$ elsewhere. With
  $b(z)=(1,z,\dots,z^{\ell-1})^\top$,
  $$L(z)\bigl(b(z)\otimes v\bigr)=e_1\otimes P(z)v,\qquad
  \det L(z)=\det P(z)$$
  for all $z\in\mathbb C$ and $v\in\mathbb C^n$. Hence
  $\ker L(\lambda)=\{b(\lambda)\otimes v:v\in\ker P(\lambda)\}$ for every
  $\lambda$; $L$ is regular if and only if $P$ is; and $L$ and $P$ have the
  same eigenvalues with the same algebraic and geometric multiplicities. If
  $w$ is a left eigenvector of $L$ for $\lambda$, its first block
  $(e_1\otimes I_n)^*w$ is nonzero and is a left eigenvector of $P$.

  *Assessment.* Partly covered. TauCeti treats scalar polynomial companion
  pencils (the case $n=1$, with determinant and invertibility). The selected
  block-coefficient version identifies the determinant, right kernel,
  algebraic multiplicities and the left-vector correspondence.

  *Scope.* The target is the block-polynomial pencil identity, its determinant
  and the correspondence of eigenvectors for finite eigenvalues.

  *Lean target.* Carriers at the pins: TauCeti's `TauCeti.companionPencil`
  and `TauCeti.det_companionPencil` for $n=1$, `Matrix.det`,
  `Matrix.mulVec`, `Matrix.vecMul`, and the block index `Fin ℓ × Fin n`. New
  definition: the block pencil, as a function of `D : ℕ → Matrix (Fin n) (Fin n) 𝕜`
  and `z`, of type `Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) 𝕜` with
  `ℓ = d + 1` (NASC's `blockCompanionPencil`). Conjuncts: (i)
  $L(z)(b(z)\otimes v)=e_1\otimes P(z)v$; (ii) $\det L=\det P$ over any field;
  (iii) the kernel description; (iv) regularity; (v) equality of algebraic
  multiplicities, as `rootMultiplicity` of the two determinant polynomials,
  and of geometric multiplicities; (vi) the left-vector statement. Pitfall:
  regularity and multiplicities are about the polynomial `det P(z)` in
  `𝕜[X]`, so the pencil must also be stated over `Polynomial 𝕜` or with
  `Matrix.det` composed with evaluation. Statable at the pins. NASC:
  `NASC.det_blockCompanionPencil` (over a commutative ring) and
  `NASC.blockCompanionPencil_mulVec_eq_zero_iff` (EigenvalueMethods.lean) state (ii) and (iii),
  `sorry`.

## 5. Iterative methods for linear systems

[Synopsis](SYNOPSIS.md#5-iterative-methods-for-linear-systems) · [Coverage inventory](STRUCTURE.md#5-iterative-methods-for-linear-systems)

The stationary theories use matrix splittings and spectral radius. The Krylov
results are statements in exact arithmetic.

This section treats the solution of $Ax=b$ with $A\in\mathbb K^{n\times n}$
nonsingular by stationary iterations and by Krylov subspace methods. Inequalities
between real matrices or vectors are entrywise: $B\ge O$ means that every entry
is nonnegative, and $B>O$ that every entry is positive. A **splitting** of $A$ is
a representation $A=M-N$ with $M$ nonsingular; its **iteration matrix** is
$G=M^{-1}N$ and the associated iteration is $x_{k+1}=Gx_k+M^{-1}b$. Write
$A=D-E-F$ with $D$ the diagonal of $A$ and $-E$, $-F$ its strictly lower and
strictly upper triangular parts. When $D$ is nonsingular, put $L=D^{-1}E$,
$U=D^{-1}F$. The **Jacobi** matrix is $B_J=L+U=I-D^{-1}A$, and for
$\omega\in\mathbb C$ the **SOR** matrix is
$$\mathcal L_\omega=(I-\omega L)^{-1}\bigl((1-\omega)I+\omega U\bigr);$$
$\mathcal L_1$ is the **Gauss–Seidel** matrix. The **Krylov space** of order
$k$ is $\mathcal K_k(A,r)=\mathrm{span}\{r,Ar,\dots,A^{k-1}r\}$, and $\mathcal P_k^0$
is the set of polynomials $p$ of degree at most $k$ with $p(0)=1$. All
statements about Krylov methods assume exact arithmetic.

Common carriers at the pins for this section: `Matrix (Fin n) (Fin n) 𝕜`,
`Matrix.toEuclideanLin`, `spectralRadius ℂ` of a complex matrix (an `ℝ≥0∞`
value; a real matrix is complexified with `A.map Complex.ofReal`, NASC's
`realMatrixSpectralRadius`, since the real spectrum of a rotation is empty),
entrywise order written as `∀ i j, 0 ≤ B i j`, `Matrix.IsIrreducible` (which
includes entrywise nonnegativity), `Matrix.PosDef`, `Polynomial.eval`,
`Polynomial.aeval`, `Polynomial.Chebyshev.T ℝ` (indexed by `ℤ`), and the
Krylov space as `Submodule.span 𝕜 (Set.range fun j : Fin k ↦ (A ^ j.val) r)`
(NASC's `krylovSubmodule`). `Matrix.inv` is `0` on singular matrices, so every
splitting statement carries `M.det ≠ 0`.

### Stationary iterations

* **5.1. Convergent matrices and splitting iterations.** For $G\in\mathbb
  C^{n\times n}$, $G^k\to O$ as $k\to\infty$ if and only if $\rho(G)<1$. For
  every matrix norm induced by a vector norm,
  $\rho(G)=\lim_{k\to\infty}\|G^k\|^{1/k}$. Let $A=M-N$ be a splitting of the
  nonsingular matrix $A$ and $x^*=A^{-1}b$. The errors of the iteration satisfy
  $x_k-x^*=G^k(x_0-x^*)$ with $G=M^{-1}N$, so $x_k\to x^*$ for every starting
  vector $x_0$ if and only if $\rho(M^{-1}N)<1$.

  *Assessment.* Partly covered. Mathlib gives the Gelfand spectral-radius
  formula. The selected assertion is the iteration-level equivalence for all
  initial vectors.

  *Scope.* The target is the splitting iteration, its exact error formula and
  the convergence criterion for every starting vector.

  *Argument.* Subtract the fixed-point equation from $x_{k+1}=M^{-1}(Nx_k+b)$
  and iterate the error recurrence. When $\rho(G)<1$, the spectral-radius
  formula gives geometric decay of the powers from some index onward. A
  complex eigenvector for an eigenvalue of modulus at least one gives the
  converse.

  *Lean target.* Carriers at the pins: `Matrix.toEuclideanLin`, `Nat.iterate`
  for the affine step, `spectralRadius ℂ`, and Mathlib's
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`. No new
  definition is needed. Conjuncts: (i) the error formula
  $x_k-x^*=G^k(x_0-x^*)$; (ii) convergence from every start iff
  `spectralRadius ℂ G < 1`. Pitfall: the spectral radius is in `ℝ≥0∞`, so the
  comparison is with `1 : ℝ≥0∞`; real splittings need the complexified
  matrix. Everything is statable at the pins. NASC:
  `NASC.splittingIteration_converges_iff`, with
  `NASC.tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one`
  (IterativeMethods.lean), all proved.

* **5.4. Nonsingular M-matrices.** Let $A\in\mathbb R^{n\times n}$ satisfy
  $a_{ij}\le0$ for all $i\ne j$. Then the following are equivalent, and $A$ is
  called a (nonsingular) **M-matrix** when they hold:
  - $A$ is nonsingular and $A^{-1}\ge O$;
  - the diagonal entries of $A$ are positive and $\rho(I-D^{-1}A)<1$;
  - $A=sI-B$ for some $B\ge O$ and some $s>\rho(B)$;
  - all principal minors of $A$ are positive.

  Moreover:
  - an M-matrix is irreducible if and only if $A^{-1}>O$;
  - if $A$ is symmetric, it is an M-matrix if and only if it is positive
    definite (a **Stieltjes matrix**);
  - if $A$ has positive diagonal and is strictly or irreducibly diagonally
    dominant, it is an M-matrix;
  - a matrix obtained from an M-matrix by replacing some off-diagonal entries
    by zero is an M-matrix.

  *Assessment.* Perron–Frobenius theory and inverse norms give ingredients.
  The selected equivalences connect the sign constraints, principal minors,
  inverse positivity and the diagonal iteration.

  *Lean target.* Carriers at the pins: `Matrix.det`, `Matrix.inv`,
  `Matrix.submatrix` along an injective `Fin k ↪ Fin n` for principal minors,
  `Matrix.IsIrreducible`, `Matrix.PosDef`, TauCeti's Perron–Frobenius
  theorems (`Matrix.IsIrreducible.exists_mulVec_eq_smul`,
  `Matrix.spectralRadius_eq_of_mulVec_eq_smul`), and the complexified spectral
  radius. New definition: `IsNonsingularMMatrix A`, taken as any one of the
  four equivalent conditions (best the first, `A.det ≠ 0 ∧ 0 ≤ A⁻¹`
  entrywise, with nonpositive off-diagonal). Conjuncts: (i)–(iv) the four
  equivalences, each as an `↔` with the first; (v) irreducible iff
  $A^{-1}>O$; (vi) Stieltjes; (vii) diagonal dominance criteria; (viii)
  zeroing off-diagonal entries. Hypothesis: nonpositive off-diagonal entries.
  Pitfall: Mathlib's `IsIrreducible` is for nonnegative matrices, so (v) must
  be stated for the nonnegative matrix $sI-A$ or for the digraph of nonzero
  off-diagonal entries; for $n=0$ every condition holds vacuously. Statable at
  the pins. NASC: `NASC.inverse_nonneg_iff_exists_smul_one_sub`
  (IterativeMethods.lean) states (i)⇔(iii), `sorry`.

* **5.5. Regular splittings.** Let $A\in\mathbb R^{n\times n}$. A splitting
  $A=M-N$ is **regular** if $M^{-1}\ge O$ and $N\ge O$, and **weak regular** if
  $M^{-1}\ge O$ and $M^{-1}N\ge O$. For a weak regular splitting, $A$ is
  nonsingular with $A^{-1}\ge O$ if and only if $\rho(M^{-1}N)<1$. For a regular
  splitting with $A$ nonsingular and $A^{-1}\ge O$,
  $$\rho(M^{-1}N)=\frac{\rho(A^{-1}N)}{1+\rho(A^{-1}N)}<1.$$
  If $A$ is an M-matrix and $M$ is obtained from $A$ by replacing some
  off-diagonal entries by zero, then $A=M-(M-A)$ is a regular splitting, so
  $\rho(M^{-1}N)<1$; this covers the point and block Jacobi and Gauss–Seidel
  splittings.

  *Assessment.* The matrix positivity framework supports this theorem. It
  remains to formalize regular and weak regular splittings with their
  convergence and spectral-radius identities.

  *Lean target.* Carriers at the pins as in 5.4, with TauCeti's
  Perron–Frobenius for nonnegative matrices
  (`TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Nonnegative.lean`). New
  predicates: `IsRegularSplitting A M N` (`A = M - N`, `M.det ≠ 0`,
  `0 ≤ M⁻¹`, `0 ≤ N` entrywise) and `IsWeakRegularSplitting` (`0 ≤ M⁻¹ * N`
  in place of `0 ≤ N`). Conjuncts: (i) weak regular: inverse positivity iff
  $\rho<1$; (ii) the identity $\rho(M^{-1}N)=\rho(A^{-1}N)/(1+\rho(A^{-1}N))$;
  (iii) the M-matrix splittings obtained by zeroing entries. Pitfall: the
  identity is in `ℝ≥0∞`, where $\rho/(1+\rho)$ is fine since $\rho<\infty$;
  the nonnegative eigenvector of $A^{-1}N$ for its spectral radius is needed,
  not only for irreducible matrices. Depends on 5.4. Statable at the pins.
  NASC: `NASC.inverse_nonneg_iff_spectralRadius_lt_one` and
  `NASC.spectralRadius_regularSplitting_eq` (IterativeMethods.lean) state (i)
  and (ii), both `sorry`.

* **5.7. Stein–Rosenberg theorem.** Let $B=L+U\ge O$ be real, with $L$ strictly
  lower and $U$ strictly upper triangular, and let $\mathcal
  L_1=(I-L)^{-1}U$. Exactly one of the following holds:
  - $\rho(\mathcal L_1)=\rho(B)=0$;
  - $0<\rho(\mathcal L_1)<\rho(B)<1$;
  - $\rho(\mathcal L_1)=\rho(B)=1$;
  - $1<\rho(B)<\rho(\mathcal L_1)$.

  In particular, if $A$ is real with positive diagonal and $a_{ij}\le0$ for
  $i\ne j$, the Jacobi and Gauss–Seidel iterations for $A$ either both converge
  or both diverge, and when the Jacobi matrix has $0<\rho(B_J)<1$, the
  Gauss–Seidel matrix has a strictly smaller spectral radius.

  *Assessment.* The nonnegative-matrix spectral theory is present. The gap is
  the strict comparison relating the Jacobi and Gauss–Seidel spectral radii on
  either side of one.

  *Lean target.* Carriers at the pins: strictly triangular parts as
  predicates `∀ i j, i ≤ j → L i j = 0` and `∀ i j, j ≤ i → U i j = 0`, the
  complexified spectral radius, and TauCeti's Perron–Frobenius theorem for
  nonnegative matrices. No new definition is needed. Conjuncts: (i) the four
  cases as one disjunction; (ii) the corollary for Jacobi and Gauss–Seidel of a
  matrix with positive diagonal and nonpositive off-diagonal entries. Pitfall:
  $(I-L)^{-1}$ exists because $L$ is nilpotent, which must be derived before
  using `Matrix.inv`; the cases are exclusive only with strict inequalities in
  the middle two. Statable at the pins. NASC: `NASC.stein_rosenberg`
  (IterativeMethods.lean) states (i), `sorry`.

* **5.9. Ostrowski–Reich theorem.** Let $A=D-E-E^*$ be Hermitian, with $D$
  Hermitian positive definite. For $0<\omega<2$ with $D-\omega E$
  nonsingular, the matrix
  $\mathcal L_\omega=(D-\omega E)^{-1}\bigl(\omega E^*+(1-\omega)D\bigr)$
  satisfies $\rho(\mathcal L_\omega)<1$ if and only if $A$ is positive
  definite. For Hermitian positive definite $A$ with $D$
  its diagonal and $-E$ its strictly lower part, point SOR with real $\omega$
  converges for every starting vector if and only if $0<\omega<2$, and the same holds for block SOR
  with $D$ the block diagonal. For the Jacobi iteration with $A$ Hermitian and
  $D$ its diagonal: if $A$ and $2D-A$ are both positive definite, then
  $\rho(B_J)=\|B_J\|_A<1$, where $\|x\|_A=(x^*Ax)^{1/2}$.

  *Assessment.* The energy inner product is available for a positive definite
  matrix. SOR convergence and the necessity of the relaxation interval require
  the splitting identities and both directions of the stability analysis.

  *Lean target.* Carriers at the pins: `Matrix.PosDef`, `Matrix.IsHermitian`,
  `spectralRadius ℂ`, `Matrix.diagonal`, block structure through a map
  `block : Fin n → Fin m` with `D i j = 0` across blocks, and an energy norm
  `√(re ⟪x, A x⟫)` (NASC's `energyNorm`). Conjuncts: (i) for fixed
  $0<\omega<2$ and nonsingular $D-\omega E$, $\rho(\mathcal L_\omega)<1$ iff $A$
  positive definite; (ii) point SOR converges iff $0<\omega<2$; (iii) block
  SOR likewise; (iv) Jacobi: $\rho(B_J)=\|B_J\|_A<1$. Pitfall: in (ii) and
  (iii) the "only if" direction uses Kahan's bound 5.8, so (ii) depends on
  5.8; the operator norm in the energy norm is a `sSup` over a bounded set,
  stated over unit vectors. Statable at the pins. NASC:
  `NASC.spectralRadius_sor_lt_one_iff`, `NASC.spectralRadius_pointSOR_lt_one_iff`,
  `NASC.spectralRadius_blockSOR_lt_one_iff` and
  `NASC.spectralRadius_jacobi_eq_energyNorm` (IterativeMethods.lean), all
  `sorry`.

* **5.10. Young's theorem.** Let $D$ and $I-\omega L$ be nonsingular, and let
  $A$ be **consistently ordered**: the eigenvalues of $zL+z^{-1}U$ do not
  depend on $z\in\mathbb C\setminus\{0\}$. This holds, for example, when $L+U$
  is tridiagonal, or block tridiagonal with zero diagonal blocks. Assume that
  $B_J=L+U$ has only real eigenvalues and that $\beta=\rho(B_J)<1$. Then for
  $0<\omega<2$ the SOR iteration converges, and with
  $$\omega_{\mathrm{opt}}=\frac{2}{1+\sqrt{1-\beta^2}},$$
  $$\rho(\mathcal L_\omega)=\begin{cases}
  1-\omega+\tfrac12\omega^2\beta^2+\omega\beta\sqrt{1-\omega+\tfrac14\omega^2\beta^2},
  &0<\omega\le\omega_{\mathrm{opt}},\\
  \omega-1,&\omega_{\mathrm{opt}}\le\omega<2.\end{cases}$$
  The minimum over real $\omega$ is attained only at $\omega_{\mathrm{opt}}$,
  where $\rho(\mathcal L_{\omega_{\mathrm{opt}}})=\omega_{\mathrm{opt}}-1$.
  For $\omega=1$ this gives $\rho(\mathcal L_1)=\beta^2$.

  *Assessment.* Not covered. Young's theory of consistently ordered matrices
  gives the exact SOR spectral radius as a function of $\omega$ and the
  optimal parameter; no library has consistent ordering or the
  eigenvalue relation between $\mathcal L_\omega$ and $B_J$.

  *Lean target.* Carriers at the pins: `Matrix.charpoly`, `spectrum ℂ`,
  `spectralRadius ℂ`, `Matrix.diagonal`, `Real.sqrt`. New definition:
  `IsConsistentlyOrdered L U`, saying that the characteristic polynomial of
  `z • L + z⁻¹ • U` is independent of `z ≠ 0`. Conjuncts: (i) tridiagonal and
  block tridiagonal matrices with zero diagonal blocks are consistently
  ordered; (ii) the eigenvalue relation $(\lambda+\omega-1)^2=\lambda\omega^2\mu^2$
  between eigenvalues $\lambda$ of $\mathcal L_\omega$ and $\mu$ of $B_J$, as
  an intermediate theorem; (iii) the formula for $\rho(\mathcal L_\omega)$ on
  $(0,2)$; (iv) the unique minimizer $\omega_{\mathrm{opt}}$; (v) $\rho(\mathcal
  L_1)=\beta^2$. Hypotheses: `(1 - ω • L).det ≠ 0`, real spectrum of $B_J$,
  $\beta<1$. Pitfall: $\rho$ is an `ℝ≥0∞` value to be compared with real
  closed forms through `ENNReal.ofReal`. Statable at the pins; depends on
  5.9. NASC: none.

* **5.11. Chebyshev semi-iteration.** Let $T_m$ be the Chebyshev polynomial
  of the first kind of degree $m$. Let $-\infty<a<b<1$. Among all real
  polynomials $p$ of degree at most $m$ with $p(1)=1$, the quantity
  $\max_{a\le x\le b}|p(x)|$ is minimized exactly by
  $$\hat p_m(x)=\frac{T_m\bigl((2x-a-b)/(b-a)\bigr)}
  {T_m\bigl((2-a-b)/(b-a)\bigr)},$$
  with minimum value $1/T_m\bigl((2-a-b)/(b-a)\bigr)$. Now let $G$ be the
  iteration matrix of a convergent iteration $x_{k+1}=Gx_k+c$ for $x^*$, with
  $G$ Hermitian and $0<\rho=\rho(G)<1$. The **Chebyshev semi-iterative
  method** forms the iterates $y_m$ with errors
  $y_m-x^*=\hat p_m(G)(x_0-x^*)$ for $[a,b]=[-\rho,\rho]$; they satisfy a
  three-term recurrence. With $\omega_b=2/(1+\sqrt{1-\rho^2})$,
  $$\|\hat p_m(G)\|_2=\frac1{T_m(1/\rho)}
  =\frac{2(\omega_b-1)^{m/2}}{1+(\omega_b-1)^m},\qquad m\ge0,$$
  this norm decreases strictly in $m$, and
  $\|\hat p_m(G)\|_2^{1/m}\to(\omega_b-1)^{1/2}$.

  *Assessment.* Mathlib has the extremal bound of Chebyshev polynomials: a
  real polynomial of degree at most $m$ bounded by $1$ on $[-1,1]$ is bounded
  by $T_m$ at every $x\ge1$. The constrained minimum on an interval, the exact
  minimizer, the iteration polynomial and the convergence factor are the
  target.

  *Lean target.* Carriers at the pins: `Polynomial.Chebyshev.T ℝ`,
  `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
  (with zero derivatives), `IsLeast`, `Polynomial.natDegree`, and the
  Hermitian operator norm `‖p(G)‖ = max |p(λ)|` from the spectral theorem
  `Matrix.IsHermitian.spectral_theorem`. Conjuncts: (i) the minimum value;
  (ii) uniqueness of the minimizer; (iii) the closed forms of $\|\hat p_m(G)\|_2$;
  (iv) strict decrease; (v) the limit of the $m$-th root. Pitfall:
  `Chebyshev.T` is indexed by `ℤ`, so the degree is `(m : ℤ)`; the maximum over
  $[a,b]$ is `sSup (… '' Set.Icc a b)` of a continuous function, fine on a
  compact interval. The extremal property is also owned by roadmaps (see
  notes). Statable at the pins. NASC: `NASC.isLeast_chebyshevSemiIteration`
  (IterativeMethods.lean) states (i) for `1 ∉ [a, b]` on either side of $1$, with the value
  `1 / |T_m(…)|`, `sorry`.

### Krylov subspace methods

* **5.12. Conjugate gradients: optimality and finite termination.** Let $A$ be
  Hermitian positive definite, $x^*=A^{-1}b$, $\|v\|_A=(v^*Av)^{1/2}$, and
  $r_0=b-Ax_0$. The **conjugate gradient (CG) method** sets $p_0=r_0$ and, for
  $k\ge0$ while $r_k\ne0$,
  $$\alpha_k=\frac{r_k^*r_k}{p_k^*Ap_k},\quad x_{k+1}=x_k+\alpha_kp_k,\quad
  r_{k+1}=r_k-\alpha_kAp_k,\quad
  p_{k+1}=r_{k+1}+\frac{r_{k+1}^*r_{k+1}}{r_k^*r_k}\,p_k.$$
  For $k\ge1$ with $r_0,\dots,r_{k-1}\ne0$, no division by zero occurs, $r_k=b-Ax_k$,
  $$\mathcal K_k(A,r_0)=\mathrm{span}\{r_0,\dots,r_{k-1}\}
  =\mathrm{span}\{p_0,\dots,p_{k-1}\},$$
  the residuals are mutually orthogonal, the directions are $A$-conjugate
  ($p_j^*Ap_i=0$ for $i\ne j$), and $x_k$ is the unique minimizer of
  $\|x-x^*\|_A$ over $x\in x_0+\mathcal K_k(A,r_0)$. Consequently
  $\|x_{k+1}-x^*\|_A\le\|x_k-x^*\|_A$, and
  $$\|x_k-x^*\|_A=\min_{p\in\mathcal P_k^0}\|p(A)(x_0-x^*)\|_A
  \le\min_{p\in\mathcal P_k^0}\max_{\lambda\in\Lambda(A)}|p(\lambda)|\;
  \|x_0-x^*\|_A.$$
  The iteration reaches $x_k=x^*$ for some $k\le n$; if $A$ has only $s$
  distinct eigenvalues, it does so for some $k\le s$.

  *Assessment.* Orthogonal projection supports the variational
  characterization. The missing argument establishes conjugacy, absence of
  breakdown before termination, Krylov optimality and finite termination for
  the recurrence.

  *Lean target.* Carriers at the pins: `EuclideanSpace 𝕜 (Fin n)`, the
  Krylov space, the energy norm, `Matrix.PosDef`. New definition: the CG
  recurrence as a predicate on sequences `x r p : ℕ → E` with a frozen branch
  after $r_k=0$ (NASC's `IsConjugateGradient A C b x₀ x r p`, which also
  carries a preconditioner `C`). Conjuncts: (i) no breakdown and
  $r_k=b-Ax_k$; (ii) the three equal spans; (iii) orthogonality and
  conjugacy; (iv) Krylov minimization of the energy error; (v) monotonicity
  and the polynomial min–max bound; (vi) termination by $n$, and by the
  number of distinct eigenvalues. Pitfall: the coefficients divide by
  $p_k^*Ap_k$ and $r_k^*r_k$, which are zero after termination, so the
  definition must freeze the sequence explicitly instead of relying on
  `x / 0 = 0`. Statable at the pins. NASC: `NASC.IsConjugateGradient.energyNorm_sub_le` (the
  residual identity of (i) and the Krylov minimization (iv) at each step) and
  `NASC.IsConjugateGradient.eq_of_ambient_dimension` (termination by $n$, part of (vi))
  (IterativeMethods.lean), both `sorry`.

* **5.13. Conjugate gradients: condition-number bound.** With $A$ Hermitian
  positive definite and $\kappa=\kappa_2(A)=\lambda_{\max}(A)/\lambda_{\min}(A)$,
  the CG iterates satisfy, for every $k\ge0$ (iterates after exact termination
  being taken to be $x^*$),
  $$\frac{\|x_k-x^*\|_A}{\|x_0-x^*\|_A}\le
  \frac{2c^k}{1+c^{2k}}\le2\Bigl(\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\Bigr)^k,
  \qquad c=\frac{\sqrt\kappa-1}{\sqrt\kappa+1}.$$

  *Assessment.* The spectral theorem and the Chebyshev extremal bound are
  available. The selected conclusion is the exact arithmetic error factor of
  the CG iterates in the energy norm.

  *Lean target.* Carriers at the pins as in 5.12, with
  `Matrix.IsHermitian.eigenvalues₀` for $\lambda_{\max}$ and $\lambda_{\min}$
  (indices `0` and `Fin.last`). No new definition is needed beyond 5.12.
  Conjuncts: (i) the bound $2c^k/(1+c^{2k})$; (ii) the weaker $2c^k$, both in
  multiplied form $\|x_k-x^*\|_A\le(\cdot)\|x_0-x^*\|_A$, since the ratio is
  `0 / 0 = 0` when $x_0=x^*$. Pitfall:
  at $\kappa=1$, $c=0$ and $0^0=1$ in Lean, matching the convention; $n\ge1$
  is needed for the eigenvalue indices. Statable at the pins; depends on 5.12
  and 5.11. NASC: `NASC.IsConjugateGradient.energyNorm_error_le`
  (IterativeMethods.lean) states (ii) for preconditioned CG, `sorry`.

* **5.14. GMRES.** For $A$ nonsingular, the $k$-th **GMRES** iterate $x_k$ is the
  minimizer of $\|b-Ax\|_2$ over $x\in x_0+\mathcal K_k(A,r_0)$; its residual
  $r_k=b-Ax_k$ satisfies $\|r_{k+1}\|_2\le\|r_k\|_2$ and
  $$\|r_k\|_2=\min_{p\in\mathcal P_k^0}\|p(A)r_0\|_2.$$
  If $A=V\Lambda V^{-1}$ is diagonalizable, then
  $$\frac{\|r_k\|_2}{\|r_0\|_2}\le\kappa_2(V)\min_{p\in\mathcal P_k^0}
  \max_{\lambda\in\Lambda(A)}|p(\lambda)|.$$

  *Assessment.* Hilbert projection supports residual minimization. The theorem
  identifies the reachable residual polynomials and gives the
  diagonalizable-matrix bound for the actual minimizers.

  *Lean target.* Carriers at the pins: the Krylov space, a minimizer
  predicate (NASC's `IsGMRESIterate A b x₀ k x`), `Polynomial.aeval`,
  `Matrix.toEuclideanCLM` with the operator norm for $\kappa_2(V)$. Conjuncts:
  (i) existence of a minimizer (orthogonal projection onto the finite-dimensional
  $A\mathcal K_k$); (ii) monotonicity; (iii) the polynomial characterization as
  an `IsLeast`; (iv) the $\kappa_2(V)$ bound for $A=V\Lambda V^{-1}$. Pitfall:
  the minimizer need not be unique when $A$ is singular, so nonsingularity is a
  hypothesis for uniqueness statements only. Statable at the pins. NASC:
  `NASC.IsGMRESIterate.isLeast_residual_polynomial` (IterativeMethods.lean)
  states (iii), `sorry`.

* **5.15. Any nonincreasing residual curve is possible for GMRES.** Let
  $f_0\ge f_1\ge\cdots\ge f_{n-1}>0$, and let $\lambda_1,\dots,\lambda_n$ be
  nonzero complex numbers. Then there are $A\in\mathbb C^{n\times n}$ with
  eigenvalues $\lambda_1,\dots,\lambda_n$ (counted with algebraic multiplicity)
  and $b\in\mathbb C^n$ such that GMRES with $x_0=0$ produces residuals with
  $\|r_k\|_2=f_k$ for $k=0,1,\dots,n-1$ (and $r_n=0$). Thus no statement about
  the convergence of GMRES can depend on the eigenvalues alone.

  *Assessment.* The result constructs matrices with a prescribed spectrum and
  prescribed residual history. Generic spectral estimates alone do not produce
  this construction.

  *Lean target.* Carriers at the pins: `Matrix.charpoly` with
  `Polynomial.roots` for the prescribed eigenvalues, the companion matrix
  of a polynomial, unitary matrices, and the GMRES predicate of 5.14.
  Conjunct: given antitone positive $f$ and nonzero $\lambda_j$, there are $A$
  and $b$ with `A.charpoly.roots = ofFn eigs` and $\|r_k\|=f_k$ for every GMRES
  iterate with $x_0=0$, $k\le n-1$, and $r_n=0$. Pitfall: $f_0=\|b\|$ fixes the
  scale of $b$; the residual norms do not depend on the choice of minimizer,
  so the statement can quantify over all minimizers. Statable at the pins;
  depends on 5.14. NASC: `NASC.exists_isGMRESIterate_norm_residual_eq`
  (IterativeMethods.lean), `sorry`.

* **5.17. Preconditioned conjugate gradients.** Let $A$ and $M$ be Hermitian
  positive definite and $\langle x,y\rangle_M=y^*Mx$. Then $M^{-1}A$ is
  self-adjoint and positive definite with respect to $\langle\cdot,\cdot\rangle_M$.
  The **preconditioned CG method** is CG applied to $M^{-1}Ax=M^{-1}b$ in the
  inner product $\langle\cdot,\cdot\rangle_M$: with $z_k=M^{-1}r_k$, it is
  the recurrence of 5.12 with $p_0=z_0$, $\alpha_k=r_k^*z_k/p_k^*Ap_k$ and
  $p_{k+1}=z_{k+1}+(r_{k+1}^*z_{k+1}/r_k^*z_k)\,p_k$. If $M=CC^*$, its iterates
  coincide with those of CG applied to $C^{-1}AC^{-*}u=C^{-1}b$ through
  $x_k=C^{-*}u_k$, when the starting vectors correspond. The iterate $x_k$
  minimizes $\|x-x^*\|_A$ over $x_0+\mathcal K_k(M^{-1}A,M^{-1}r_0)$, and if
  $\gamma M\le A\le\Gamma M$ in the sense of Hermitian forms with $\gamma>0$,
  then 5.13 holds with $\kappa=\Gamma/\gamma$; the best choice is
  $\kappa=\lambda_{\max}(M^{-1}A)/\lambda_{\min}(M^{-1}A)$.

  *Assessment.* The spectral theorem and a positive-definite factorization
  support the change of inner product. The selected result proves that the
  specified recurrence realizes that transformation and inherits the spectral
  ratio bound.

  *Lean target.* Carriers at the pins: `Matrix.PosDef`, the Loewner order on
  Hermitian matrices (`Matrix.PosSemidef (A - γ • M)`), a Cholesky-type factor
  `M = C * Cᴴ` from `Matrix.PosDef` (via `CFC.sqrt` or the spectral theorem),
  and the CG predicate of 5.12 with preconditioner $M^{-1}$. Conjuncts: (i)
  self-adjointness and positivity of $M^{-1}A$ in $\langle\cdot,\cdot\rangle_M$;
  (ii) equality with transformed CG; (iii) Krylov optimality; (iv) the
  condition-number bound with $\Gamma/\gamma$ and with the eigenvalue ratio.
  Pitfall: as in 5.12, the recurrence needs an explicit frozen branch.
  Statable at the pins; depends on 5.12–5.13. NASC:
  `NASC.IsConjugateGradient.energyNorm_error_le` (IterativeMethods.lean)
  states (iv) with $\Gamma/\gamma$, `sorry`.

* **5.18. GMRES field-of-values bound.** Let $A\in\mathbb C^{n\times n}$
  with $n\ge1$. Its **field of values** is
  $W(A)=\{v^*Av:\|v\|_2=1\}$. If $\nu=\min_{z\in W(A)}|z|>0$, then
  $A$ is nonsingular and the GMRES residuals of 5.14 satisfy
  $$\|r_k\|_2\le
  \left(1-\frac{\nu^2}{\|A\|_2^2}\right)^{k/2}\|r_0\|_2
  \qquad(k\ge1).$$
  Iterates after exact termination are taken to be the exact solution.

  *Assessment.* The selected estimate is meaningful for nonnormal operators
  with numerical range separated from zero. It uses the GMRES minimal residual
  property and a scalar trial update.

  *Argument.* At a nonzero residual, $x_k+\alpha r_k$ is feasible in the next
  Krylov space. Minimizing $\|r_k-\alpha Ar_k\|_2$ over complex $\alpha$
  reduces its squared norm by $|r_k^*Ar_k|^2/\|Ar_k\|_2^2$. The
  field-of-values lower bound and the operator-norm upper bound give the
  one-step factor. Iteration gives the result, with zero residuals remaining
  zero.

  *Lean target.* Carriers at the pins: the GMRES predicate of 5.14, the
  inner product on `EuclideanSpace ℂ (Fin (n + 1))`, and the operator norm. No
  new definition is needed: the field of values enters only through the
  hypothesis `∀ v, ‖v‖ = 1 → ν ≤ ‖⟪v, A v⟫‖`. Conjuncts: (i) nonsingularity of
  $A$; (ii) the residual bound for $k\ge1$. Pitfall: $(1-\nu^2/\|A\|^2)^{k/2}$
  is a real power of a nonnegative base, `Real.rpow`, with $\nu\le\|A\|$
  automatic. Everything is statable at the pins; depends on 5.14. NASC:
  `NASC.IsGMRESIterate.norm_residual_le_of_fieldOfValues`
  (IterativeMethods.lean), `sorry`.

## 6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation

[Synopsis](SYNOPSIS.md#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation) · [Coverage inventory](STRUCTURE.md#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation)

The selected matrix functions depend on the Jordan structure or holomorphic
calculus. Low-rank statements use the Euclidean operator or Frobenius norm as
indicated in each entry.

Matrices are complex unless a
statement says otherwise. In 6.1–6.5, $A\in\mathbb C^{n\times n}$ has
distinct eigenvalues $\lambda_1,\dots,\lambda_s$, and the **index** $n_i$ of
$\lambda_i$ is the order of the largest Jordan block of $A$ for $\lambda_i$.
In 6.9–6.11 the unadorned norm $\|\cdot\|$ is the spectral norm, a
**standard normal** matrix is a real matrix with independent $N(0,1)$
entries, $P_Y$ is the orthogonal projector onto the range of $Y$, and
$Y^\dagger$ is the Moore–Penrose pseudoinverse.

Common carriers at the pins for this section: `Matrix (Fin n) (Fin n) ℂ` as
a complete normed algebra (any of the scoped matrix norms), `spectrum ℂ A`,
TauCeti's holomorphic functional calculus `TauCeti.holomorphicCalculus`
(an algebra homomorphism on germs near the spectrum) with
`TauCeti.holomorphicCalculus_ofFun_eq_integral`, `NormedSpace.exp`,
`Matrix.fromBlocks`, `HasFDerivAt`, `Matrix.rank`, `LinearMap.singularValues`,
`Submodule.starProjection`, `LinearMap.moorePenroseInverse`, `stdGaussian`
and `ProbabilityTheory.gaussianReal`, and, for tensors, coordinate arrays
`(∀ j : Fin d, Fin (dims j)) → 𝕜` (NASC's `CoordinateTensor`) rather than
`PiTensorProduct`, whose topology is not set up for these statements.

### Functions of matrices

* **6.1. Definition and basic properties of $f(A)$.** A scalar function $f$
  is **defined on the spectrum** of $A$ if the values $f^{(j)}(\lambda_i)$
  exist for $0\le j\le n_i-1$ and $1\le i\le s$. For such $f$ the following
  two definitions give the same matrix $f(A)$.
  - (Jordan form.) If $Z^{-1}AZ=\mathrm{diag}(J_1,\dots,J_p)$ is a Jordan
    form, with $J_k$ the Jordan block of order $m_k$ for the eigenvalue
    $\mu_k$, then $f(A)=Z\,\mathrm{diag}(f(J_1),\dots,f(J_p))\,Z^{-1}$, where
    $f(J_k)$ is the upper triangular Toeplitz matrix with
    $(f(J_k))_{ij}=f^{(j-i)}(\mu_k)/(j-i)!$ for $j\ge i$. The same branch of
    $f$ is used in all blocks with the same eigenvalue (a **primary matrix
    function**).
  - (Hermite interpolation.) $f(A)=r(A)$, where $r$ is the unique
    polynomial of degree less than $\sum_{i=1}^s n_i$ with
    $r^{(j)}(\lambda_i)=f^{(j)}(\lambda_i)$ for $0\le j\le n_i-1$, $1\le i\le
    s$.

  In particular $f(A)$ is a polynomial in $A$, whose coefficients depend on
  $A$. Moreover $f(A)$ commutes with $A$; $f(A^\top)=f(A)^\top$;
  $f(XAX^{-1})=Xf(A)X^{-1}$ for every invertible $X$; the eigenvalues of
  $f(A)$ are the $f(\lambda)$ for the eigenvalues $\lambda$ of $A$; and if
  $A$ is block upper triangular, then $f(A)$ is block upper triangular
  with the same block structure and with diagonal blocks $f(A_{ii})$, so
  that $f$ of a block diagonal matrix is the block diagonal matrix of the
  $f(A_{ii})$.

  *Assessment.* Partly covered. Continuous functional calculus supplies the
  Hermitian case, TauCeti's holomorphic calculus supplies $f(A)$ for $f$
  holomorphic near the spectrum with spectral mapping, and TauCeti has Hermite
  interpolation at distinct nodes. The primary matrix function for $f$ only
  defined on the spectrum needs the equality of the Jordan and polynomial
  constructions, including repeated eigenvalues.

  *Scope.* The target is the primary matrix function for general Jordan
  structure and its equivalence with the Hermite interpolant.

  *Lean target.* Carriers at the pins: `Module.End.maxGenEigenspace` and the
  minimal polynomial `minpoly ℂ A` (whose root multiplicities are the indices
  $n_i$), `Polynomial.aeval`, `iteratedDeriv`, TauCeti's
  `TauCeti.existsUnique_hermite_interpolation` and
  `TauCeti.ordinaryHermiteJet_bijective`, and NASC's `jordanBlock`. New
  definitions: the predicate "defined on the spectrum" (for each eigenvalue
  $\lambda$, a jet `Fin (rootMultiplicity λ (minpoly ℂ A)) → ℂ` of values
  standing for $f^{(j)}(\lambda)$, so that $f$ need not be differentiable
  anywhere else), and `primaryFunction A jet := aeval A r` with $r$ the Hermite
  interpolant. Conjuncts: (i) the Jordan-block formula for `jordanBlock`;
  (ii) independence of the Jordan form; (iii) commutation, transpose,
  similarity; (iv) spectral mapping; (v) block triangular structure; (vi)
  agreement with `TauCeti.holomorphicCalculus` for holomorphic $f$. Pitfall:
  the derivative data must be taken at the index $n_i$, not the algebraic
  multiplicity, or the polynomial degree bound changes; Mathlib has no Jordan
  normal form of matrices, so (i)–(ii) use the generalized eigenspace
  decomposition and Jordan-chain bases (`Module.End.exists_jordanChainBasis`).
  Statable at the pins. NASC: `NASC.existsUnique_polynomial_iteratedDerivative`
  (MatrixFunctions.lean) states the interpolation step, `sorry` (it follows
  from the TauCeti Hermite interpolation); NASC's
  `aeval_jordanBlock_apply` gives (i) for polynomials, proved. Both are over a field of
  characteristic zero, and the interpolation step bounds `p.degree < ∑ m`, so `∑ m = 0` gives
  `p = 0`.

* **6.2. Power series, Cauchy integral and approximation.**
  - Let $f(z)=\sum_{k\ge0}a_k(z-\alpha)^k$ have radius of convergence $r>0$.
    Then $f(A)$ is defined and equals $\sum_{k\ge0}a_k(A-\alpha I)^k$ if and
    only if every distinct eigenvalue $\lambda_i$ satisfies either
    $|\lambda_i-\alpha|<r$, or $|\lambda_i-\alpha|=r$ and the series for
    $f^{(n_i-1)}$ converges at $\lambda_i$.
  - Let $f$ be holomorphic on an open set $D\subset\mathbb C$, and let
    $\Omega$ be a bounded open set with $\overline\Omega\subset D$ and
    $\Lambda(A)\subset\Omega$, whose boundary $\Gamma$ consists of finitely
    many rectifiable closed curves oriented positively with respect to
    $\Omega$. Then
    $$f(A)=\frac1{2\pi i}\oint_\Gamma f(\zeta)(\zeta I-A)^{-1}\,d\zeta,$$
    and for every $g$ holomorphic on $D$,
    $$\|f(A)-g(A)\|_2\le\frac1{2\pi}\oint_\Gamma|f(\zeta)-g(\zeta)|\,
    \|(\zeta I-A)^{-1}\|_2\,|d\zeta|.$$
  - If $A=Z\,\mathrm{diag}(\lambda)\,Z^{-1}$ is diagonalizable and $f$, $g$
    are defined on $\Lambda(A)$, then
    $$\|f(A)-g(A)\|_2\le\kappa_2(Z)\max_{\lambda\in\Lambda(A)}
    |f(\lambda)-g(\lambda)|.$$
    If $A$ is normal one may take $\kappa_2(Z)=1$.

  *Assessment.* Partly covered. TauCeti's holomorphic calculus is given by
  the resolvent integral over admissible cycles, agrees with power series
  whose disc contains the spectrum, and has a supremum-type contour bound.
  The boundary case of the power series criterion, the agreement with the
  Jordan definition of 6.1 and the integral form of the estimate are the
  targets.

  *Scope.* The selected claims concern the Jordan-size criterion on the circle
  of convergence and the Cauchy representation for general matrices.

  *Lean target.* Carriers at the pins: `Summable`/`HasSum` of
  `a k • (A - α • 1) ^ k`, `FormalMultilinearSeries.radius`,
  `TauCeti.hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall`,
  `FormalMultilinearSeries.summable_norm_coeff_smul_pow_of_spectrum_subset_eball`,
  `circleIntegral` for the circle case and TauCeti's cycles
  (`TauCeti.Contour.Cycle`) for general boundaries, and
  `TauCeti.norm_holomorphicCalculusOn_le`. Conjuncts: (i) the "if and only
  if" criterion with the boundary condition, stated for the Jordan index
  $n_i$ through `rootMultiplicity λ (minpoly ℂ A)`; (ii) the Cauchy formula;
  (iii) the integral bound. Pitfall: the criterion has to say that the series
  converges to the primary function of 6.1, so (i) depends on 6.1; for a
  circle, `circleIntegral` requires `0 ≤ r` and the spectrum in the open
  ball. (ii) and (iii) are statable at the pins for piecewise $C^1$ boundaries, which
  are TauCeti cycles; merely rectifiable boundaries need more contour theory. NASC:
  `NASC.summable_smul_pow_jordanBlock_iff` (MatrixFunctions.lean) proves the
  Jordan-block summability criterion, and
  `NASC.matrixFunctionOnCircle_jordanBlock_apply` states the circle integral on
  a Jordan block, `sorry`.

* **6.4. Fréchet derivative and condition number.** Let $f$ map an open
  subset of $\mathbb C^{n\times n}$ into $\mathbb C^{n\times n}$. Its
  **Fréchet derivative** at $A$ is the linear map $L_f(A):E\mapsto
  L_f(A,E)$ with $f(A+E)-f(A)-L_f(A,E)=o(\|E\|)$.
  - If $f$ is holomorphic on an open set containing $\Lambda(A)$, or $A$ has
    real spectrum and $f$ is $2n-1$ times continuously differentiable on an
    open interval $D\supset\Lambda(A)$ (the limit in the definition then
    being over $E$ with $\Lambda(A+E)\subset D$), then $L_f(A)$ exists and
    $$f\begin{pmatrix}A&E\\0&A\end{pmatrix}=
    \begin{pmatrix}f(A)&L_f(A,E)\\0&f(A)\end{pmatrix}.$$
  - If $L_f(A)$ exists, then with $\|L_f(A)\|=\max_{\|Z\|=1}\|L_f(A,Z)\|$ for
    a given matrix norm, and $f(A)\ne0$, the relative **condition number**
    $$\mathrm{cond}(f,A)=\lim_{\varepsilon\to0}\ \sup_{\|E\|\le\varepsilon\|A\|}
    \frac{\|f(A+E)-f(A)\|}{\varepsilon\|f(A)\|}$$
    equals $\|L_f(A)\|\,\|A\|/\|f(A)\|$.
  - If $f(x)=\sum_{k\ge0}a_kx^k$ has radius of convergence $r$ and
    $\|A\|<r$ for a submultiplicative norm, then
    $$L_f(A,E)=\sum_{k\ge1}a_k\sum_{j=1}^kA^{j-1}EA^{k-j},$$
    and $\|L_f(A)\|\le\tilde f'(\|A\|)$, where $\tilde f(x)=\sum_{k\ge0}|a_k|x^k$;
    if moreover $\|I\|=1$ (for example for every induced norm), then
    $\|f(A)\|\le\tilde f(\|A\|)$.

  *Assessment.* Partly covered. TauCeti proves the exponential insertion
  formula and block identities. The selected Fréchet derivative and
  conditioning statements concern a general primary matrix function.

  *Scope.* The selected block identity uses a scalar function holomorphic near
  the spectrum, or of class $C^{2n-1}$ on an interval for real spectrum. The
  derivative, condition number and differentiated series concern the
  resulting primary matrix function.

  *Lean target.* Carriers at the pins: `HasFDerivAt` for maps
  `Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ`, `Matrix.fromBlocks`,
  `TauCeti.holomorphicCalculus`, `TauCeti.hasFDerivAt_exp` and
  `TauCeti.expFDeriv_apply` for the exponential, `ContinuousLinearMap.opNorm`.
  Conjuncts: (i) holomorphic case: `HasFDerivAt (fun X ↦ f(X)) L A` on the
  open set of matrices with spectrum in the domain, and the block identity;
  (ii) real-spectrum case with `ContDiffOn ℝ (2 * n - 1)`, stated as
  `HasFDerivWithinAt` within $\{X:\Lambda(X)\subset D\}$; (iii) the condition
  number as a `limsup` (or `Filter.Tendsto` of the supremum over a ball, an
  `ℝ≥0∞` quantity) equal to $\|L\|\|A\|/\|f(A)\|$; (iv) the series formula and
  the bound $\|L\|\le\tilde f'(\|A\|)$, and $\|f(A)\|\le\tilde f(\|A\|)$ when
  `‖(1 : Matrix _ _ ℂ)‖ = 1`. Pitfall: the supremum in (iii) must be in
  `ℝ≥0∞` or over a bounded set to avoid `sSup` junk; the matrix norm in (iv)
  must be submultiplicative, and the Frobenius norm has $\|I\|=\sqrt n$. (i),
  (iii), (iv) are statable at the pins; (ii) needs the primary function of 6.1
  for non-holomorphic $f$. NASC:
  `NASC.exists_hasFDerivAt_matrixFunctionOnCircle_fromBlocks`
  (MatrixFunctions.lean) states (i) for the circle calculus, `sorry`.

* **6.5. Padé approximation of the exponential and scaling and squaring.**
  For $k,m\in\mathbb N_0$ the $[k/m]$ Padé approximant of $e^x$ is
  $r_{km}=p_{km}/q_{km}$ with
  $$p_{km}(x)=\sum_{j=0}^k\frac{(k+m-j)!\,k!}{(k+m)!\,(k-j)!\,j!}x^j,\qquad
  q_{km}(x)=\sum_{j=0}^m\frac{(k+m-j)!\,m!}{(k+m)!\,(m-j)!\,j!}(-x)^j;$$
  it satisfies $e^x-r_{km}(x)=O(x^{k+m+1})$, and it is the unique rational
  function with numerator degree at most $k$, denominator degree at most
  $m$ and $q(0)=1$ with this property. For $m\ge1$ write $r_m=r_{mm}$, let
  $\nu_m$ be the smallest modulus of a zero of $q_{mm}$, and let
  $$\Omega_m=\{X\in\mathbb C^{n\times n}:\rho(e^{-X}r_m(X)-I)<1,\
  \rho(X)<\nu_m\}.$$
  Let $h_{2m+1}(x)=\log(e^{-x}r_m(x))=\sum_{k\ge2m+1}c_kx^k$ near $0$. If
  $s\in\mathbb N_0$, $A\ne0$ and $2^{-s}A\in\Omega_m$, then
  $$r_m(2^{-s}A)^{2^s}=e^{A+\Delta A},\qquad
  \Delta A=2^s\,h_{2m+1}(2^{-s}A),$$
  and for every submultiplicative norm (the right side may be $+\infty$)
  $$\frac{\|\Delta A\|}{\|A\|}\le\frac{\sum_{k\ge2m+1}|c_k|\,
  \|2^{-s}A\|^k}{\|2^{-s}A\|}.$$
  Thus the scaling and squaring approximation is the exact exponential of
  a relatively small perturbation of $A$ (exact arithmetic assumed).

  *Assessment.* Not covered. The Padé approximants of the exponential, their
  uniqueness and the backward-error statement of scaling and squaring are not
  in any library; the matrix exponential and the holomorphic calculus are the
  ingredients.

  *Lean target.* Carriers at the pins: `Polynomial ℂ`, `Polynomial.aeval`,
  `NormedSpace.exp`, `Matrix.inv`, `spectralRadius`, TauCeti's
  `TauCeti.holomorphicCalculus` for $h_{2m+1}(X)$ and a principal logarithm
  near $1$. New definitions: `padeNum k m`, `padeDen k m : ℂ[X]` with the
  displayed coefficients, and `ν m` the least modulus of a root of
  `padeDen m m`. Conjuncts: (i) the order condition, as `q * exp − p`
  having `analyticOrderAt` at least $k+m+1$ at $0$; (ii) uniqueness among
  rational functions with $q(0)=1$; (iii) the identity $r_m(2^{-s}A)^{2^s}=e^{A+\Delta A}$ for
  $2^{-s}A\in\Omega_m$; (iv) the relative bound, in `ℝ≥0∞` since the series may
  diverge. Hypotheses: $m\ge1$, $A\ne0$. Pitfall: `Matrix.inv` of a singular
  $q_m(X)$ is `0`, so $\rho(X)<\nu_m$ is needed before $r_m(X)$ means
  anything; the series $\sum|c_k|x^k$ is a `tsum` in `ℝ≥0∞`. Statable at the
  pins. NASC: none.

### Matrix equations

* **6.6. Sylvester equation.** Let $A\in\mathbb C^{m\times m}$, $B\in\mathbb
  C^{n\times n}$. The linear map $X\mapsto AX-XB$ on $\mathbb C^{m\times n}$
  has the eigenvalues $\lambda-\mu$, $\lambda\in\Lambda(A)$,
  $\mu\in\Lambda(B)$. Hence the **Sylvester equation** $AX-XB=C$ has a
  unique solution $X$ for every $C\in\mathbb C^{m\times n}$ if and only if
  $\Lambda(A)\cap\Lambda(B)=\emptyset$. In that case:
  - if $\Omega$ is a bounded open set with positively oriented rectifiable
    boundary $\Gamma$, $\Lambda(A)\subset\Omega$ and
    $\Lambda(B)\cap\overline\Omega=\emptyset$, then
    $$X=\frac1{2\pi i}\oint_\Gamma(\zeta I-A)^{-1}C(\zeta I-B)^{-1}\,d\zeta;$$
  - if every eigenvalue of $A$ has positive real part and every eigenvalue
    of $B$ has negative real part, then
    $X=\int_0^\infty e^{-tA}Ce^{tB}\,dt$.

  *Assessment.* Partly covered. TauCeti gives the self-adjoint
  disjoint-spectrum solvability of the Sylvester equation in finite dimension
  and Rosenblum's uniqueness for self-adjoint operators. The gap comprises the
  spectrum of the general Sylvester map and the contour and half-line
  representations.

  *Scope.* The selected claims are the spectrum of the general Sylvester map
  and the contour and half-line representations under their stated spectral
  hypotheses.

  *Lean target.* Carriers at the pins: `Matrix.mulLeftLinearMap`,
  `Matrix.mulRightLinearMap` (NASC's `sylvesterLinearMap`),
  `spectrum ℂ` of a linear endomorphism of `Matrix (Fin m) (Fin n) ℂ`,
  `Module.End.HasEigenvalue`, `circleIntegral` or TauCeti's cycle integrals,
  `MeasureTheory.integral` over `Set.Ioi 0` with `NormedSpace.exp`, and
  `MeasureTheory.IntegrableOn`. Conjuncts: (i) the spectrum is
  $\{\lambda-\mu\}$; (ii) unique solvability iff disjoint spectra; (iii) the
  contour formula; (iv) the half-line formula, with integrability of the
  integrand as a conjunct. Pitfall: the Bochner integral is `0` for a
  non-integrable integrand, so (iv) must prove integrability (exponential
  decay from the spectral hypotheses). Statable at the pins. NASC:
  `NASC.spectrum_sylvesterLinearMap` states (i) over an algebraically closed field and
  `NASC.sylvester_integral_spec` states (iv) with uniqueness
  (MatrixFunctions.lean), both `sorry`.

* **6.7. Lyapunov equation.** Let $A\in\mathbb C^{n\times n}$. The
  **Lyapunov equation** $AX+XA^*=C$ is the Sylvester equation with
  $B=-A^*$; it is uniquely solvable for every $C$ if and only if
  $\lambda+\bar\mu\ne0$ for all $\lambda,\mu\in\Lambda(A)$, and then for
  Hermitian $C$ the solution is Hermitian. If $A$ is **stable**, that is,
  every eigenvalue of $A$ has negative real part, then for every $C$ the
  unique solution of $AX+XA^*+C=0$ is
  $$X=\int_0^\infty e^{tA}Ce^{tA^*}\,dt;$$
  if moreover $C$ is positive semidefinite (definite), then $X$ is positive
  semidefinite (definite). In particular, for $B\in\mathbb C^{n\times q}$ the
  **reachability Gramian** $P=\int_0^\infty e^{tA}BB^*e^{tA^*}dt$ is the
  positive semidefinite solution of $AP+PA^*+BB^*=0$.

  *Assessment.* Partly covered. TauCeti's positive Sylvester equivalence
  solves the positive self-adjoint case after sign conversion. General stable
  matrices and the positive-semidefinite integral and Gramian conclusions
  remain.

  *Scope.* The target includes the integral solution and its positivity
  properties, with the reachability Gramian as a special case.

  *Lean target.* Carriers at the pins: `Matrix.IsHermitian`, `Matrix.PosDef`,
  `Matrix.PosSemidef`, `NormedSpace.exp`, `Matrix.conjTranspose`, the
  integral over `Set.Ioi (0 : ℝ)`, and TauCeti's
  `ContinuousLinearMap.positiveSylvesterEquiv`. Conjuncts: (i) unique
  solvability iff $\lambda+\bar\mu\ne0$; (ii) Hermitian solution for
  Hermitian $C$; (iii) for stable $A$ the integral solves $AX+XA^*+C=0$
  uniquely, with integrability; (iv) positivity transfer, semidefinite and
  definite; (v) the Gramian. Pitfall: as in 6.6, the integral formula needs
  integrability, and stability must be stated through `spectrum ℂ A`, not real
  eigenvalues. Depends on 6.6. Statable at the pins. NASC:
  `NASC.lyapunov_integral_spec` (MatrixFunctions.lean) states (iii)–(iv), `sorry`.

### Low-rank and randomized approximation

* **6.8. Schmidt–Eckart–Young–Mirsky theorem.** Let $A\in\mathbb K^{m\times
  n}$ have the singular value decomposition $A=\sum_{j=1}^p\sigma_ju_jv_j^*$,
  $p=\min\{m,n\}$, and put $\sigma_{p+1}=0$. For $0\le k\le p$ let
  $A_k=\sum_{j=1}^k\sigma_ju_jv_j^*$. Then
  $$\min_{\mathrm{rank}\,B\le k}\|A-B\|_2=\|A-A_k\|_2=\sigma_{k+1},\qquad
  \min_{\mathrm{rank}\,B\le k}\|A-B\|_F=\|A-A_k\|_F
  =\Bigl(\sum_{j=k+1}^p\sigma_j^2\Bigr)^{1/2}.$$

  *Assessment.* Partly covered. TauCeti identifies approximation numbers with
  singular values (the operator-norm case) and has the singular-value
  Hoffman–Wielandt inequality in Frobenius norm and the Frobenius norm as the
  root of the sum of squared singular values. The minimum and attaining
  truncation in Frobenius norm are the selected gap.

  *Scope.* The selected claim is the Frobenius-norm optimum and its attaining
  truncated singular value decomposition.

  *Argument.* For $\mathrm{rank}\,B\le k$ the singular values $\sigma_i(B)$
  vanish for $i>k$, so the singular-value Hoffman–Wielandt inequality gives
  $\|A-B\|_F^2\ge\sum_i(\sigma_i(A)-\sigma_i(B))^2\ge\sum_{i>k}\sigma_i(A)^2$.
  The truncated rank-one expansion attains the bound.

  *Lean target.* Carriers at the pins: `Matrix.rank`, the Frobenius norm
  (`open scoped Matrix.Norms.Frobenius`, or the entrywise sum of squares),
  `LinearMap.singularValues` of `Matrix.toEuclideanLin A`, TauCeti's
  `Matrix.sum_sq_singularValues_toEuclideanLin_sub_le_frobenius_norm_sub_sq`
  and `LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`.
  No new definition is needed. Conjuncts: (i) the lower bound for every $B$
  of rank at most $k$; (ii) attainment by the truncation; together an
  `IsLeast` of squared errors. Pitfall: `singularValues` is zero-extended
  beyond the rank, so the tail sum can be written over `Finset.Ico k (min m n)`.
  Everything is statable at the pins. NASC:
  `NASC.isLeast_rankApproximation_frobenius_sq` (LowRankApproximation.lean),
  `sorry`.

* **6.9. Randomized range finder.** Let $B\in\mathbb R^{m\times n}$ have
  singular values $\sigma_1\ge\sigma_2\ge\cdots$, let $X\in\mathbb
  R^{n\times\ell}$ be a test matrix and $Y=BX$. The approximation
  $P_YB=QQ^*B$, with $Q$ an orthonormal basis of the range of $Y$, is the
  output of the randomized range finder, and of the randomized SVD that
  factors $Q^*B$.
  - (Deterministic bound.) Let $k\le\ell$, let $V_1$ and $V_2$ hold the
    first $k$ and the remaining right singular vectors of $B$ (with $B$
    padded by zero rows or columns to be square), $\Sigma_2$ the remaining
    singular values, and suppose $X_1=V_1^*X$ has full row rank. Then, with
    $X_2=V_2^*X$,
    $$\|(I-P_Y)B\|\le\sigma_{k+1}+\|\Sigma_2X_2X_1^\dagger\|.$$
  - (Gaussian test matrix.) Let $X=\Omega$ be standard normal and $k<\ell-1$.
    Let $Z=\|\Gamma^\dagger\|$ with $\Gamma\in\mathbb R^{k\times\ell}$
    standard normal. Then
    $$\mathbb E\|(I-P_Y)B\|\le\Bigl(1+\sqrt{\tfrac{k}{\ell-k-1}}\Bigr)
    \sigma_{k+1}+(\mathbb EZ)\Bigl(\sum_{j>k}\sigma_j^2\Bigr)^{1/2},$$
    and $\mathbb EZ\le e\sqrt\ell/(\ell-k)$ when $2\le k<\ell$. So for
    $k\ge2$ and oversampling $\ell-k\ge2$ the expected error is at most
    $(1+\sqrt{k/(\ell-k-1)})\sigma_{k+1}+(e\sqrt\ell/(\ell-k))
    (\sum_{j>k}\sigma_j^2)^{1/2}$.

  *Assessment.* Projection, SVD, the Moore–Penrose inverse and
  finite-dimensional Gaussian measures are available. The gap combines
  deterministic block estimates with the independence and pseudoinverse
  estimates used for Gaussian tests.

  *Lean target.* Carriers at the pins: `Submodule.starProjection` of the
  range of `(B * X).toEuclideanLin`, `Matrix.toEuclideanCLM` with the operator
  norm, `LinearMap.singularValues`, TauCeti's `LinearMap.moorePenroseInverse`,
  and a product Gaussian law on matrices (NASC's
  `gaussianMatrixLaw m n v = Measure.pi (fun _ ↦ Measure.pi (fun _ ↦ gaussianReal 0 v))`).
  Conjuncts: (i) the deterministic bound, with $X_1^\dagger$ a right inverse
  of $X_1$ (full row rank) and $B$ padded to square; (ii) the expectation
  bound, with $\mathbb E Z$ finite as a conjunct; (iii) the bound on
  $\mathbb EZ$; (iv) the combined bound. Hypotheses: $k<\ell-1$ for (ii),
  $2\le k<\ell$ for (iii). Pitfall: $\mathbb E\|(I-P_Y)B\|$ is a Bochner
  integral of a bounded measurable function, fine, but $Z=\|\Gamma^\dagger\|$
  is unbounded, so its expectation should be `∫⁻` in `ℝ≥0∞`; the
  pseudoinverse of a rank-deficient sample is junk-free but discontinuous, so
  measurability must be proved. (i) is statable at the pins; (ii)–(iii) need
  the law of $\|\Gamma^\dagger\|$ (inverse Wishart moments), which no library
  has. NASC: `NASC.rangeFinder_error_le` (LowRankApproximation.lean) states
  (i), `sorry`.

* **6.10. Gaussian embeddings, Johnson–Lindenstrauss and subspace
  embeddings.** For $E$ a nonempty subset of the unit sphere $S^{n-1}$ of
  $\mathbb R^n$ let $w(E)=\mathbb E\sup_{x\in E}\langle g,x\rangle$, with
  $g\in\mathbb R^n$ standard normal, be its **Gaussian width**, and for
  $S\in\mathbb R^{d\times n}$ let $\sigma_{\min}(S;E)=\inf_{x\in E}\|Sx\|_2$
  and $\sigma_{\max}(S;E)=\sup_{x\in E}\|Sx\|_2$. Let $\Gamma\in\mathbb
  R^{d\times n}$ have independent $N(0,1/d)$ entries. Then for every
  $t>0$
  $$\mathbb P\Bigl\{\sigma_{\min}(\Gamma;E)\le1-\frac{w(E)+1}{\sqrt d}-t
  \Bigr\}\le e^{-dt^2/2},\qquad
  \mathbb P\Bigl\{\sigma_{\max}(\Gamma;E)\ge1+\frac{w(E)}{\sqrt d}+t\Bigr\}
  \le e^{-dt^2/2}.$$
  - (Subspace embedding.) If $L\subset\mathbb R^n$ is a subspace of
    dimension $k\ge1$, then $\sqrt{k-1}<w(L\cap S^{n-1})<\sqrt k$, so with
    probability at least $1-2e^{-dt^2/2}$,
    $$\Bigl(1-\frac{1+\sqrt k}{\sqrt d}-t\Bigr)\|x\|_2\le\|\Gamma x\|_2\le
    \Bigl(1+\frac{\sqrt k}{\sqrt d}+t\Bigr)\|x\|_2\qquad\text{for all }x\in L.$$
  - (Johnson–Lindenstrauss.) Let $a_1,\dots,a_N\in\mathbb R^n$ be distinct,
    $N\ge2$, $M=N(N-1)/2$, $\varepsilon\in(0,1)$ and $t>0$ with
    $(1+\sqrt{2\log M})/\sqrt d+t\le\varepsilon$. Then with probability at
    least $1-2e^{-dt^2/2}$,
    $$(1-\varepsilon)\|a_i-a_j\|_2\le\|\Gamma(a_i-a_j)\|_2\le
    (1+\varepsilon)\|a_i-a_j\|_2\qquad\text{for all }i\ne j.$$
    Hence an embedding dimension $d$ of order $\varepsilon^{-2}\log N$
    suffices.

  *Assessment.* The Gaussian moment and concentration APIs supply ingredients
  for the random projection, and TauCeti has the chi law of a Gaussian norm
  with the bounds $k/\sqrt{k+1}\le\mathbb E\chi_k\le\sqrt k$. Uniform control
  over a set or subspace requires the Gaussian width comparison and both
  singular-direction bounds.

  *Lean target.* Carriers at the pins: `stdGaussian` on
  `EuclideanSpace ℝ (Fin n)`, NASC's `gaussianMatrixLaw d n (1/d)`,
  `Matrix.toEuclideanLin`, `iSup`/`iInf` over $E$, TauCeti's
  `TauCeti.Probability.stdGaussian_map_norm`,
  `TauCeti.Probability.integral_id_chiMeasure_le` and
  `TauCeti.Probability.mul_div_sqrt_add_one_le_integral_id_chiMeasure`. New
  definition: the Gaussian width `gaussianWidth E := ∫ g, ⨆ x ∈ E, ⟪g, x⟫ ∂stdGaussian`.
  Conjuncts: (i) the two tail bounds of Gordon's theorem; (ii) the width of a
  subspace section; (iii) the subspace embedding; (iv) Johnson–Lindenstrauss.
  Hypotheses: $E$ nonempty and contained in the sphere, $d\ge1$, $t>0$.
  Pitfall: `⨆ x ∈ E` over a real-valued function is junk for unbounded
  families, but here $|\langle g,x\rangle|\le\|g\|$; the width integral needs
  integrability of the supremum (dominated by $\|g\|$) and measurability, which
  holds for separable $E$ (take a countable dense subset). In (ii) the width is
  $\mathbb E\chi_k$; the lower bound is strict since $k/\sqrt{k+1}>\sqrt{k-1}$,
  while the TauCeti upper bound is non-strict and the strict one needs the
  positive variance of $\chi_k$.
  (iv) is statable at the pins from a union bound and the chi-squared tail;
  (i) needs Gordon's comparison inequality, which no library has. NASC:
  `NASC.gaussianMatrixLaw_exists_distorted_pair_le` (LowRankApproximation.lean, with
  `NASC.gaussianMatrixLaw` from `NASC/Support/GaussianMatrix.lean`) states (iv), `sorry`.

### Tensors

For finite-dimensional vector spaces $V_1,\dots,V_d$ over $\mathbb K$ let
$V=V_1\otimes\cdots\otimes V_d$; it is **non-degenerate** if $d\ge1$ and
$\dim V_j\ge2$ for all $j$. Let $\mathcal R_r\subset V$ be the set of sums of
at most $r$ elementary tensors $v^{(1)}\otimes\cdots\otimes v^{(d)}$.
For $V=\mathbb K^{n_1\times\cdots\times n_d}$ with the Euclidean
(Frobenius) norm and $\emptyset\ne\alpha\subsetneq\{1,\dots,d\}$,
$M_\alpha(v)$ is the matricization of $v$ with row indices
$(i_j)_{j\in\alpha}$ and column indices $(i_j)_{j\notin\alpha}$, and
$M_j=M_{\{j\}}$.

* **6.12. Tensor rank, border rank and ill-posedness.** The **tensor rank**
  of $v\in V$ is $\min\{r:v\in\mathcal R_r\}$, and its **border rank** is
  $\min\{r:v\in\overline{\mathcal R_r}\}$, the closure being taken in any
  norm. Let $V$ be non-degenerate of order $d\ge3$.
  - Let $d=3$ (the example embeds in every order $d\ge3$). If
    $v_j,w_j\in V_j$ are linearly independent ($j=1,2,3$), then
    $$v=v_1\otimes v_2\otimes w_3+v_1\otimes w_2\otimes v_3+w_1\otimes
    v_2\otimes v_3$$
    has tensor rank $3$, while
    $$v_n=\bigl(w_1+nv_1\bigr)\otimes\bigl(v_2+\tfrac1nw_2\bigr)\otimes v_3
    +v_1\otimes v_2\otimes\bigl(w_3-nv_3\bigr)\in\mathcal R_2$$
    satisfies $v-v_n=-\frac1nw_1\otimes w_2\otimes v_3\to0$. So $v$ has
    border rank $2$, and $v$ has no best approximation in $\mathcal R_2$ in
    any norm.
  - $\mathcal R_1$ is closed, and $\mathcal R_r$ is not closed for
    $2\le r\le\min_j\dim V_j$.
  - Every convergent sequence in $\mathcal R_r$ whose terms have
    representations $\sum_{i=1}^r\bigotimes_jv^{(j)}_{n,i}$ with
    $\sum_i\prod_j\|v^{(j)}_{n,i}\|$ bounded by a constant times
    $\|\sum_i\bigotimes_jv^{(j)}_{n,i}\|$ has its limit in $\mathcal R_r$.
    Hence for every sequence in $\mathcal R_r$ converging to a tensor
    outside $\mathcal R_r$, and every choice of representations, the sums
    $\sum_i\prod_j\|v^{(j)}_{n,i}\|$ are unbounded: the terms cancel.

  *Assessment.* Tensor products are available. The gap concerns rank strata,
  their closures and existence of nearest low-rank approximants in the
  specified dimensions.

  *Lean target.* Carriers at the pins: coordinate tensors
  `(∀ j : Fin d, Fin (dims j)) → 𝕜` with the product topology, `closure`,
  `IsClosed`, `Metric.infDist`, and `sInf` on `ℕ` for the ranks. New
  definitions: `HasTensorRankLE dims T r` (a sum of `r` products, zero
  factors padding shorter sums), `tensorRank T := sInf {r | HasTensorRankLE dims T r}`
  and `borderRank T := sInf {r | T ∈ closure {S | HasTensorRankLE dims S r}}`.
  Conjuncts: (i) the rank-3 tensor $v$ and the sequence $v_n$, with border
  rank $2$ and no best approximation in $\mathcal R_2$ (`¬∃ u ∈ R₂, dist v u = infDist v R₂`);
  (ii) $\mathcal R_1$ closed; (iii) $\mathcal R_r$ not closed for
  $2\le r\le\min_j\dim V_j$; (iv) the cancellation statement. Pitfall:
  `sInf ∅ = 0` on `ℕ` is harmless here since every tensor has finite rank, but
  the non-degeneracy hypothesis $\dim V_j\ge2$ must be explicit; "in any norm"
  reduces to the coordinate topology by equivalence of norms. Statable at the
  pins. NASC: `NASC.isClosed_setOf_hasTensorRankLE_one` states (ii) and
  `NASC.exists_borderRankTwo_not_rankTwo` states (i) for $2\times2\times2$
  without the best-approximation part (LowRankApproximation.lean), both
  `sorry`.

* **6.13. Quasi-optimality of HOSVD truncation.** For $v\in\mathbb
  K^{n_1\times\cdots\times n_d}$ let $s_j=\mathrm{rank}\,M_j(v)$, let
  $\sigma^{(j)}_1\ge\cdots\ge\sigma^{(j)}_{s_j}>0$ be the singular values
  and $b^{(j)}_1,\dots,b^{(j)}_{s_j}$ the left singular vectors of $M_j(v)$.
  For $r=(r_1,\dots,r_d)$ with $r_j\le s_j$ let $\mathcal T_r$ be the set of
  tensors in $U_1\otimes\cdots\otimes U_d$ for some subspaces
  $U_j\subset\mathbb K^{n_j}$ with $\dim U_j\le r_j$, let $P_j$ be the
  orthogonal projector onto $\mathrm{span}\{b^{(j)}_i:i\le r_j\}$, and
  $u_{\mathrm{HOSVD}}=(P_1\otimes\cdots\otimes P_d)v\in\mathcal T_r$. Then
  a best approximation $u_{\mathrm{best}}\in\mathcal T_r$ exists and
  $$\|v-u_{\mathrm{HOSVD}}\|\le\Bigl(\sum_{j=1}^d\sum_{i=r_j+1}^{s_j}
  (\sigma_i^{(j)})^2\Bigr)^{1/2}\le\sqrt d\,\|v-u_{\mathrm{best}}\|.$$
  The factor $\sqrt d$ may be replaced by the square root of the number of
  $j$ with $r_j<s_j$.

  *Assessment.* The matrix SVD can be applied to each unfolding. The selected
  theorem assembles the mode-wise deficiencies into a tensor error bound
  relative to the best Tucker approximation.

  *Lean target.* Carriers at the pins: coordinate tensors as in 6.12, mode
  unfoldings as matrices `Matrix (Fin (dims j)) (∀ k : {k // k ≠ j}, Fin (dims k)) 𝕜`
  (NASC's `modeUnfold`), `LinearMap.singularValues`, orthonormal frames
  `U j : Matrix (Fin (dims j)) (Fin (r j)) 𝕜` with `(U j)ᴴ * U j = 1`, and the
  Euclidean norm on coordinate tensors. New definition: the Tucker set
  $\mathcal T_r$ as the image of the multilinear maps with frames of the
  given sizes. Conjuncts: (i) the HOSVD error bound; (ii) existence of a best
  approximation in $\mathcal T_r$ (closedness of $\mathcal T_r$); (iii) the
  $\sqrt d$ comparison, and the refined count. Pitfall: the frames must be
  leading singular vectors (the NASC statement expresses this through the
  Gram eigen-equation); singular values are zero-extended, so the tail sums
  may run to `dims j`. Statable at the pins. NASC:
  `NASC.hosvd_projection_error_sq_le` (LowRankApproximation.lean) states (i)
  in squared form, `sorry`.

* **6.14. Tensor trains.** For $\rho=(\rho_1,\dots,\rho_{d-1})\in\mathbb
  N^{d-1}$ and $\rho_0=\rho_d=1$, the **tensor train** set $\mathcal
  T_\rho$ consists of the $v\in\mathbb K^{n_1\times\cdots\times n_d}$ with
  $$v[i_1,\dots,i_d]=G_1[i_1]\,G_2[i_2]\cdots G_d[i_d],\qquad
  G_j[i_j]\in\mathbb K^{\rho_{j-1}\times\rho_j}.$$
  - Let $v\ne0$. Then $v\in\mathcal T_\rho$ implies $\rho_j\ge\rho_j^*:=\mathrm{rank}\,
    M_{\{1,\dots,j\}}(v)$ for $1\le j\le d-1$, and $v\in\mathcal T_{\rho^*}$.
  - Let $\rho_j\le\rho_j^*$ for all $j$, and let $\sigma^{(j)}_i$ be the
    singular values of $M_{\{1,\dots,j\}}(v)$. Let $u\in\mathcal T_\rho$
    be obtained from $v$ by applying successively, for $j=d-1,d-2,\dots,1$,
    the orthogonal projection onto the span of the leading $\rho_j$ left
    singular vectors of $M_{\{1,\dots,j\}}(v)$, acting on the first $j$
    factors (HOSVD truncation in the tensor train format). Then a best
    approximation $u_{\mathrm{best}}$ of $v$ in $\mathcal T_\rho$ exists and
    $$\|v-u\|\le\Bigl(\sum_{j=1}^{d-1}\sum_{i>\rho_j}(\sigma_i^{(j)})^2
    \Bigr)^{1/2}\le\sqrt{d-1}\,\|v-u_{\mathrm{best}}\|.$$

  *Assessment.* Matrix ranks of unfoldings and finite tensors supply
  ingredients. The missing results identify the minimal representable ranks
  and control the approximation produced by successive truncations.

  *Lean target.* Carriers at the pins: coordinate tensors, cut unfoldings at
  position $j$ (NASC's `cutUnfold`), `Matrix.rank`, and finite bond indices
  `Fin (ρ j)`. New definition: `HasTensorTrain T ρ` with `ρ : Fin (d + 1) → ℕ`,
  `ρ 0 = ρ (Fin.last d) = 1`, and cores `G j : Fin (ρ j) → Fin (ρ (j+1)) → Fin (dims j) → 𝕜`.
  Conjuncts: (i) ranks of a representation dominate the cut ranks; (ii)
  $v\in\mathcal T_{\rho^*}$ for $v\ne0$; (iii) the truncation bound; (iv) a
  best approximation exists and the $\sqrt{d-1}$ comparison. Pitfall: with
  `ρ j = 0` allowed, `HasTensorTrain` holds only for `T = 0`, which is why the
  synopsis takes $v\ne0$; the projections must be applied in the order
  $j=d-1,\dots,1$. (i)–(iii) are statable at the pins; (iv) needs closedness of
  the tensor train set of bounded ranks. NASC:
  `NASC.hasTensorTrain_iff_cutRank_le` (LowRankApproximation.lean) states
  (i)–(ii) as one equivalence, `sorry`; NASC's `HasTensorTrain` carries a scalar factor, so that
  for `d = 0` every scalar is a tensor train, and the equivalence holds for every `d`.

### Hierarchical matrices

Let $I$ and $J$ be finite index sets and let each index $i$ have a support
$X_i\subset\mathbb R^m$ (for example the support of a basis function). For
$\tau\subset I$ put $X_\tau=\bigcup_{i\in\tau}X_i$, and define $Y_\sigma$
for $\sigma\subset J$ alike. A **cluster tree** $T(I)$ is a tree of subsets
of $I$ with root $I$ in which the sons of each non-leaf cluster partition
it; a **block partition** $P$ is a set of disjoint blocks $\tau\times\sigma$
with $\tau\in T(I)$, $\sigma\in T(J)$, covering $I\times J$.

* **6.16. Low-rank approximability of asymptotically smooth kernels.** A
  kernel $\kappa$, infinitely differentiable on a neighbourhood of
  $\{(x,y)\in X\times Y:x\ne y\}\subset\mathbb R^m\times\mathbb R^m$, is
  **asymptotically smooth** on $X\times Y$ if for some $C,\gamma>0$ and
  $\rho,s\in\mathbb R$,
  $$|\partial_x^\alpha\partial_y^\beta\kappa(x,y)|\le
  C\,(\alpha+\beta)!\,|\alpha+\beta|^\rho\gamma^{|\alpha+\beta|}\,
  |x-y|^{-|\alpha|-|\beta|-s}$$
  for $x\in X$, $y\in Y$, $x\ne y$ and multi-indices $(\alpha,\beta)\ne0$.
  Examples are $|x-y|^{-a}$ ($s=a$) and $\log|x-y|$ ($s=0$) on $\mathbb
  R^m\times\mathbb R^m$.
  - Let $X$ be convex, $x_0\in X$, $\mathrm{dist}(X,Y)>0$, $q\in\mathbb N$
    with $q+s\ge0$, and let $\kappa^{(r)}$ be the Taylor polynomial of
    $\kappa(\cdot,y)$ of degree $q-1$ about $x_0$, a separable expansion
    $\sum_{\nu=1}^r\varphi_\nu(x)\psi_\nu(y)$ with
    $r=\binom{q-1+m}{m}\le q^m$ terms. If $\mathrm{diam}\,X\le\eta\,
    \mathrm{dist}(X,Y)$, then for $x\in X$, $y\in Y$,
    $$|\kappa(x,y)-\kappa^{(r)}(x,y)|\le C\,q^\rho\binom{q+m-1}{m-1}
    \,\mathrm{dist}(X,Y)^{-s}\,(\gamma\eta)^q.$$
    For $\gamma\eta<1$ and every $c<\log(1/(\gamma\eta))$ the error is at
    most $C_c\exp(-c\,r^{1/m})$, with $C_c$ depending only on $c$, $C$,
    $\rho$, $m$, $\gamma\eta$ and $\mathrm{dist}(X,Y)^{-s}$. The same holds with the
    roles of $x$ and $y$ exchanged, so on every $\eta$-admissible block with convex supports the
    kernel has such a separable approximation. The Galerkin block
    $\bigl(\int\!\int\kappa^{(r)}(x,y)\phi_i(x)\phi_j(y)\,dx\,dy\bigr)
    _{i\in\tau,j\in\sigma}$ of the separable kernel has rank at most $r$, and
    its entries differ from those of $\kappa$ by at most the above bound
    times $\|\phi_i\|_{L^1}\|\phi_j\|_{L^1}$, when $\mathrm{supp}\,\phi_i
    \subset X$ and $\mathrm{supp}\,\phi_j\subset Y$.
  - For $m=1$, $\kappa(x,y)=\log|x-y|$, $X=[a,b]$, $Y=[c,e]$ with
    $a<b<c\le e$, $\eta=(b-a)/(c-b)$ and $x_0=(a+b)/2$, the Taylor
    expansion with $r$ terms satisfies, for every $\eta>0$,
    $$|\kappa(x,y)-\kappa^{(r)}(x,y)|\le\frac{2+\eta}{2r}
    \Bigl(\frac{\eta}{2+\eta}\Bigr)^r.$$

  *Assessment.* The approximation machinery provides Taylor's theorem and
  finite-rank maps. The gap connects the derivative bounds and admissibility
  geometry to quantitative separated kernel approximations.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℝ (Fin m)`, `Convex ℝ X`, `ContDiffOn ℝ ∞`
  (smooth; `⊤ = ω` means analytic at the pins), `iteratedFDeriv` (or coordinate partials via
  `iteratedDeriv` along basis directions for multi-indices), `Metric.diam`,
  `Metric.infDist`/`EMetric.infEdist` for $\mathrm{dist}(X,Y)$, `taylorWithinEval` for $m=1$, and
  `MeasureTheory.integral` for the Galerkin block. New definitions: multi-indices `Fin m → ℕ` with
  factorials, the asymptotic smoothness predicate (an inequality for all $(\alpha,\beta)\ne0$), and
  the separable expansion as `Fin r → (ℝ^m → ℝ) × (ℝ^m → ℝ)`. Conjuncts: (i) the explicit Taylor
  bound; (ii) the exponential rate in $r^{1/m}$; (iii) the exchanged roles; (iv) the Galerkin block
  rank and entry bound; (v) the one-dimensional logarithmic bound. Hypotheses: $q\ge1$, $q+s\ge0$,
  $\mathrm{dist}(X,Y)>0$, $x_0\in X$ convex. Pitfall: $|\alpha+\beta|^\rho$ at $\alpha+\beta=0$ is
  excluded by $(\alpha,\beta)\ne0$; `Metric.diam` is `0` for unbounded sets, so boundedness of $X$
  must be assumed. Statable at the pins. NASC: `NASC.exists_separatedApproximation_of_fderiv_bound`
  (LowRankApproximation.lean) states a Taylor-remainder form of (i) with a uniform bound $M$ on the
  $q$-th derivative and constant $MD^q/q!$, `sorry`.

## 7. Interval arithmetic and verified computation

[Synopsis](SYNOPSIS.md#7-interval-arithmetic-and-verified-computation) · [Coverage inventory](STRUCTURE.md#7-interval-arithmetic-and-verified-computation)

Mathlib's endpoint arithmetic for sums and differences and its dyadic
inclusion machinery, and TauCeti's Brouwer and Schauder fixed-point theorems,
supply the starting points. These gaps link real interval semantics and
outward rounding to validated numerical conclusions.

In this section $\mathbb{IR}$ is the set of nonempty compact real
intervals $X=[\underline x,\overline x]$ with $\underline x\le\overline x$. A
real number $a$ is identified with the **point interval** $[a,a]$. Write
$w(X)=\overline x-\underline x$ for the **width**,
$\mathop{\mathrm{mid}}X=(\underline x+\overline x)/2$,
$\mathop{\mathrm{rad}}X=w(X)/2$, and
$\mathop{\mathrm{mag}}X=\max\{|x|:x\in X\}$. An **interval vector**
$X\in\mathbb{IR}^n$ is a box $X_1\times\cdots\times X_n$, equivalently
$X=\{x\in\mathbb R^n:\underline x\le x\le\overline x\}$ with componentwise
order. Interval matrices $\mathbb{IR}^{m\times n}$ are defined in the same
way. Width, midpoint, radius and absolute value $|\cdot|$ act componentwise.
$\mathop{\mathrm{int}}X$ is the interior of $X$, and the **hull** of a bounded
set $S\subset\mathbb R^n$ is the smallest box containing it. Bold letters
are not used, so the role of each symbol is stated.

### Interval arithmetic

* **7.1. Interval operations.** For $X,Y\in\mathbb{IR}$ and
  $\circ\in\{+,-,\cdot,/\}$, with $0\notin Y$ when $\circ$ is division, the
  set $X\circ Y=\{x\circ y:x\in X,\ y\in Y\}$ is again an element of
  $\mathbb{IR}$, and
  $$X\circ Y=\bigl[\min\{\underline x\circ\underline y,\underline x\circ
  \overline y,\overline x\circ\underline y,\overline x\circ\overline y\},\
  \max\{\underline x\circ\underline y,\underline x\circ\overline y,
  \overline x\circ\underline y,\overline x\circ\overline y\}\bigr].$$
  In particular
  $X+Y=[\underline x+\underline y,\overline x+\overline y]$ and
  $X-Y=[\underline x-\overline y,\overline x-\underline y]$. These are the
  **interval operations**. Widths add under both addition and subtraction:
  $$w(X+Y)=w(X-Y)=w(X)+w(Y),$$
  so $w(X-X)=2w(X)$ although $\{x-x:x\in X\}=\{0\}$.

  *Assessment.* Partly covered. Mathlib gives the exact range of the sum and the difference of two
  closed real intervals and the additivity of widths. The endpoint rule for products, including
  products of intervals that contain zero, and for quotients with $0\notin Y$ is the remaining
  content.

  *Scope.* The selected claims are the exact ranges of the product and of the quotient; the sum,
  the difference and the width identities are in Mathlib.

  *Lean target.* Carriers: `NonemptyInterval ℝ` with `NonemptyInterval.fst`,
  `NonemptyInterval.snd` and the coercion to `Set ℝ`, which is `Set.Icc X.fst X.snd`;
  `Set.image2`; `Set.Icc_add_Icc`, `Set.Icc_sub_Icc`, `NonemptyInterval.length_add` and
  `NonemptyInterval.length_sub` for the covered part. New definition: the four corner values of a
  binary operation, a `Finset ℝ`, or directly an interval product
  `NonemptyInterval ℝ → NonemptyInterval ℝ → NonemptyInterval ℝ` whose endpoints are the least and
  greatest of the four endpoint products. Conjuncts: (i) `Set.image2 (· * ·) X Y` is the closed
  interval between the least and greatest corner products; (ii) under `0 ∉ (Y : Set ℝ)` the same
  for `(· / ·)`. Pitfall: Lean's `x / 0 = 0` makes the quotient image a set containing junk values
  when $0\in Y$, so the hypothesis $0\notin Y$ must be kept even though the statement typechecks
  without it; the least and greatest corners should be taken with `Finset.min'` and `Finset.max'`
  or with `min`/`max`, not with `sInf`/`sSup` of an arbitrary set. Statable and provable at the
  pins; no dependency. NASC: `NASC.image2_eq_Icc_intervalCorners`
  (`NASC/VerifiedComputation.lean`), covering all four operations through a disjunction of cases,
  `sorry`.

* **7.3. Fundamental theorem of interval arithmetic.** An **arithmetic
  expression** in variables $\xi_1,\dots,\xi_n$ is built from real constants
  and the variables by the operations $+,-,\cdot,/$ and by finitely many
  continuous **standard functions** $\varphi$ (such as $\exp$, $\sin$,
  $\sqrt{\cdot}$, $x\mapsto x^2$), each defined on an interval
  $\mathop{\mathrm{dom}}\varphi$. For $Z\in\mathbb{IR}$ with
  $Z\subseteq\mathop{\mathrm{dom}}\varphi$ set
  $\varphi(Z)=\{\varphi(z):z\in Z\}\in\mathbb{IR}$. The **natural interval
  extension** $F$ of an expression $f$ is obtained by replacing each variable
  $\xi_i$ by $X_i\in\mathbb{IR}$ and each operation and standard function by
  its interval version. Call $F(X_1,\dots,X_n)$ **defined** when no
  denominator interval contains $0$ and every argument interval of a
  standard function lies in its domain. If $F(X)$ is defined, then $f$ is
  defined at every $x\in X$ and
  $$\{f(x):x\in X\}\subseteq F(X).$$
  Moreover $F$ is inclusion isotone: if $X'\subseteq X$ and $F(X)$ is
  defined, then $F(X')$ is defined and $F(X')\subseteq F(X)$. If each
  variable occurs at most once in the expression, then equality holds:
  $F(X)=\{f(x):x\in X\}$. The enclosure depends on the expression and not
  only on the function. With the square as a standard function, on
  $X=[1,4]$ the expressions $x^2-4x$, $x(x-4)$ and $(x-2)^2-4$ give
  $[-15,12]$, $[-12,0]$ and the exact range $[-4,0]$.

  *Assessment.* Mathlib's `inclusion` tactic proves the inclusion property of single operations on
  its own interval type and dyadic enclosures of the exponential. The theorem for arbitrary
  expressions with continuous standard functions, the isotonicity of the natural extension, and
  the exactness for expressions without repeated variables are not in a library.

  *Lean target.* Carriers: `NonemptyInterval ℝ`, `Set.image2`, `Set.image`, `ContinuousOn`, and
  `IsCompact.image_of_continuousOn` with `IsPreconnected.image` for the interval property of images.
  New definitions: an inductive type of expressions over a variable type `ι` (variables, real
  constants, the four operations, and a unary node carrying a function `ℝ → ℝ` and its domain
  `Set ℝ`); scalar evaluation `(ι → ℝ) → ℝ`; the natural extension on a box `ι → NonemptyInterval ℝ`
  as a `Set ℝ`, built from images of the operations and functions; an admissibility predicate (no
  divisor enclosure contains $0$, every unary argument enclosure lies in the domain, every unary
  function is continuous on its domain); and the list of variable occurrences. Conjuncts: (i) the
  image of the box under evaluation lies in the extension; (ii) admissibility and the extension are
  monotone under shrinking the box; (iii) if the occurrence list has no duplicates, the extension
  equals the image; (iv) under admissibility each intermediate extension is a nonempty compact
  interval, equal to the interval computed by the endpoint rules of 7.1. Pitfalls: evaluation is a
  total function, so "$f$ is defined at $x$" is encoded by admissibility and `x / 0 = 0` must not
  leak into (i)–(iii); the unary domain is part of the syntax. Conjuncts (i)–(iii) are statable and
  provable at the pins; (iv) depends on 7.1. NASC: `NASC.IntervalExpr.range_subset_enclosure`
  (`NASC/VerifiedComputation.lean`) states (i)–(iii) for the set-valued extension and is proved,
  with the separate proved lemmas `NASC.IntervalExpr.image_eval_subset_enclosure` and
  `NASC.IntervalExpr.enclosure_eq_image_eval_of_nodup`; the expressions have one binary constructor
  `bin` over `IntervalExpr.BinOp`. (iv) is not stated.

### Rounding and overestimation

* **7.5. Outward rounding.** Let $\mathbb F$ be a set of floating-point
  numbers with radix $\beta$ and precision $p$, and let
  $u=\tfrac12\beta^{1-p}$. For real $z$ in the range of $\mathbb F$ let
  $\mathrm{RD}(z)=\max\{f\in\mathbb F:f\le z\}$ and
  $\mathrm{RU}(z)=\min\{f\in\mathbb F:f\ge z\}$. Then
  $\mathrm{RD}(z)\le z\le\mathrm{RU}(z)$, with $\mathrm{RD}(z)=\mathrm{RU}(z)$
  if and only if $z\in\mathbb F$. Let $\mathbb{IF}\subset\mathbb{IR}$ be the
  intervals with endpoints in $\mathbb F$, let
  $\Diamond[a,b]=[\mathrm{RD}(a),\mathrm{RU}(b)]$, and for $X,Y\in\mathbb{IF}$
  define the **rounded interval operation** $X\circledcirc Y=\Diamond(X\circ Y)$.
  - If the endpoints of $X\circ Y$ lie in the range of $\mathbb F$, then
    $X\circledcirc Y$ is the smallest element of $\mathbb{IF}$ containing
    $X\circ Y$.
  - Consequently, if every interval operation in the natural extension of
    7.3 is replaced by its rounded version and every standard function
    $\varphi$ by an interval function returning an element of $\mathbb{IF}$
    that contains $\varphi(Z)$, then the result $F_\Diamond(X)$ satisfies
    $\{f(x):x\in X\}\subseteq F(X)\subseteq F_\Diamond(X)$ for all
    $X\in\mathbb{IF}^n$ for which the evaluation is defined.
  - If $z$ lies in the normal range of $\mathbb F$, then
    $\mathrm{RU}(z)-\mathrm{RD}(z)\le 2u|z|$. If $X,Y\in\mathbb{IF}$ are
    contained in $[0,\infty)$ and no underflow or overflow occurs, then
    $$w\bigl(\Diamond(X+Y)\bigr)\le w(X+Y)+4u\mathop{\mathrm{mid}}(X+Y).$$

  *Assessment.* Mathlib's dyadic interval arithmetic proves that outward rounding to a given
  precision keeps a real number in the interval. No library has a floating-point format with
  directed roundings, the best-possible property of the rounded operation, the floating inclusion
  principle for natural extensions, or the width bounds.

  *Lean target.* Carriers: no Mathlib or TauCeti floating-point carrier with real semantics exists
  at the pins (Lean's `Float` has none). The model is the NASC format `NASC.FloatingPointFormat`
  (`NASC/FloatingPoint/Basic.lean`) with its value set `numbers`, extended values `extendedNumbers`,
  `maxFinite`, `normalRange`, and the predicate `IsRounding` for the modes `.down` and `.up`,
  which specifies $\mathrm{RD},\mathrm{RU}:\mathbb R\to$ `EReal` as greatest lower and least upper
  extended floating-point numbers, so overflow gives $\pm\infty$. New definitions: the unit
  roundoff $u=\beta^{1-p}/2$ as a real number, the outward rounding of a `NonemptyInterval ℝ`, and
  a rounded evaluation of the expressions of 7.3 in which each operation is followed by outward
  rounding and each standard function by a supplied enclosing interval function. Conjuncts: (i)
  $\mathrm{RD}(z)\le z\le\mathrm{RU}(z)$, with equality of the two exactly when $z$ is in
  `numbers`, for $|z|\le$ `maxFinite`; (ii) the outward rounding of $X\circ Y$ is the least
  interval with endpoints in `numbers` containing $X\circ Y$, when the endpoints of $X\circ Y$ are
  within $\pm$`maxFinite`; (iii) the rounded evaluation contains the natural extension; (iv)
  $\mathrm{RU}(z)-\mathrm{RD}(z)\le2u|z|$ on `normalRange`; (v) the width bound for the sum of two
  nonnegative intervals when both endpoint sums lie in `normalRange`. Pitfalls: the roundings are
  `EReal`-valued and `EReal.toReal` sends $\pm\infty$ to $0$, so every conjunct needs the range
  hypotheses before converting to `ℝ`; $u$ needs the radix cast to `ℝ`. Statable at the pins;
  (iii) depends on 7.3, and the format API on the floating-point model of section 1. NASC:
  `NASC.FloatingPointFormat.exists_least_outwardInterval` (`NASC/VerifiedComputation.lean`) states
  (ii) for a single interval, `sorry`; the other conjuncts are not stated.

* **7.7. Order of overestimation.** Let $X^0\in\mathbb{IR}^n$, and let $F$
  be the natural interval extension of an expression $f$ with $F(X^0)$
  defined. Suppose each standard function occurring in it is Lipschitz
  continuous on the argument interval that arises in the evaluation of
  $F(X^0)$.
  - **Linear overestimation.** There is a constant $L$, depending on the
    expression and on $X^0$, with
    $w(F(X))\le L\,\|w(X)\|_\infty$ for all boxes $X\subseteq X^0$. Hence
    the excess width $w(F(X))-w(\{f(x):x\in X\})$ is at most
    $L\|w(X)\|_\infty$. The order is sharp. For the expression $x-x$ on
    $X=[-r,r]$ the range is $\{0\}$ and $F(X)=[-2r,2r]$.
  - **Quadratic convergence of the mean-value form.** Let $f$ be
    continuously differentiable on an open set containing $X^0$. Let
    $F'_1,\dots,F'_n$ be interval functions on the boxes $X\subseteq X^0$
    with $\partial_if(x)\in F'_i(X)$ for all $x\in X$, and with
    $w(F'_i(X))\le L'\|w(X)\|_\infty$. For $X\subseteq X^0$ with midpoint
    $m$, the **mean-value form** is
    $$F_{\mathrm{MV}}(X)=f(m)+\sum_{i=1}^nF'_i(X)\,(X_i-m_i).$$
    Then $\{f(x):x\in X\}\subseteq F_{\mathrm{MV}}(X)$ and
    $$w(F_{\mathrm{MV}}(X))-w(\{f(x):x\in X\})\le C\,\|w(X)\|_\infty^2
    \qquad(X\subseteq X^0),$$
    with $C=2nL'$.

  *Assessment.* The exact interval API, Lipschitz maps and the mean value theorem are ingredients.
  The quantitative result distinguishes the width of the computed interval from the width of the
  true range, both for the natural extension and for the mean-value form.

  *Lean target.* Carriers: the expressions and natural extension of 7.3, `LipschitzOnWith`,
  `fderiv`, `ContDiffOn`, `exists_hasDerivAt_eq_slope` or
  `Convex.norm_image_sub_le_of_norm_fderiv_le`, and the sup norm of `Fin n → ℝ`, which is
  $\|\cdot\|_\infty$. New definitions: width of a `NonemptyInterval ℝ` (Mathlib's
  `NonemptyInterval.length`) and of a box as a vector; a Lipschitz predicate on the unary nodes
  along the enclosures of a reference box. Conjuncts: (i) there is $L$ with the width of the
  extension on every sub-box at most $L$ times the largest input width; (ii) the mean-value form
  contains the range; (iii) its excess width is at most $2nL'\|w(X)\|_\infty^2$. Hypotheses:
  admissibility on the reference box $X^0$, Lipschitz bounds on the argument enclosures, for
  (ii)–(iii) $f$ of class $C^1$ on an open set containing $X^0$ and derivative enclosures with
  $w(F_i'(X))\le L'\|w(X)\|_\infty$. Pitfall: if widths are written as `sSup s - sInf s`, the set
  must be known to be nonempty and bounded, or the value is junk; using `NonemptyInterval` results
  or compactness of the extension avoids this. Statable and provable at the pins; (i) depends on
  7.3. NASC: `NASC.IntervalExpr.exists_enclosure_width_le` states (i) and
  `NASC.meanValueEnclosure_excessWidth_le` states (ii) and (iii) with $f$ of class $C^1$ at every
  point of the box (`ContDiffAt`), over any finite index type, both in
  `NASC/VerifiedComputation.lean`, both `sorry`.

### Nonlinear systems

* **7.8. Univariate interval Newton operator.** Let $X=[a,b]\in\mathbb{IR}$,
  let $f:X\to\mathbb R$ be continuous on $X$ and differentiable at every
  point of $(a,b)$, let $\tilde x\in X$, and let $D\in\mathbb{IR}$ satisfy
  $f'(x)\in D$ for all $x\in(a,b)$ and $0\notin D$. Put
  $N(\tilde x,X)=\tilde x-f(\tilde x)/D$, computed by interval operations.
  - Every zero of $f$ in $X$ lies in $N(\tilde x,X)$.
  - If $N(\tilde x,X)\subseteq X$, then $f$ has exactly one zero in $X$.
  - If $N(\tilde x,X)\cap X=\emptyset$, then $f$ has no zero in $X$.

  *Assessment.* Mathlib has the scalar mean value and intermediate value theorems. The interval
  Newton assertion uses a derivative enclosure to retain every zero and, under the inclusion
  $N\subseteq X$, to certify existence and uniqueness.

  *Lean target.* Carriers: `NonemptyInterval ℝ`, `HasDerivAt`, `exists_hasDerivAt_eq_slope`,
  `intermediate_value_Icc` and `intermediate_value_Icc'`. No new definition: $N(\tilde x,X)$ is
  the image of $D$ under $d\mapsto\tilde x-f(\tilde x)/d$, which equals the interval quotient by
  7.1. Conjuncts: (i) zeros in $X$ lie in $N$; (ii) $N\subseteq X$ gives a unique zero in $X$;
  (iii) $N\cap X=\emptyset$ gives no zero. Hypotheses: $f$ continuous on $X$,
  `HasDerivAt f (f' x) x` with $f'(x)\in D$ for $x$ in the open interval, $\tilde x\in X$,
  $0\notin D$. Pitfall: $0\notin D$ is what excludes the junk value `f x̃ / 0 = 0`. Statable and
  provable at the pins; no dependency. NASC: `NASC.zeros_subset_intervalNewton_and_existsUnique`
  (`NASC/VerifiedComputation.lean`) proves (i) and (ii) under the hypothesis that $f$ has at every
  point of $X$ a derivative within $X$ lying in $D$ (continuity on $X$ follows; at the endpoints
  this is slightly stronger than the entry); (iii) is not stated and follows from (i).

* **7.9. Interval mean value theorem and interval Newton operator.** Let
  $U\subseteq\mathbb R^n$ be open, $f:U\to\mathbb R^n$ continuously
  differentiable, and $X\in\mathbb{IR}^n$ with $X\subseteq U$. Let
  $J\in\mathbb{IR}^{n\times n}$ contain the Jacobian $f'(x)$ for every
  $x\in X$.
  - For all $x,\tilde x\in X$ there is a matrix $M\in J$ with
    $f(x)=f(\tilde x)+M(x-\tilde x)$. Hence
    $f(x)\in f(\tilde x)+J(x-\tilde x)$.
  - Suppose every matrix in $J$ is nonsingular, let $\tilde x\in X$, and
    let $N(\tilde x,X)=\{\tilde x-M^{-1}f(\tilde x):M\in J\}$. Every zero of
    $f$ in $X$ lies in $N(\tilde x,X)$. If $N(\tilde x,X)\subseteq X$,
    then $f$ has exactly one zero in $X$. If $N(\tilde x,X)\cap X=\emptyset$,
    then $f$ has no zero in $X$.

  *Assessment.* The vector mean-value integral can be built from Mathlib's calculus, and TauCeti's
  Brouwer fixed-point theorem for compact convex sets gives the existence step. The enclosure of
  the averaged Jacobian in an interval matrix and the localization of zeros by the interval Newton
  operator are the targets.

  *Lean target.* Carriers: `Matrix (Fin n) (Fin n) ℝ`, `Matrix.mulVec`, `Matrix.det`, `fderiv`,
  `ContDiffOn`, `intervalIntegral` with `intervalIntegral.integral_mono_on` for entrywise bounds,
  and `TauCeti.brouwerFixedPoint_compactConvex`. New definitions: the box of a family
  `Fin n → NonemptyInterval ℝ` as a set of vectors and the set of matrices of an interval matrix
  `Fin n → Fin n → NonemptyInterval ℝ`. Conjuncts: (i) for $x,\tilde x$ in the box there is $M$ in
  the interval matrix with $f(x)=f(\tilde x)+M(x-\tilde x)$; (ii) zeros in the box lie in
  $N(\tilde x,X)$; (iii) $N\subseteq X$ gives a unique zero; (iv) $N\cap X=\emptyset$ gives no
  zero. Hypotheses: $f$ of class $C^1$ on an open set containing the box, every Jacobian on the
  box in the interval matrix, every matrix of the interval matrix with nonzero determinant,
  $\tilde x$ in the box. Pitfall: `M⁻¹` is the junk value $0$ for a singular matrix, so the
  determinant hypothesis must be kept; $N$ is the image set of the interval matrix, not an
  interval hull. Statable and provable at the pins with TauCeti's Brouwer theorem; no dependency.
  NASC: `NASC.zeros_subset_intervalNewtonBox_and_existsUnique` (`NASC/VerifiedComputation.lean`)
  states (ii) and (iii), over any finite index type, with $f$ of class $C^1$ at every point of the
  box, `sorry`.

* **7.10. Krawczyk operator.** Let $U\subseteq\mathbb R^n$ be open,
  $f:U\to\mathbb R^n$ continuously differentiable, $\tilde x\in\mathbb R^n$,
  $R\in\mathbb R^{n\times n}$, and $X\in\mathbb{IR}^n$ with $0\in X$ and
  $\tilde x+X\subseteq U$. Let $J\in\mathbb{IR}^{n\times n}$ contain $f'(y)$
  for every $y\in\tilde x+X$. Define, with interval operations,
  $$K(X)=-Rf(\tilde x)+(I-RJ)X.$$
  If $K(X)\subseteq\mathop{\mathrm{int}}X$, then $R$ and every matrix in $J$
  are nonsingular. Moreover $f$ has exactly one zero $\hat x$ in
  $\tilde x+X$, and $\hat x\in\tilde x+K(X)$. Existence follows from
  Brouwer's fixed-point theorem applied to $x\mapsto x-Rf(\tilde x+x)$ on $X$.
  Nonsingularity follows from the next lemma (7.12) applied to
  $Z=-Rf(\tilde x)$ and $C=I-RJ$.

  *Assessment.* TauCeti's Brouwer fixed-point theorem supplies the existence step and its
  Perron–Frobenius results the ingredients of the spectral bound of 7.12. The Krawczyk result
  needs the Jacobian enclosure, the fixed-point enclosure in $\tilde x+K(X)$, and the
  nonsingularity and injectivity that give uniqueness.

  *Lean target.* Carriers: as in 7.9, with `TauCeti.brouwerFixedPoint_compactConvex` applied to
  the box $X$ and the map $x\mapsto x-Rf(\tilde x+x)$, and `interior` in `Fin n → ℝ`. No new
  definition beyond those of 7.9; $K(X)$ may be stated as the set of $-Rf(\tilde x)+(I-RM)y$ with
  $M$ in the interval matrix and $y$ in the box, which lies in the interval-arithmetic $K(X)$, so
  the hypothesis is weaker and the theorem stronger, and it remains true. Conjuncts: (i) $R$ and
  every matrix of the interval matrix are nonsingular; (ii) there is exactly one zero in
  $\tilde x+X$; (iii) every zero in $\tilde x+X$ lies in $\tilde x+K(X)$. Hypotheses: $0\in X$,
  $f$ of class $C^1$ on an open set containing $\tilde x+X$, Jacobians on $\tilde x+X$ in the
  interval matrix. Pitfall: the interior of a box with a degenerate side is empty, so the
  hypothesis then fails rather than holding vacuously. Statable and provable at the pins; (i)
  depends on the first bullet of 7.12, (ii) on the first bullet of 7.9. NASC:
  `NASC.existsUnique_zero_of_krawczyk_subset_interior` (`NASC/VerifiedComputation.lean`) states
  (i)–(iii) in the set form, over any finite index type, with $f$ of class $C^1$ at every point of
  $\tilde x+X$, `sorry`.

### Linear systems

* **7.11. Norm-based verification for linear systems.** Let
  $A,R\in\mathbb R^{n\times n}$ and $b,\tilde x\in\mathbb R^n$.
  - If $\rho(I-RA)<1$, then $A$ and $R$ are nonsingular.
  - If $\|I-RA\|<1$ for a matrix norm induced by a vector norm $\|\cdot\|$,
    then $A$ and $R$ are nonsingular and
    $$\|A^{-1}b-\tilde x\|\le\frac{\|R(b-A\tilde x)\|}{1-\|I-RA\|}.$$

  *Assessment.* Partly covered. Mathlib gives the nonsingularity from either hypothesis, and
  TauCeti the Neumann-series bound $\|(I-G)^{-1}\|\le(1-\|G\|)^{-1}$. The residual-to-error
  estimate is the selected conclusion.

  *Scope.* The selected certificate uses the computable residual and the induced-norm defect of
  the approximate inverse.

  *Argument.* Write $G=I-RA$. The Neumann series gives $\|(I-G)^{-1}\|\le(1-\|G\|)^{-1}$. Apply
  $(I-G)^{-1}$ to the preconditioned residual equation $(I-G)(A^{-1}b-\tilde x)=R(b-A\tilde x)$.

  *Lean target.* Carriers: for an arbitrary induced norm, continuous linear maps `E →L[ℝ] E` on a
  finite-dimensional normed space `E`, whose operator norm is the induced norm and whose unit has
  norm one when `E` is nontrivial; for matrices, the normed ring structure
  `Matrix.linftyOpNormedRing` and the scoped instances of `Matrix.Norms.L2Operator`. Mathlib's
  `isUnit_one_sub_of_norm_lt_one` and TauCeti's `NormedRing.norm_inverse_one_sub_le`. Conjuncts:
  (i) $\rho(I-RA)<1$ implies $A$ and $R$ nonsingular, with $\rho$ the spectral radius over `ℂ`
  (`spectralRadius ℂ` of the complexified matrix); (ii) $\|I-RA\|<1$ implies nonsingularity and
  the error bound. Pitfalls: with $n=0$ or `E` trivial the unit has norm $0$ and the TauCeti bound
  carries the term $\|1\|-1$; the bound must be stated with $1-\|I-RA\|>0$ from the hypothesis,
  not with a junk division. Statable and provable at the pins; no dependency. NASC:
  `NASC.norm_error_le_of_approximateInverse` (`NASC/VerifiedComputation.lean`) proves (ii) for the
  Euclidean induced norm, and `NASC.norm_sub_le_of_norm_one_sub_comp_lt_one` proves the error bound
  of (ii) for continuous linear maps `A : E →L[𝕜] F`, `R : F →L[𝕜] E` between normed spaces (any
  induced norm, no completeness or invertibility); (i) and the nonsingularity part of (ii) for
  other induced norms are not stated.

* **7.12. Verification by interior inclusion.**
  - Let $Z,X\in\mathbb{IR}^n$ and $C\in\mathbb{IR}^{n\times n}$ with
    $Z+CX\subseteq\mathop{\mathrm{int}}X$. Then $\rho(C_0)<1$ for every
    matrix $C_0\in C$.
  - Let $A\in\mathbb{IR}^{n\times n}$, $b\in\mathbb{IR}^n$,
    $R\in\mathbb R^{n\times n}$, $\tilde x\in\mathbb R^n$ and
    $X\in\mathbb{IR}^n$, and define with interval operations
    $$Y=R(b-A\tilde x)+(I-RA)X.$$
    If $Y\subseteq\mathop{\mathrm{int}}X$, then $R$ and every matrix
    $A_0\in A$ are nonsingular. For all $A_0\in A$ and $b_0\in b$, the
    solution of $A_0x=b_0$ lies in $\tilde x+Y$. Hence the solution set
    $\{x:A_0x=b_0\text{ for some }A_0\in A,\ b_0\in b\}$ is contained in
    $\tilde x+Y$. For point data and $\tilde x=0$ this reads: if
    $Rb+(I-RA)X\subseteq\mathop{\mathrm{int}}X$, then $A$ and $R$ are
    nonsingular and $A^{-1}b\in Rb+(I-RA)X$.

  *Assessment.* The gap couples interval interior inclusion with a strict spectral bound and a
  simultaneous enclosure of all the permitted linear systems. TauCeti's Perron–Frobenius results
  give the comparison $|\mu|\,|z|\le|C|\,|z|$ used in the proof.

  *Lean target.* Carriers: the box and interval-matrix sets of 7.9, `interior`, `spectralRadius ℂ`
  of the complexified real matrix, TauCeti's `Matrix.norm_smul_le_mulVec_norm`, and Mathlib's
  `Matrix.det`. New definition: the interval product of an interval matrix and an interval vector
  by interval operations, or its midpoint–radius form for a point matrix (7.4). Conjuncts: (i)
  $Z+CX\subseteq\mathop{\mathrm{int}}X$ gives $\rho(C_0)<1$ for all $C_0\in C$; (ii)
  $Y\subseteq\mathop{\mathrm{int}}X$ gives $R$ and every $A_0\in A$ nonsingular; (iii) for
  $A_0\in A$, $b_0\in b$, $A_0^{-1}b_0\in\tilde x+Y$; (iv) the point-data corollary. Pitfall: the
  spectral radius over `ℝ` ignores nonreal eigenvalues, so the complex one must be used; it is
  `ℝ≥0∞`-valued. Statable at the pins; provable with the TauCeti comparison lemma and Mathlib's
  Neumann series. Dependency: 7.4 for the interval product (not selected). NASC:
  `NASC.realMatrixSpectralRadius_lt_one_of_image_subset_interior`
  (`NASC/VerifiedComputation.lean`) states (i) for a point matrix with the image of the affine map
  in place of the interval product, a weaker hypothesis that still implies the conclusion,
  `sorry`; (ii)–(iv) are not stated.

### Computer-assisted proofs for elliptic problems

* **7.13. Plum's existence and enclosure theorem.** Let $\mathcal X$,
  $\mathcal Y$ be real Hilbert spaces and $\mathcal F:\mathcal X\to\mathcal Y$
  Fréchet differentiable. Let $\omega\in\mathcal X$ and
  $L=\mathcal F'(\omega)$. Suppose there are constants $\delta,K$ and a
  nondecreasing $g:[0,\infty)\to[0,\infty)$ with $g(t)\to0$ as $t\to0$,
  such that
  $$\|\mathcal F(\omega)\|_{\mathcal Y}\le\delta,\qquad
  \|v\|_{\mathcal X}\le K\|L v\|_{\mathcal Y},\qquad
  \|\mathcal F'(\omega+v)-\mathcal F'(\omega)\|_{\mathcal B(\mathcal X,
  \mathcal Y)}\le g(\|v\|_{\mathcal X})$$
  for all $v\in\mathcal X$. Let $G(t)=\int_0^tg(s)\,ds$ and suppose some
  $\alpha>0$ satisfies
  $$\delta\le\frac{\alpha}{K}-G(\alpha).$$
  Suppose further that one of the following holds:
  1. (compact case) $\mathcal F=L_0+\mathcal N$ with $L_0\in\mathcal
     B(\mathcal X,\mathcal Y)$ bijective and $\mathcal N:\mathcal X\to
     \mathcal Y$ compact (mapping bounded sets to relatively compact sets)
     and Fréchet differentiable;
  2. $L(\mathcal X)$ is dense in $\mathcal Y$, and $Kg(\alpha)<1$. Density
     holds, for example, when $\mathcal Y=\mathcal X'$ and
     $(Lu)[v]=(Lv)[u]$ for all $u,v\in\mathcal X$.

  Then $\mathcal F(u)=0$ has a solution $u$ with
  $\|u-\omega\|_{\mathcal X}\le\alpha$. If $Kg(\alpha)<1$, this solution is
  non-degenerate, that is, $\mathcal F'(u)$ is bijective. If
  $Kg(\alpha)<1$ and $\delta<\tilde\alpha/K-G(\tilde\alpha)$ for some
  $\tilde\alpha>\alpha$, then $u$ is the only solution with
  $\|u-\omega\|_{\mathcal X}\le\tilde\alpha$. In the compact case, the
  existence statement remains true when $\mathcal N$ is only compact,
  continuous, and Fréchet differentiable at $\omega$, provided the third
  bound is replaced by
  $\|\mathcal F(\omega+v)-\mathcal F(\omega)-Lv\|_{\mathcal Y}\le
  G(\|v\|_{\mathcal X})$ for all $v$, with a nondecreasing
  $G:[0,\infty)\to[0,\infty)$ satisfying $G(t)=o(t)$ as $t\to0$, and
  $\delta\le\alpha/K-G(\alpha)$ holds for this $G$.

  *Assessment.* Mathlib's Banach fixed-point theorem and Neumann series and TauCeti's Schauder
  fixed-point theorem are the analytic ingredients, and TauCeti's coercive weak elliptic
  solvability is the setting of the applications. The verified theorem relates the residual and
  inverse bounds at an approximate solution to a ball containing an exact solution.

  *Lean target.* Carriers: real Hilbert spaces as `InnerProductSpace ℝ` with `CompleteSpace` (the
  dense-range case also works in Banach spaces), `fderiv` and `HasFDerivAt`, `E →L[ℝ] F` with its
  operator norm, `DenseRange`, `Function.Bijective`, `intervalIntegral` for $G(t)=\int_0^tg$,
  `ContractingWith` with `ContractingWith.fixedPoint`, and
  `TauCeti.schauderFixedPoint_closedConvex_continuousOn`. New definition: a compact nonlinear map,
  continuous and sending bounded sets to sets with compact closure (Mathlib's `IsCompactOperator`
  is for linear maps). Conjuncts: (i) dense-range case: a zero in `Metric.closedBall ω α` at which
  the derivative is bijective; (ii) compact case: a zero in that ball, and bijectivity of the
  derivative under $Kg(\alpha)<1$; (iii) uniqueness in `Metric.closedBall ω α̃`; (iv) the weakened
  compact case with the remainder majorant $G$. Hypotheses: $K>0$, $\alpha>0$, $g$ monotone and
  nonnegative, `Tendsto g (𝓝[>] 0) (𝓝 0)`, the three bounds for all $v$. Pitfall: $G$ is a Bochner
  interval integral, which is $0$ for a non-integrable $g$; monotonicity gives integrability on
  $[0,\alpha]$ (`MonotoneOn.intervalIntegrable`), so it must be kept. Statable and provable at the
  pins; no dependency. NASC: `NASC.exists_zero_mem_closedBall_of_plum_bound`
  (`NASC/VerifiedComputation.lean`) states (i) in Banach spaces with $g(0)=0$ in place of
  $g(t)\to0$, which the dense-range proof does not need, `sorry`; (ii)–(iv) are not stated.

* **7.14. Constructive a priori error constants.** Let $\mathcal X$,
  $\mathcal Y$ be Hilbert spaces and $\mathcal D$ a Banach space with
  continuous embeddings $\mathcal D\hookrightarrow\mathcal X\hookrightarrow
  \mathcal Y$. Let $A:\mathcal D\to\mathcal Y$ be linear and bijective with
  $\langle u,v\rangle_{\mathcal X}=\langle Au,v\rangle_{\mathcal Y}$ for
  $u\in\mathcal D$, $v\in\mathcal X$. Let $\mathcal X_h\subseteq\mathcal X$
  be finite-dimensional, with $\mathcal X$-orthogonal projection $P_h$, and
  suppose
  $$\|v-P_hv\|_{\mathcal X}\le C(h)\|Av\|_{\mathcal Y}\qquad
  (v\in\mathcal D).$$
  - (Aubin–Nitsche) For all $v\in\mathcal X$,
    $\|(I-P_h)v\|_{\mathcal Y}\le C(h)\|(I-P_h)v\|_{\mathcal X}$, and for
    $v\in\mathcal D$, $\|(I-P_h)v\|_{\mathcal Y}\le C(h)^2\|Av\|_{\mathcal Y}$.
  - Take $\mathcal X=H^1_0(\Omega)$ with inner product
    $\langle\nabla u,\nabla v\rangle_{L^2}$, $\mathcal Y=L^2(\Omega)$,
    $\mathcal D=H^2(\Omega)\cap H^1_0(\Omega)$ and $A=-\Delta$. For
    $\Omega=(a,b)$ and continuous piecewise linear functions on a uniform
    mesh of width $h$, $\|(u-P_hu)'\|_{L^2}\le(h/\pi)\|u''\|_{L^2}$ for
    $u\in H^2\cap H^1_0$, so $C(h)=h/\pi$. For continuous piecewise
    quadratics, $C(h)=h/(2\pi)$ is the best constant.
  - For $\Omega=(0,1)^2$ and continuous piecewise bilinear functions on the
    uniform square mesh of width $h=1/N$, $C(h)=h/\pi$. The proof uses
    $|u|_{H^2(\Omega)}=\|\Delta u\|_{L^2(\Omega)}$ for
    $u\in H^2(\Omega)\cap H^1_0(\Omega)$ on a convex polygon.
  - Let $\Gamma$ be the triangle with vertices $(0,0),(1,0),(0,1)$, and let
    $C_0$ be the least constant with
    $\|\nabla(u-Iu)\|_{L^2(\Gamma)}\le C_0|u|_{H^2(\Gamma)}$ for
    $u\in H^2(\Gamma)$, where $Iu$ is the linear interpolant at the
    vertices. Then $0.49282<C_0<0.49293$. Hence $C(h)=0.493\,h$ for
    continuous piecewise linear functions on a convex polygon meshed by
    right isosceles triangles with legs of length $h$.

  *Assessment.* No library has the abstract constructive error bound or the explicit constant for
  a finite element projection. TauCeti's Sobolev spaces and weak Dirichlet problems give the
  continuous setting, and the projection onto a finite-dimensional subspace is Mathlib's
  orthogonal projection.

  *Scope.* The selected claims are the abstract Aubin–Nitsche bounds of the first bullet and the
  one-dimensional constant $C(h)=h/\pi$ for continuous piecewise linear functions. The quadratic
  and two-dimensional constants rest on cited literature, on Grisvard's identity for convex
  polygons and on computer-assisted bounds.

  *Argument.* The abstract bounds are the duality argument of 18.14 with $\mathcal X$ in place of
  $H^1_0$: for $v\in\mathcal X$ solve $Aw=(I-P_h)v$, use
  $\langle Aw,e\rangle_{\mathcal Y}= \langle w-P_hw,e\rangle_{\mathcal X}$ for $e=(I-P_h)v$, and
  apply the hypothesis to $w$. For the one-dimensional constant, $P_hu$ interpolates $u$ at the
  nodes; on each element $\|e\|_{L^2}\le(h/\pi)\|e'\|_{L^2}$ for $e$ vanishing at both ends, and
  $\|e'\|^2=-(e,u'')\le\|e\|\,\|u''\|$.

  *Lean target.* Carriers: `InnerProductSpace ℝ` with `CompleteSpace`, a finite-dimensional
  `Submodule` with `Submodule.starProjection` (Mathlib's orthogonal projection as an operator),
  continuous linear maps for the embeddings, and for the one-dimensional part `intervalIntegral`,
  `deriv` and `ContDiffOn`. New definitions: the uniform partition of $[a,b]$ into $N$ cells and
  the continuous piecewise linear interpolant at its nodes. Conjuncts: (i) and (ii) the two
  abstract inequalities with the embeddings and $A$ explicit (an injective `X →L[ℝ] Y`, and $A$ a
  linear bijection from `D` onto `Y` with
  $\langle u,v\rangle_{\mathcal X}=\langle Au,v\rangle_{\mathcal Y}$); (iii) for $u\in C^2[a,b]$
  with $u(a)=u(b)=0$ and $h=(b-a)/N$, $\|(u-I_hu)'\|_{L^2}\le(h/\pi)\|u''\|_{L^2}$; (iv) the
  interpolant is the $H^1_0$-projection, which upgrades (iii) to the form with $P_h$. Pitfall:
  (iii) is stated with $C^2$ functions because $H^2(a,b)$ is not available at the pins; the full
  form needs second weak derivatives on an interval. The scalar inequality of the Argument
  (Wirtinger's inequality with the constant $\pi$) is in neither library. Statable at the pins;
  (i)–(ii) are provable with Mathlib's projection API and follow from 18.14. NASC: none for this
  entry; `NASC.norm_weak_galerkinError_le_of_dualApproximation` (`NASC/Galerkin.lean`, 18.14,
  proved) gives (i) after instantiation.

## 8. Nonlinear equations, continuation, and algorithmic differentiation

[Synopsis](SYNOPSIS.md#8-nonlinear-equations-continuation-and-algorithmic-differentiation) · [Coverage inventory](STRUCTURE.md#8-nonlinear-equations-continuation-and-algorithmic-differentiation)

Fixed-point theory, differentiation, and the implicit function theorem supply
the continuous ingredients. The selected gaps encode the numerical
recurrences, their convergence, and differentiation of evaluated programs.

Unless stated
otherwise, $F:D\subset\mathbb R^n\to\mathbb R^n$, $F'(x)$ is its Jacobian
matrix, $\|\cdot\|$ is a vector norm on $\mathbb R^n$ together with the
induced matrix norm, and $B(x,r)=\{y:\|y-x\|<r\}$ and $\bar B(x,r)$ are the
open and closed balls. The **Newton iteration** is
$$x^{k+1}=x^k-F'(x^k)^{-1}F(x^k),\qquad k=0,1,2,\dots,$$
and $\Delta x^k=x^{k+1}-x^k$ is the **Newton correction**. A zero $x^*$ of
$F$ is **nondegenerate** if $F'(x^*)$ is invertible. A sequence $x^k\to x^*$
converges **Q-linearly** if $\|x^{k+1}-x^*\|\le c\|x^k-x^*\|$ for some $c<1$
and all large $k$, **Q-superlinearly** if
$\|x^{k+1}-x^*\|/\|x^k-x^*\|\to0$, and **Q-quadratically** if
$\|x^{k+1}-x^*\|\le C\|x^k-x^*\|^2$ for all large $k$; the ratios are only
required where $x^k\ne x^*$. Results on unconstrained minimization,
including the Dennis–Moré characterization of superlinear convergence, are
in section 9.

### Fixed-point iteration and scalar equations

* **8.3. Bisection.** Let $f\in C[a,b]$ with $a<b$, $f(a)<0$ and $f(b)>0$.
  Put $a_1=a$, $b_1=b$, and for $n\ge1$ let $x_n=\frac12(a_n+b_n)$; if
  $f(x_n)<0$, put $a_{n+1}=x_n$, $b_{n+1}=b_n$, and otherwise
  $a_{n+1}=a_n$, $b_{n+1}=x_n$. Then $f(a_n)<0\le f(b_n)$ and
  $b_n-a_n=2^{-(n-1)}(b-a)$ for all $n$. The sequences $(a_n)$ and $(b_n)$
  converge to a common limit $\alpha\in[a,b]$ with $f(\alpha)=0$, and
  $$|x_n-\alpha|\le\frac{b-a}{2^n},\qquad n\ge1.$$

  *Assessment.* The intermediate value theorem gives a root in a sign-changing
  interval, and nested compact sets have a common point. The midpoint
  recursion and its invariant identify a nested enclosure with a geometric
  length bound.

  *Lean target.* Carriers: `ContinuousOn f (Set.Icc a b)`, `Function.iterate` on
  pairs `ℝ × ℝ`, `intermediate_value_Icc` and
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`. New
  definition: one bisection step `bisect f : ℝ × ℝ → ℝ × ℝ`, keeping the right
  half when the midpoint value is negative. Hypotheses: `a < b`, `f a < 0`,
  `0 < f b`. Conjuncts, with Lean's iterate index `k = n − 1`: (i) the
  invariant `f aₖ < 0 ≤ f bₖ`; (ii) `bₖ − aₖ = (b − a)/2^k`; (iii) a zero `α`
  of `f` in `[a, b]` lying in every interval; (iv) `|xₖ − α| ≤ (b − a)/2^(k+1)`
  for the midpoint `xₖ`; (v) `aₖ → α` and `bₖ → α`. The convention
  `f(xₙ) = 0 ⇒` right endpoint must match the source (Gautschi), otherwise the
  invariant reads `f aₖ ≤ 0`. All statable and provable at the pins; no
  dependency. NASC: `NASC.exists_bisection_root` (`NASC/NonlinearEquations.lean`),
  proved; it states (i)–(iv) and not the convergence (v) of the endpoints, which
  follows from (ii)–(iii).

* **8.4. Secant method.** Let $\alpha$ be a zero of $f$, let
  $I_\varepsilon=[\alpha-\varepsilon,\alpha+\varepsilon]$, let
  $f\in C^2(I_\varepsilon)$ with $f'(t)\ne0$ for $t\in I_\varepsilon$, put
  $$M=\max_{s,t\in I_\varepsilon}\left|\frac{f''(s)}{2f'(t)}\right|,$$
  and assume $\varepsilon M<1$. Let $x_0\ne x_1$ lie in $I_\varepsilon$ and
  define
  $$x_{n+1}=x_n-f(x_n)\frac{x_n-x_{n-1}}{f(x_n)-f(x_{n-1})},$$
  stopping if $f(x_n)=0$. Then $\alpha$ is the only zero of $f$ in
  $I_\varepsilon$, all iterates lie in $I_\varepsilon$, consecutive iterates
  are distinct until the iteration stops at $x_n=\alpha$, and
  $x_n\to\alpha$. With $p=\frac12(1+\sqrt5)$, the positive root of
  $p^2=p+1$, and
  $$E=\max\bigl(M|x_0-\alpha|,\,(M|x_1-\alpha|)^{1/p}\bigr)<1,$$
  every iterate satisfies $M|x_n-\alpha|\le E^{p^n}$. Thus the secant
  method converges with order at least $p\approx1.618$.

  *Assessment.* Scalar mean value and Taylor theorems supply the error
  identity through divided differences. The changing pair of points, the
  Fibonacci-type recursion for the scaled errors and the golden-ratio bound
  require a secant-specific argument.

  *Lean target.* Carriers: `ContDiffOn ℝ 2 f (Set.Icc (α - ε) (α + ε))`,
  `deriv`, `iteratedDerivWithin 2`, `Real.rpow`. New definition: the secant
  step on pairs, `secantStep f : ℝ × ℝ → ℝ × ℝ`, frozen once `f xₙ = 0`.
  Hypotheses: `f α = 0`, `0 < ε`, `deriv f t ≠ 0` on the interval, a bound
  `M ≥ 0` for `|f''(s)/(2f'(t))|` over pairs in the interval, `ε * M < 1`,
  `x₀ ≠ x₁` in the interval. Conjuncts: (i) `α` is the only zero in the
  interval; (ii) all iterates lie in the interval, and consecutive iterates
  differ unless the iteration has stopped at `α`; (iii) `xₙ → α`; (iv)
  `M * |xₙ − α| ≤ E ^ (p ^ n)` with `p = (1 + √5)/2` and
  `E = max (M|x₀ − α|) ((M|x₁ − α|) ^ (1/p))`, real powers. Pitfall: the
  quotient `(xₙ − xₙ₋₁)/(f xₙ − f xₙ₋₁)` is `0` in Lean when the denominator
  vanishes, so (ii) must be proved, not assumed through the definition; with
  `M = 0` (affine `f`) the bound (iv) reads `0 ≤ 0`. All statable at the pins; no
  dependency. NASC: `NASC.secant_error_le_rpow` (`NASC/NonlinearEquations.lean`)
  states (ii) membership, (iii) and (iv) with `f` of class $C^2$ at every point of the interval
  (`ContDiffAt`), and is `sorry`; (i) and the distinctness are not stated.

### Newton's method

* **8.5. Local convergence of Newton's method.** Let $D\subset\mathbb R^n$
  be open and convex and $F\in C^1(D;\mathbb R^n)$.
  - Let $x^*\in D$ be a zero with $\|F'(x^*)^{-1}\|\le C$, and let
    $\|F'(x)-F'(y)\|\le L\|x-y\|$ for all $x,y\in B(x^*,R)\subset D$, where
    $C,L,R>0$. Put $r=\min(R,1/(2CL))$. Then for every $x^0\in B(x^*,r)$
    the Newton iterates are well defined, remain in $B(x^*,r)$, and
    $$\|x^{k+1}-x^*\|\le CL\|x^k-x^*\|^2,\qquad k\ge0.$$
  - If $x^*\in D$ is a nondegenerate zero and no Lipschitz condition is
    assumed, then $\|x^{k+1}-x^*\|=o(\|x^k-x^*\|)$ for $x^k$ sufficiently
    close to $x^*$.
  - (Affine-covariant form) Let $F'(x)$ be invertible for every $x\in D$, and
    let $\omega>0$ satisfy
    $$\|F'(x)^{-1}(F'(x+sv)-F'(x))v\|\le s\omega\|v\|^2$$
    for all $s\in[0,1]$, $x\in D$ and $v$ with $x+v\in D$. Let $x^*\in D$ be
    a zero, and let $x^0\in D$ satisfy $\rho:=\|x^0-x^*\|<2/\omega$ and
    $B(x^*,\rho)\subset D$. Then the Newton iterates satisfy
    $\|x^k-x^*\|\le\rho$ for all $k$, with strict inequality for $k\ge1$ if
    $x^0\ne x^*$, converge to $x^*$, and
    $$\|x^{k+1}-x^*\|\le\frac\omega2\|x^k-x^*\|^2,\qquad k\ge0.$$
    Moreover $x^*$ is the only zero of $F$ in $D\cap B(x^*,2/\omega)$.

  *Assessment.* The Banach perturbation lemma for continuous linear maps, the
  Neumann-series bound and the integral form of the mean value theorem are
  available. The local theorem must keep every Newton iterate in the
  neighbourhood, control the inverse derivative there and prove quadratic
  convergence, and the affine-covariant form must replace the norm of the
  inverse by the Lipschitz constant of the scaled derivative.

  *Lean target.* Carriers: real Banach spaces `E`, `F`; `fderiv ℝ f`,
  `HasFDerivAt`, `ContinuousLinearMap.inverse`, `E ≃L[ℝ] F` for the derivative
  at the zero, `Metric.ball`, `Function.iterate`; Tau Ceti's
  `ContinuousLinearMap.IsInvertible.norm_inverse_le_of_mul_norm_sub_lt`. New
  definition: the Newton map `x − (fderiv ℝ f x).inverse (f x)` (the
  `newtonMap` of the NewtonAndQuasiNewtonMethods roadmap, §1.1). Three
  theorems: (a) with `0 < C, L, R`, `‖A⁻¹‖ ≤ C` for `A = f'(x*)`, `f x* = 0`
  and `fderiv` `L`-Lipschitz on `ball x* R`, every start in
  `ball x* (min R (1/(2CL)))` gives iterates in that ball with
  `‖x_{k+1} − x*‖ ≤ C L ‖x_k − x*‖²`; (b) with `f` `C¹` near a nondegenerate
  zero, `(fun x ↦ newtonMap f x − x*) =o[𝓝 x*] (fun x ↦ x − x*)`; (c) the
  affine-covariant form with `ω > 0`, `ρ < 2/ω`, `ball x* ρ ⊆ D`, the bound
  `(ω/2)‖x_k − x*‖²`, convergence, and uniqueness of the zero in
  `D ∩ ball x* (2/ω)`. Pitfall: `ContinuousLinearMap.inverse` is `0` at a
  non-invertible derivative, so invertibility along the iterates is a
  conjunct, not a hypothesis. All statable and provable at the pins; (a) and
  its uniqueness radius are owned by NewtonAndQuasiNewtonMethods §§1.3–1.4.
  NASC: `NASC.newtonStep_iterate_quadratic` (`NASC/NonlinearEquations.lean`)
  states (a) with bijectivity of the derivative along the iterates and
  convergence, `sorry`; it defines the step with `Function.invFun`, which
  agrees with the inverse only where the derivative is bijective. (b) and (c)
  are not stated.

* **8.6. Newton–Kantorovich theorem.** Let $X$ and $Y$ be Banach spaces,
  $\Omega\subset X$ open, $f\in C^1(\Omega;Y)$, and $x_0\in\Omega$ with
  $f'(x_0)$ a bijection of $X$ onto $Y$. Let $\lambda,\mu,\nu$ be constants
  with
  $$0<\lambda\mu\nu\le\tfrac12,\qquad
  \|f'(x_0)^{-1}f(x_0)\|\le\lambda,\qquad \|f'(x_0)^{-1}\|\le\mu,$$
  put $r=1/(\mu\nu)$, and assume $B(x_0,r)\subset\Omega$ and
  $\|f'(\tilde x)-f'(x)\|\le\nu\|\tilde x-x\|$ for all
  $x,\tilde x\in B(x_0,r)$. Put
  $$r_\pm=\frac{1\pm\sqrt{1-2\lambda\mu\nu}}{\mu\nu}.$$
  Assume $\bar B(x_0,r_-)\subset\Omega$ so that the limit point is in the
  domain, including when $r_-=r$. Then $f'(x)$ is invertible for every
  $x\in B(x_0,r)$, the Newton
  iterates $x_{k+1}=x_k-f'(x_k)^{-1}f(x_k)$ lie in $B(x_0,r_-)$ and
  converge to a zero $a\in\bar B(x_0,r_-)$ of $f$, and for $k\ge0$
  $$\|x_k-a\|\le\frac{r}{2^k}\Bigl(\frac{r_-}{r}\Bigr)^{2^k}
  \ \text{ if }\lambda\mu\nu<\tfrac12,\qquad
  \|x_k-a\|\le\frac{r}{2^k}\ \text{ if }\lambda\mu\nu=\tfrac12.$$
  If $\lambda\mu\nu<\frac12$, $B(x_0,r_+)\subset\Omega$, and the Lipschitz
  condition holds on $B(x_0,r_+)$, then $a$ is the only zero of $f$ in
  $B(x_0,r_+)$. If $\lambda\mu\nu=\frac12$, then $a$ is the only zero of
  $f$ in $\bar B(x_0,r)$.

  *Assessment.* The Banach fixed-point theorem, the Banach perturbation
  lemma, and Tau Ceti's simplified-Newton existence theorems with non-sharp
  radii are available. The main gap is the majorant iteration giving the
  Kantorovich radii, convergence of the Newton sequence with its error bound,
  and the uniqueness enclosure.

  *Lean target.* Carriers as in 8.5, with `A : E ≃L[ℝ] F`,
  `HasFDerivAt f A x₀`, `Metric.closedBall`. Hypotheses: `0 < λ, μ, ν`,
  `λμν ≤ 1/2`, `‖A⁻¹ (f x₀)‖ ≤ λ`, `‖A⁻¹‖ ≤ μ`, `f` differentiable with
  `ν`-Lipschitz derivative on `ball x₀ r`, `r = 1/(μν)`, and `f` continuous on
  `closedBall x₀ r₋`. Conjuncts: (i) the derivative is invertible on
  `ball x₀ r`; (ii) the Newton iterates lie in `ball x₀ r₋`; (iii) they converge
  to a zero `a ∈ closedBall x₀ r₋`; (iv)
  `‖x_k − a‖ ≤ (r/2^k)(r₋/r)^(2^k)`, which at `λμν = 1/2` is `r/2^k`; (v) for
  `λμν < 1/2`, with differentiability and the Lipschitz bound on
  `ball x₀ r₊`, `a` is the only zero there; (vi) for `λμν = 1/2`, with
  differentiability and the Lipschitz bound on `closedBall x₀ r`, `a` is the
  only zero in `closedBall x₀ r`. The radii use `Real.sqrt (1 − 2λμν)`, whose
  argument is nonnegative under the hypotheses; dropping `λμν ≤ 1/2` would make
  the square root the junk value `0`. All statable and provable at the pins;
  depends on the Newton map of 8.5. The affine-covariant form (8.7, first part)
  with closed-ball uniqueness is owned by NewtonAndQuasiNewtonMethods §§2.1–2.2,
  from which (i)–(iii) and (v) follow with `L = μν`, `b = λ`; (iv) and (vi) are
  not stated there. NASC: `NASC.exists_newtonKantorovich_root`
  (`NASC/NonlinearEquations.lean`) states (i)–(vi), `sorry`; its critical-case
  conjunct assumes differentiability and the Lipschitz bound only on the open
  ball `ball x₀ r`, which does not control the derivative on the boundary sphere
  used by Ciarlet's uniqueness argument.

* **8.8. Global convergence of damped Newton.** Let $f:\mathbb R^n\to
  \mathbb R^n$, $h(x)=f(x)^\top f(x)$, use the Euclidean norm, and write
  $\kappa_2$ for the condition number. Given $x_0$, define for $k\ge0$
  $$d_k=f'(x_k)^{-1}f(x_k),\qquad \gamma_k=1/\kappa_2(f'(x_k)),$$
  let $j\ge0$ be the least integer with
  $$h(x_k-2^{-j}d_k)\le h(x_k)-2^{-j}\frac{\gamma_k}4\|d_k\|\,
  \|\nabla h(x_k)\|,$$
  and let $x_{k+1}=x_k-\lambda_kd_k$, where $\lambda_k\in\{2^{-i}:0\le i\le
  j\}$ minimizes $h(x_k-2^{-i}d_k)$ over that set. Assume that the level
  set $K=\{x:h(x)\le h(x_0)\}$ is compact, that $f$ is continuously
  differentiable on an open set containing $K$, and that $f'(x)$ is
  invertible for every $x\in K$. Then the sequence $(x_k)$ is well defined,
  lies in $K$, has at least one accumulation point, and every accumulation
  point $\bar x$ satisfies $f(\bar x)=0$.

  *Assessment.* The calculus inequalities, compactness of the level set and
  linear solves are available as ingredients. The proof must show that the
  backtracking rule terminates with a step bounded below uniformly on the
  level set, through the angle bound `1/κ₂`, and relate that step to descent
  and to convergence.

  *Lean target.* Carriers: `EuclideanSpace ℝ (Fin n)`, `fderiv ℝ f`,
  `ContinuousLinearMap.inverse`, `gradient`, `IsCompact`, `MapClusterPt`, and
  the condition number through `‖A‖ * ‖A⁻¹‖` in the operator norm. New
  definition: the damped Newton sequence as a function of `x₀`, with the least
  `j` given by `Nat.find` on the acceptance test and `λ_k` chosen as a
  minimizer of `h(x_k − 2^{−i} d_k)` over `i ≤ j` (any choice rule). Hypotheses:
  `IsCompact {x | h x ≤ h x₀}`, `f` `C¹` on an open set containing it, the
  derivative invertible on it. Conjuncts: (i) the acceptance set is nonempty at
  every iterate, so the sequence is well defined (the `Nat.find` proof
  obligation); (ii) every iterate lies in the level set; (iii) there is a
  cluster point; (iv) every cluster point is a zero. Pitfall: with
  `Nat.find` the existence in (i) must be proved before the sequence is
  defined, so the definition takes it as a parameter or uses a total fallback.
  All statable and provable at the pins; no dependency. NASC:
  `NASC.eq_zero_of_mapClusterPt_dampedNewton` (`NASC/NonlinearEquations.lean`),
  `sorry`, states a different rule (an Armijo test on `‖f‖²` with a parameter
  `σ` and the first acceptable step, no minimization over `i ≤ j`, no factor
  `γ_k`) and assumes the existence of the accepted step; it states (iv) only.

* **8.9. Inexact Newton methods.** Let $D\subset\mathbb R^n$ be open and
  convex, $r\in C^1(D;\mathbb R^n)$ with Jacobian $J$, and let $x^*\in D$ be
  a nondegenerate zero. Let $0\le\eta_k\le\eta<1$, and let
  $x^{k+1}=x^k+p_k$, where the step $p_k$ satisfies
  $$\|r(x^k)+J(x^k)p_k\|\le\eta_k\|r(x^k)\|.$$
  Then there are $\delta>0$ and $\bar\eta>0$, depending on $r$ and $x^*$,
  such that for $\eta\le\bar\eta$ and $x^0\in B(x^*,\delta)$ the iterates
  remain in $B(x^*,\delta)$ and converge to $x^*$ Q-linearly. If moreover
  $\eta_k\to0$, the convergence is Q-superlinear. If in addition $J$ is
  Lipschitz continuous in a neighbourhood of $x^*$ and
  $\eta_k=O(\|r(x^k)\|)$, the convergence is Q-quadratic.

  *Assessment.* The exact Newton local estimates and the Banach perturbation
  lemma support the analysis. The selected theorem adds residual forcing
  terms and distinguishes linear, superlinear and quadratic convergence by
  their decay.

  *Lean target.* Carriers: `E` a real Banach space (finite dimension is not
  needed), `fderiv`, `E ≃L[ℝ] E` for `J(x*)`, `Asymptotics.IsLittleO` and
  `Filter.Tendsto` for the rates. The steps `p_k` are an arbitrary sequence
  satisfying the forcing inequality, so no new definition is needed. Three
  theorems: (i) there are `δ, η̄ > 0` and `q < 1` with
  `‖x_{k+1} − x*‖ ≤ q‖x_k − x*‖` and the iterates in `ball x* δ` whenever
  `η_k ≤ η̄` and `x₀ ∈ ball x* δ`; (ii) adding `η_k → 0`,
  `‖x_{k+1} − x*‖/‖x_k − x*‖ → 0` along the indices with `x_k ≠ x*`; (iii) adding
  a Lipschitz derivative near `x*` and `η_k ≤ c‖r(x_k)‖`, a bound
  `‖x_{k+1} − x*‖ ≤ C‖x_k − x*‖²`. Pitfall: the quotient in (ii) is `0` where
  `x_k = x*`, so state it as `IsLittleO` along `atTop` or with the exception
  explicit. Statable and provable at the pins; depends on 8.5 (a). NASC:
  `NASC.exists_inexactNewton_linear_bound` (`NASC/NonlinearEquations.lean`)
  states (i) without the ball invariance, for `f` of class $C^1$ at the zero (`ContDiffAt`),
  `sorry`; (ii)–(iii) are not stated.

* **8.10. Local superlinear convergence of Broyden's method.** Let
  $D\subset\mathbb R^n$ be open and convex, $r\in C^1(D;\mathbb R^n)$ with
  Jacobian $J$ Lipschitz continuous near a nondegenerate zero $x^*$. Given
  $x^0$ and an invertible $B_0$, **Broyden's method** sets
  $s_k=-B_k^{-1}r(x^k)$, $x^{k+1}=x^k+s_k$, $y_k=r(x^{k+1})-r(x^k)$ and
  $$B_{k+1}=B_k+\frac{(y_k-B_ks_k)s_k^\top}{s_k^\top s_k}.$$
  Then there are $\delta,\varepsilon>0$ such that if
  $\|x^0-x^*\|\le\delta$ and $\|B_0-J(x^*)\|\le\varepsilon$, the
  iteration is well defined (every $B_k$ is invertible; if $r(x^k)=0$ the
  iteration stops with $x^k=x^*$) and converges to $x^*$ Q-superlinearly.

  *Assessment.* No library has Broyden's update or a bounded-deterioration
  argument. The Dennis–Moré characterization reduces superlinear convergence
  to the convergence of `(B_k − J(x*))s_k/‖s_k‖` to zero, which the update
  must be shown to produce.

  *Lean target.* Carriers: `Matrix (Fin n) (Fin n) ℝ` with the scoped norm
  `Matrix.Norms.L2Operator` (or `EuclideanSpace ℝ (Fin n) →L[ℝ] _`),
  `Matrix.vecMulVec`, `Matrix.mulVec`, `Matrix.inv`, `fderiv`. New
  definitions: the update `broydenUpdate B s y = B + (⟪s, s⟫)⁻¹ • vecMulVec
  (y − B *ᵥ s) s` and the Broyden sequence of pairs `(x_k, B_k)`. Hypotheses:
  `C¹` near a nondegenerate zero, Lipschitz Jacobian near it. Conjuncts: there
  are `δ, ε > 0` such that for `‖x₀ − x*‖ ≤ δ` and `‖B₀ − J(x*)‖ ≤ ε` (i) every
  `B_k` is invertible until `r(x_k) = 0`, after which the sequence is constant;
  (ii) `x_k → x*`; (iii) the convergence is Q-superlinear. Pitfall: `Matrix.inv`
  is `0` for a singular matrix and `(⟪s, s⟫)⁻¹` is `0` for `s = 0`, so (i) is a
  conclusion. Statable at the pins; depends on the Dennis–Moré
  characterization owned by NewtonAndQuasiNewtonMethods §4.1. No NASC
  declaration.

* **8.11. Local convergence of the Gauss–Newton method.** Let
  $D\subset\mathbb R^n$ be open and convex, $F\in C^1(D;\mathbb R^m)$ with
  $m\ge n$, and let $F'(x)$ have rank $n$ for every $x\in D$, with
  Moore–Penrose inverse $F'(x)^+$ (Euclidean norms). The **Gauss–Newton
  iteration** is $x^{k+1}=x^k-F'(x^k)^+F(x^k)$. Let $x^*\in D$ satisfy
  $F'(x^*)^+F(x^*)=0$, and let $\omega>0$ and $0\le\kappa_*<1$ satisfy
  $$\|F'(x)^+(F'(x+sv)-F'(x))v\|\le s\omega\|v\|^2,\qquad
  \|F'(x)^+F(x^*)\|\le\kappa_*\|x-x^*\|$$
  for all $s\in[0,1]$, $x\in D$ and $v$ with $x+v\in D$. Let $x^0\in D$
  with $\rho:=\|x^0-x^*\|<\sigma:=2(1-\kappa_*)/\omega$ and
  $B(x^*,\rho)\subset D$. Then the iterates satisfy $\|x^k-x^*\|\le\rho$ for
  all $k$, with strict inequality for $k\ge1$ if $x^0\ne x^*$, converge to
  $x^*$, and
  $$\|x^{k+1}-x^*\|\le\frac\omega2\|x^k-x^*\|^2+\kappa_*\|x^k-x^*\|.$$
  In particular the convergence is quadratic if $F(x^*)=0$ (a compatible
  problem), where one may take $\kappa_*=0$. The point $x^*$ is the only
  $x\in D\cap B(x^*,\sigma)$ with $F'(x)^+F(x)=0$.

  *Assessment.* Tau Ceti's Moore–Penrose inverse and the finite-dimensional
  adjoint underlie the iteration. The rate and its dependence on the
  limiting residual require the least-squares-specific linearization through
  the scaled Lipschitz condition.

  *Lean target.* Carriers: `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin m)`, `fderiv`, Tau
  Ceti's `LinearMap.moorePenroseInverse` and `LinearMap.IsMoorePenroseInverse`, `LinearMap.ker`. New
  definition: the Gauss–Newton step `x − (f' x)⁺ (f x)`. Hypotheses: `m ≥ n`, full column rank on
  `D` (`LinearMap.ker (fderiv ℝ f x) = ⊥`), `D` open convex, the two scaled bounds with `ω > 0`,
  `0 ≤ κ* < 1`, `ρ < σ = 2(1 − κ*)/ω`, `ball x* ρ ⊆ D`. Conjuncts: (i) one-step bound
  `‖x⁺ − x*‖ ≤ (ω/2)‖x − x*‖² + κ*‖x − x*‖`; (ii) convergence, iterates in `closedBall x* ρ`, and in
  `ball x* ρ` for `k ≥ 1` when `x₀ ≠ x*` (with `ρ = 0` the open ball is empty); (iii) uniqueness of
  stationary points `(f' x)⁺ f x = 0` in `D ∩ ball x* σ`; (iv) with `κ* = 0`, quadratic convergence.
  Under full column rank `(f' x)⁺` is a left inverse, which is all (i) uses. Statable and provable
  at the pins; no dependency. NASC: `NASC.norm_gaussNewtonStep_sub_le`
  (`NASC/NonlinearEquations.lean`), proved, states (i) for any continuous linear left inverse `P` of
  the derivative; (ii)–(iv) are not stated.

### Continuation

* **8.13. Predictor–corrector continuation.** A **predictor** for a curve
  $x:[-\varepsilon,\varepsilon]\to\mathbb R^n$ is a curve $\hat x$ on the
  same interval; it has **order** $p\in\mathbb N$ with constant $\eta>0$ if
  $\|x(s)-\hat x(s)\|\le\eta|s|^p$ for $|s|\le\varepsilon$.
  - The **classical predictor** $\hat x(s)=x(0)$ has order $1$ with
    $\eta=\max_{|t|\le\varepsilon}\|x'(t)\|$ when $x$ is $C^1$, and the
    **tangent predictor** $\hat x(s)=x(0)+sx'(0)$ has order $2$ with
    $\eta=\frac12\max_{|t|\le\varepsilon}\|x''(t)\|$ when $x$ is $C^2$.
  - Let $D\subset\mathbb R^n$ be open and convex,
    $F\in C^1(D\times[a,b];\mathbb R^n)$ with $F_x(x,\lambda)$ invertible on
    $D\times[a,b]$, and let $\omega>0$ satisfy
    $$\|F_x(x,\lambda)^{-1}(F_x(x+sv,\lambda)-F_x(x,\lambda))v\|
    \le s\omega\|v\|^2$$
    for all $\lambda\in[a,b]$, $s\in[0,1]$, $x\in D$ and $v$ with
    $x+v\in D$. Let $x(s)$, $|s|\le\varepsilon$, be a $C^1$ solution curve,
    $F(x(s),\lambda_0+s)=0$, and $\hat x$ a predictor of order $p$ with
    constant $\eta$. If $|s|\le\varepsilon$ and
    $$|s|<\Bigl(\frac2{\omega\eta}\Bigr)^{1/p},$$
    and $\hat x(s)\in D$ and $B(x(s),\|\hat x(s)-x(s)\|)\subset D$, then
    Newton's method for $F(\cdot,\lambda_0+s)=0$ started at $\hat x(s)$
    converges quadratically to $x(s)$, as in 8.5.

  *Assessment.* The implicit function theorem gives the local solution curve
  and its smoothness. The numerical content is the predictor error, the
  corrector's convergence from the predicted point and the resulting
  step-size bound.

  *Lean target.* Carriers: curves `ℝ → E` with `ContDiffOn ℝ 1` or `2` on
  `Set.Icc (−ε) ε`, `deriv`, `iteratedDeriv 2`, the Newton map of 8.5 applied to
  `fun x ↦ F (x, λ₀ + s)`. New definition: a predictor of order `p` with
  constant `η` as the predicate `∀ s, |s| ≤ ε → ‖x s − x̂ s‖ ≤ η * |s| ^ p`.
  Conjuncts: (i) the classical predictor has order 1 with
  `η = sup ‖x'‖`; (ii) the tangent predictor has order 2 with
  `η = (1/2) sup ‖x''‖`; (iii) under the affine-covariant Lipschitz condition
  uniform in `λ` and `|s| < (2/(ωη))^(1/p)`, the hypotheses of 8.5 (c) hold at
  `x̂ s`, so Newton converges quadratically to `x s`. Pitfall: `(2/(ωη))^(1/p)`
  is a real power and needs `η > 0`; a predictor with `η = 0` is exact. (i)–(ii)
  provable at the pins; (iii) depends on 8.5 (c). NASC:
  `NASC.norm_sub_tangentPredictor_le` (`NASC/NonlinearEquations.lean`), proved,
  states (ii); (i) and (iii) are not stated.

### Algorithmic differentiation

* **8.14. Evaluation procedures, forward and reverse mode.** An
  **evaluation procedure** for $F:\mathbb R^n\to\mathbb R^m$ sets
  $v_{i-n}=x_i$ for $i=1,\dots,n$, then
  $v_i=\varphi_i(u_i)$ with $u_i=(v_j)_{j\prec i}$ for $i=1,\dots,l$, and
  returns $y_{m-i}=v_{l-i}$ for $i=m-1,\dots,0$. Here the precedence
  relation $j\prec i$ implies $j<i$, the dependent variables
  $v_{l-m+1},\dots,v_l$ are arguments of no $\varphi_i$, and each
  **elemental function** $\varphi_i$ is $C^d$ ($d\ge1$) on an open domain.
  The set of $x$ at which the procedure is defined is open, and $F$ is
  $C^d$ there. Let $c_{ij}=\partial\varphi_i/\partial v_j(u_i)$ be the
  **elemental partials**.
  - (Forward or tangent mode) Given $\dot x\in\mathbb R^n$, set
    $\dot v_{i-n}=\dot x_i$ and $\dot v_i=\sum_{j\prec i}c_{ij}\dot v_j$ for
    $i=1,\dots,l$. Then $\dot y=(\dot v_{l-m+1},\dots,\dot v_l)=F'(x)\dot x$.
  - (Reverse or adjoint mode) Given $\bar y\in\mathbb R^m$, set
    $\bar v_j=0$ for all $j$, then $\bar v_{l-i}=\bar y_{m-i}$ for
    $i=0,\dots,m-1$, and for $i=l,l-1,\dots,1$ in this order increment
    $\bar v_j\mathrel{+}=\bar v_i\,c_{ij}$ for each $j\prec i$. Then
    $\bar x=(\bar v_{1-n},\dots,\bar v_0)$ satisfies
    $\bar x^\top=\bar y^\top F'(x)$. For $m=1$ and $\bar y=1$ this is
    $\nabla F(x)$.

  *Assessment.* Mathlib proves the Fréchet chain rule. The missing result
  relates the forward and reverse recurrences on an evaluation procedure to
  the derivative of its composed function.

  *Lean target.* Carriers: `ι → ℝ` for registers, `HasFDerivAt`, `fderiv`,
  `ContinuousLinearMap.adjoint` or the pairing `∑ j, a j * b j`. New definitions: an evaluation
  procedure as a list of instructions, each writing one register from an elemental function of
  finitely many registers with a continuous linear derivative there, its evaluation by `List.foldl`,
  the tangent recursion and the adjoint (reverse) recursion. Conjuncts: (i) the forward recursion
  computes `fderiv ℝ run x ẋ`; (ii) the reverse recursion computes the adjoint,
  `⟨x̄, ẋ⟩ = ⟨ȳ, F'(x) ẋ⟩` for all `ẋ`; (iii) the set of inputs at which all elementals are
  evaluated inside their open domains is open, and the composed map is `C^d` there when every
  elemental is. The single-assignment form of the source is the special case of distinct target
  registers; a register model with overwriting is more general. All statable and provable at the
  pins; no dependency. NASC: `NASC.ScalarInstruction.fderiv_evalProgram_apply` and
  `NASC.ScalarInstruction.sum_reverseProgram_mul_eq_sum_mul_fderiv` (`NASC/NonlinearEquations.lean`,
  over any nontrivially normed field), proved, state (i) and (ii) for constants, sums, products and
  globally differentiable unary functions; (iii) and elementals with several arguments or restricted
  domains are not stated.

* **8.15. Complexity of tangents and gradients.** Let the elemental
  functions be constants, $\pm$, $\times$ and univariate nonlinear functions
  (a division counts as a reciprocal and a multiplication). Measure work by
  the vector of numbers of memory moves (fetches and stores), additions,
  multiplications and nonlinear operations, each elemental costing
  $(1,0,0,0)$, $(3,1,0,0)$, $(3,0,1,0)$ and $(2,0,0,1)$ respectively, and
  measure time by $\mathrm{TIME}=w^\top\mathrm{WORK}$ with weights
  $w=(\mu,1,\pi,\nu)$, where $\mu\ge\pi\ge1$ and $\nu\ge2\pi$. Then for every
  evaluation procedure, with the forward and reverse modes of 8.14
  executed together with the evaluation of $F$ and without overwriting of
  intermediate values:
  - $\mathrm{TIME}\{F(x),F'(x)\dot x\}\le\omega_{\mathrm{tang}}
    \mathrm{TIME}\{F(x)\}$ with $\omega_{\mathrm{tang}}\in[2,5/2]$;
  - for $p\ge1$ and $\dot X\in\mathbb R^{n\times p}$ propagated simultaneously,
    $\mathrm{TIME}\{F(x),F'(x)\dot X\}\le\omega_{\mathrm{tang}_p}
    \mathrm{TIME}\{F(x)\}$ with $\omega_{\mathrm{tang}_p}\in[1+p,1+1.5p]$;
  - (cheap gradient principle)
    $\mathrm{TIME}\{F(x),\bar y^\top F'(x)\}\le\omega_{\mathrm{grad}}
    \mathrm{TIME}\{F(x)\}$ with $\omega_{\mathrm{grad}}\in[3,4]$; in
    particular, evaluating a scalar function together with its gradient
    costs at most $4$ times the evaluation of the function alone,
    independently of $n$;
  - for $q\ge1$ adjoint vectors propagated simultaneously the ratio lies in
    $[1+2q,1.5+2.5q]$.

  The constants are explicit functions of $(\mu,\pi,\nu)$. The stated
  intervals contain their values under the constraints on $w$, and the upper
  ends are attained at $\mu=\pi=1$, $\nu=2$.

  *Assessment.* The derivative identities of 8.14 are ingredients for the cost
  result. A separate operation model is needed to count the elemental
  evaluations and derivative operations and to bound the weighted ratios.

  *Lean target.* Carriers: `Fin 4 → ℕ` or `ℝ` for the work vector, `Matrix`,
  `List.sum`. New definitions: the four elemental classes, their evaluation
  work (Griewank–Walther Table 4.11) and their tangent, vector tangent and
  adjoint work (Tables 4.13, 4.15, 4.16 and the vector adjoint table), the work
  of a procedure as the sum over its elementals, and `TIME = w ⬝ᵥ WORK` with
  `w = (μ, 1, π, ν)`. Hypotheses: `1 ≤ π ≤ μ`, `2π ≤ ν`. Conjuncts: for every
  procedure (i) `TIME tang ≤ (5/2) TIME eval`; (ii) for `1 ≤ p`,
  `TIME tang_p ≤ (1 + 3p/2) TIME eval`; (iii) `TIME grad ≤ 4 TIME eval`; (iv) for `1 ≤ q`,
  `TIME grad_q ≤ (3/2 + 5q/2) TIME eval` (both fail at `p = 0`, `q = 0`); and the explicit `max`
  formulas (4.17), (4.18), (4.21), (4.23) as the per-elemental ratios. Each reduces to finitely many
  linear inequalities in `(μ, π, ν)`, so all are provable at the pins; depends
  on the procedures of 8.14. The statements concern a cost model fixed by
  definition, not executed code. NASC: `NASC.ScalarInstruction.sum_reverseWork_le`
  (`NASC/NonlinearEquations.lean`), proved, is a unit-cost count (reverse work at
  most four times the primal operation count); the four-component model and
  the weighted bounds are not stated.

## 9. Numerical optimization

[Synopsis](SYNOPSIS.md#9-numerical-optimization) · [Coverage inventory](STRUCTURE.md#9-numerical-optimization)

The mathematical primitives include local differential tests, convexity and
matrix scaling. The gaps concern constrained optimality, algorithmic rates and
the quantitative hypotheses that make those rates hold.

Unless
stated otherwise, the space is $\mathbb R^n$ with the Euclidean inner
product and norm, $f^*$ is the optimal value, $x^*$ is a minimizer, and
$\nabla f_k=\nabla f(x_k)$. A function is **$L$-smooth** on a set when it is
differentiable there and its gradient is Lipschitz continuous with constant
$L$. A differentiable function $f$ is **$\mu$-strongly convex**, $\mu>0$, if
$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac\mu2\|y-x\|^2$ for all
$x,y$. Newton's method for nonlinear equations, Broyden's method, and the
Gauss–Newton method are in section 8.

### Optimality conditions

* **9.2. Karush–Kuhn–Tucker conditions.** Consider
  $$\min_{x\in\mathbb R^n}f(x)\quad\text{subject to}\quad c_i(x)=0\ (i\in\mathcal E),
  \qquad c_i(x)\ge0\ (i\in\mathcal I),$$
  with finite disjoint index sets $\mathcal E,\mathcal I$ and real functions
  $f,c_i$ on $\mathbb R^n$. The **active set** of a feasible $x$ is
  $\mathcal A(x)=\mathcal E\cup\{i\in\mathcal I:c_i(x)=0\}$, and the
  **linear independence constraint qualification** (LICQ) holds at $x$ if the
  gradients $\nabla c_i(x)$, $i\in\mathcal A(x)$, are linearly independent.
  The **Lagrangian** is
  $\mathcal L(x,\lambda)=f(x)-\sum_{i\in\mathcal E\cup\mathcal I}\lambda_ic_i(x)$.
  - (First order.) Let $f$ and all $c_i$ be continuously differentiable, let
    $x^*$ be a local solution, and let LICQ hold at $x^*$. Then there is a
    $\lambda^*$ with
    $$\nabla_x\mathcal L(x^*,\lambda^*)=0,\quad c_i(x^*)=0\ (i\in\mathcal E),\quad
    c_i(x^*)\ge0,\ \lambda_i^*\ge0\ (i\in\mathcal I),\quad
    \lambda_i^*c_i(x^*)=0\ (i\in\mathcal E\cup\mathcal I).$$
  - Let $f,c_i$ be twice continuously differentiable and let $(x^*,\lambda^*)$
    satisfy these conditions. The **critical cone** $C(x^*,\lambda^*)$ is the
    set of $w$ with $\nabla c_i(x^*)^\top w=0$ for $i\in\mathcal E$ and for
    $i\in\mathcal A(x^*)\cap\mathcal I$ with $\lambda_i^*>0$, and
    $\nabla c_i(x^*)^\top w\ge0$ for $i\in\mathcal A(x^*)\cap\mathcal I$ with
    $\lambda_i^*=0$.
  - (Second-order necessary.) If $x^*$ is a local solution, LICQ holds at
    $x^*$, and $\lambda^*$ is the multiplier vector of the first part, then
    $w^\top\nabla^2_{xx}\mathcal L(x^*,\lambda^*)w\ge0$ for all
    $w\in C(x^*,\lambda^*)$.
  - (Second-order sufficient.) If $x^*$ is feasible, $(x^*,\lambda^*)$
    satisfies the conditions of the first part, and
    $w^\top\nabla^2_{xx}\mathcal L(x^*,\lambda^*)w>0$ for all nonzero
    $w\in C(x^*,\lambda^*)$, then $x^*$ is a strict local solution. No
    constraint qualification is needed here.

  *Assessment.* Partly covered. Mathlib has equality-constrained multiplier
  results. Inequality feasibility, multiplier signs, complementarity and the
  second-order tests on the critical cone are the selected content.

  *Scope.* The targets are the multiplier sign and complementarity conditions
  for active inequalities and the two tests on the critical cone.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℝ (Fin n)`, `gradient`,
  `ContDiff ℝ 1` and `ContDiff ℝ 2`, `IsLocalMinOn`, `LinearIndependent`, and
  `iteratedFDeriv ℝ 2` for the Hessian of the Lagrangian; Mathlib's
  `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` (equality part) and
  `ProperCone.relative_hyperplane_separation` (the Farkas step) are the analytic suppliers.
  Index the constraints by `c : Fin p ⊕ Fin q → E → ℝ`, equalities on `.inl` and
  inequalities $c_i\ge0$ on `.inr`. New definitions: the feasible set, the active index
  set `{i // c i x = 0}` (all equality indices are active), the Lagrangian
  $f-\sum_i\lambda_ic_i$, and the critical cone `criticalCone c λ x : Set E` as the set of
  $w$ with $Dc_i(x)w=0$ for equalities and for active inequalities with $\lambda_i>0$, and
  $Dc_i(x)w\ge0$ for active inequalities with $\lambda_i=0$. Three theorems: (i) local
  solution + LICQ ⇒ ∃ λ with stationarity, $\lambda_i\ge0$ on inequalities and
  $\lambda_ic_i(x^*)=0$; (ii) local solution + LICQ + `C²` + λ from (i) ⇒ the Hessian of the
  Lagrangian is nonnegative on the critical cone (λ is unique under LICQ, so "the"
  multiplier is well defined); (iii) KKT point + strict positivity on the nonzero critical
  directions ⇒ strict local solution, with no constraint qualification. Pitfalls: with
  $p=q=0$ the statements reduce to 9.1 and LICQ over the empty family holds; the Hessian via
  `iteratedFDeriv` is meaningful only under `ContDiff ℝ 2`; the sign convention of the
  Lagrangian must match $c_i\ge0$. All three are statable and provable at the pins in finite
  dimension. NASC: `NASC.exists_kkt_multipliers` states (i) and
  `NASC.kkt_strict_local_min_of_hessian` states (iii) (`NASC/Optimization.lean`), both
  `sorry`, in a finite-dimensional real inner product space with finite index types and local
  `ContDiffAt` hypotheses at the point; (ii) is not stated.

### Line search, Newton and quasi-Newton methods

* **9.3. Wolfe conditions and Zoutendijk's theorem.** Let $f$ be
  continuously differentiable, let $p$ be a **descent direction** at $x$
  ($\nabla f(x)^\top p<0$), and let $0<c_1<c_2<1$. A step $\alpha>0$ satisfies
  the **Wolfe conditions** if
  $$f(x+\alpha p)\le f(x)+c_1\alpha\nabla f(x)^\top p,\qquad
  \nabla f(x+\alpha p)^\top p\ge c_2\nabla f(x)^\top p,$$
  and the **strong Wolfe conditions** if the second inequality is replaced by
  $|\nabla f(x+\alpha p)^\top p|\le c_2|\nabla f(x)^\top p|$.
  - If $f$ is bounded below on the ray $\{x+\alpha p:\alpha>0\}$, then there
    are intervals of positive length consisting of steps that satisfy the
    Wolfe conditions, and likewise for the strong Wolfe conditions.
  - (Zoutendijk.) Let $x_{k+1}=x_k+\alpha_kp_k$, where each $p_k$ is a descent
    direction at $x_k$ and each $\alpha_k$ satisfies the Wolfe conditions. Let
    $f$ be bounded below on $\mathbb R^n$ and continuously differentiable on an
    open set $N$ containing the level set $\{x:f(x)\le f(x_0)\}$, with
    $\nabla f$ Lipschitz continuous on $N$. With
    $\cos\theta_k=-\nabla f_k^\top p_k/(\|\nabla f_k\|\,\|p_k\|)$,
    $$\sum_{k\ge0}\cos^2\theta_k\,\|\nabla f_k\|^2<\infty .$$
    In particular, if $\cos\theta_k\ge\delta>0$ for all $k$, then
    $\nabla f_k\to0$.

  *Assessment.* The calculus of a function restricted to a search line is
  available. Existence of admissible step lengths and the summability estimate
  over accepted steps are the optimization-specific assertions.

  *Lean target.* Carriers at the pins: a real inner-product space `H`, `gradient`,
  `LipschitzWith` / `LipschitzOnWith` for the gradient, `BddBelow (Set.range f)`,
  `Summable`. New definitions: `IsWolfeStep f x p c₁ c₂ α` (exists in NASC) and
  `IsStrongWolfeStep` with the absolute-value curvature condition. Conjuncts: (i) for `C¹`
  $f$ bounded below on the open ray, a descent direction $p$ and $0<c_1<c_2<1$, there are
  $a<b$ with every $\alpha\in(a,b)$ a strong Wolfe step (hence a Wolfe step); (ii)
  Zoutendijk: for Wolfe steps along descent directions, $f$ bounded below and the gradient
  Lipschitz on an open set containing the sublevel set $\{f\le f(x_0)\}$,
  $\sum_k\langle\nabla f_k,p_k\rangle^2/\|p_k\|^2<\infty$; (iii) $\cos\theta_k\ge\delta>0$
  ⇒ $\nabla f_k\to0$. Writing the summand as $\langle\nabla f_k,p_k\rangle^2/\|p_k\|^2$
  instead of $\cos^2\theta_k\|\nabla f_k\|^2$ avoids the junk value $x/0$ at
  $\nabla f_k=0$; $p_k\ne0$ follows from the descent hypothesis. In (ii) the iterates stay
  in the sublevel set by the Armijo condition, which the proof must show before using the
  local Lipschitz bound. Statable and provable at the pins. NASC:
  `NASC.summable_wolfe_gradient_sq` (`NASC/Optimization.lean`, `sorry`) states (ii) with a
  global Lipschitz gradient and global differentiability, a stronger hypothesis than the
  entry; (i) and (iii) are not stated.

* **9.5. Dennis–Moré condition and the BFGS method.** Let $f$ be twice
  continuously differentiable.
  - Let $x_{k+1}=x_k+\alpha_kp_k$ with descent directions $p_k$ and steps
    satisfying the Wolfe conditions with $0<c_1<\frac12$. Suppose $x_k\to x^*$,
    $\nabla f(x^*)=0$, $\nabla^2f(x^*)$ is positive definite, and
    $\|\nabla f_k+\nabla^2f_kp_k\|/\|p_k\|\to0$. Then $\alpha_k=1$ satisfies
    the Wolfe conditions for all $k$ beyond some $k_0$, and if $\alpha_k=1$ for
    all $k>k_0$, then $x_k\to x^*$ superlinearly.
  - (Dennis–Moré.) Let $x_{k+1}=x_k+p_k$ with $p_k=-B_k^{-1}\nabla f_k$ for
    nonsingular $B_k$, let $x_k\ne x^*$ for all $k$, and let $x_k\to x^*$ with
    $\nabla f(x^*)=0$ and $\nabla^2f(x^*)$ positive definite. Then the
    convergence is superlinear if and only if
    $$\lim_{k\to\infty}\frac{\|(B_k-\nabla^2f(x^*))p_k\|}{\|p_k\|}=0 .$$
  - The **BFGS method** takes $p_k=-B_k^{-1}\nabla f_k$, a Wolfe step
    $\alpha_k$, $s_k=x_{k+1}-x_k$, $y_k=\nabla f_{k+1}-\nabla f_k$, and
    $$B_{k+1}=B_k-\frac{B_ks_ks_k^\top B_k}{s_k^\top B_ks_k}
    +\frac{y_ky_k^\top}{y_k^\top s_k},$$
    starting from a symmetric positive definite $B_0$. Suppose the level set
    $\{x:f(x)\le f(x_0)\}$ is convex and there are $0<m\le M$ with
    $m\|z\|^2\le z^\top\nabla^2f(x)z\le M\|z\|^2$ for all $z$ and all $x$ in
    that level set. Then the BFGS iterates converge to the unique minimizer
    $x^*$ of $f$ in the level set.
  - If moreover $\|\nabla^2f(x)-\nabla^2f(x^*)\|\le L\|x-x^*\|$ for $x$ near
    $x^*$, and $\sum_k\|x_k-x^*\|<\infty$, then the BFGS matrices satisfy the
    Dennis–Moré condition $\|(B_k-\nabla^2f(x^*))s_k\|/\|s_k\|\to0$, so the
    first part applies: the unit step is eventually acceptable, and with unit
    steps the convergence is superlinear.

  *Assessment.* Generic positive-definite matrix theory is available. The
  selected gap is the superlinear criterion and its verification for the BFGS
  updates.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℝ (Fin n)` (or a finite-dimensional
  inner-product space), `gradient`, the Hessian `fderiv ℝ (gradient f)`, `ContDiff ℝ 2`,
  continuous linear equivalences `E ≃L[ℝ] E` for nonsingular $B_k$, positive definiteness
  as `0 < ⟪v, H v⟫` for `v ≠ 0` (or `Matrix.PosDef` in coordinates), and the Wolfe predicate
  of 9.3. New definitions: the BFGS update `bfgsUpdate B s y` as an operator
  $B-\frac{Bs\otimes Bs}{\langle s,Bs\rangle}+\frac{y\otimes y}{\langle y,s\rangle}$ (via
  `InnerProductSpace.rankOne`), and a BFGS run as sequences satisfying the update and Wolfe
  relations. Superlinear convergence is
  `Tendsto (fun k ↦ ‖x (k+1) - x*‖ / ‖x k - x*‖) atTop (𝓝 0)` with $x_k\ne x^*$ for all
  $k$. Four theorems: (i) unit step eventually Wolfe for $0<c_1<\frac12$ and superlinear
  convergence with unit steps; (ii) Dennis–Moré equivalence; (iii) global convergence of
  BFGS under a convex sublevel set with uniform Hessian bounds $m\le\nabla^2f\le M$; (iv)
  the Dennis–Moré condition for BFGS under a Lipschitz Hessian at $x^*$ and
  $\sum_k\|x_k-x^*\|<\infty$. Pitfalls: $c_1=\frac12$ falsifies (i); the update divides by
  $\langle s_k,B_ks_k\rangle$ and $\langle y_k,s_k\rangle$, which are positive only because of
  positive definiteness and the Wolfe curvature condition, so both facts must be proved
  before the update is used (otherwise Lean's $x/0=0$ silently changes the update). Depends
  on 9.3. Statable at the pins. NASC: `NASC.tendsto_error_ratio_iff_dennisMore`
  (`NASC/Optimization.lean`, `sorry`) states (ii) with an invertible Hessian at $x^*$ in
  place of positive definiteness, which the proof allows; (i), (iii), (iv) are not stated.

* **9.6. Trust-region methods.** At $x_k$ let $g_k=\nabla f(x_k)\ne0$, let
  $B_k$ be symmetric, and let $m_k(p)=f(x_k)+g_k^\top p+\frac12p^\top B_kp$.
  The **Cauchy point** is $p_k^C=\tau_kp_k^S$ with
  $p_k^S=-\Delta_kg_k/\|g_k\|$ and $\tau_k\in[0,1]$ minimizing
  $m_k(\tau p_k^S)$. Write $\|g_k\|/\|B_k\|=+\infty$ when $B_k=0$.
  - (Cauchy decrease.)
    $m_k(0)-m_k(p_k^C)\ge\frac12\|g_k\|\min(\Delta_k,\|g_k\|/\|B_k\|)$. Any
    $p_k$ with $\|p_k\|\le\Delta_k$ and
    $m_k(0)-m_k(p_k)\ge c_2(m_k(0)-m_k(p_k^C))$, $c_2>0$, satisfies
    $$m_k(0)-m_k(p_k)\ge c_1\|g_k\|\min(\Delta_k,\|g_k\|/\|B_k\|)\qquad(*)$$
    with $c_1=c_2/2$; the exact minimizer of $m_k$ on the ball of radius
    $\Delta_k$ satisfies $(*)$ with $c_1=\frac12$.
  - (Global convergence.) In the basic trust-region algorithm one computes
    $\rho_k=(f(x_k)-f(x_k+p_k))/(m_k(0)-m_k(p_k))$, sets
    $\Delta_{k+1}=\Delta_k/4$ if $\rho_k<\frac14$,
    $\Delta_{k+1}=\min(2\Delta_k,\hat\Delta)$ if $\rho_k>\frac34$ and
    $\|p_k\|=\Delta_k$, and $\Delta_{k+1}=\Delta_k$ otherwise, and sets
    $x_{k+1}=x_k+p_k$ if $\rho_k>\eta$ and $x_{k+1}=x_k$ otherwise; here
    $0<\Delta_0<\hat\Delta$. Suppose $\|B_k\|\le\beta$ for all $k$, $f$ is
    bounded below on $S=\{x:f(x)\le f(x_0)\}$ and has Lipschitz continuous
    gradient on $\{x:\mathop{\mathrm{dist}}(x,S)<R_0\}$ for some $R_0>0$, and every
    $p_k$ satisfies $(*)$ and $\|p_k\|\le\gamma\Delta_k$ for constants
    $c_1>0$, $\gamma\ge1$. If $\eta=0$, then $\liminf_k\|g_k\|=0$. If
    $0<\eta<\frac14$, then $\lim_k\|g_k\|=0$.

  *Assessment.* The quadratic model, the Cauchy point and the ratio test are
  elementary finite-dimensional objects. The decrease estimate and the two convergence
  theorems of the basic trust-region algorithm are the selected content.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℝ (Fin n)`, self-adjoint operators
  `B : E →L[ℝ] E` with `IsSelfAdjoint B` and the operator norm, `gradient`,
  `LipschitzOnWith`. New definitions: the model `m g B p = ⟪g, p⟫ + ⟪p, B p⟫ / 2` (the
  constant $f(x_k)$ dropped), the Cauchy point `cauchyPoint g B Δ`, the decrease bound
  `cauchyBound g B Δ`, and a trust-region run as sequences $(x_k,\Delta_k,p_k)$ with the
  ratio and radius-update relations of the entry as hypotheses. Conjuncts: (i) Cauchy
  decrease for $g\ne0$, $\Delta>0$; (ii) the $c_2$-fraction consequence; (iii) for $\eta=0$,
  $\liminf\|g_k\|=0$, stated as `∃ᶠ k in atTop, ‖g k‖ < ε` for every $\varepsilon>0$ (with
  the convention that the run stops at $g_k=0$); (iv) for $0<\eta<\frac14$,
  $\|g_k\|\to0$. Pitfalls: the term $\|g\|/\|B\|$ must be replaced by its intended
  value $+\infty$ when $B=0$, for instance by defining `cauchyBound` with a case split,
  since Lean's $\|g\|/0=0$ would make $\min(\Delta,\|g\|/\|B\|)=0$ and the bound vacuous;
  $\rho_k$ divides by the model decrease, which (i) shows positive. Statable and provable at
  the pins. NASC: no declaration.

### First-order methods for convex problems

* **9.7. Gradient descent.** Let $f:\mathbb R^n\to\mathbb R$ be convex and
  $L$-smooth with a minimizer $x^*$, and let $x_{k+1}=x_k-h\nabla f(x_k)$.
  - If $0<h<2/L$ and $x_0\ne x^*$, then
    $$f(x_k)-f^*\le\frac{2(f(x_0)-f^*)\|x_0-x^*\|^2}
    {2\|x_0-x^*\|^2+kh(2-Lh)(f(x_0)-f^*)}\qquad(k\ge0).$$
  - If $h=1/L$, then
    $f(x_k)-f^*\le L\|x_0-x^*\|^2/(2k)$ for $k\ge1$ and
    $f(x_k)-f^*\le2L\|x_0-x^*\|^2/(k+4)$ for $k\ge0$.
  - If $f$ is also $\mu$-strongly convex and $0<h\le2/(\mu+L)$, then
    $\|x_k-x^*\|^2\le\bigl(1-\frac{2h\mu L}{\mu+L}\bigr)^k\|x_0-x^*\|^2$. For
    $h=2/(\mu+L)$,
    $$\|x_k-x^*\|\le\Bigl(\frac{L-\mu}{L+\mu}\Bigr)^k\|x_0-x^*\|,\qquad
    f(x_k)-f^*\le\frac L2\Bigl(\frac{L-\mu}{L+\mu}\Bigr)^{2k}\|x_0-x^*\|^2 .$$

  *Assessment.* Convex derivative inequalities are available. The algorithmic
  statement joins the smoothness estimate and descent recursion to obtain
  explicit function-value rates.

  *Lean target.* Carriers at the pins: a real Hilbert space `H` (the source has
  $\mathbb R^n$; the proofs are dimension free), `gradient`, `ConvexOn ℝ univ f`,
  `LipschitzWith L (gradient f)`, `StrongConvexOn univ μ f` (Mathlib's midpoint form,
  equivalent for differentiable $f$ to the first-order definition of the section preamble;
  the equivalence is a lemma to prove), and the iterate `step^[k] x₀` of
  $y\mapsto y-h\nabla f(y)$. Conjuncts: (i) the general bound for $0<h<2/L$; (ii) the two
  bounds for $h=1/L$; (iii) the contraction of $\|x_k-x^*\|^2$ for strongly convex $f$ and
  $0<h\le2/(\mu+L)$; (iv) the two rates at $h=2/(\mu+L)$. Pitfalls: in (i) both sides
  vanish when $x_0=x^*$, so the hypothesis $x_0\ne x^*$ only rules out a $0/0$ that Lean
  evaluates harmlessly; (ii) needs $k\ge1$ for $L\|x_0-x^*\|^2/(2k)$. Statable and
  provable at the pins. NASC: `NASC.gradientDescent_objective_error_le`
  (`NASC/Optimization.lean`) proves the first bound of (ii) in Hilbert space, with the
  helpers `NASC.abs_gradientModel_error_le` and `NASC.gradient_step_sub_le`, proved; (i),
  (iii), (iv) and the second bound of (ii) are not stated.

* **9.8. Lower complexity bounds and the optimal method.** A method is
  **first-order** in the sense of this item if its iterates satisfy
  $x_k\in x_0+\mathop{\mathrm{span}}\{\nabla f(x_0),\dots,\nabla f(x_{k-1})\}$
  for $k\ge1$.
  - Let $L>0$, $x_0\in\mathbb R^n$, and $1\le k\le\frac12(n-1)$. There is a
    convex $L$-smooth infinitely differentiable $f$ on $\mathbb R^n$, with
    minimizer $x^*$, such that every first-order method satisfies
    $$f(x_k)-f^*\ge\frac{3L\|x_0-x^*\|^2}{32(k+1)^2},\qquad
    \|x_k-x^*\|^2\ge\frac18\|x_0-x^*\|^2 .$$
  - Let $0<\mu<L$, $Q=L/\mu$, and $x_0\in\ell^2$. There is a $\mu$-strongly
    convex $L$-smooth $f$ on $\ell^2$ with minimizer $x^*$ such that every
    first-order method satisfies, for all $k$,
    $$\|x_k-x^*\|^2\ge q^{2k}\|x_0-x^*\|^2,\qquad
    f(x_k)-f^*\ge\frac\mu2q^{2k}\|x_0-x^*\|^2,\qquad
    q=\frac{\sqrt Q-1}{\sqrt Q+1}.$$
  - (Accelerated gradient method.) Let $f$ on $\mathbb R^n$ be
    $\mu$-strongly convex and $L$-smooth, $0<\mu\le L$, $q_f=\mu/L$. Put
    $y_0=x_0$ and
    $$x_{k+1}=y_k-\tfrac1L\nabla f(y_k),\qquad
    y_{k+1}=x_{k+1}+\frac{1-\sqrt{q_f}}{1+\sqrt{q_f}}(x_{k+1}-x_k).$$
    Then $f(x_k)-f^*\le\frac{L+\mu}2\|x_0-x^*\|^2e^{-k\sqrt{q_f}}$ for $k\ge0$.
    For $\mu=0$ the method of 9.9 with $g=0$ attains
    $f(x_k)-f^*\le2L\|x_0-x^*\|^2/(k+1)^2$, so both lower bounds are attained
    up to constant factors.

  *Assessment.* The gap comprises a first-order information model, the
  worst-case lower bound, and a method attaining the indicated order under the
  given smoothness and convexity assumptions.

  *Lean target.* Carriers at the pins: `EuclideanSpace ℝ (Fin n)`, the Hilbert space
  `lp (fun _ : ℕ ↦ ℝ) 2` with `lp.instInnerProductSpace` for the strongly convex lower
  bound, `gradient`, `ContDiff ℝ ∞`, `LipschitzWith`, `StrongConvexOn`, `Submodule.span`.
  New definition: the span model `NASC.IsSpanFirstOrder f x`
  ($x_k-x_0\in\mathrm{span}\{\nabla f(x_j):j<k\}$), which exists in NASC. Three theorems:
  (i) for $1\le k$ and $2k+1\le n$ there exist $f$ and $x^*$ (depending on $k$) such that
  every span-model sequence from $x_0$ has the two lower bounds at step $k$; (ii) for
  $0<\mu<L$ there are a $\mu$-strongly convex $L$-smooth $f$ on $\ell^2$ and $x^*$ with the
  geometric lower bounds for all $k$; (iii) the constant-step accelerated scheme satisfies
  $f(x_k)-f^*\le\frac{L+\mu}2\|x_0-x^*\|^2e^{-k\sqrt{\mu/L}}$. Pitfalls: the quantifier order
  is ∀k ∃f in (i) but ∃f ∀k in (ii); in (ii) the minimizer has coordinates $q^i$, so the
  construction needs $x_0$ fixed (by translation, $x_0=0$) and summability of $q^{2i}$.
  (i) and (iii) are statable and provable at the pins; (ii) is statable on `lp`. The
  $\mu=0$ upper bound is 9.9. NASC: `NASC.exists_firstOrder_lowerBound`
  (`NASC/Optimization.lean`, `sorry`) states (i); (ii) and (iii) are not stated.

* **9.9. Proximal gradient method and FISTA.** Let $E$ be a Euclidean space,
  $g:E\to(-\infty,\infty]$ proper, closed and convex, $f:E\to\mathbb R$
  convex and $L_f$-smooth, and suppose $F=f+g$ has a nonempty set $X^*$ of
  minimizers, with minimum $F_{\mathrm{opt}}$. The **proximal map** is
  $\mathop{\mathrm{prox}}_{tg}(x)=\mathop{\mathrm{argmin}}_u\{g(u)+\frac1{2t}\|u-x\|^2\}$ for $t>0$;
  it is single-valued. Let $x^*\in X^*$ and $x^0\in E$.
  - The **proximal gradient method**
    $x^{k+1}=\mathop{\mathrm{prox}}_{g/L_f}\bigl(x^k-\frac1{L_f}\nabla f(x^k)\bigr)$
    satisfies $F(x^k)-F_{\mathrm{opt}}\le L_f\|x^0-x^*\|^2/(2k)$ for $k\ge1$.
  - **FISTA**: $y^0=x^0$, $t_0=1$, and for $k\ge0$
    $$x^{k+1}=\mathop{\mathrm{prox}}_{g/L_f}\Bigl(y^k-\tfrac1{L_f}\nabla f(y^k)\Bigr),\quad
    t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}2,\quad
    y^{k+1}=x^{k+1}+\frac{t_k-1}{t_{k+1}}(x^{k+1}-x^k).$$
    It satisfies
    $$F(x^k)-F_{\mathrm{opt}}\le\frac{2L_f\|x^0-x^*\|^2}{(k+1)^2}\qquad(k\ge1).$$

  *Assessment.* Projection and convex analysis provide ingredients for
  proximal steps. The selected estimates need control of the composite
  objective and the accelerated iteration's parameter sequence.

  *Lean target.* Carriers at the pins: a real Hilbert space, `gradient`, `ConvexOn`,
  `LipschitzWith L (gradient f)`, extended-valued $g:H\to$ `EReal` with TauCeti's
  `TauCeti.subdifferential` and `TauCeti.fenchelConjugate` available for later use. New
  definitions: properness and closedness of $g$ (no `⊥` value, closed epigraph over real
  heights), and the proximal relation `NASC.IsProximalPoint g t x z` (exists in NASC),
  together with a lemma that a proper closed convex $g$ has exactly one proximal point,
  which turns the relation into a map. Conjuncts: (i) the proximal gradient bound
  $L_f\|x^0-x^*\|^2/(2k)$ for $k\ge1$; (ii) the FISTA bound $2L_f\|x^0-x^*\|^2/(k+1)^2$;
  (iii) existence and uniqueness of the proximal point. Pitfalls: the composite objective
  takes values in `EReal`, so the bounds are stated in `EReal` (or after showing
  $g(x^k)<\top$, which holds because proximal points lie in $\mathrm{dom}\,g$); the minimizer
  must have $g(x^*)<\top$. Statable at the pins. NASC: `NASC.fista_objective_le`
  (`NASC/Optimization.lean`, `sorry`) states (ii); (i) and (iii) are not stated.

### Monotone operator splitting

* **9.12. Firmly nonexpansive operators and fixed-point iterations.** Let $H$
  be a real Hilbert space and $\emptyset\ne D\subseteq H$. An operator
  $T:D\to H$ is **nonexpansive** if $\|Tx-Ty\|\le\|x-y\|$, and **firmly
  nonexpansive** if
  $\|Tx-Ty\|^2+\|(x-Tx)-(y-Ty)\|^2\le\|x-y\|^2$ for all $x,y\in D$;
  equivalently $\|Tx-Ty\|^2\le\langle x-y,Tx-Ty\rangle$, or $2T-I$ is
  nonexpansive. For a maximally monotone $A:H\to2^H$ the **resolvent**
  $J_A=(I+A)^{-1}$ is defined on $H$; an operator $T:H\to H$ is firmly
  nonexpansive if and only if $T=J_A$ for some maximally monotone $A$. For a
  proper lower semicontinuous convex $f$ and $\gamma>0$,
  $J_{\gamma\partial f}=\mathop{\mathrm{prox}}_{\gamma f}$, so proximal maps are firmly
  nonexpansive. Weak convergence is written $\rightharpoonup$.
  - (Krasnosel'skiĭ–Mann.) Let $D$ be closed and convex, $T:D\to D$
    nonexpansive with $\mathop{\mathrm{Fix}}T\ne\emptyset$, $\lambda_n\in[0,1]$ with
    $\sum_n\lambda_n(1-\lambda_n)=\infty$, $x_0\in D$, and
    $x_{n+1}=x_n+\lambda_n(Tx_n-x_n)$. Then $(x_n)$ is **Fejér monotone** with
    respect to $\mathop{\mathrm{Fix}}T$ ($\|x_{n+1}-z\|\le\|x_n-z\|$ for all
    $z\in\mathop{\mathrm{Fix}}T$ and $n$), $Tx_n-x_n\to0$, and $x_n$ converges weakly to a
    point of $\mathop{\mathrm{Fix}}T$.
  - (Proximal point.) If $A$ is maximally monotone with a zero,
    $\gamma_n>0$ with $\sum_n\gamma_n^2=\infty$, and
    $x_{n+1}=J_{\gamma_nA}x_n$, then $x_n$ converges weakly to a zero of $A$.
  - (Forward–backward.) Let $A$ be maximally monotone, let $B:H\to H$ be
    **$\beta$-cocoercive** ($\langle x-y,Bx-By\rangle\ge\beta\|Bx-By\|^2$),
    $\beta>0$, let $\mathop{\mathrm{zer}}(A+B)\ne\emptyset$, $\gamma\in(0,2\beta)$,
    $\delta=2-\gamma/(2\beta)$, and $\lambda_n\in[0,\delta]$ with
    $\sum_n\lambda_n(\delta-\lambda_n)=\infty$. Then
    $x_{n+1}=x_n+\lambda_n\bigl(J_{\gamma A}(x_n-\gamma Bx_n)-x_n\bigr)$
    converges weakly to a zero of $A+B$.
  - (Douglas–Rachford.) Let $A,B$ be maximally monotone with
    $\mathop{\mathrm{zer}}(A+B)\ne\emptyset$, $\gamma>0$, and $\lambda_n\in[0,2]$ with
    $\sum_n\lambda_n(2-\lambda_n)=\infty$. Let $x_n=J_{\gamma B}y_n$,
    $z_n=J_{\gamma A}(2x_n-y_n)$, $y_{n+1}=y_n+\lambda_n(z_n-x_n)$. Then
    $y_n\rightharpoonup y$ for some $y$, the point $x=J_{\gamma B}y$ is a zero of
    $A+B$, $x_n-z_n\to0$, $x_n\rightharpoonup x$ and $z_n\rightharpoonup x$.

  *Assessment.* Convex projections and resolvent ingredients are available.
  The selected result connects the firm inequality to monotone resolvents and
  proves the convergence of the stated relaxed iterations.

  *Lean target.* Carriers at the pins: a real Hilbert space `H` with `CompleteSpace H`,
  `LipschitzOnWith 1` for nonexpansiveness, set-valued operators `A : H → Set H`, weak
  convergence expressed by `∀ y, Tendsto (fun n ↦ ⟪y, x n⟫) atTop (𝓝 ⟪y, x⟫)` (or through
  `WeakSpace ℝ H`), `TauCeti.subdifferential` for $\partial f$. New definitions:
  `FirmlyNonexpansiveOn`, `Monotone`/`MaximalMonotone` for set-valued operators (named to avoid
  the order-theoretic `Monotone`, e.g. `IsMaximalMonotoneOp`), the resolvent as a relation
  and, after Minty's theorem, as a map, cocoercivity, `Fix T`, `zer A`, and Fejér
  monotonicity. Separate theorems: (i) the three characterizations of firm
  nonexpansiveness; (ii) Minty: $J_A$ is single-valued with full domain for maximally
  monotone $A$, and firmly nonexpansive maps are exactly resolvents; (iii)
  $J_{\gamma\partial f}=\mathrm{prox}_{\gamma f}$; (iv) Krasnosel'skiĭ–Mann; (v) proximal
  point with $\sum\gamma_n^2=\infty$; (vi) forward–backward; (vii) Douglas–Rachford.
  Pitfalls: divergence of $\sum\lambda_n(1-\lambda_n)$ is `¬ Summable` of a nonnegative
  sequence; $\lambda_n=0$ for all $n$ must be excluded by that hypothesis, not by a
  separate positivity assumption; the conclusions are weak limits, and strong convergence
  fails in infinite dimension. Minty's theorem (ii) is the largest missing piece of
  infrastructure. Statable at the pins. NASC: `NASC.exists_weakLimit_krasnoselskiiMann`
  (`NASC/Optimization.lean`, `sorry`) states (iv) with weak convergence by scalar products;
  the rest is not stated.

* **9.13. Primal–dual hybrid gradient method.** Let $X,Y$ be real Hilbert
  spaces, $K:X\to Y$ bounded linear with $L=\|K\|$, and
  $g:X\to(-\infty,\infty]$, $f:Y\to(-\infty,\infty]$ proper, convex and lower
  semicontinuous. For $\min_xf(Kx)+g(x)$ let
  $\mathcal L(x,y)=\langle y,Kx\rangle-f^*(y)+g(x)$, with $f^*$ the convex
  conjugate. Given $\tau,\sigma>0$ and $(x^0,y^0)$, let
  $$x^{k+1}=\mathop{\mathrm{prox}}_{\tau g}(x^k-\tau K^*y^k),\qquad
  y^{k+1}=\mathop{\mathrm{prox}}_{\sigma f^*}\bigl(y^k+\sigma K(2x^{k+1}-x^k)\bigr).$$
  If $\tau\sigma L^2\le1$, then for all $(x,y)\in X\times Y$ and $k\ge1$,
  with ergodic averages $X^k=\frac1k\sum_{i=1}^kx^i$,
  $Y^k=\frac1k\sum_{i=1}^ky^i$,
  $$\mathcal L(X^k,y)-\mathcal L(x,Y^k)\le
  \frac1k\Bigl(\frac{\|x-x^0\|^2}\tau+\frac{\|y-y^0\|^2}\sigma\Bigr).$$
  If $\tau\sigma L^2<1$ and $\mathcal L$ has a saddle point, then $(x^k,y^k)$
  converges weakly to a saddle point.

  *Assessment.* The continuum saddle problem and operator norm are
  ingredients. The primal–dual iteration needs a fixed-point representation
  with the specified step restriction and its convergence estimate.

  *Lean target.* Carriers at the pins: real Hilbert spaces `X`, `Y`, `K : X →L[ℝ] Y` with
  `ContinuousLinearMap.adjoint` and `‖K‖`, extended-valued proper convex lower
  semicontinuous $g$, $f$ with $f^*$ given by `TauCeti.fenchelConjugate` (for the inner
  pairing), and the proximal relation of 9.9. New definitions: the Lagrangian
  $\mathcal L(x,y)=\langle y,Kx\rangle-f^*(y)+g(x)$ in `EReal`, a saddle point, and the
  PDHG run as sequences satisfying the two proximal relations. Conjuncts: (i) the ergodic
  gap bound for $\tau\sigma\|K\|^2\le1$ and $k\ge1$, for all $(x,y)$; (ii) weak convergence
  to a saddle point when $\tau\sigma\|K\|^2<1$ and a saddle point exists. Pitfalls: with
  extended values the gap $\mathcal L(X^k,y)-\mathcal L(x,Y^k)$ can be $\top-\top$, so state
  (i) for $x\in\mathrm{dom}\,g$, $y\in\mathrm{dom}\,f^*$ or in the form
  $\mathcal L(X^k,y)\le\mathcal L(x,Y^k)+\text{bound}$; the ergodic averages use iterates
  $1,\dots,k$, not $0,\dots,k-1$. (i) is statable at the pins; (ii) needs the Opial
  argument of 9.12. NASC: `NASC.primalDualHybridGradient_gap_le` (`NASC/Optimization.lean`,
  `sorry`) states (i) for finite-valued convex $g$ and $f^*$, a special case; (ii) is not
  stated.

### Interior-point methods

* **9.14. Self-concordant functions and path following.** Let $E$ be a
  finite-dimensional real vector space and $f$ a closed convex function, three
  times continuously differentiable on its open domain. It is
  **self-concordant** with constant $M_f\ge0$ if
  $$|D^3f(x)[u,u,u]|\le2M_f\bigl(D^2f(x)[u,u]\bigr)^{3/2}\qquad
  (x\in\mathop{\mathrm{dom}}f,\ u\in E),$$
  and **standard** if $M_f=1$. Assume $\nabla^2f(x)$ is positive definite on
  $\mathop{\mathrm{dom}}f$ and $M_f>0$, and write
  $\lambda_f(x)=\langle\nabla f(x),\nabla^2f(x)^{-1}\nabla f(x)\rangle^{1/2}$
  (the **Newton decrement**), $\omega(t)=t-\log(1+t)$ and
  $\omega_*(\tau)=-\tau-\log(1-\tau)$.
  - If $\lambda_f(x)<1/M_f$, then $f$ has a unique minimizer $x_f^*$ and
    $f(x)-f(x_f^*)\le\omega_*(M_f\lambda_f(x))/M_f^2$.
  - The damped Newton step
    $x_{k+1}=x_k-\frac1{1+M_f\lambda_f(x_k)}\nabla^2f(x_k)^{-1}\nabla f(x_k)$
    gives $f(x_{k+1})\le f(x_k)-\omega(M_f\lambda_f(x_k))/M_f^2$.
  - If $\lambda=\lambda_f(x)<1/M_f$ and
    $x_+=x-\nabla^2f(x)^{-1}\nabla f(x)$, then $x_+\in\mathop{\mathrm{dom}}f$ and
    $\lambda_f(x_+)\le M_f\lambda^2/(1-M_f\lambda)^2$. For standard $f$
    this gives $\lambda_f(x_+)<\lambda_f(x)$ whenever
    $0<\lambda_f(x)<(3-\sqrt5)/2$.
  - A standard self-concordant $F$ is a **$\nu$-self-concordant barrier** if
    $\langle\nabla F(x),u\rangle^2\le\nu\langle\nabla^2F(x)u,u\rangle$ for all
    $x\in\mathop{\mathrm{dom}}F$, $u\in E$. Let $Q$, the closure of
    $\mathop{\mathrm{dom}}F$, be bounded, let $c^*=\min_{x\in Q}\langle c,x\rangle$,
    $x^*(t)=\mathop{\mathrm{argmin}}_x\{t\langle c,x\rangle+F(x)\}$ for $t>0$, and
    $\|v\|_x^*=\langle v,\nabla^2F(x)^{-1}v\rangle^{1/2}$. Then
    $\langle c,x^*(t)\rangle-c^*\le\nu/t$, and if
    $\|tc+\nabla F(x)\|_x^*\le\beta<1$, then
    $\langle c,x\rangle-c^*\le\frac1t\bigl(\nu+\frac{(\beta+\sqrt\nu)\beta}{1-\beta}\bigr)$.
  - (Path following.) Let $\tau=0.29$,
    $\beta=\tau^2\bigl(1+\tau+\frac{\tau}{1+\tau+\tau^2}\bigr)\approx0.126$ and
    $\gamma=\tau-\beta\approx0.164$. Start from $t_0=0$ and
    $x_0$ with $\|\nabla F(x_0)\|_{x_0}^*\le\beta$, and iterate
    $t_{k+1}=t_k+\gamma/\|c\|_{x_k}^*$,
    $x_{k+1}=x_k-\frac1{1+\xi_k}\nabla^2F(x_k)^{-1}(t_{k+1}c+\nabla F(x_k))$,
    where $\lambda_k=\|t_{k+1}c+\nabla F(x_k)\|_{x_k}^*$ and
    $\xi_k=\lambda_k^2/(1+\lambda_k)$. Stop as soon as
    $t_k\ge\frac1\varepsilon\bigl(\nu+\frac{(\beta+\sqrt\nu)\beta}{1-\beta}\bigr)$.
    The method stops after
    $N=O\bigl(\sqrt\nu\log(\nu\|c\|_{x_F^*}^*/\varepsilon)\bigr)$ steps, with
    $x_F^*$ the minimizer of $F$, and $\langle c,x_N\rangle-c^*\le\varepsilon$.

  *Assessment.* The derivatives of the objective are already expressible.
  Quantitative control of the local Hessian norm, the Newton decrement and
  central-path progress is the gap.

  *Lean target.* Carriers at the pins: a finite-dimensional real inner-product space,
  `ContDiffOn ℝ 3 f U` on an open convex domain `U`, `iteratedFDeriv ℝ 3`, the Hessian as
  `H x : E ≃L[ℝ] E` with `HasFDerivAt (gradient f) (H x) x`, `Real.log`, `Real.sqrt`. New
  definitions: `IsSelfConcordant M f U`, the Newton decrement
  $\lambda_f(x)=\langle\nabla f(x),H(x)^{-1}\nabla f(x)\rangle^{1/2}$, the dual local norm,
  $\omega$, $\omega_*$, `IsSelfConcordantBarrier ν F U`, the central path $x^*(t)$ and the
  path-following run. Separate theorems: (i) existence of the minimizer and the
  $\omega_*$ bound when $M\lambda<1$; (ii) damped Newton decrease; (iii) the full Newton step
  stays in the domain and $\lambda_f(x_+)\le M\lambda^2/(1-M\lambda)^2$; (iv) the
  central-path gap $\nu/t$ and the approximate-centering bound; (v) the iteration bound of
  path following. Pitfalls: $\omega_*(\tau)=-\tau-\log(1-\tau)$ has `Real.log` of a
  nonpositive number for $\tau\ge1$, so (i) must keep $M\lambda<1$; "closed convex" means
  $f(x)\to\infty$ at the boundary of `U` (closed epigraph of the extension by $+\infty$);
  (v) has an $O(\cdot)$ that should be made explicit (Nesterov's leading constant 6.11) or
  stated with `Asymptotics.IsBigO`. Statable at the pins. NASC:
  `NASC.newton_mem_and_decrement_le_of_selfConcordance` (`NASC/Optimization.lean`, `sorry`)
  states (iii); the rest is not stated.

### Further topics

* **9.17. Linear-quadratic optimal control.** Let $H,U$ be Hilbert spaces,
  $Y,Z$ Banach spaces, $A\in\mathcal L(Y,Z)$ with bounded inverse,
  $B\in\mathcal L(U,Z)$, $Q\in\mathcal L(Y,H)$, $q_d\in H$, $g\in Z$, and
  $\alpha\ge0$. Consider
  $$\min_{(y,u)}\ J(y,u)=\tfrac12\|Qy-q_d\|_H^2+\tfrac\alpha2\|u\|_U^2
  \quad\text{subject to}\quad Ay+Bu=g,\ u\in U_{\mathrm{ad}},\ y\in Y_{\mathrm{ad}}.$$
  - (Existence.) If $U_{\mathrm{ad}}\subseteq U$ is convex and closed, and
    bounded when $\alpha=0$, and $Y_{\mathrm{ad}}\subseteq Y$ is convex and
    closed and the problem has a feasible point, then an optimal pair
    $(\bar y,\bar u)$ exists; it is unique if $\alpha>0$.
  - (Optimality system.) Let $Y_{\mathrm{ad}}=Y$ and let $U_{\mathrm{ad}}$ be
    nonempty, closed and convex. If $(\bar y,\bar u)$ is optimal, there is an
    **adjoint state** $\bar p\in Z^*$ with
    $$A\bar y+B\bar u=g,\qquad A^*\bar p=-Q^*(Q\bar y-q_d),\qquad
    \bar u\in U_{\mathrm{ad}},\ \ (\alpha\bar u+B^*\bar p,u-\bar u)_U\ge0
    \ \ (u\in U_{\mathrm{ad}}),$$
    with $U^*$ identified with $U$. Since the reduced objective
    $u\mapsto J(y(u),u)$ is convex, these conditions are also sufficient.
    For $U=L^2(\Omega)$, $U_{\mathrm{ad}}=\{u:a\le u\le b\text{ a.e.}\}$ with
    $a\le b$ in $L^2(\Omega)$, and $\alpha>0$, the variational inequality is
    equivalent to $\bar u=\min\bigl(\max(a,-\alpha^{-1}B^*\bar p),b\bigr)$
    pointwise a.e.

  *Assessment.* Bounded inverses, adjoints and weak compactness are available. The
  existence of optimal controls, the adjoint-based optimality system and the projection
  formula for box constraints are the selected content.

  *Lean target.* Carriers at the pins: real Hilbert spaces `H`, `U`, real Banach spaces
  `Y`, `Z`, continuous linear maps `A : Y →L[ℝ] Z` (with `A` a `ContinuousLinearEquiv` for
  the bounded inverse), `B`, `Q`, `ContinuousLinearMap.adjoint` on Hilbert spaces and
  `StrongDual ℝ Z` for the adjoint state, with $A^*p=p\circ A$ written as `p.comp A`, closed
  convex sets, `IsMinOn`. New definitions: the reduced objective $u\mapsto J(A^{-1}(g-Bu),u)$
  and the feasible set. Conjuncts: (i) existence of an optimal pair under the stated
  closedness, convexity and (for $\alpha=0$) boundedness, uniqueness for $\alpha>0$; (ii) the
  optimality system with $\bar p\in Z^*$ when $Y_{\mathrm{ad}}=Y$; (iii) sufficiency; (iv) for
  $U=L^2(\Omega)$ and box constraints, the pointwise projection formula. Pitfalls: (i) uses
  weak compactness of bounded closed convex sets in the Hilbert space `U`; Mathlib has
  Banach–Alaoglu (`WeakDual.isCompact_closedBall`), transported by
  `InnerProductSpace.toDual`; (iv) needs `MeasureTheory.Lp`
  with a.e. order and the identification $U^*=U$ by `InnerProductSpace.toDual`. (i)–(iii)
  are statable at the pins; (iv) is statable with `Lp ℝ 2 μ`. NASC: no declaration.

## 10. Polynomial and rational approximation

[Synopsis](SYNOPSIS.md#10-polynomial-and-rational-approximation) · [Coverage inventory](STRUCTURE.md#10-polynomial-and-rational-approximation)

Uniform polynomial density, finite-node interpolation and the Chebyshev
extremal polynomial API provide the main ingredients for quantitative
approximation.

Unless stated otherwise, $C[a,b]$ is the space of real
continuous functions on a compact interval $[a,b]$ with $a<b$, and
$\|g\|=\max_{a\le x\le b}|g(x)|$ is the supremum norm on that interval. For
$f\in C[a,b]$ and $n\in\mathbb N_0$, the **best approximation error** is
$$E_n(f)=\inf_{p\in\mathbb P_n}\|f-p\|,$$
where $\mathbb P_n$ consists of the real polynomials of degree at most $n$.
A function $g\in C[a,b]$ **equioscillates between $k$ extreme points** if
there are $a\le x_1<\cdots<x_k\le b$ and $\sigma\in\{1,-1\}$ such that
$g(x_j)=\sigma(-1)^j\|g\|$ for $j=1,\dots,k$. The **Chebyshev polynomial**
$T_n$ is the polynomial with $T_n(\cos\theta)=\cos n\theta$; equivalently
$T_0=1$, $T_1(x)=x$ and $T_{k+1}(x)=2xT_k(x)-T_{k-1}(x)$ for $k\ge1$. The
**Chebyshev points** of degree $n\ge1$ are $x_j=\cos(j\pi/n)$, $0\le j\le n$.

### Best uniform approximation

* **10.2. Haar spaces.** Let $K$ be a Hausdorff topological space (for
  instance a subset of $\mathbb R^d$) containing at least $N$ points and
  let $V$ be an $N$-dimensional space of real continuous functions on $K$.
  The space $V$ is a **Haar space** (or Chebyshev space) if for all distinct
  $x_1,\dots,x_N\in K$ and all $f_1,\dots,f_N\in\mathbb R$ there is exactly
  one $v\in V$ with $v(x_i)=f_i$ for all $i$. The following are equivalent:
  $V$ is a Haar space; every $v\in V\setminus\{0\}$ has at most $N-1$ zeros in
  $K$; for some (equivalently, every) basis $v_1,\dots,v_N$ of $V$ and all
  distinct $x_1,\dots,x_N\in K$ one has $\det\bigl(v_j(x_i)\bigr)\ne0$.
  - The space $\mathbb P_{N-1}$ is a Haar space on every subset of
    $\mathbb R$ with at least $N$ points.
  - (Mairhuber–Curtis) If $K\subseteq\mathbb R^d$ with $d\ge2$ has an interior
    point, then there is no Haar space on $K$ of dimension $N\ge2$.
  - (Alternation theorem) Let $V\subseteq C[a,b]$ be a Haar space of dimension
    $n+1$ on $[a,b]$ and $f\in C[a,b]$. An element $v\in V$ satisfies
    $\|f-v\|=\inf_{w\in V}\|f-w\|$ if and only if $f-v$ equioscillates between
    at least $n+2$ extreme points. The best approximation from $V$ is unique.
  - (Haar's theorem) Let $K$ be a compact Hausdorff space with at least $N$
    points and $V\subseteq C(K)$ a subspace of finite dimension $N\ge1$.
    Every $f\in C(K)$ has a unique best
    approximation from $V$ in the supremum norm if and only if $V$ is a Haar
    space on $K$.

  *Assessment.* Partly covered. Mathlib proves Lagrange interpolation over a
  field: for distinct real nodes the interpolant has degree below the number
  of nodes and is the unique such polynomial, and the Vandermonde determinant
  of distinct nodes is nonzero. This is the first bullet. The equivalence of
  unisolvence, zero counts and nonvanishing determinants for a general
  finite-dimensional space, the Mairhuber–Curtis theorem, the alternation
  theorem for Haar spaces and Haar's theorem are missing; the nearest-point
  theorem of Mathlib is stated for proper ambient spaces, which $C(K)$ is not.

  *Scope.* The target is the three-way equivalence for a general
  $N$-dimensional space, the Mairhuber–Curtis theorem, the alternation theorem
  for a Haar space on $[a,b]$, and Haar's theorem.

  *Lean target.* Carriers at the pins: `ContinuousMap` (`C(K, ℝ)`) with
  `Submodule ℝ C(K, ℝ)`, `Module.finrank`, `Matrix.det` of `Matrix.of fun i j ↦ v j (x i)`,
  `Matrix.det_vandermonde_ne_zero_iff`, `Lagrange.interpolate`, `Lagrange.eq_interpolate`,
  `Polynomial.degreeLT`, `Polynomial.toContinuousMapOn`, and `Metric.infDist` for the
  distance to `V` in the sup norm of `C(K, ℝ)` (which needs `[CompactSpace K]`). New
  definitions: `NASC.IsHaarSpace V N`, a predicate on a submodule `V` of `C(K, ℝ)` and a
  dimension `N : ℕ` (unique interpolation of arbitrary data at every injective
  `x : Fin N → K`), and an equioscillation predicate on `g : ℝ → ℝ`, `a b : ℝ` and `k : ℕ`
  asserting a `StrictMono` family `x : Fin k → ℝ` in `Set.Icc a b` with
  `g (x j) = σ * (-1) ^ j * ‖g‖` for some `σ ∈ {1, -1}`. Conjuncts, each with
  `[FiniteDimensional ℝ V]`, `Module.finrank ℝ V = N` and at least $N$ points in `K`
  (`N ≤ Nat.card K` with `Finite K` or `Infinite K`): (i) `IsHaarSpace V N` iff no nonzero
  `v ∈ V` vanishes at `N` distinct points; (ii) for every basis `b : Basis (Fin N) ℝ V`,
  `IsHaarSpace V N` iff the collocation determinant is nonzero for every injective `x`;
  (iii) the polynomial restrictions of degree below `N` form a Haar space on every
  `s : Set ℝ` with `N ≤ s.ncard` or `s.Infinite`; (iv) Mairhuber–Curtis for `K` a subset of
  `EuclideanSpace ℝ (Fin d)` with `2 ≤ d`, `(interior K).Nonempty` and `2 ≤ N`; (v) the
  alternation theorem for a Haar space of dimension `n + 1` in `C(Set.Icc a b, ℝ)` with
  `a < b`, and uniqueness; (vi) Haar's theorem for `[CompactSpace K] [T2Space K]`. Pitfalls:
  the space must carry its own sup norm; an unrestricted `ℝ → ℝ` with `⨆` gives `0` on
  unbounded error sets, so the norm is that of `C(K, ℝ)` or of a restriction to a compact
  interval. All conjuncts are statable at the pins; (iv) needs a connectedness argument on
  the configuration space of $N$ points (the swap of two points along a path in the
  interior) that no library provides, and (v) and (vi) need the strong-unicity argument.
  Dependency: (v) specializes to 10.3. NASC: `NASC.IsHaarSpace` with
  `NASC.isHaarSpace_iff_forall_eq_zero`, proved; it is conjunct (i) only.

* **10.3. Chebyshev equioscillation theorem.** Let $n\in\mathbb N_0$.
  - Every $f\in C[a,b]$ has a unique best approximation $p^*\in\mathbb P_n$,
    and $p\in\mathbb P_n$ equals $p^*$ if and only if $f-p$ equioscillates
    between at least $n+2$ extreme points. The same existence and uniqueness
    hold for a complex-valued continuous $f$ on $[-1,1]$ and complex
    polynomials of degree at most $n$.
  - Every continuous $2\pi$-periodic $g$ has a unique best approximation, in
    the supremum norm on $\mathbb R$, among the real trigonometric polynomials
    of degree at most $n$.
  - (de la Vallée Poussin) Let $f\in C[a,b]$, $q\in\mathbb P_n$ and
    $a\le x_0<x_1<\cdots<x_{n+1}\le b$, and suppose that
    $f(x_j)-q(x_j)=(-1)^je_j$ for $j=0,\dots,n+1$, where all $e_j$ are nonzero
    and have the same sign. Then
    $$\min_{0\le j\le n+1}|e_j|\le E_n(f)\le\|f-q\|.$$

  *Assessment.* Mathlib proves the Weierstrass theorem, density of the
  trigonometric polynomials and the Chebyshev extremal property of $T_n$ in
  the leading-coefficient form. Existence of a best approximation from a
  finite-dimensional subspace of $C[a,b]$, uniqueness, the alternation
  characterization, the complex and trigonometric cases and the de la Vallée
  Poussin bound are missing.

  *Lean target.* Carriers at the pins: `Polynomial.degreeLE ℝ n` (or `natDegree ≤ n`),
  `Polynomial.eval`, `C(Set.Icc a b, ℝ)` with its sup norm, `Polynomial.toContinuousMapOn`,
  `Metric.infDist`, `fourier` on `AddCircle (2 * π)` for the trigonometric case and
  `Polynomial.Chebyshev.T`. New definitions: the best error `E n f : ℝ` as `Metric.infDist`
  of `f` to the image of `Polynomial.degreeLE ℝ n` in `C(Set.Icc a b, ℝ)`, and a real
  trigonometric-polynomial submodule of `C(AddCircle (2 * π), ℝ)` of degree at most `n`.
  Conjuncts, all with `a < b` and `f` continuous on `Set.Icc a b`: (i) existence of a
  minimizer; (ii) `p` with `p.natDegree ≤ n` is a minimizer iff `f - p` equioscillates at
  `n + 2` points, as a `StrictMono` `x : Fin (n + 2) → ℝ` in `Set.Icc a b`; (iii) uniqueness
  of the minimizer as a polynomial; (iv) the complex case on `Set.Icc (-1) 1` with complex
  polynomials, existence and uniqueness only; (v) the trigonometric case; (vi) de la Vallée
  Poussin with `StrictMono` nodes in `Set.Icc a b`, all `e j ≠ 0` of one sign, giving
  `⨅ j, |e j| ≤ E n f ≤ ‖f - q‖`. Pitfalls: `NASC.intervalError` is an `sSup` of
  `|f x|` over `Set.Icc a b`, which is `0` for an unbounded image, so the continuity
  hypothesis is essential; for `n + 2` points the equioscillation index runs from `0`.
  Statable at the pins; existence needs local compactness of the finite-dimensional
  subspace, available through `FiniteDimensional.proper` for the subspace, not for the
  ambient space. Dependency: 10.2 (v) gives (ii) and (iii) once (iii) of 10.2 is in place.
  NASC: `NASC.forall_intervalError_le_iff_exists_alternation`, `sorry`; it is conjunct (ii) only,
  with `intervalError` and continuity on `Set.Icc a b`.

### Polynomial interpolation

* **10.5. Lagrange interpolation and its error.** For distinct real nodes
  $x_0,\dots,x_n$ and values $f_0,\dots,f_n$ there is exactly one
  $p\in\mathbb P_n$ with $p(x_i)=f_i$ for all $i$, namely
  $p=\sum_{i=0}^nf_i\ell_i$ with the **Lagrange polynomials**
  $\ell_i(x)=\prod_{j\ne i}(x-x_j)/(x_i-x_j)$. Write $p_n(f;\cdot)$ when
  $f_i=f(x_i)$, and let $\omega_{n+1}(x)=\prod_{i=0}^n(x-x_i)$. Let $x$ be
  real, let $I$ be the smallest closed interval containing $x,x_0,\dots,x_n$,
  and let $f$ be $n+1$ times differentiable on $I$. Then there is $\xi\in I$
  with
  $$f(x)-p_n(f;x)=\frac{f^{(n+1)}(\xi)}{(n+1)!}\,\omega_{n+1}(x).$$
  If $f\in C^{n+1}[-1,1]$ and the nodes are the zeros of $T_{n+1}$, then
  $$\|f-p_n(f;\cdot)\|\le\frac{\|f^{(n+1)}\|}{2^n\,(n+1)!}.$$

  *Assessment.* Partly covered. Mathlib proves the Lagrange construction,
  uniqueness and evaluation at the nodes. The selected results are the
  derivative remainder and the sharp nodal-product bound at Chebyshev nodes.

  *Scope.* The selected claims are the derivative remainder for interpolation
  at arbitrary distinct real nodes and the bound
  $\|f^{(n+1)}\|/(2^n(n+1)!)$ for the zeros of $T_{n+1}$.

  *Lean target.* Carriers at the pins: `Lagrange.interpolate`, `Lagrange.nodal`,
  `Lagrange.eval_interpolate_at_node`, `Lagrange.degree_interpolate_lt`,
  `iteratedDerivWithin` on `Set.uIcc`-style intervals, `ContDiffOn`, `Polynomial.Chebyshev.T`
  with `Polynomial.Chebyshev.roots_T_real` and `Polynomial.Chebyshev.leadingCoeff_T`.
  No new definition is needed. Conjuncts: (i) for an injective `nodes : Fin (n + 1) → ℝ`,
  `x : ℝ`, and `f` that is `n + 1` times differentiable on the convex hull `I` of `x` and the
  nodes (`ContDiffOn ℝ (n + 1) f I` is a sufficient strengthening; the source asks only for
  existence of the derivatives, which needs `iteratedDerivWithin` and a Rolle argument on
  `I`), there is `ξ ∈ I` with the remainder identity; (ii) for `ContDiffOn ℝ (n + 1) f
  (Set.Icc (-1) 1)` and nodes the zeros of `T (n + 1)`, the sup bound with the
  sup of `|iteratedDerivWithin (n + 1) f (Set.Icc (-1) 1)|`. Pitfalls: the degenerate
  interval when all nodes and `x` coincide needs `n = 0`; the sup must be over a compact set
  where the derivative is continuous. Statable and provable at the pins; (ii) uses
  10.4, the identity $\omega_{n+1}=2^{-n}T_{n+1}$ for the Chebyshev zeros and
  $|T_{n+1}|\le1$. NASC: `NASC.exists_lagrange_remainder`, proved, for `n` nodes and the
  `n`-th derivative (the index shift is harmless) under the stronger hypothesis
  `ContDiff ℝ n f` on all of `ℝ`, with any `Set.Icc a b` containing the nodes and `x`;
  (ii) has no NASC declaration.

* **10.7. Growth of Lebesgue constants and Faber's theorem.** Let
  $[a,b]=[-1,1]$.
  - For every $n\in\mathbb N_0$ and every set of $n+1$ distinct nodes in
    $[-1,1]$,
    $$\Lambda_n\ge\frac2\pi\log(n+1)+\frac2\pi\Bigl(\gamma+\log\frac4\pi\Bigr),
    \qquad\frac2\pi\Bigl(\gamma+\log\frac4\pi\Bigr)=0.52125\ldots,$$
    where $\gamma$ is Euler's constant.
  - For the Chebyshev points, $\Lambda_n\le\frac2\pi\log(n+1)+1$ for $n\ge1$,
    and $\Lambda_n\sim\frac2\pi\log n$ as $n\to\infty$. The same upper bound
    holds for the zeros of $T_{n+1}$.
  - For the equispaced nodes $x_j=-1+2j/n$, $0\le j\le n$, one has
    $\Lambda_n>2^{n-2}/n^2$ for $n\ge1$ and
    $\Lambda_n\sim2^{n+1}/(e\,n\log n)$ as $n\to\infty$.
  - With $f_n$ the degree-$n$ truncation of the Chebyshev series (see 10.10)
    and $p_n$ the interpolant in the Chebyshev points, for every
    $f\in C[-1,1]$ and $n\ge1$,
    $$\|f-p_n\|\le\Bigl(2+\frac2\pi\log(n+1)\Bigr)E_n(f),\qquad
    \|f-f_n\|\le\Bigl(4+\frac4{\pi^2}\log(n+1)\Bigr)E_n(f).$$
  - (Faber) For every triangular array of nodes, with $n+1$ distinct nodes
    $x_0^{(n)},\dots,x_n^{(n)}\in[a,b]$ in row $n$, there is $f\in C[a,b]$
    such that the interpolants $p_n(f;\cdot)$ in the nodes of row $n$ do not
    converge to $f$ uniformly on $[a,b]$. Equivalently, by the uniform
    boundedness principle, $\sup_n\Lambda_n=\infty$ for every such array.

  *Assessment.* Mathlib proves the uniform boundedness principle and the
  algebra of Lagrange interpolation. The Lebesgue function and constant, the
  logarithmic lower bound for all node sets, the upper bounds and asymptotics
  for Chebyshev and equispaced nodes, the near-best constants and Faber's
  theorem are missing.

  *Lean target.* Carriers at the pins: `Lagrange.basis` and `Lagrange.interpolate`,
  `Real.eulerMascheroniConstant`, `Real.log`, `Asymptotics.IsEquivalent` for `∼`,
  `banach_steinhaus`, `C(Set.Icc a b, ℝ)` with its norm, and `Polynomial.Chebyshev.T`.
  New definitions: the Lebesgue function `lebesgueFun nodes x : ℝ` as
  `∑ i, |(Lagrange.basis univ nodes i).eval x|` for `nodes : Fin (n + 1) → ℝ`, the Lebesgue
  constant `lebesgueConst nodes : ℝ` as its maximum on `Set.Icc (-1) 1` (an `sSup` of a
  continuous image of a compact set, nonempty), the Chebyshev and equispaced node families,
  and the Chebyshev truncation `f_n` of 10.10. Conjuncts, each with injective nodes in
  `Set.Icc (-1) 1`: (i) the lower bound for every `n` and every node set; (ii) the Chebyshev
  upper bound for `1 ≤ n` and its asymptotics, and the same upper bound for the zeros of
  `T (n + 1)`; (iii) the equispaced lower bound for `1 ≤ n` and the asymptotics
  $2^{n+1}/(en\log n)$; (iv) the two near-best inequalities with `E n f` from 10.3;
  (v) Faber: for every family `nodes : ∀ n, Fin (n + 1) → ℝ` of injective maps into
  `Set.Icc a b` with `a < b` there is a continuous `f` whose interpolants do not converge
  uniformly, and equivalently the Lebesgue constants are unbounded. Pitfalls: `Real.log`
  at `n + 1` avoids `log 0`; in the asymptotics `log n` is `0` at `n = 1`, so use
  `Filter.atTop`. Statable at the pins; (i) needs the Erdős–Brutman lower-bound argument
  and (iii) the explicit asymptotics, both without library support. Dependencies: 10.3 for
  `E n f`, 10.6 for $\|P_n\|=\Lambda_n$, 10.10 for (iv). NASC:
  `NASC.exists_not_tendsto_uniform_lagrange`, `sorry`; it is the first half of (v), with
  `NASC.intervalError` as the uniform error.

### Rates of polynomial approximation

* **10.8. Jackson theorems.** Let $k\in\mathbb N_0$, $\alpha\in(0,1]$ and
  $c=1+\pi^2/2$.
  - Let $g$ be $2\pi$-periodic and $k$ times continuously differentiable, with
    $|g^{(k)}(\theta_1)-g^{(k)}(\theta_2)|\le M_k|\theta_1-\theta_2|^\alpha$
    for all real $\theta_1,\theta_2$. For $n\ge1$ the best approximation
    $q_n$ of $g$ among the real trigonometric polynomials of degree at most
    $n$ satisfies
    $$\max_{\theta\in\mathbb R}|g(\theta)-q_n(\theta)|\le c^{k+1}\frac{M_k}{n^{k+\alpha}}.$$
  - Let $f\in C^k[-1,1]$ with
    $|f^{(k)}(x_1)-f^{(k)}(x_2)|\le M_k|x_1-x_2|^\alpha$ on $[-1,1]$. For
    $n>k$,
    $$E_n(f)\le d_k\,c^{k+1}\frac{M_k}{n^{k+\alpha}},\qquad\text{for any }
    d_k\ge\frac{n^{k+\alpha}}{n(n-1)\cdots(n-k+1)(n-k)^\alpha}.$$
  - (Favard-type constant) Let $S_N$ be the span of $e^{ikx}$,
    $-N\le k<N$, with $N\ge1$. If $u$ is $2\pi$-periodic, $m\in\mathbb N_0$,
    and $u^{(m)}\in L^\infty(0,2\pi)$ as a periodic distribution, then
    $$\inf_{\varphi\in S_N}\|u-\varphi\|_{L^\infty(0,2\pi)}\le\frac\pi2N^{-m}
    \|u^{(m)}\|_{L^\infty(0,2\pi)}.$$

  *Assessment.* The density theorems do not specify a rate. The selected
  estimates quantify polynomial approximation by the stated smoothness or
  modulus.

  *Lean target.* Carriers at the pins: `HolderOnWith` (exponent of type `ℝ≥0`),
  `iteratedDerivWithin`, `ContDiffOn`, `fourier` and `fourierCoeff` on `AddCircle (2 * π)`,
  `MeasureTheory.Lp` and `eLpNorm` with `p = ∞` on `AddCircle.haarAddCircle` or on
  `volume.restrict (Set.Ioc 0 (2 * π))`, and `Polynomial.degreeLE`. New definitions: the
  real trigonometric polynomials of degree at most `n` as a submodule of `C(ℝ, ℝ)` of
  `2π`-periodic functions (`Function.Periodic`), and the space $S_N$ as the span of
  `fourier k` for `-N ≤ k < N`. Conjuncts: (i) for `g : ℝ → ℝ` periodic,
  `ContDiff ℝ k g` and the Hölder bound on `iteratedDeriv k g`, with `1 ≤ n`, there is a
  trigonometric polynomial of degree at most `n` with sup error at most
  `c ^ (k + 1) * M / n ^ (k + α)`; (ii) for `ContDiffOn ℝ k f (Set.Icc (-1) 1)` with the
  Hölder bound on `iteratedDerivWithin k f (Set.Icc (-1) 1)` and `k < n`, there is `p` with
  `p.natDegree ≤ n` and the stated bound; (iii) the Favard-type bound for `u` periodic with
  `iteratedDeriv m u` (or a distributional derivative) essentially bounded, and `1 ≤ N`.
  Pitfalls: natural subtraction in `n - j` is safe only under `k < n`; `n ^ (k + α)` is a
  real power `Real.rpow` with a positive base; stating the bound for some approximant
  rather than for the best one avoids the existence question of 10.3. (i) and (ii) are
  statable at the pins; (iii) needs weak derivatives of periodic functions, which TauCeti
  provides only through its circle Sobolev spaces, so a classical `ContDiff` version is the
  statable form. Dependency: (ii) follows from (i) by $x=\cos\theta$. NASC:
  `NASC.exists_polynomial_uniform_error_le_jackson`, `sorry`; it is (ii) with
  `ContDiff ℝ k f` on all of `ℝ` and the minimal admissible `d_k`.

* **10.9. Bernstein inequality and inverse theorems.**
  - (Bernstein inequality) For $N\ge1$, $1\le p\le\infty$, $r\in\mathbb N$
    and every $\varphi\in S_N$ (as in 10.8),
    $\|\varphi^{(r)}\|_{L^p(0,2\pi)}\le N^r\|\varphi\|_{L^p(0,2\pi)}$.
  - (Bernstein inverse theorem) Let $g$ be continuous and $2\pi$-periodic, let
    $r\in\mathbb N_0$ and $0<\alpha<1$, and suppose that for all $n\ge1$ the
    best uniform approximation of $g$ by real trigonometric polynomials of
    degree at most $n$ has error at most $Mn^{-r-\alpha}$. Then $g\in C^r$ and
    $g^{(r)}$ is Hölder continuous with exponent $\alpha$. The statement fails
    for $\alpha=1$.
  - (Converse for analytic functions) If $f$ is a function on $[-1,1]$ and
    there are $C>0$, $\rho>1$ and polynomials $q_n\in\mathbb P_n$ with
    $\|f-q_n\|\le C\rho^{-n}$ for all $n\ge0$, then $f$ extends to an analytic
    function in the open Bernstein ellipse $E_\rho$ (defined in 10.11).

  *Assessment.* Mathlib bounds the iterated derivatives at points $x\ge1$ of a
  polynomial bounded by one on $[-1,1]$, an endpoint form of Markov's
  inequality. The Bernstein inequality for trigonometric polynomials in
  $L^p$, the Bernstein inverse theorem and the analytic converse are missing.

  *Lean target.* Carriers at the pins: `fourier`, `eLpNorm` on `AddCircle.haarAddCircle`
  (or `volume.restrict (Set.Ioc 0 (2 * π))`), `deriv` and `iteratedDeriv`, `HolderWith`,
  `AnalyticOnNhd ℂ`, `Polynomial.eval` on `ℂ[X]` and
  `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`. New definitions:
  `NASC.bernsteinEllipse ρ : Set ℂ` (the open ellipse $|z-1|+|z+1|<\rho+\rho^{-1}$) and
  $S_N$ from 10.8. Conjuncts: (i) for `1 ≤ N`, `1 ≤ p` in `ℝ≥0∞` and `r ≥ 1`, the bound
  `eLpNorm (iteratedDeriv r φ) p ≤ N ^ r * eLpNorm φ p` for `φ ∈ S_N`; (ii) for `g`
  continuous and periodic with errors at most `M * n ^ (-(r + α))` for all `1 ≤ n` and
  `0 < α < 1`, `ContDiff ℝ r g` and `HolderWith C α (iteratedDeriv r g)` for some `C`;
  (iii) the counterexample at `α = 1` (a function with $E_n\le M/n$ whose derivative is
  not Lipschitz, for instance a Zygmund-class function); (iv) for `f : ℝ → ℂ`, `1 < ρ`,
  `C > 0` and `q n` of degree at most `n` with
  `‖f x - (q n).eval x‖ ≤ C * ρ ^ (-n)` on `Set.Icc (-1) 1` for all `n`, there is `F`
  analytic on `NASC.bernsteinEllipse ρ` agreeing with `f` there. Pitfalls: `eLpNorm` is
  `ℝ≥0∞`-valued, so (i) is best stated in `ℝ≥0∞` with `ENNReal.ofReal (N ^ r)`. (i), (ii)
  and (iv) are statable at the pins; (iii) needs an explicit lacunary construction.
  Dependencies: (ii) uses (i) on the dyadic blocks $q_{2^{k+1}}-q_{2^k}$, and 10.8 (i) is
  its converse; (iv) uses the Bernstein lemma on the growth of polynomials off $[-1,1]$.
  NASC: `NASC.exists_analyticOnNhd_of_geometric_polyApprox`, `sorry`; it is (iv).

* **10.10. Chebyshev series and functions of bounded variation.** Let
  $[a,b]=[-1,1]$. If $f$ is Lipschitz continuous, then $f$ has a unique
  representation $f=\sum_{k=0}^\infty a_kT_k$, absolutely and uniformly
  convergent on $[-1,1]$, with
  $$a_k=\frac2\pi\int_{-1}^1\frac{f(x)T_k(x)}{\sqrt{1-x^2}}\,dx\quad(k\ge1),$$
  and with $2/\pi$ replaced by $1/\pi$ for $k=0$. The **Chebyshev projection**
  is $f_n=\sum_{k=0}^na_kT_k$, and the **Chebyshev interpolant** $p_n$ is the
  interpolant in the Chebyshev points. Let $\nu\in\mathbb N_0$, let
  $f,f',\dots,f^{(\nu-1)}$ be absolutely continuous on $[-1,1]$, and let
  $f^{(\nu)}$ have bounded variation $V$. Then for $k\ge\nu+1$
  $$|a_k|\le\frac{2V}{\pi k(k-1)\cdots(k-\nu)}\le\frac{2V}{\pi(k-\nu)^{\nu+1}}.$$
  If moreover $\nu\ge1$, then for every $n>\nu$
  $$\|f-f_n\|\le\frac{2V}{\pi\nu(n-\nu)^\nu},\qquad
  \|f-p_n\|\le\frac{4V}{\pi\nu(n-\nu)^\nu}.$$

  *Assessment.* Mathlib proves the orthogonality of the Chebyshev polynomials
  for the measure $(1-x^2)^{-1/2}dx$ on $(-1,1]$ and has bounded variation and
  absolute continuity on intervals. TauCeti proves that the normalized
  Chebyshev polynomials form a Hilbert basis of $L^2$ of that measure, with
  Parseval's identity and $L^2$ convergence of the expansion. Absolute and
  uniform convergence for Lipschitz $f$, the coefficient bound for
  derivatives of bounded variation, and the uniform error bounds for the
  projection and the interpolant are missing.

  *Lean target.* Carriers at the pins: `Polynomial.Chebyshev.T` (indexed by `ℤ`),
  `Polynomial.Chebyshev.measureT` with `Polynomial.Chebyshev.integral_measureT`,
  `LipschitzOnWith`, `AbsolutelyContinuousOnInterval`, `eVariationOn` (valued in `ℝ≥0∞`),
  `iteratedDerivWithin`, `HasSum` and `TendstoUniformlyOn`, and
  `TauCeti.chebyshevTHilbertBasis` with `TauCeti.hasSum_chebyshevT_expansion` for the $L^2$
  identification. New definitions: the Chebyshev coefficient `chebCoeff f k : ℝ` as
  `(if k = 0 then 1 else 2) / π * ∫ x, f x * (T ℝ k).eval x ∂measureT`, the projection
  `chebProj f n : ℝ[X]`, and the Chebyshev interpolant at `Real.cos (j * π / n)`.
  Conjuncts: (i) for `LipschitzOnWith K f (Set.Icc (-1) 1)`, `Summable (|chebCoeff f ·|)`
  and the series converges uniformly to `f` on `Set.Icc (-1) 1`, and the coefficients are
  unique among absolutely summable expansions; (ii) for `ν : ℕ`, the derivatives
  `iteratedDerivWithin j f (Set.Icc (-1) 1)` absolutely continuous for `j < ν`, and
  `eVariationOn (iteratedDerivWithin ν f (Set.Icc (-1) 1)) (Set.Icc (-1) 1) = V` finite,
  the coefficient bound for `ν + 1 ≤ k`; (iii) for `1 ≤ ν` and `ν < n` the two uniform
  bounds. Pitfalls: the integrand is not Lebesgue integrable without the weight, so the
  integral must be against `measureT` (a non-integrable integrand gives `0` silently);
  `V` must be finite before `ENNReal.toReal`; the factor `π (k - ν) ^ (ν + 1)` uses natural
  subtraction, safe under `ν + 1 ≤ k`. Statable at the pins; the proof transfers to the
  cosine series of `f (cos θ)` and needs integration by parts against a Stieltjes measure
  of bounded variation, which Mathlib has only for monotone functions. Dependency: (iii)
  for the interpolant uses the aliasing identity of the Chebyshev points. NASC: none.

* **10.11. Analytic functions and Bernstein ellipses.** For $\rho>1$ the
  **open Bernstein ellipse** $E_\rho$ is the open region bounded by the image
  of the circle $|z|=\rho$ under $x=(z+z^{-1})/2$; it has foci $\pm1$ and the
  sum of its semi-axes is $\rho$. Let $f$ be analytic on $[-1,1]$ and
  continue analytically to $E_\rho$, with $|f|\le M$ there. Then the
  Chebyshev coefficients satisfy $|a_0|\le M$ and $|a_k|\le2M\rho^{-k}$ for
  $k\ge1$, and for every $n\ge0$
  $$\|f-f_n\|\le\frac{2M\rho^{-n}}{\rho-1},\qquad
  \|f-p_n\|\le\frac{4M\rho^{-n}}{\rho-1}.$$
  For a singularity at a real point $\pm\alpha$ with $\alpha>1$, the largest
  such ellipse has $\rho=\alpha+\sqrt{\alpha^2-1}$; for a singularity at
  $\pm i\beta$ with $\beta>0$, it has $\rho=\beta+\sqrt{\beta^2+1}$.
  Together with 10.9, a function on $[-1,1]$ admits polynomial approximations
  with error $O(\rho^{-n})$ for some $\rho>1$ if and only if it is analytic on
  $[-1,1]$.

  *Assessment.* Mathlib supplies analytic functions, contour integrals and the
  Chebyshev polynomials as cosines. The Bernstein-ellipse coefficient bound,
  the tail and interpolation bounds, the ellipse parameter of a singularity
  and the characterization of analyticity by geometric rates are missing.

  *Lean target.* Carriers at the pins: `AnalyticOnNhd ℂ`, `intervalIntegral` for the
  coefficient formula $a_k=\frac{2}{\pi}\int_0^\pi f(\cos t)\cos kt\,dt$, `Complex.cos`,
  `Polynomial.Chebyshev.T`, and the Joukowski map `fun z ↦ (z + z⁻¹) / 2`. New definitions:
  `NASC.bernsteinEllipse ρ` and the coefficient and projection of 10.10 extended to complex
  values. Conjuncts, each with `1 < ρ`, `f` analytic on `NASC.bernsteinEllipse ρ` and
  `‖f z‖ ≤ M` there: (i) `‖a 0‖ ≤ M` and `‖a k‖ ≤ 2 * M * ρ ^ (-k)` for `1 ≤ k`; (ii) the
  projection bound $2M\rho^{-n}/(\rho-1)$ and the interpolant bound $4M\rho^{-n}/(\rho-1)$
  on `Set.Icc (-1) 1`; (iii) the ellipse through `α > 1` has parameter
  `α + √(α ^ 2 - 1)` and through `I * β` with `β > 0` has `β + √(β ^ 2 + 1)`; (iv) a
  function on `Set.Icc (-1) 1` has polynomial approximants with error `O(ρ ^ (-n))` for
  some `ρ > 1` iff it is the restriction of a function analytic on a neighbourhood of
  `Set.Icc (-1) 1` in `ℂ`. Pitfalls: the definition of the ellipse by the foci sum is
  equivalent to the Joukowski image for `1 < ρ` only; for `ρ ≤ 1` it is empty or degenerate.
  All conjuncts are statable at the pins; (i) needs the substitution $z=e^{it}$ and a
  contour shift to the circle $|z|=\rho'$ for every $\rho'<\rho$. Dependencies: (ii) uses
  the aliasing identity of 10.10; (iv) uses 10.9 (iv). NASC:
  `NASC.norm_chebyshevCoeff_le_of_analyticOnEllipse`, `sorry`; it is (i), with the
  coefficient written as a cosine integral and `f : ℂ → ℂ`.

### Rational and Padé approximation

* **10.13. Best rational approximation.** For $m,n\in\mathbb N_0$ let
  $R_{mn}$ be the set of rational functions $p/q$ with $p\in\mathbb P_m$,
  $q\in\mathbb P_n$, $q\ne0$ (real or complex coefficients), and
  $R_{mn}^{\mathrm{real}}$ the subset with real coefficients. A nonzero
  $r\in R_{mn}$ written in lowest terms has **exact type** $(\mu,\nu)$, the
  exact degrees of numerator and denominator; its **defect** in $R_{mn}$ is
  $d=\min\{m-\mu,n-\nu\}$, and $r=0$ has defect $n$. Every real
  $f\in C[-1,1]$ has a unique best approximation $r^*\in R_{mn}^{\mathrm{real}}$
  in the supremum norm, and $r\in R_{mn}^{\mathrm{real}}$ equals $r^*$ if and
  only if $f-r$ equioscillates between at least $m+n+2-d$ extreme points,
  where $d$ is the defect of $r$ in $R_{mn}$.

  *Assessment.* Mathlib has rational functions over a field with numerator
  and denominator in lowest terms. Existence of a best rational approximation,
  its uniqueness and the alternation characterization with the defect are
  missing.

  *Lean target.* Carriers at the pins: `RatFunc ℝ` with `RatFunc.num` and `RatFunc.denom`
  (lowest terms, monic denominator), `Polynomial.natDegree`, `IsCoprime`, and
  `C(Set.Icc (-1) 1, ℝ)` with its norm. New definitions: the set `R m n` of real rational
  functions whose numerator has degree at most `m` and denominator at most `n`, the exact
  type and the defect `d : ℕ` (with the convention $d=n$ for $r=0$), and the uniform error
  of `f - r` on `Set.Icc (-1) 1` for `r` whose denominator has no zero there. Conjuncts,
  with `f` continuous on `Set.Icc (-1) 1`: (i) existence of a best `r ∈ R m n` without poles
  in `Set.Icc (-1) 1`; (ii) uniqueness as a rational function; (iii) `r` is best iff
  `f - r` equioscillates at `m + n + 2 - d` points. Pitfalls: evaluating a quotient
  `p.eval x / q.eval x` at a zero of `q` gives `0`, so the error must be taken only over
  pairs whose denominator does not vanish on the interval, or over `RatFunc` in lowest
  terms; `m + n + 2 - d` is natural subtraction, safe because `d ≤ n`. Statable at the pins;
  existence needs a compactness argument on normalized coefficient pairs with control of
  cancelling zeros. Dependency: 10.3 is the case `n = 0`. NASC:
  `NASC.exists_best_rational_uniform` with `NASC.IsRationalPairOn`, `sorry`; it is (i) and
  (ii) on a general `Set.Icc a b`, with uniqueness of values rather than of pairs.

* **10.14. Padé approximants and the Padé table.** Let
  $f(z)=\sum_{k\ge0}c_kz^k$ be a formal power series with complex
  coefficients and let $m,n\in\mathbb N_0$.
  - There are $p\in\mathbb P_m$ and $q\in\mathbb P_n$, $q\ne0$, with
    $p-fq=O(z^{m+n+1})$. All such pairs define the same rational function
    $r_{mn}=p/q$, the type $(m,n)$ **Padé approximant**. In lowest terms
    $r_{mn}=\hat p/\hat q$ with $\hat q(0)\ne0$, and every such pair is
    $(p,q)=(\pi\hat p,\pi\hat q)$ with $\pi$ a polynomial of degree at most
    the defect $d$ of $r_{mn}$ in $R_{mn}$.
  - A function $r\in R_{mn}$ analytic at $0$ equals $r_{mn}$ if and only if
    $f-r=O(z^{m+n+1-d})$, where $d$ is the defect of $r$ in $R_{mn}$.
  - The approximant in the sense of Baker, a quotient $A/B$ with
    $A\in\mathbb P_m$, $B\in\mathbb P_n$, $B(0)=1$ and
    $A/B-f=O(z^{m+n+1})$, exists if and only if $f-r_{mn}=O(z^{m+n+1})$, and
    then it equals $r_{mn}$. It exists when the Hankel determinant
    $C(m/n)=\det\bigl(c_{m-n+i+j-1}\bigr)_{i,j=1}^n$ is nonzero, where
    $c_k=0$ for $k<0$ and $C(m/0)=1$.
  - (Block structure) Let $r\ne0$ be an entry of the Padé table, of exact
    type $(\lambda,\mu)$, and suppose that $f\ne r$, with
    $f-r=cz^{\lambda+\mu+k+1}+O(z^{\lambda+\mu+k+2})$ for some $c\ne0$ and
    $k\in\mathbb N_0$. Then $r_{mn}=r$ exactly for
    $\lambda\le m\le\lambda+k$ and $\mu\le n\le\mu+k$, and within this
    square block the Baker approximant exists exactly when
    $m+n\le\lambda+\mu+k$. If $f$ is itself a rational function of exact type
    $(\lambda,\mu)$, then $r_{mn}=f$ for all $m\ge\lambda$ and $n\ge\mu$.

  *Assessment.* Mathlib supplies formal power series with truncation and
  order, polynomials and rational functions, and determinants. Existence of
  Padé pairs, uniqueness of the approximant, the lowest-terms description, the
  Baker criterion with the Hankel determinant and the block structure of the
  Padé table are missing.

  *Lean target.* Carriers at the pins: `PowerSeries ℂ` with `PowerSeries.coeff`,
  `PowerSeries.trunc`, `PowerSeries.order` (valued in `ℕ∞`) and `PowerSeries.X_pow_dvd_iff`,
  `Polynomial` coerced to `PowerSeries`, `RatFunc ℂ` with `RatFunc.num` and `RatFunc.denom`, and
  `Matrix.det`. New definitions: `NASC.IsPadePair c m n p q`, a predicate on a coefficient sequence
  `c : ℕ → ℂ` and `p q : ℂ[X]` (degree bounds, `q ≠ 0`, and the convolution identity up to index
  `m + n`, equivalently `X ^ (m + n + 1) ∣ (p : ℂ⟦X⟧) - f * q`); the Padé approximant
  `pade c m n : RatFunc ℂ`; the defect; the Baker predicate with `q.eval 0 = 1`; and the Hankel
  matrix `Matrix (Fin n) (Fin n) ℂ` with entries `c (m - n + i + j + 1)` where the index is an
  integer and negative indices give `0`. Conjuncts: (i) existence of a pair; (ii) all pairs give the
  same `RatFunc`; (iii) the lowest-terms factorization with a common factor of degree at most the
  defect; (iv) the characterization by `order` with the defect; (v) the Baker approximant exists iff
  the order condition holds for `pade c m n`, and it exists when the Hankel determinant is nonzero;
  (vi) the block structure for a nonzero entry of exact type `(λ, μ)` with `f - r` of exact order
  `λ + μ + k + 1`; (vii) a rational `f` of exact type `(λ, μ)` is its own approximant for `λ ≤ m`
  and `μ ≤ n`. Pitfalls: the Hankel indices need integer arithmetic (natural subtraction in `m - n`
  silently gives `0`); `PowerSeries.order` is `⊤` for `0`. All conjuncts are statable at the pins
  and need only linear algebra; (vi) is the longest. Dependency: 10.15 and 10.16 use (v). NASC:
  `NASC.exists_padePair_and_eq_cross` with `NASC.IsPadePair` (over any field), `sorry`; it is (i)
  and (ii), with equality stated by cross-multiplication `p * Q = P * q`.

* **10.15. Theorem of de Montessus de Ballore.** Let $R>0$ and let $f$ be
  meromorphic in the closed disk $|z|\le R$, with poles exactly at the
  distinct points $z_1,\dots,z_m$, where $0<|z_1|\le\cdots\le|z_m|<R$, of
  multiplicities $\mu_1,\dots,\mu_m$ with $\sum_k\mu_k=M$. Then for all
  sufficiently large $L$ the Padé approximant $[L/M]$ (in the sense of Baker)
  of the Maclaurin series of $f$ exists, and
  $$[L/M]\to f\qquad(L\to\infty)$$
  uniformly on every compact subset of $\{z:|z|\le R\}\setminus\{z_1,\dots,z_m\}$.

  *Assessment.* Mathlib supplies meromorphic functions, uniform convergence on
  sets and the Cauchy integral formula. The convergence of a Padé row with
  fixed denominator degree for a function with poles of prescribed total
  multiplicity is missing.

  *Lean target.* Carriers at the pins: `MeromorphicOn`, `AnalyticOnNhd ℂ`,
  `Metric.closedBall`, `TendstoUniformlyOn`, `IsCompact`, `Polynomial.roots` with
  multiplicities, and `iteratedDeriv k f 0 / k !` for the Maclaurin coefficients. New
  definitions: the Baker approximant of 10.14. Conjuncts, with `0 < R`, a polynomial `Q`
  with `Q.eval 0 ≠ 0`, all roots in the open disk of radius `R`, `Q.natDegree = M`,
  `H` analytic on `Metric.closedBall 0 R` and nonzero at the roots of `Q`, and
  `f = H / Q` off the roots: (i) for all large `L` the Baker approximant of type `(L, M)`
  exists; (ii) it converges to `f` uniformly on every compact subset of the closed disk
  avoiding the roots. Pitfalls: `f z = H z / Q.eval z` is junk `0` at the roots, so the
  hypothesis must exclude them; the Maclaurin coefficients must be those of `H / Q` near
  `0`, which is analytic there because `Q.eval 0 ≠ 0`. Statable at the pins; the proof
  needs the Hadamard-type estimate for the Padé denominators, which no library has.
  Dependency: 10.14 (v). NASC: `NASC.exists_pade_row_tendstoUniformlyOn`, `sorry`; it is
  (i) and (ii), with the pole data encoded by `Q` and `H`.

* **10.16. Stieltjes series.** Let $\varphi$ be a bounded nondecreasing
  function on $[0,\infty)$ that takes infinitely many values and has finite
  moments $f_j=\int_0^\infty u^j\,d\varphi(u)$ for all $j\in\mathbb N_0$. The
  **Stieltjes function**
  $$f(z)=\int_0^\infty\frac{d\varphi(u)}{1+zu}$$
  is analytic in $\mathbb C\setminus(-\infty,0]$ and has the formal
  expansion $\sum_{j\ge0}f_j(-z)^j$, its **Stieltjes series**. For the Padé
  approximants $[L/M]$ of this series:
  - every $[L/M]$ with $L\ge M-1$ exists;
  - for fixed $J\ge-1$, the poles of $[M+J/M]$ are simple, lie on the
    negative real axis, and have positive residues;
  - for fixed $J\ge-1$, the sequence $[M+J/M]$ converges as $M\to\infty$,
    uniformly on every bounded set at positive distance from $(-\infty,0]$,
    to a function analytic in $\mathbb C\setminus(-\infty,0]$;
  - if the series has radius of convergence $R>0$, then for every $J\ge-1$
    the limit is $f$, and the poles of $[M+J/M]$ lie in $(-\infty,-R)$;
  - if $\sum_{j\ge1}f_j^{-1/(2j)}=\infty$ (Carleman's condition), then for
    every $J\ge-1$ the limit is $f$.

  *Assessment.* TauCeti proves that a Stieltjes function
  $a/w+b+\int(w+x)^{-1}d\mu(x)$ has a holomorphic extension to the slit
  plane; the function of 10.16 is $w\,S(w)$ for such an $S$ with $a=b=0$ and
  $w=1/z$. Moment sequences, the existence of the Padé approximants, the
  location of their poles and residues, and their convergence under the
  radius or Carleman condition are missing.

  *Lean target.* Carriers at the pins: a finite measure `μ` on `ℝ` with
  `∀ᵐ x ∂μ, 0 ≤ x` (in place of $d\varphi$), `MeasureTheory.integral`, `Integrable` of
  `fun x ↦ x ^ k`, `Complex.slitPlane`, `TauCeti.stieltjesExtension` (on `Measure ℝ≥0`)
  with `TauCeti.analyticOnNhd_stieltjesExtension`, `TendstoUniformlyOn`, and
  `Polynomial.roots`. New definitions: the moment sequence `f j = ∫ x, x ^ j ∂μ`, the
  Stieltjes series coefficients `(-1) ^ j * f j`, and the Baker approximant of 10.14.
  Conjuncts, with infinite support (`¬ ∀ᵐ x ∂μ, x ∈ s` for every `s : Finset ℝ`) and all
  moments finite: (i) every Baker approximant of type `(L, M)` with `M ≤ L + 1` exists;
  (ii) for `J ≥ -1` (an integer, with `L = M + J ≥ 0`) the poles of the diagonal
  sequence are simple, negative and have positive residues; (iii) the sequence converges
  uniformly on bounded sets at positive distance from `Set.Iic 0` to a function analytic on
  `Complex.slitPlane`; (iv) if the series has positive radius `R` the limit is the
  Stieltjes function and the poles lie in `Set.Iio (-R)`; (v) under Carleman's condition
  `¬ Summable (fun j ↦ f j ^ (-(1 / (2 * j))))` for `j ≥ 1` the limit is the Stieltjes
  function. Pitfalls: `Real.rpow` of a moment is safe because the moments of even order
  are positive under infinite support, but odd moments must be shown nonnegative (they are,
  on `[0, ∞)`); the index `J ≥ -1` needs `ℤ`. Statable at the pins; (ii)–(v) need the
  orthogonal-polynomial and Gauss-quadrature theory of section 12 for the measure `μ` and
  the determinacy of the Stieltjes moment problem under Carleman's condition, which no
  library has. Dependencies: 10.14 (v), 12.1–12.6. NASC: `NASC.exists_padePair_of_stieltjes`,
  `sorry`; it is (i).
## 11. Splines, kernels and wavelets

[Synopsis](SYNOPSIS.md#11-splines-kernels-and-wavelets) · [Coverage inventory](STRUCTURE.md#11-splines-kernels-and-wavelets)

This section selects the local B-spline basis, spline collocation, cubic spline interpolation
and its error, strict positive definiteness and conditional positive definiteness of radial
kernels, the power-function error and stability estimates of scattered-data interpolation,
and the theorems on multiresolution analysis, Daubechies wavelets and approximation spaces.

A spline of **order** $m$ is piecewise of degree at
most $m-1$, so its pieces lie in $\mathbb P_{m-1}$. Divided differences of
functions of $t$ at repeated arguments are taken in the Hermite sense, and
$(t-x)_+^{r}$ is $(t-x)^r$ for $t>x$ and $0$ otherwise. The Fourier transform
on $\mathbb R^d$ is $\hat f(\omega)=(2\pi)^{-d/2}\int f(x)e^{-ix^\top\omega}\,dx$.
For a function $\eta$ on $\mathbb R$ write
$\eta_{j,k}(x)=2^{j/2}\eta(2^jx-k)$ for $j,k\in\mathbb Z$.

### Splines

* **11.2. B-splines.** Let $y_1\le y_2\le\cdots$ be real numbers, and let
  $m\ge1$ and $i$ be such that $y_i<y_{i+m}$. The **normalized B-spline** of
  order $m$ with knots $y_i,\dots,y_{i+m}$ is
  $$N_i^m(x)=(-1)^m(y_{i+m}-y_i)\,[y_i,\dots,y_{i+m}](x-y)_+^{m-1},$$
  the divided difference acting on the variable $y$; it is $0$ by
  definition when $y_i=y_{i+m}$. Then:
  - $N_i^1$ is the indicator function of $[y_i,y_{i+1})$.
  - **Recurrence.** For $m\ge2$ and all real $x$,
    $$N_i^m(x)=\frac{x-y_i}{y_{i+m-1}-y_i}N_i^{m-1}(x)
    +\frac{y_{i+m}-x}{y_{i+m}-y_{i+1}}N_{i+1}^{m-1}(x),$$
    where a term whose denominator vanishes is omitted (its B-spline is
    zero).
  - **Local support and positivity.** $N_i^m(x)=0$ for $x\notin[y_i,y_{i+m}]$,
    and $N_i^m(x)>0$ for $y_i<x<y_{i+m}$.
  - **Smoothness.** $N_i^m$ is a piecewise polynomial of degree at most
    $m-1$ with breakpoints among the $y_j$. At a knot of multiplicity
    $\mu<m$ in $y_i,\dots,y_{i+m}$ it has continuous derivatives up to
    order $m-1-\mu$; at a knot of multiplicity $m$ it may jump.
  - **Partition of unity.** If $y_\ell<y_{\ell+1}$, then
    $\sum_{i=\ell+1-m}^{\ell}N_i^m(x)=1$ for $y_\ell\le x<y_{\ell+1}$.

  *Assessment.* Neither library defines B-splines or divided differences of real functions,
  and Mathlib's polynomials and piecewise definitions are the available material. The
  divided-difference definition, its agreement with the Cox–de Boor recurrence for repeated
  knots, strict positivity on the open support, the multiplicity-dependent smoothness and the
  partition of unity all remain to be proved.

  *Lean target.* Carriers at the pins: `Polynomial` with `Polynomial.natDegree`,
  `ContDiffAt`, `Monotone` for the knot sequence, and `Finset.sum` over `Finset.Ico`. The
  recurrence serves as the definition, as in `NASC.bSpline (t : ℕ → ℝ) (m i : ℕ) : ℝ → ℝ`,
  which has order $m+1$ and knots `t i, …, t (i + m + 1)`; the off-by-one against the synopsis
  order must be tracked in every statement. Conjuncts, all for `Monotone t`: (i) nonnegativity
  and vanishing off `Ico (t i) (t (i + m + 1))`; (ii) positivity on
  `Ioo (t i) (t (i + m + 1))`; (iii) on each `Ico (t j) (t (j + 1))` with `t j < t (j + 1)` the
  B-spline agrees with a polynomial of `natDegree ≤ m`; (iv) at a knot value of multiplicity
  $\mu\le m$ among `t i, …, t (i + m + 1)`, `ContDiffAt ℝ (m - μ) (bSpline t m i)`; (v) the
  partition of unity of the active B-splines on `Ico (t m) (t n)`; (vi) for pairwise distinct
  knots, the explicit divided-difference formula
  $N=(y_{i+m}-y_i)\sum_j(y_j-x)_+^{m-1}/\omega'(y_j)$ in the synopsis order. Pitfall: Lean's
  `x / 0 = 0` makes a term with vanishing denominator zero, which agrees with the omitted-term
  convention only because the B-spline it multiplies is itself zero; without `Monotone t` the
  support statement fails. The confluent divided difference needed for (vi) with repeated knots
  is infrastructure no library has. No dependency on other entries. NASC:
  `NASC.bSpline_nonneg` and `NASC.bSpline_eq_zero_of_notMem` (proved) are (i), and
  `NASC.sum_bSpline_eq_one` (proved) is (v); (ii)–(iv) and (vi) are not stated.

* **11.3. Curry–Schoenberg theorem.** In the setting of 11.1, choose an
  **extended partition** $y_1\le\cdots\le y_m\le a$,
  $b\le y_{m+K+1}\le\cdots\le y_{2m+K}$, with $b<y_{2m+K}$, and with
  $y_{m+1}\le\cdots\le y_{m+K}$ equal to the knots $x_1,\dots,x_k$, each
  $x_i$ repeated $m_i$ times. Then the restrictions to $[a,b]$ of the
  B-splines $N_1^m,\dots,N_{m+K}^m$ form a basis of
  $\mathcal S(\mathbb P_{m-1};\mathcal M;\Delta)$. They are nonnegative and
  sum to $1$ on $[a,b]$. If instead $b=y_{m+K+1}=\cdots=y_{2m+K}$, the same
  holds after the value of $N_{m+K}^m$ at $b$ is replaced by its left limit.

  *Assessment.* Finite-dimensional linear algebra and polynomials are available; no library
  defines spline spaces with knot multiplicities. The theorem identifies the B-splines of 11.2
  on the extended partition as a basis of the spline space, which also gives the dimension
  count of 11.1.

  *Lean target.* Carriers at the pins: `Submodule ℝ (Icc a b → ℝ)` or functions on `ℝ` compared
  by `Set.EqOn` on `Icc a b`, `LinearIndependent`, `Submodule.span`, `Module.finrank`, and
  `Polynomial.X`, `Polynomial.C` for divisibility. New definition: `splineSpace m x mult`, for
  `m : ℕ` with `1 ≤ m`, strictly increasing breakpoints `x : Fin (k + 2) → ℝ` and
  `mult : Fin k → ℕ` with `1 ≤ mult i ≤ m`, the submodule of functions that agree on each
  `Ico (x i) (x (i + 1))` (the last piece closed) with a polynomial of `natDegree ≤ m - 1`,
  consecutive pieces $s_{i-1},s_i$ satisfying `(X - C (x i)) ^ (m - mult i) ∣ s_{i-1} - s_i`;
  the divisibility form avoids one-sided derivatives. Conjuncts: (i) `finrank = m + K` with
  `K = ∑ i, mult i` (the dimension claim of 11.1); (ii) for an extended partition with
  `b < y (2m+K)`, the restrictions of the $m+K$ B-splines are linearly independent and span
  `splineSpace`; (iii) nonnegativity and sum $1$ on `Icc a b`; (iv) the variant with
  `b = y (m+K+1) = ⋯` after replacing the value at $b$ by the left limit. Pitfall: with
  half-open supports every B-spline vanishes at $b$ when $b$ is the last knot, so (iii) on the
  closed interval holds only under `b < y (2m+K)`. Everything is statable at the pins; depends
  on 11.2. NASC: `NASC.sum_bSpline_eq_one` (proved) gives the partition of unity on the open
  active interval; the basis statement has no declaration.

* **11.4. Schoenberg–Whitney theorem.** Let $y_1\le\cdots\le y_{n+m}$ with
  $y_i<y_{i+m}$ for all $i$, and let $t_1<\cdots<t_n$. The collocation matrix
  $\bigl(N_j^m(t_i)\bigr)_{i,j=1}^n$ is nonsingular if and only if
  $N_i^m(t_i)\ne0$ for $i=1,\dots,n$. Hence, under this condition, for all
  data $v_1,\dots,v_n$ there is exactly one spline
  $s=\sum_{j=1}^nc_jN_j^m$ with $s(t_i)=v_i$ for all $i$.

  *Assessment.* Matrix determinants and invertibility are available. The missing theorem
  connects the nonsingularity of the collocation matrix to the interlacing of the sites with
  the B-spline supports.

  *Lean target.* Carriers at the pins: `Matrix.of`, `Matrix.det`, `Matrix.mulVec`,
  `StrictMono` for the sites, `Monotone` for the knots. Conjuncts: (i) for
  `t : ℕ → ℝ` monotone with `t j < t (j + m + 1)` for `j < n` and sites `x : Fin n → ℝ`
  strictly increasing, `det (of fun i j ↦ bSpline t m j (x i)) ≠ 0 ↔ ∀ i, bSpline t m i (x i) ≠ 0`;
  (ii) under the right side, `∃! c : Fin n → ℝ, ∀ i, ∑ j, c j * bSpline t m j (x i) = v i`,
  which follows from (i) and `Matrix.mulVec` injectivity. The standard proofs pass through
  total positivity of the collocation matrix or the variation-diminishing property (11.5),
  neither available at the pins. Statable at the pins; depends on 11.2. NASC:
  `NASC.det_bSpline_collocation_ne_zero_iff` (sorry) is (i) in the order-$m+1$ indexing, without
  the support hypothesis `t i < t (i + m + 1)`; (ii) has no declaration.

* **11.6. Minimum curvature of interpolating cubic splines.** Let
  $\Delta=\{a=x_0<\cdots<x_n=b\}$ with $n\ge1$. A **cubic spline** on $\Delta$
  is a function in $C^2[a,b]$ that is a cubic polynomial on each
  $[x_{i-1},x_i]$. Let $K^2[a,b]$ be the set of $f$ with $f'$ absolutely
  continuous and $f''\in L^2(a,b)$. Let $f\in K^2[a,b]$, and let $S$ be a
  cubic spline on $\Delta$ with $S(x_i)=f(x_i)$ for all $i$ that satisfies
  one of
  - (natural) $S''(a)=S''(b)=0$;
  - (periodic) $f^{(j)}(a)=f^{(j)}(b)$ and $S^{(j)}(a)=S^{(j)}(b)$ for
    $j=0,1$, and $S''(a)=S''(b)$;
  - (complete) $S'(a)=f'(a)$ and $S'(b)=f'(b)$.

  For each of the three conditions such an $S$ exists and is unique, and
  $$\int_a^b|f''-S''|^2\,dx=\int_a^b|f''|^2\,dx-\int_a^b|S''|^2\,dx\ge0.$$
  So $S$ minimizes $\int_a^b|g''|^2$ over all $g\in K^2[a,b]$ that interpolate
  the same data and satisfy the same side condition on $g$ as is imposed on
  $f$, and equality holds only for $g=S$. In the natural case there is no
  side condition on $g$: the natural cubic spline interpolant minimizes
  $\int_a^b|g''|^2$ among all interpolants in $K^2[a,b]$ (Holladay).

  *Assessment.* Hilbert projection and absolutely continuous functions on an interval are
  available. Existence and uniqueness of the three interpolants, the energy identity from
  integration by parts on each piece, and the minimality with its equality case remain gaps.

  *Lean target.* Carriers at the pins: `AbsolutelyContinuousOnInterval`, `IntervalIntegrable`,
  `intervalIntegral`, `iteratedDerivWithin`, `HasDerivWithinAt`, `Polynomial`. Definitions:
  `NASC.IsCubicSpline t s` for `t : Fin (n + 1) → ℝ` (global `ContDiff ℝ 2 s` and cubic pieces
  on each `Icc`), and a predicate for $K^2[a,b]$: `f` has a derivative `f'` within `Icc a b`
  at every point, `AbsolutelyContinuousOnInterval f' a b`, and the a.e. derivative of `f'` is
  square integrable on `[a, b]`. Conjuncts, for `StrictMono t` and `n ≥ 1`: (i) for each side
  condition there is a unique cubic spline with the side condition interpolating $f$ at the
  knots; (ii) the energy identity; (iii) minimality over interpolants in $K^2$ with the same
  side condition, with equality only for $g=S$ on `Icc a b`; (iv) the natural case without
  side condition on $g$. Pitfall: `deriv` and `iteratedDeriv` are $0$ where a function is not
  differentiable, so endpoint conditions must use `derivWithin` on `Icc a b` or a global
  `ContDiff` hypothesis; a global `ContDiff ℝ 2` cubic spline is harmless because end pieces
  extend. Statable at the pins; no dependency. NASC: `NASC.cubicSpline_curvature_identity`
  (sorry) states (ii) in the natural case, with `ContDiff ℝ 2 f` instead of $f\in K^2$;
  existence, uniqueness, the periodic and complete cases and (iii) are not stated.

* **11.7. Error of complete cubic spline interpolation.** Let
  $f\in C^4[a,b]$ with $|f^{(4)}|\le L$ on $[a,b]$, let $\Delta$ be as in 11.6
  with mesh size $\|\Delta\|=\max_j(x_{j+1}-x_j)$, and let $K\ge1$ satisfy
  $\|\Delta\|\le K(x_{j+1}-x_j)$ for all $j$. Let $S$ be the complete cubic
  spline interpolant of 11.6. Then, for all $x\in[a,b]$, with one-sided
  values of $S'''$ at the knots,
  $$|f^{(k)}(x)-S^{(k)}(x)|\le c_kL\|\Delta\|^{4-k}\quad(k=0,1,2,3),$$
  $$c_0=\frac5{384},\qquad c_1=\frac1{24},\qquad c_2=\frac38,\qquad
  c_3=\frac{K+K^{-1}}2,$$
  and $c_0$ and $c_1$ are best possible. Cruder bounds with
  $c_0,c_1,c_2\le2$ and $c_3=2K$ hold as well. Hence $S$, $S'$ and $S''$
  converge uniformly to $f$, $f'$ and $f''$ as $\|\Delta\|\to0$, and $S'''$
  converges uniformly to $f'''$ along mesh sequences with bounded $K$.

  *Assessment.* No library defines cubic spline interpolation. The estimate needs the
  complete interpolant of 11.6 and the mesh-dependent bounds for the moments of the spline.

  *Lean target.* Carriers at the pins: `ContDiffOn ℝ 4 f (Icc a b)`, `iteratedDerivWithin`,
  `NASC.IsCubicSpline`, `Filter.Tendsto` for the convergence corollaries. Conjuncts, for
  `StrictMono t`, `n ≥ 1`, `1 ≤ K`, `∀ j, ‖Δ‖ ≤ K * (t (j+1) - t j)` and
  `∀ x ∈ Icc a b, |f⁽⁴⁾ x| ≤ L`: (i) the bounds for `k = 0, 1, 2` with
  $c_0=5/384$, $c_1=1/24$, $c_2=3/8$; (ii) the bound for `k = 3` stated piecewise, with $S'''$
  on $[x_j,x_{j+1}]$ replaced by the constant third derivative of the cubic piece there, which
  removes the one-sided values; (iii) the cruder bounds; (iv) sharpness of $c_0,c_1$: for every
  smaller constant there are a mesh and an $f$ violating the bound; (v) the uniform
  convergence corollaries. Statable at the pins; depends on 11.6 for the interpolant. NASC:
  `NASC.completeSpline_derivative_error_le` (sorry) states the cruder bound with constant $2$
  for `k : Fin 3`, for global `ContDiff ℝ 4 f`, at least one mesh interval (`0 < n`; for `n = 0`
  the statement fails) and any upper bound `h` of the mesh widths; the
  Hall–Meyer constants, the third-derivative bound and sharpness are not stated.

### Kernels and scattered data

* **11.9. Positive definite functions and Bochner's theorem.** A continuous
  $\Phi:\mathbb R^d\to\mathbb C$ is **positive semidefinite** if
  $\sum_{j,k=1}^N\alpha_j\overline{\alpha_k}\Phi(x_j-x_k)\ge0$ for all
  $N\in\mathbb N$, all pairwise distinct $x_1,\dots,x_N\in\mathbb R^d$ and all
  $\alpha\in\mathbb C^N$. It is **positive definite** if the form is positive
  for every $\alpha\ne0$.
  - (Bochner.) A continuous $\Phi$ is positive semidefinite if and only if
    there is a finite nonnegative Borel measure $\mu$ on $\mathbb R^d$ with
    $\Phi(x)=(2\pi)^{-d/2}\int e^{-ix^\top\omega}\,d\mu(\omega)$ for all $x$.
    If the support of $\mu$ contains a nonempty open set, then $\Phi$ is
    positive definite.
  - If $\Phi\in L^1(\mathbb R^d)$ is continuous, then $\Phi$ is positive
    definite if and only if $\Phi$ is bounded and $\hat\Phi$ is nonnegative
    and not identically zero.
  - The Gaussian $e^{-\alpha\|x\|_2^2}$ with $\alpha>0$ and the inverse
    multiquadric $(c^2+\|x\|_2^2)^{-\beta}$ with $c>0$, $\beta>0$ are positive
    definite on $\mathbb R^d$ for every $d$.
  - The truncated power $(1-\|x\|_2)_+^\ell$ is positive definite on
    $\mathbb R^d$ for every integer $\ell\ge\lfloor d/2\rfloor+1$.

  *Assessment.* Partly covered. TauCeti proves Bochner's theorem for the nonstrict condition,
  with uniqueness of the measure, the nonnegativity of the Fourier transform of an integrable
  positive semidefinite function, and the positive semidefiniteness of the Gaussian. The
  strict condition is missing throughout: the open-support implication, the strict integrable
  characterization and the strict positivity of the listed examples.

  *Scope.* The selected part is strict positive definiteness: the open-support implication of
  the first bullet, the integrable characterization of the second, and the strict positivity
  of the Gaussian, the inverse multiquadric and the truncated powers.

  *Lean target.* Carriers at the pins: `TauCeti.IsPositiveDefiniteSub` (nonstrict, complex
  coefficients, no distinctness), `TauCeti.bochner` with `TauCeti.fourierAtom`, the
  transform $v\mapsto e^{-2\pi i\langle v,q\rangle}$ in Mathlib's $2\pi$ convention,
  `TauCeti.fourier_re_nonneg_of_posSemidef`, `TauCeti.posSemidef_cexp_neg_mul_sq_norm`,
  `MeasureTheory.Measure.support`, `EuclideanSpace ℝ (Fin d)` and the Fourier transform `𝓕` on
  functions of a finite-dimensional inner product space. New definition:
  `IsStrictPositiveDefiniteSub (F : V → ℂ) : Prop`, positivity of the form for every
  injective `v : Fin n → V` and every nonzero `c : Fin n → ℂ`. Conjuncts: (i) for a finite
  measure `μ` with `(interior μ.support).Nonempty`, the function $v\mapsto\int\text{fourierAtom}$
  is strictly positive definite; (ii) for continuous `Φ` with `Integrable Φ`: strict positive
  definiteness ↔ boundedness, `0 ≤ 𝓕 Φ` and `𝓕 Φ ≠ 0`; (iii) the four examples, with
  `max (1 - ‖x‖) 0 ^ ℓ` and `d / 2 + 1 ≤ ℓ` in natural-number division. Pitfalls: the synopsis
  convention differs from `fourierAtom` by the factor $(2\pi)^{-d/2}$ and the pushforward of
  $\mu$ under $\omega\mapsto\omega/(2\pi)$, which preserve support having interior; the Fourier
  transform of a non-integrable function is the junk value $0$, so (ii) needs `Integrable Φ`
  explicitly. The truncated-power case needs the radial Fourier transform (Askey's theorem);
  Mathlib has `Complex.besselJ` but no Hankel-transform formula. Otherwise statable at the
  pins; no dependency. NASC: `NASC.fourier_gram_pos_of_spectral_support` (sorry) is (i) with
  the synopsis sign convention, without the factor $(2\pi)^{-d/2}$ (a positive constant, so
  harmless), on a finite-dimensional real inner product space, and with the support hypothesis
  as a nonempty open set `U ⊆ μ.support`; (ii) and (iii) have no declaration.

* **11.10. Compactly supported functions of minimal degree.** For a
  function $\varphi$ on $[0,\infty)$ with $t\varphi(t)$ integrable, let
  $(\mathcal I\varphi)(r)=\int_r^\infty t\varphi(t)\,dt$ for $r\ge0$. For
  $d\ge1$ and $k\ge0$ put
  $$\varphi_{d,k}=\mathcal I^k\bigl[(1-r)_+^{\lfloor d/2\rfloor+k+1}\bigr].$$
  Then $\Phi_{d,k}=\varphi_{d,k}(\|\cdot\|_2)$ is positive definite on
  $\mathbb R^d$. On $[0,1]$ the function $\varphi_{d,k}$ is a polynomial of
  degree $\lfloor d/2\rfloor+3k+1$, it vanishes for $r\ge1$, and its even
  extension to $\mathbb R$ is in $C^{2k}$. Among the functions of the form
  "polynomial on $[0,1]$, zero on $(1,\infty)$" that are positive definite
  on $\mathbb R^d$ and have $2k$ continuous derivatives, $\varphi_{d,k}$ has
  minimal degree and is unique up to a positive constant factor. Up to
  positive constant factors,
  $$\varphi_{d,0}=(1-r)_+^{\lfloor d/2\rfloor+1},\qquad
  \varphi_{d,1}=(1-r)_+^{\ell+1}\bigl((\ell+1)r+1\bigr)\quad
  \text{with }\ell=\lfloor d/2\rfloor+2;$$
  for example $\varphi_{3,1}=(1-r)_+^4(4r+1)$.

  *Assessment.* TauCeti's positive-definite kernels and Bochner's theorem are the available
  ingredients. The positive definiteness of the compactly supported radial polynomials, their
  degree and smoothness, and the minimality and uniqueness remain gaps.

  *Lean target.* Carriers at the pins: `MeasureTheory.integral` over `Ioi r` or `Ioc r 1`,
  `Polynomial` with `Polynomial.natDegree`, `ContDiff ℝ (2 * k)`, `Nat.iterate`, and the strict
  predicate of 11.9. Definition: `NASC.radialIntegral p r = ∫ t in Ioc r 1, t * p t`, equal to
  $\mathcal I p$ for profiles vanishing on $(1,\infty)$, and
  `wendland d k = radialIntegral^[k] (fun r ↦ max (1 - r) 0 ^ (d / 2 + k + 1))`. Conjuncts,
  for `1 ≤ d`: (i) $r\mapsto$ `wendland d k ‖x‖` is strictly positive definite on
  `EuclideanSpace ℝ (Fin d)`; (ii) there is `p : ℝ[X]` with
  `p.natDegree = d / 2 + 3 * k + 1` and `EqOn (wendland d k) p.eval (Icc 0 1)`, and
  `wendland d k r = 0` for `1 ≤ r`; (iii) `ContDiff ℝ (2 * k) (fun r ↦ wendland d k |r|)`;
  (iv) minimality of the degree and uniqueness up to a positive factor among
  positive definite piecewise polynomial profiles of class $C^{2k}$; (v) the closed forms of
  $\varphi_{d,0}$ and $\varphi_{d,1}$ up to positive constants. Pitfall: for real kernels,
  positivity with real coefficients implies it with complex ones, so a real statement suffices.
  (ii), (iii) and (v) are statable and provable at the pins; (i) and (iv) need the radial
  Fourier transform through Bessel functions and its positivity for truncated powers, which no
  library has. Depends on 11.9. NASC: `NASC.wendland_gram_pos` (sorry) is (i) with real
  coefficients, for every dimension `d`, including `d = 0`; (ii)–(v) have no declaration.

* **11.11. Conditionally positive definite functions; Micchelli's
  theorem.** Let $m\in\mathbb N_0$. A continuous $\Phi:\mathbb R^d\to\mathbb C$
  is **conditionally positive semidefinite of order $m$** if
  $\sum_{j,k}\alpha_j\overline{\alpha_k}\Phi(x_j-x_k)\ge0$ for all pairwise
  distinct $x_1,\dots,x_N$ and all $\alpha\in\mathbb C^N$ with
  $\sum_j\alpha_jp(x_j)=0$ for every polynomial $p$ of degree less than $m$.
  It is **conditionally positive definite of order $m$** if moreover the form
  vanishes only for $\alpha=0$. Order $0$ is positive (semi)definiteness. A
  function $\psi\in C^\infty(0,\infty)$ is **completely monotone** if
  $(-1)^j\psi^{(j)}\ge0$ on $(0,\infty)$ for all $j\in\mathbb N_0$.
  - (Micchelli.) Let $\varphi\in C[0,\infty)\cap C^\infty(0,\infty)$. Then
    $\Phi=\varphi(\|\cdot\|_2^2)$ is conditionally positive semidefinite of
    order $m$ on every $\mathbb R^d$ if and only if $(-1)^m\varphi^{(m)}$ is
    completely monotone on $(0,\infty)$. If in addition $\varphi$ is not a
    polynomial of degree at most $m$, then $\Phi$ is conditionally positive
    definite of order $m$ on every $\mathbb R^d$.
  - The multiquadric $(-1)^{\lceil\beta\rceil}(c^2+\|x\|_2^2)^\beta$ with
    $c>0$, $\beta>0$, $\beta\notin\mathbb N$ is conditionally positive
    definite of order $\lceil\beta\rceil$; the power
    $(-1)^{\lceil\beta/2\rceil}\|x\|_2^\beta$ with $\beta>0$,
    $\beta\notin2\mathbb N$ is conditionally positive definite of order
    $\lceil\beta/2\rceil$; and the thin-plate spline
    $(-1)^{k+1}\|x\|_2^{2k}\log\|x\|_2$ with $k\in\mathbb N$ is conditionally
    positive definite of order $k+1$.

  *Assessment.* TauCeti proves the Hausdorff–Bernstein–Widder theorem, which represents the
  functions continuous on $[0,\infty)$ and completely monotone on $(0,\infty)$ as Laplace
  transforms of finite positive measures, and Schoenberg's theorem relating conditionally
  negative semidefinite kernels to positive semidefinite exponentials. These are the two
  ingredients of Micchelli's theorem. The theorem, its order-$m$ form, the strict version and
  the examples remain gaps.

  *Lean target.* Carriers at the pins: `TauCeti.IsCompletelyMonotoneOnIoi`
  (`ContDiffOn ℝ ∞ f (Ioi 0)` and sign conditions on `iteratedDeriv`),
  `TauCeti.IsContinuousCompletelyMonotoneOnIoi`, `TauCeti.hausdorff_bernstein_widder`,
  `Matrix.CondNegSemidef` with `Matrix.condNegSemidef_iff_forall_posSemidef_cexp_neg_mul`,
  `MvPolynomial.totalDegree` and `MvPolynomial.eval`. Definitions:
  `NASC.ConditionallyPosSemidefRadial m d p` (real coefficients annihilating the polynomials of
  total degree below `m`, form in `p (‖x i - x j‖ ^ 2)`), and its strict analogue for nonzero
  coefficients. Conjuncts, for `ContinuousOn φ (Ici 0)` and `ContDiffOn ℝ ∞ φ (Ioi 0)`: (i)
  `ConditionallyPosSemidefRadial m d φ` for every `d` if and only if
  `IsCompletelyMonotoneOnIoi ((-1) ^ m • iteratedDeriv m φ)`; (ii) strictness for every
  `d` when `φ` does not agree on `Ici 0` with a polynomial of degree at most `m`; (iii)
  the multiquadric, the power and the thin-plate spline with their orders, using `Real.rpow`
  and `Nat.ceil`. Pitfalls: at this Mathlib
  `ContDiffOn ℝ ⊤` means analytic (`⊤ = ω` in `WithTop ℕ∞`); `C^∞` is `∞`; `Real.log 0 = 0`
  gives the thin-plate spline the correct value $0$ at the origin for $k\ge1$. Statable at the
  pins, and the Gaussian-mixture proof route is available from (i)'s ingredients; depends on
  11.9 for strictness. NASC: `NASC.conditionallyPosSemidefRadial_iff_derivative_nonneg`
  (sorry) is (i), with the right side written as the sign conditions on `iteratedDeriv (m + j)`
  and with hypothesis `ContDiffOn ℝ ∞ p (Ioi 0)` (smoothness, as in the synopsis); (ii) and (iii)
  have no declaration.

* **11.13. Power function and error estimates.** Let $\Phi$ be a symmetric
  positive definite kernel on $\Omega$, let $X=\{x_1,\dots,x_N\}\subseteq
  \Omega$ be pairwise distinct, and let $s_{f,X}=\sum_j\alpha_j\Phi(\cdot,x_j)$
  be the unique interpolant of $f$ on $X$. Its **cardinal functions**
  $u_j^*\in\mathrm{span}\{\Phi(\cdot,x_k)\}$ satisfy $u_j^*(x_k)=\delta_{jk}$.
  The **power function** is given by
  $$P_{\Phi,X}(x)^2=\Phi(x,x)-2\sum_{j}u_j^*(x)\Phi(x,x_j)
  +\sum_{i,j}u_i^*(x)u_j^*(x)\Phi(x_i,x_j).$$
  - For every $x\in\Omega$, the vector $(u_j^*(x))_j$ minimizes the
    quadratic form $u\mapsto\Phi(x,x)-2\sum_ju_j\Phi(x,x_j)+\sum_{i,j}u_iu_j
    \Phi(x_i,x_j)$ over $\mathbb R^N$, and
    $$|f(x)-s_{f,X}(x)|\le P_{\Phi,X}(x)\,\|f\|_{\mathcal N_\Phi(\Omega)},
    \qquad f\in\mathcal N_\Phi(\Omega).$$
  - Let $\Omega$ be open and bounded and satisfy an **interior cone
    condition** (there are $\theta\in(0,\pi/2)$ and $r>0$ such that every
    $x\in\Omega$ is the vertex of a cone of radius $r$ and angle $\theta$
    contained in $\Omega$). The **fill distance** is
    $h_{X,\Omega}=\sup_{x\in\Omega}\min_j\|x-x_j\|_2$. For $\Phi_{d,k}$ of
    11.10 there are constants $C,h_0>0$, independent of $f$, $x$ and $X$,
    such that for all $f\in\mathcal N_{\Phi_{d,k}}(\Omega)$, all
    $\alpha\in\mathbb N_0^d$ with $|\alpha|\le k$, all $x\in\Omega$, and all
    $X$ with $h_{X,\Omega}\le h_0$,
    $$|D^\alpha f(x)-D^\alpha s_{f,X}(x)|\le C\,h_{X,\Omega}^{k+1/2-|\alpha|}
    \|f\|_{\mathcal N_{\Phi_{d,k}}(\Omega)}.$$

  *Assessment.* Mathlib constructs the reproducing kernel Hilbert space of a positive
  semidefinite kernel, which is the native space of 11.12, proves its uniqueness, and
  describes the kernel of a closed subspace through the orthogonal projection. The
  identification of the interpolant with the projection onto the span of the kernel sections,
  the cardinal-function form of the power function, its minimization property and the
  fill-distance estimate remain gaps.

  *Lean target.* Carriers at the pins: `RKHS`, `RKHS.OfKernel` with `RKHS.kernel_ofKernel`,
  `RKHS.kerFun`, `RKHS.kernel_submodule`, `Submodule.starProjection`, `Matrix.PosDef`,
  `Metric.infDist`, `iteratedFDeriv`. New definitions: the power function
  `powerFunction Φ X : Ω → ℝ` by the synopsis formula, and a predicate
  `InteriorConeCondition (Ω : Set (EuclideanSpace ℝ (Fin d))) (θ r : ℝ)`. Conjuncts, for a
  real symmetric kernel with `Matrix.PosDef` Gram matrices on injective site families:
  (i) existence and uniqueness of the interpolant and of the cardinal functions; (ii)
  minimization of the quadratic form by $(u_j^*(x))_j$, with minimum value $P(x)^2$; (iii)
  $P(x)^2=\|k_x-\Pi_Xk_x\|^2$ in `RKHS.OfKernel`, where $\Pi_X$ is the projection onto the span
  of the kernel sections at $X$, and the error bound for $f$ in that space; (iv) the
  fill-distance estimate for $\Phi_{d,k}$, for `IsOpen Ω`, `Bornology.IsBounded Ω`, the cone
  condition and `1 ≤ d`. Pitfalls: define $h_{X,\Omega}$ as a supremum of `Metric.infDist x X`
  over `Ω` with `Ω` bounded and `X` nonempty, since `Metric.infDist x ∅ = 0` and a real
  supremum over an unbounded set is junk; the native-space norm in (iv) is that of
  `RKHS.OfKernel` restricted to `Ω`. (i)–(iii) are statable and provable at the pins; (iv)
  needs the smoothness of native-space functions (from 11.12, Mathlib's
  `BesselPotentialSpace` being the Sobolev carrier) and local polynomial reproduction on cone
  domains, which no library has. Depends on 11.10 and 11.12. NASC:
  `NASC.abs_kernelInterpolation_error_le` (proved) is the abstract form of the error bound in
  (iii) for sites indexed by any finite type, for a feature map into a Hilbert space and the
  projection onto the closed span of the site features; the identification with the
  cardinal-function formula, (ii) and (iv) are not stated.

* **11.14. Separation distance and the smallest eigenvalue.** For
  $X=\{x_1,\dots,x_N\}$ pairwise distinct with $N\ge2$, the **separation
  distance** is $q_X=\frac12\min_{i\ne j}\|x_i-x_j\|_2$. Let
  $\Phi\in C(\mathbb R^d)\cap L^1(\mathbb R^d)$ be real-valued and even with
  $\hat\Phi>0$ on $\mathbb R^d$, and let $\lambda_{\min}$ be the smallest
  eigenvalue of $A_{\Phi,X}=(\Phi(x_i-x_j))_{i,j=1}^N$. Put
  $\varphi_0(M)=\inf_{\|\omega\|_2\le2M}\hat\Phi(\omega)$. Then
  $$\lambda_{\min}\ge\frac{\varphi_0(M)}{2\,\Gamma(d/2+1)}
  \Bigl(\frac{M}{2^{3/2}}\Bigr)^d\quad\text{for every }
  M\ge\frac{12}{q_X}\Bigl(\frac{\pi\,\Gamma^2(d/2+1)}{9}\Bigr)^{1/(d+1)},$$
  and the condition on $M$ holds whenever $M\ge6.38\,d/q_X$.
  - For the Gaussian $e^{-\alpha\|x\|_2^2}$, with
    $M_d=12\bigl(\pi\Gamma^2(d/2+1)/9\bigr)^{1/(d+1)}$, this gives
    $$\lambda_{\min}\ge\frac{M_d^d}{2^{3d/2+1}\Gamma(d/2+1)}(2\alpha)^{-d/2}
    e^{-M_d^2/(\alpha q_X^2)}\,q_X^{-d}.$$
  - For $\Phi_{d,k}$ of 11.10 with $k\ge1$ or $d\ge3$, and for every
    $Q>0$, there is $C>0$ depending only on $d$, $k$ and $Q$ such that
    $\lambda_{\min}\ge Cq_X^{2k+1}$ for all $X$ with $q_X\le Q$.

  *Assessment.* Mathlib has the spectral theorem for Hermitian matrices, the Gamma function
  and the Fourier transform on Euclidean space. The lower bound for the smallest eigenvalue in
  terms of the separation distance, the stability counterpart of the error estimate of 11.13,
  is missing, together with its Gaussian and compactly supported instances.

  *Lean target.* Carriers at the pins: `Matrix.IsHermitian.eigenvalues`, `Matrix.PosDef`,
  `Real.Gamma`, the Fourier transform `𝓕`, `Integrable`, `EuclideanSpace ℝ (Fin d)`. New
  definitions: `separationDistance x` for `x : Fin N → EuclideanSpace ℝ (Fin d)` as half the
  `Finset.inf'` of `‖x i - x j‖` over the nonempty set of pairs `i ≠ j`, which needs
  `2 ≤ N`. The eigenvalue bound is best stated as the quadratic-form inequality
  $c\|\alpha\|^2\le\sum_{i,j}\alpha_i\alpha_j\Phi(x_i-x_j)$ for all real $\alpha$, which avoids
  the unordered indexing of `Matrix.IsHermitian.eigenvalues`. Conjuncts, for `1 ≤ d`, injective
  `x`, continuous, integrable, real, even `Φ` with `0 < Φ̂` everywhere: (i) the general bound for
  every admissible $M$, with $\varphi_0(M)$ the infimum of `Φ̂` over `Metric.closedBall 0 (2 * M)`;
  (ii) the numerical fact that $M\ge6.38\,d/q_X$ is admissible; (iii) the Gaussian bound; (iv)
  for `wendland d k` with `1 ≤ k ∨ 3 ≤ d`, `∀ Q > 0, ∃ C > 0` with the bound for $q_X\le Q$.
  Pitfalls: `sInf ∅ = 0` and `Finset.inf'` need a nonempty index set, hence `2 ≤ N`; `𝓕` uses
  the $2\pi$ convention, so $\hat\Phi$ and the radius $2M$ change under $\omega=2\pi\xi$; the
  infimum in $\varphi_0$ is of a continuous function on a compact ball and is attained. (i)–(iii)
  are statable at the pins, (i) needing an explicit bump-function construction; (iv) needs the
  two-sided Fourier decay of $\Phi_{d,k}$ from 11.12. Depends on 11.9, 11.10 and 11.12. NASC: no
  declaration.

### Wavelets

* **11.15. Multiresolution analysis and orthonormal wavelets.** A
  **multiresolution analysis** of $L^2(\mathbb R)$ is a sequence
  $(V_j)_{j\in\mathbb Z}$ of closed subspaces such that $V_j\subseteq V_{j+1}$;
  $f\in V_j$ if and only if $f(2\cdot)\in V_{j+1}$; $\bigcup_jV_j$ is dense in
  $L^2(\mathbb R)$; $\bigcap_jV_j=\{0\}$; and some $\varphi\in V_0$, the
  **scaling function**, has integer translates $\varphi(\cdot-k)$,
  $k\in\mathbb Z$, that form a Riesz basis of $V_0$. Suppose that $\varphi$ is
  real-valued and compactly supported and that its integer translates are
  orthonormal. Then $\varphi(x)=\sum_nh_n\varphi(2x-n)$ with finitely many
  nonzero real $h_n$, and $\sum_nh_nh_{n+2k}=2\delta_{0,k}$ for all
  $k\in\mathbb Z$. Define the **wavelet**
  $$\psi(x)=\sum_n(-1)^nh_{1-n}\,\varphi(2x-n).$$
  Then $\{\psi(\cdot-k)\}_{k\in\mathbb Z}$ is an orthonormal basis of the
  orthogonal complement $W_0$ of $V_0$ in $V_1$, the spaces $W_j=\{f(2^j\cdot):
  f\in W_0\}$ are mutually orthogonal, $\{\psi_{j,k}\}_{j,k\in\mathbb Z}$ is an
  orthonormal basis of $L^2(\mathbb R)$, and for each $j_0$ the system
  $\{\varphi_{j_0,k}\}_k\cup\{\psi_{j,k}\}_{j\ge j_0,k}$ is an orthonormal
  basis of $L^2(\mathbb R)$.

  *Assessment.* Mathlib has $L^2(\mathbb R)$, orthonormal families and Hilbert bases, and
  TauCeti has the Haar Schauder basis of $L^p([0,1])$. Multiresolution analyses, the
  refinement equation and the orthonormal wavelet basis built from them are missing.

  *Lean target.* Carriers at the pins: `MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)`,
  `MeasureTheory.MemLp.toLp`, `Orthonormal`, `HilbertBasis`, `Submodule.topologicalClosure`,
  `Submodule.orthogonal`, `HasCompactSupport`, `Finsupp`. New definitions: the dilation
  `dilate : Lp ℝ 2 volume →ₗᵢ[ℝ] Lp ℝ 2 volume`, $f\mapsto\sqrt2f(2\cdot)$, and integer
  translation as linear isometries; a structure `MultiresolutionAnalysis` with
  `V : ℤ → Submodule ℝ (Lp ℝ 2 volume)`, closedness, `Monotone V`, `V (j+1)` equal to the image
  of `V j` under `dilate`, dense union, trivial intersection, and a scaling function whose
  translates form a Riesz basis (a new predicate: a basis of the closed span with two-sided
  $\ell^2$ bounds). Conjuncts: (i) for a compactly supported real orthonormal scaling
  function, a finitely supported mask `h : ℤ →₀ ℝ` with the a.e. refinement equation and
  $\sum_nh_nh_{n+2k}=2\delta_{0,k}$; (ii) the translates of $\psi$ are an orthonormal basis of
  `V 1 ⊓ (V 0)ᗮ`; (iii) $\{\psi_{j,k}\}$ is a `HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 volume)`; (iv)
  the same for the system started at level $j_0$. Pitfalls: the refinement equation holds only
  almost everywhere; the factor $2^{j/2}$ must be built into `dilate`, unlike
  `NASC.scaleTranslate`, which omits it. Statable at the pins; no dependency. NASC:
  `NASC.exists_finite_refinementMask` (sorry) is (i), with the orthonormality of translates and
  the inclusion $V_0\subseteq V_1$ as hypotheses on a function `φ : ℝ → ℝ`; (ii)–(iv) have no
  declaration.

* **11.16. Daubechies wavelets.** For every $N\in\mathbb N$ there are real
  numbers $h_0,\dots,h_{2N-1}$ whose symbol
  $m_N(\omega)=\frac12\sum_{n=0}^{2N-1}h_ne^{-in\omega}$ has the form
  $\bigl((1+e^{-i\omega})/2\bigr)^Np_N(\omega)$ with a trigonometric
  polynomial $p_N$ of degree $N-1$, such that the solution $\varphi_N$ of
  $\varphi_N(x)=\sum_nh_n\varphi_N(2x-n)$ with $\int\varphi_N=1$ is an
  orthonormal scaling function of a multiresolution analysis as in 11.15.
  It is supported in $[0,2N-1]$, and the associated wavelet $\psi_N$ is
  supported in $[1-N,N]$, an interval of length $2N-1$. The wavelet has $N$
  **vanishing moments**: $\int x^q\psi_N(x)\,dx=0$ for $q=0,\dots,N-1$. Its
  smoothness grows linearly in $N$:
  $\sup\{s:(1+|\omega|)^s\hat\varphi_N\in L^\infty\}\ge
  N\bigl(1-\tfrac12\log_23\bigr)$, so $\varphi_N$ and $\psi_N$ are Hölder
  continuous of every order $\mu<N(1-\frac12\log_23)-1$. For $N=1$ this is the
  Haar system.

  *Assessment.* No library has refinable functions or the Daubechies construction. The filter
  construction by spectral factorization, the existence of the scaling function, its compact
  support and orthonormality, the vanishing moments and the regularity estimate remain to be
  developed.

  *Lean target.* Carriers at the pins: `Polynomial` (the symbol as a polynomial in
  $z=e^{-i\omega}$, so the factorization is `(1 + X) ^ N ∣ ∑ n, C (h n) * X ^ n`), `Integrable`,
  `Function.support`, `HolderWith`, `Real.logb`, the Fourier transform `𝓕`, and the structure
  of 11.15. Conjuncts, for `1 ≤ N`: (i) a mask `h : Fin (2 * N) → ℝ` with the factorization,
  `∑ n, h n = 2` and the quadrature-mirror identities; (ii) a scaling function with
  `∫ φ = 1`, the a.e. refinement equation, `support φ ⊆ Icc 0 (2N - 1)`, orthonormal integer
  translates, generating a `MultiresolutionAnalysis`; (iii) `support ψ ⊆ Icc (1 - N) N` and the
  vanishing moments with integrability of `x ^ q * ψ x`; (iv) the Fourier decay
  $(1+|\omega|)^s|\hat\varphi_N|$ bounded for $s<N(1-\frac12\log_23)$ and Hölder continuity
  of the corresponding orders, using `HolderWith` on derivatives of order $\lfloor\mu\rfloor$;
  (v) the case $N=1$ is the Haar system. Pitfalls: support statements refer to a chosen
  representative, and for $N=1$ that representative is discontinuous; an orthonormality
  condition written as `∫ x, φ x * φ (x - j) = …` is vacuous for non-integrable products,
  because the Bochner integral then takes the junk value $0$, so square integrability of `φ`
  must be a conjunct. (i)–(iii) and (v) are statable at the pins; the existence of the scaling
  function (cascade or infinite-product construction) and the regularity estimate need
  infrastructure no library has. Depends on 11.15. NASC:
  `NASC.exists_daubechies_vanishingMoments` (sorry) states (ii) without the multiresolution
  conclusion and (iii), with $\psi$ written by the reindexing $n\mapsto n-2N+2$, which agrees
  with the synopsis; it requires only `Integrable φ`, so its orthogonality for `j ≠ 0` is
  subject to the junk-value pitfall; the factorization, (iv) and (v) are not stated.

* **11.18. Approximation spaces and $n$-term wavelet approximation.** Let
  $X$ be a normed space and $X_0=\{0\}\subseteq X_1\subseteq\cdots\subseteq X$
  sets with $aX_n=X_n$ for $a\ne0$, $X_n+X_n\subseteq X_{cn}$ for a fixed
  integer $c$, such that every $f\in X$ has a best approximation from each
  $X_n$ and $E_n(f)=\inf_{g\in X_n}\|f-g\|_X\to0$. For $\alpha>0$ and
  $0<q\le\infty$ the **approximation space** $\mathcal A^\alpha_q(X)$
  consists of the $f$ with
  $|f|_{\mathcal A^\alpha_q}=\bigl(\sum_{n\ge1}[n^\alpha E_n(f)]^q
  n^{-1}\bigr)^{1/q}<\infty$ (the supremum of $n^\alpha E_n(f)$ if
  $q=\infty$).
  - Let $Y$ be continuously embedded in $X$ with a seminorm $|\cdot|_Y$, and
    let $r>0$. If the **Jackson inequality** $E_n(f)\le Cn^{-r}|f|_Y$ for
    $f\in Y$ and the **Bernstein inequality** $|S|_Y\le Cn^r\|S\|_X$ for
    $S\in X_n$ hold for all $n\ge1$, then for $0<\gamma<r$ and
    $0<q\le\infty$, $\mathcal A^\gamma_q(X)$ is the real interpolation space
    $(X,Y)_{\gamma/r,q}$, with equivalent norms.
  - Let $1<p<\infty$ and $t>0$, and for $0<s\le t$ let $1/\tau_s=1/p+s/d$.
    Let $\{\psi_\lambda\}$ be a wavelet basis of $L^p(\mathbb R^d)$ as in
    11.17, with coefficients $c_\lambda$, such that for every $0<s\le t$
    $$\|f\|_{B^s_{\tau_s,\tau_s}}\asymp\Bigl(\sum_\lambda\|c_\lambda
    \psi_\lambda\|_{L^p}^{\tau_s}\Bigr)^{1/\tau_s}$$
    (the Besov space being defined as in 11.17, also for $\tau_s<1$). Let
    $\Sigma_N$ be the set of linear combinations of at most $N$ of the
    $\psi_\lambda$, and $\sigma_N(f)_p=\inf_{g\in\Sigma_N}\|f-g\|_{L^p}$.
    Then for $0<s\le t$ and $N\ge1$,
    $\sigma_N(f)_p\le CN^{-s/d}\|f\|_{B^s_{\tau_s,\tau_s}}$, and
    $\|g\|_{B^s_{\tau_s,\tau_s}}\le CN^{s/d}\|g\|_{L^p}$ for
    $g\in\Sigma_N$, with $C$ independent of $N$, $f$ and $g$. Consequently,
    for $0<s<t$, $f\in B^s_{\tau_s,\tau_s}$ if and only if $f\in L^p$ and
    $\sum_{j\ge0}\bigl(2^{sj}\sigma_{2^{dj}}(f)_p\bigr)^{\tau_s}<\infty$,
    with equivalent norms; and for $0<\gamma<s\le t$ and $0<q\le\infty$
    the $n$-term approximation spaces are
    $\mathcal A^{\gamma/d}_q(L^p)=(L^p,B^s_{\tau_s,\tau_s})_{\gamma/s,q}$.

  *Assessment.* TauCeti has Peetre's $K$-functional of a compatible couple and the real
  interpolation spaces $(X_0,X_1)_{\theta,q}$ for $1\le q\le\infty$, Besov spaces defined by
  Littlewood–Paley decompositions for $p\ge1$, and the Haar basis of $L^p([0,1])$. The
  identification of approximation spaces with interpolation spaces, the quasi-normed range
  $q<1$, Besov spaces with $\tau<1$ defined by moduli of smoothness, and the $n$-term wavelet
  estimates remain gaps.

  *Lean target.* Carriers at the pins: `TauCeti.CompatibleCouple` with
  `CompatibleCouple.kFunctional`, `CompatibleCouple.kMethodENorm`, `CompatibleCouple.kMethod`
  and `CompatibleCouple.KMethodSpace` (normed for `1 ≤ q`), `NASC.bestApproximationError`,
  `ENNReal` with `tsum` and `iSup`, `MeasureTheory.Lp`. New definitions: `approxENorm α q A f`
  in `ℝ≥0∞`, the sum $\sum_{n\ge1}(n^\alpha E_n(f))^qn^{-1}$ raised to $1/q$ in `ℝ≥0∞`, or the
  supremum for `q = ∞`, and the approximation space as the set where it is finite. Conjuncts:
  (i) under the Jackson and Bernstein inequalities, for the couple $(X,Y)$ with
  $\|y\|_Y=\|y\|_X+|y|_Y$, $0<\gamma<r$ and $1\le q\le\infty$, `approxENorm γ q` and
  `kMethodENorm (γ / r) q` are finite for the same elements and are equivalent there; (ii) the
  same for $0<q<1$, which needs a quasi-normed $K$-method; (iii) the $n$-term Jackson and
  Bernstein inequalities for $\Sigma_N$; (iv) the characterization of $B^s_{\tau,\tau}$ by
  $\sigma_{2^{dj}}$ and the interpolation identity. Pitfalls: a real `tsum` of a non-summable
  family is $0$, so the approximation norm must be extended-valued; `bestApproximationError`
  is a real `sInf`, safe only because $0\in X_n$ makes the set nonempty and bounded below. (i)
  is statable at the pins; (ii)–(iv) need wavelet bases of $L^p(\mathbb R^d)$ (11.15–11.17) and
  Besov spaces with $\tau<1$, which no library has, since `TauCeti.BesovSpace` requires
  `1 ≤ p`. Depends on 11.15–11.17. NASC: `NASC.bddAbove_approximation_iff_bddAbove_KFunctional`
  (sorry) is (i) for `q = ∞` with $\alpha=\gamma$, written with its own $K$-functional, an
  `sInf` over `Y` of $\|x-y\|+t(\|y\|+|y|_Y)$, instead of `CompatibleCouple.kFunctional`, and
  without the hypotheses on existence of best approximations and $E_n(f)\to0$; finite
  exponents have no declaration.
## 12. Orthogonal polynomials and numerical quadrature

[Synopsis](SYNOPSIS.md#12-orthogonal-polynomials-and-numerical-quadrature) · [Coverage inventory](STRUCTURE.md#12-orthogonal-polynomials-and-numerical-quadrature)

Gaussian quadrature rests on a common moment, polynomial and spectral
framework: the Hankel criterion, the three-term recurrence, the zeros of the
orthogonal polynomials and the Jacobi matrix. The libraries treat the
Chebyshev measure as a worked case. The integration-error gaps include
convergence theory for sequences of rules, Peano kernels, the Euler–Maclaurin
remainder, and exponential estimates for analytic integrands.

Throughout, $\mu$ is a
positive Borel measure on $\mathbb R$ whose **moments**
$\mu_r=\int t^r\,d\mu(t)$, $r\in\mathbb N_0$, are all finite, and whose
**support** (the set of points every neighbourhood of which has positive
measure) is an infinite set, unless stated otherwise. The **support interval**
$[a,b]$ is the convex hull of the support; $a=-\infty$ or $b=+\infty$ is
allowed unless the support is said to be compact. Write
$(u,v)=\int uv\,d\mu$ and $\|u\|=(u,u)^{1/2}$ for real polynomials $u,v$. An
**$n$-point quadrature rule** for $\mu$ is a functional
$Q_n(f)=\sum_{k=1}^n w_kf(x_k)$ with distinct real **nodes** $x_k$ and real
**weights** $w_k$; its error is $E_n(f)=\int f\,d\mu-Q_n(f)$. The rule has
**degree of exactness** $d$ if $E_n(p)=0$ for all $p\in\mathbb P_d$, and it is
**interpolatory** if it has degree of exactness $n-1$. The **Gauss rule**
$Q_n^G$ is the unique $n$-point rule with degree of exactness $2n-1$
(synopsis 12.5); its nodes are the zeros of $\pi_n$.

### Orthogonal polynomials

* **12.1. Existence.** For $n\in\mathbb N$ let $\Delta_n=\det[\mu_{i+j}]_{i,j=0}^{n-1}$
  be the Hankel determinant of the moments. The form $(\cdot,\cdot)$ is
  positive definite on all real polynomials if and only if $\Delta_n>0$ for
  every $n\ge1$; this holds because the support is infinite. There is then a
  unique sequence of **monic orthogonal polynomials** $\pi_k(t)=t^k+\cdots$,
  $k\in\mathbb N_0$, with $(\pi_k,\pi_l)=0$ for $k\ne l$. The **orthonormal
  polynomials** are $p_k=\pi_k/\|\pi_k\|$. For each $n$, the polynomials
  $\pi_0,\dots,\pi_n$ form a basis of $\mathbb P_n$, and $\pi_n$ is orthogonal
  to $\mathbb P_{n-1}$.

  *Assessment.* Mathlib has the Chebyshev polynomials as an orthogonal family
  for the Chebyshev measure, and TauCeti assembles Hilbert bases from
  orthogonal systems of exact degree for weighted measures with a finite
  exponential moment. No library constructs the monic orthogonal sequence of
  a general moment measure or relates its existence to the Hankel
  determinants.

  *Lean target.* Carriers at the pins: `MeasureTheory.Measure ℝ`,
  `MeasureTheory.Integrable`, `MeasureTheory.Measure.support`, `Polynomial.Monic`,
  `Polynomial.natDegree`, `Polynomial.degreeLE`, `Polynomial.degreeLT`, `Matrix.det` and
  `Matrix.PosDef`. This project supplies the predicate `NASC.HasInfiniteMomentSupport μ`
  (every monomial is integrable and no finite set has full measure), the pairing
  `NASC.polynomialMomentPair μ p q` (the integral of the product) and
  `NASC.IsMonicOrthogonalSeq μ p` for `p : ℕ → ℝ[X]`. New definitions: the moment
  `∫ t, t ^ r ∂μ : ℝ` and the Hankel matrix of order `n`, a `Matrix (Fin n) (Fin n) ℝ` with
  entry $(i,j)$ the moment of order $i+j$. Conjuncts: (i) if every monomial is integrable,
  the pairing is positive on nonzero polynomials if and only if the Hankel determinant of
  every order $n\ge1$ is positive; (ii) `HasInfiniteMomentSupport μ` implies that
  positivity; (iii) there is exactly one `p` with `IsMonicOrthogonalSeq μ p`; (iv) for each
  `n`, `p 0, …, p n` is a basis of `degreeLE ℝ n` and `p n` is orthogonal to every element
  of `degreeLT ℝ n`. Pitfalls: a Bochner integral of a non-integrable monomial is `0`, so
  integrability of every monomial is a hypothesis, never implied by the integrals being
  written; integrability of the constant `1` makes `μ` finite; `p k / ‖p k‖` needs the
  positivity of (ii), or the division is junk. The finite-set condition of
  `HasInfiniteMomentSupport` is equivalent to `(μ.support).Infinite` for a finite measure on
  $\mathbb R$; stating (ii) with the support needs that small lemma. Everything is statable
  and provable at the pins; 12.2–12.8 depend on this entry. NASC:
  `NASC.existsUnique_monicOrthogonal` states (iii) and is `sorry`; (i), (ii) and (iv) are not
  stated. The helpers `NASC.HasInfiniteMomentSupport.polynomialMomentPair_self_pos`,
  `NASC.polynomialMomentPair_eq_zero_of_degree_lt` and
  `NASC.eq_of_monic_polynomialMomentPair_eq_zero` are proved.

* **12.2. Three-term recurrence and Favard's theorem.** The monic orthogonal
  polynomials satisfy
  $$\pi_{k+1}(t)=(t-\alpha_k)\pi_k(t)-\beta_k\pi_{k-1}(t),\qquad
  k\in\mathbb N_0,\qquad \pi_{-1}=0,\ \pi_0=1,$$
  with
  $$\alpha_k=\frac{(t\pi_k,\pi_k)}{(\pi_k,\pi_k)},\qquad
  \beta_k=\frac{(\pi_k,\pi_k)}{(\pi_{k-1},\pi_{k-1})}>0\quad(k\ge1),$$
  and, with the convention $\beta_0=\mu(\mathbb R)$, one has
  $\|\pi_n\|^2=\beta_0\beta_1\cdots\beta_n$. The orthonormal polynomials
  satisfy
  $$\sqrt{\beta_{k+1}}\,p_{k+1}(t)=(t-\alpha_k)p_k(t)-\sqrt{\beta_k}\,p_{k-1}(t),
  \qquad p_{-1}=0,\ p_0=\beta_0^{-1/2}.$$
  If the support interval $[a,b]$ is bounded, then $a<\alpha_k<b$ for all
  $k\in\mathbb N_0$ and $0<\beta_k\le\max(a^2,b^2)$ for all $k\ge1$.
  Conversely (**Favard's theorem**), if $\alpha_k\in\mathbb R$ for
  $k\in\mathbb N_0$ and $\beta_k>0$ for $k\in\mathbb N$, then the monic
  polynomials defined by the recurrence above are orthogonal with respect to
  some positive measure on $\mathbb R$ with infinite support and finite moments.

  *Assessment.* The libraries have recurrences for individual families, such
  as the Chebyshev recurrence. The gap is the general recurrence with the
  stated coefficients and their bounds, and Favard's converse, which
  constructs a measure from positive recurrence coefficients.

  *Lean target.* Carriers at the pins: `Polynomial.X`, `Polynomial.C`, `Real.sqrt`,
  `MeasureTheory.IsFiniteMeasure`, and the 12.1 carriers; no library has a carrier for the
  polynomials of a general recurrence. New definitions: the coefficients `α μ k` and
  `β μ k : ℝ` as the quotients of pairings in the statement, with `β μ 0` equal to
  `(μ univ).toReal`, and the recurrence polynomials of sequences `α β : ℕ → ℝ`, a function
  `ℕ → ℝ[X]` with `p 0 = 1`, `p 1 = X - C (α 0)` and the recurrence for `p (k + 2)`. Conjuncts:
  (i) the monic recurrence with these coefficients; (ii) `0 < β μ k` for `k ≥ 1` and
  `‖π_n‖² = ∏ k ∈ range (n + 1), β μ k`; (iii) the orthonormal recurrence; (iv) if
  `∀ᵐ t ∂μ, t ∈ Icc a b`, then `α μ k ∈ Ioo a b` and `β μ k ≤ max (a ^ 2) (b ^ 2)` for
  `k ≥ 1` (both hold for any interval containing the support, so the endpoints need not be
  the convex hull); (v) Favard: for all `α`, and `β` with `0 < β (k + 1)` for every `k`,
  there is a finite measure with `HasInfiniteMomentSupport` for which the recurrence
  polynomials are monic orthogonal. Pitfalls: `(μ univ).toReal` is `0` for an infinite
  measure, harmless here because (i) of 12.1 makes `μ` finite, but the finiteness must be in
  scope; `Real.sqrt` of a negative number is `0`, so the orthonormal recurrence needs the
  positivity of (ii); the shift between the source indexing ($\pi_{-1}=0$) and a recursion
  on `ℕ` with two base cases. (i)–(iv) are statable and provable at the pins. (v) needs
  infrastructure no library has: either the Hamburger moment problem (a positive linear
  functional on `ℝ[X]` is integration against a measure) or a weak-limit argument for the
  discrete Gauss measures of 12.6 together with moment convergence. Depends on 12.1; 12.4
  and 12.8 use (i)–(ii). NASC: `NASC.exists_monicOrthogonal_threeTerm` states the
  recurrence with some coefficients `a b` and `0 < b (n + 1)` but not their formulas, the
  norm product, the orthonormal form or the bounds;
  `NASC.exists_measure_monicOrthogonal_of_threeTerm` states (v)
  with a probability measure; both are `sorry`.

* **12.3. Zeros.** For $n\ge1$, all zeros of $\pi_n$ are real and simple and
  lie in the open interval $(a,b)$, where $[a,b]$ is the support interval. The
  zeros of $\pi_n$ and $\pi_{n+1}$ strictly interlace: if
  $\tau^{(m)}_1>\cdots>\tau^{(m)}_m$ are the zeros of $\pi_m$, then
  $$\tau^{(n+1)}_{n+1}<\tau^{(n)}_n<\tau^{(n+1)}_n<\cdots<\tau^{(n)}_1
  <\tau^{(n+1)}_1.$$
  Every open interval $(c,d)$ with $\mu((c,d))=0$ contains at most one zero of
  $\pi_n$.

  *Assessment.* Partly covered. For the Chebyshev measure, Mathlib proves that
  the zeros of $T_n$ are the $n$ points $\cos((2k+1)\pi/(2n))$, each of
  multiplicity one; since $2^{1-n}T_n$ is the monic orthogonal polynomial of
  degree $n\ge1$, this is the first claim in that case. Interlacing and the
  general measure are open.

  *Scope.* The target is the general measure: reality, simplicity and
  location of the zeros, strict interlacing, and the bound on zeros in a gap
  of the support.

  *Lean target.* Carriers at the pins: `Polynomial.roots`, `Multiset.card`, `Multiset.Nodup`,
  `Multiset.filter`, `Polynomial.rootMultiplicity`, `StrictMono`, and for the Chebyshev case
  `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.measureT`, `Polynomial.Chebyshev.roots_T_real`
  and `Polynomial.Chebyshev.rootMultiplicity_T_real`. No new definition is needed beyond 12.1.
  Conjuncts, for `p` with `IsMonicOrthogonalSeq μ p` and `n ≥ 1`: (i) `(p n).roots.card = n`
  and `(p n).roots.Nodup`; (ii) every root `τ` satisfies `0 < μ (Iio τ)` and
  `0 < μ (Ioi τ)`, which says $\tau\in(a,b)$ without naming the endpoints and covers
  unbounded support; (iii) with strictly increasing enumerations `x : Fin n → ℝ` of the
  roots of `p n` and `y : Fin (n + 1) → ℝ` of those of `p (n + 1)`,
  `y i.castSucc < x i < y i.succ` for every `i`; (iv) if `μ (Ioo c d) = 0`, then
  `((p n).roots.filter (· ∈ Ioo c d)).card ≤ 1`. Pitfalls: `roots` counts multiplicity, so
  simplicity is the `Nodup` conjunct and not a consequence of the cardinality; the source
  numbers zeros in decreasing order from $1$, an ascending `Fin` enumeration reverses it.
  Everything is statable and provable at the pins. Depends on 12.1; 12.6 and 12.8 use (i)
  and (ii). NASC: `NASC.exists_monicOrthogonal_interlacing_roots` (`sorry`) states
  enumerations of the roots of `p n` and `p (n + 1)` by lists and strict interlacing, with no
  interval hypothesis; `NASC.monicOrthogonal_roots_mem_Ioo` (`sorry`) states the location of the
  roots in `Ioo a b` under `∀ᵐ x ∂μ, x ∈ Icc a b`, a bounded-support form of (ii); (iv) is not
  stated.

* **12.4. Jacobi matrix and Christoffel–Darboux formula.** The **Jacobi
  matrix** of order $n$ is the real symmetric tridiagonal matrix $J_n$ with
  diagonal entries $\alpha_0,\dots,\alpha_{n-1}$ and off-diagonal entries
  $\sqrt{\beta_1},\dots,\sqrt{\beta_{n-1}}$. Then $\pi_n(t)=\det(tI-J_n)$; the
  zeros of $\pi_n$ are the eigenvalues of $J_n$, and an eigenvector for the
  zero $\tau$ is $(p_0(\tau),\dots,p_{n-1}(\tau))^\top$. For $n\in\mathbb N_0$
  and real $x\ne t$,
  $$\sum_{k=0}^np_k(x)p_k(t)=\sqrt{\beta_{n+1}}\,
  \frac{p_{n+1}(x)p_n(t)-p_n(x)p_{n+1}(t)}{x-t},$$
  and
  $$\sum_{k=0}^np_k(t)^2=\sqrt{\beta_{n+1}}\,
  \bigl(p_{n+1}'(t)p_n(t)-p_n'(t)p_{n+1}(t)\bigr).$$

  *Assessment.* The spectral theorem for real symmetric matrices is
  available. The gap relates the characteristic polynomial and the
  eigenvectors of the Jacobi matrix to the orthogonal family, and proves the
  Christoffel–Darboux identities.

  *Lean target.* Carriers at the pins: `Matrix.charpoly` (the determinant of `X • 1 - M`,
  hence monic), `Matrix.IsHermitian`, `Matrix.IsHermitian.eigenvalues`,
  `Matrix.IsHermitian.eigenvectorBasis`, `Matrix.mulVec`, `spectrum`, `Polynomial.derivative`.
  This project defines `NASC.jacobiMatrix a b n : Matrix (Fin n) (Fin n) ℝ` with diagonal
  `a i` and off-diagonal `Real.sqrt (b j)` at the positions $(j-1,j)$ and $(j,j-1)$.
  Conjuncts: (i) for recurrence polynomials `p` with coefficients `a b` and `0 ≤ b (k + 1)`,
  `(jacobiMatrix a b n).charpoly = p n`, a purely algebraic statement; (ii) with the
  coefficients of 12.2, for every root `τ` of `π_n` the vector `fun k : Fin n ↦ (p k).eval τ`
  of orthonormal values is an eigenvector with eigenvalue `τ`; (iii) Christoffel–Darboux in
  the multiplied form `(x - t) * ∑ k ∈ range (n + 1), p_k(x) p_k(t) = …`, which needs no
  hypothesis `x ≠ t`; (iv) the confluent form with `Polynomial.derivative`. Pitfalls:
  `Matrix.IsHermitian.eigenvalues` is indexed without an order matching the zeros, so
  compare as multisets with `(π n).roots`; `Real.sqrt` of a negative `b` is `0`, which is
  why (i) keeps `0 ≤ b`; the source writes $\det(J_j-xI)$, which differs from
  `Matrix.charpoly` by $(-1)^j$; for `n = 0` the empty matrix has characteristic polynomial
  `1`. Everything is statable and provable at the pins. Depends on 12.2; 12.7 uses (i)
  and (ii). NASC: `NASC.charpoly_jacobiMatrix_eq` states (i) and is `sorry`; (ii)–(iv) are
  not stated.

### Gaussian quadrature

* **12.6. Properties of the Gauss rule.** Let $x_1,\dots,x_n$ and
  $w_1,\dots,w_n$ be the nodes and weights of $Q_n^G$.
  - The nodes are distinct and lie in the open support interval $(a,b)$.
  - The weights are positive: $w_k=\int\ell_k^2\,d\mu>0$, and
    $\sum_kw_k=\mu(\mathbb R)$.
  - The weights are the **Christoffel numbers**
    $$w_k=\Bigl(\sum_{j=0}^{n-1}p_j(x_k)^2\Bigr)^{-1},\qquad k=1,\dots,n.$$
  - (Markov) For every $f$ differentiable at the nodes,
    $Q_n^G(f)=\int h\,d\mu$, where $h\in\mathbb P_{2n-1}$ is the Hermite
    interpolant with $h(x_k)=f(x_k)$ and $h'(x_k)=f'(x_k)$ for all $k$.

  *Assessment.* For the Chebyshev measure, Mathlib proves that the rule with
  the zeros of $T_n$ and the weights $\pi/n$ is exact through degree $2n-1$;
  this is the Chebyshev case of the Gauss rule, without the general weight
  formulas. TauCeti has Hermite interpolation with prescribed jets at
  distinct nodes. The gap links the orthogonal zeros to the positive rule,
  its weights and its Hermite form for a general measure.

  *Lean target.* Carriers at the pins: `Lagrange.basis`, `Lagrange.interpolate`,
  `Lagrange.nodal`, `Polynomial.hasseJet` and `Polynomial.hasseJet_surjective` from
  TauCeti (the jets of multiplicity $2$ are the values and first derivatives),
  `Polynomial.derivative`, `deriv`, `DifferentiableAt`, and for the Chebyshev case
  `Polynomial.Chebyshev.integral_eq_sumZeroes` with `Polynomial.Chebyshev.sumZeroes`. This
  project defines `NASC.IsGaussRule μ x w` for `x w : Fin n → ℝ` (injective nodes, and
  exactness for every polynomial of `natDegree < 2 * n`). Conjuncts, for `n ≥ 1`: (i) the
  nodes are the roots of `π_n` and lie in the open support interval, stated as in 12.3 (ii);
  (ii) `w i = ∫ ℓ_i² ∂μ` and `0 < w i`; (iii) `∑ i, w i = (μ univ).toReal`; (iv) Christoffel
  numbers in the form `w i * ∑ j ∈ range n, (p_j(x i))² = 1`, which avoids an inverse of a
  possibly zero sum; (v) for `f : ℝ → ℝ` with `DifferentiableAt ℝ f (x i)` for every `i`,
  `∑ i, w i * f (x i) = ∫ t, h.eval t ∂μ` for the polynomial `h` of `degree < 2 * n` with
  `h.eval (x i) = f (x i)` and `(derivative h).eval (x i) = deriv f (x i)`. Pitfalls: for
  `n = 0` `IsGaussRule` is vacuous and the weight sum is `0`, not $\mu(\mathbb R)$, so (iii)
  needs `n ≥ 1`; `deriv f` is `0` where `f` is not differentiable, so (v) must keep the
  differentiability hypothesis. Everything is statable and provable at the pins; existence
  of the Gauss rule is 12.5, not selected, and is a hypothesis here. Depends on 12.1, 12.3,
  12.5. NASC: `NASC.IsGaussRule.eq_nodal` (the monic orthogonal polynomial is the nodal
  polynomial of the nodes), `NASC.IsGaussRule.weight_eq_integral_basis_sq` (positive weights
  $w_i=\int\ell_i^2\,d\mu$) and their combination `NASC.IsGaussRule.roots_and_weights` are proved
  and give the root part of (i) and all of (ii); the interior location, (iii), (iv) and (v) are
  not stated.

* **12.7. Golub–Welsch.** Let $J_n=V\,\mathrm{diag}(x_1,\dots,x_n)\,V^\top$
  with $V$ orthogonal and columns $v_1,\dots,v_n$. Then the nodes of the
  $n$-point Gauss rule are the eigenvalues $x_k$ of $J_n$, and its weights
  are
  $$w_k=\beta_0\,v_{k,1}^2=\mu(\mathbb R)\,v_{k,1}^2,\qquad k=1,\dots,n,$$
  where $v_{k,1}$ is the first component of the unit eigenvector $v_k$.

  *Assessment.* The spectral decomposition of real symmetric matrices is
  available. The gap retrieves the Gauss nodes and weights from the
  eigenvalues and the squared first components of the eigenvectors of the
  Jacobi matrix.

  *Lean target.* Carriers at the pins: `Matrix.IsHermitian.spectral_theorem`,
  `Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.eigenvalues`, `Matrix.transpose`,
  `Matrix.diagonal`, `NASC.jacobiMatrix` and `NASC.IsGaussRule`. Conjunct: for `n ≥ 1`, the
  recurrence coefficients of 12.2, an orthogonal `Q : Matrix (Fin n) (Fin n) ℝ`
  (`Qᵀ * Q = 1`) and `x : Fin n → ℝ` with `jacobiMatrix a b n * Q = Q * diagonal x`, the pair
  `x` and `fun i ↦ (μ univ).toReal * Q 0 i ^ 2` is a Gauss rule. Injectivity of `x` is part
  of the conclusion and follows from the simplicity of the eigenvalues of an unreduced
  tridiagonal matrix. Pitfalls: `(μ univ).toReal` is junk `0` for an infinite measure, so the
  finiteness from 12.1 must be available; `Q 0 i` is the first component of column `i`, the
  eigenvector for `x i`, and indexing the row instead silently gives a different rule; the
  eigenvalue order of `Matrix.IsHermitian.eigenvalues` is arbitrary, so the statement
  quantifies over all diagonalizations. Everything is statable and provable at the pins.
  Depends on 12.4 and 12.6. NASC: `NASC.isGaussRule_of_jacobiDiagonalization` states this
  for `n + 1` nodes and is `sorry`.

* **12.8. Error of Gauss, Gauss–Radau and Gauss–Lobatto rules.** Assume
  in this item that the support of $\mu$ is compact, with support interval
  $[a,b]$.
  - If $f\in C^{2n}[a,b]$, then for some $\xi\in(a,b)$,
    $$\int f\,d\mu-Q_n^G(f)=\frac{f^{(2n)}(\xi)}{(2n)!}\int\pi_n^2\,d\mu
    =\frac{f^{(2n)}(\xi)}{(2n)!}\,\beta_0\beta_1\cdots\beta_n.$$
  - (Gauss–Radau) Let $d\mu_a(t)=(t-a)\,d\mu(t)$. The $(n+1)$-point rule
    with nodes $a$ and the $n$ zeros of $\pi_n(\cdot\,;\mu_a)$, with
    interpolatory weights, has degree of exactness $2n$. For
    $f\in C^{2n+1}[a,b]$ its error is
    $\gamma^a_nf^{(2n+1)}(\xi)/(2n+1)!$ for some $\xi\in(a,b)$, where
    $\gamma^a_n=\int\pi_n(t;\mu_a)^2\,d\mu_a(t)>0$.
  - (Gauss–Lobatto) Let $d\mu_{a,b}(t)=(t-a)(b-t)\,d\mu(t)$. The
    $(n+2)$-point rule with nodes $a$, $b$ and the $n$ zeros of
    $\pi_n(\cdot\,;\mu_{a,b})$, with interpolatory weights, has degree of
    exactness $2n+1$. For $f\in C^{2n+2}[a,b]$ its error is
    $-\gamma_nf^{(2n+2)}(\xi)/(2n+2)!$ for some $\xi\in(a,b)$, where
    $\gamma_n=\int\pi_n(t;\mu_{a,b})^2\,d\mu_{a,b}(t)>0$.

  *Assessment.* Mathlib has the first mean value theorem for integrals and
  Taylor remainders, and TauCeti has Hermite interpolation. The gap is the
  Hermite interpolation remainder and the three error formulas with their
  exact constants, which need the weighted orthogonality for $\mu_a$ and
  $\mu_{a,b}$.

  *Lean target.* Carriers at the pins: `ContDiffOn`, `iteratedDerivWithin`, `iteratedDeriv`,
  `MeasureTheory.Measure.withDensity`, `exists_eq_const_mul_setIntegral_of_nonneg` (first mean
  value theorem, root namespace), `exists_hasDerivAt_eq_zero` (Rolle), `Polynomial.hasseJet`,
  `NASC.IsGaussRule` and `NASC.IsMonicOrthogonalSeq`. New definitions: the measures
  `μ.withDensity (fun t ↦ ENNReal.ofReal (t - a))` and the analogue with `(t - a) * (b - t)`,
  and the Radau and Lobatto rules as `Fin (n + 1)` and `Fin (n + 2)` node and weight
  families. Conjuncts, with `a < b`, `∀ᵐ t ∂μ, t ∈ Icc a b`, `HasInfiniteMomentSupport μ` and
  `n ≥ 1`: (i) for `ContDiffOn ℝ (2 * n) f (Icc a b)` there is `ξ ∈ Ioo a b` with the Gauss
  error equal to `iteratedDerivWithin (2 * n) f (Icc a b) ξ / (2 * n)! * ∫ π_n² ∂μ`, and
  `∫ π_n² ∂μ` equals the product of 12.2 (ii); (ii) the Radau rule is exact through degree
  `2 * n` and has the stated error under `ContDiffOn ℝ (2 * n + 1)`; (iii) the Lobatto rule
  likewise through degree `2 * n + 1` under `ContDiffOn ℝ (2 * n + 2)`; (iv) `0 < γ` in both
  cases. Pitfalls: `ENNReal.ofReal` clips negative densities, so the support hypothesis is
  what makes `withDensity` equal to $(t-a)\,d\mu$; `iteratedDeriv` of a function that is only
  $C^{2n}$ on `Icc a b` is junk outside, so use `iteratedDerivWithin` or a global
  hypothesis; the mean value point must lie in the open interval. Needs the Hermite
  interpolation remainder $f-h=f^{(2n)}(\xi)\,\omega_n^2/(2n)!$, absent from every library;
  the Lagrange remainder of 10.5 is the model. Depends on 10.5, 12.1, 12.2 and 12.6. NASC:
  `NASC.exists_gauss_remainder` states (i) without the product formula, for
  `ContDiffOn ℝ (2 * n) f (Icc a b)` (the derivative at the interior point $\xi$ written with
  `iteratedDeriv`), and is `sorry`; (ii)–(iv) are not stated.

* **12.9. Convergence of quadrature rules.** Let $w\ge0$ be an integrable
  weight function on a compact interval $[a,b]$ with $\int_a^bw>0$, let
  $Q(g)=\int_a^bwg$, and let $(Q_n)$ be a sequence of rules
  $Q_n(g)=\sum_{j=1}^{m_n}w_{n,j}g(x_{n,j})$ with all nodes in $[a,b]$.
  - (Pólya–Szegő) $Q_n(g)\to Q(g)$ for every $g\in C[a,b]$ if and only if
    $Q_n(g)\to Q(g)$ for every $g$ in some dense subset of $C[a,b]$ and
    $\sup_n\sum_j|w_{n,j}|<\infty$.
  - (Steklov) If all weights are nonnegative and $Q_n(1)\to Q(1)$, then
    $Q_n(g)\to Q(g)$ for every $g\in C[a,b]$ if and only if this holds for
    every $g$ in a dense subset; in particular, it holds if every polynomial
    is integrated exactly by $Q_n$ for all large $n$.
  - For the $n$-point Gauss rule and every $f\in C[a,b]$,
    $$\Bigl|\int_a^bwf-Q_n^G(f)\Bigr|\le2\Bigl(\int_a^bw\Bigr)
    \inf_{p\in\mathbb P_{2n-1}}\|f-p\|_\infty,$$
    so the Gauss rules converge for every continuous $f$.

  *Assessment.* Mathlib has the Banach–Steinhaus theorem and the density of
  polynomials in $C[a,b]$. The gap is the convergence criterion for sequences
  of rules, its positive-weight form, and the near-best bound that gives
  convergence of the Gauss rules for every continuous function.

  *Lean target.* Carriers at the pins: `C(Set.Icc a b, ℝ)` with its supremum norm,
  `ContinuousLinearMap` with `ContinuousLinearMap.opNorm`, `banach_steinhaus`
  (Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean), `Dense`,
  `polynomialFunctions_closure_eq_top`, `MeasureTheory.IntegrableOn`, and
  `NASC.bestApproximationError` for the infimum. New definitions: a rule as a `Finset` of
  nodes in `Icc a b` with a weight function, and its evaluation as a continuous linear
  functional on `C(Set.Icc a b, ℝ)`. Conjuncts, with `a < b`, `w` integrable and nonnegative on
  `Icc a b` and `0 < ∫ x in a..b, w x`: (i) pointwise convergence on `C(Icc a b, ℝ)` if and
  only if convergence on a dense set and `BddAbove` of the weight sums `∑ j, |w n j|`;
  (ii) with nonnegative weights and convergence at `1`, convergence on a dense set suffices,
  and exactness on all polynomials for large `n` suffices; (iii) for `n ≥ 1` the Gauss error
  is at most `2 * (∫ w) * bestApproximationError` over `degreeLT ℝ (2 * n)` mapped to
  `C(Icc a b, ℝ)`, and the Gauss rules converge for every continuous `f`. Pitfalls: the norm
  of the functional equals `∑ j, |w n j|` only for distinct nodes, so repeated nodes must be
  merged or excluded; a weight given as `ℝ → ℝ` must be integrable, or the Bochner integral
  is `0` and the hypothesis `0 < ∫ w` fails silently; the infimum is over a nonempty set
  bounded below, so `sInf` is not junk. Everything is statable and provable at the pins.
  Depends on 12.5 and on 12.6 (ii)–(iii) for the Gauss part; 12.15 uses (ii). NASC: none.

### Interpolatory rules, Euler–Maclaurin and extrapolation

* **12.10. Peano kernel theorem.** Let $n\in\mathbb N_0$ and let
  $$R(f)=\sum_{j=0}^n\sum_ka_{jk}f^{(j)}(x_{jk})-\int_a^bf(x)\,dx$$
  be a finite linear combination of point values of derivatives of order at
  most $n$ at points $x_{jk}\in[a,b]$, minus the integral. Suppose $R(p)=0$
  for all $p\in\mathbb P_n$. Then for every $f\in C^{n+1}[a,b]$,
  $$R(f)=\int_a^bK(t)f^{(n+1)}(t)\,dt,\qquad
  K(t)=\frac1{n!}R_x\bigl[(x-t)_+^n\bigr],$$
  where $(x-t)_+^n$ equals $(x-t)^n$ for $x\ge t$ and $0$ for $x<t$, and
  $R_x$ acts on the variable $x$. The function $K$ is the **Peano kernel**.
  If $K$ does not change sign on $[a,b]$, then for every $f\in C^{n+1}[a,b]$
  there is $\xi\in(a,b)$ with
  $$R(f)=\frac{R(x^{n+1})}{(n+1)!}\,f^{(n+1)}(\xi).$$

  *Assessment.* Mathlib has Taylor's theorem with integral remainder and the
  first mean value theorem for integrals, the two ingredients. The gap is the
  kernel representation of every such functional that annihilates
  $\mathbb P_n$, and the mean-value form for a kernel of constant sign.

  *Lean target.* Carriers at the pins: `taylor_integral_remainder` (Mathlib, with
  `taylorWithinEval` and `iteratedDerivWithin` on `uIcc`), `intervalIntegral`, `ContDiffOn`,
  `iteratedDerivWithin`, `exists_eq_const_mul_setIntegral_of_nonneg`. New definitions: the
  functional, given by a finite family of triples (order `j ≤ n`, point in `Icc a b`,
  coefficient), as a map `(ℝ → ℝ) → ℝ`; the truncated power `fun x ↦ if t ≤ x then (x - t) ^ n
  else 0`; the kernel `K t`. Conjuncts, with `a < b` and `ContDiffOn ℝ (n + 1) f (Icc a b)`:
  (i) the representation; (ii) if `(∀ t ∈ Icc a b, 0 ≤ K t)` or `(∀ t ∈ Icc a b, K t ≤ 0)`,
  there is `ξ ∈ Ioo a b` with the mean-value form, using `R (fun x ↦ x ^ (n + 1))`.
  Pitfalls: the truncated power is only $C^{n-1}$, so its derivative of order $n$ is a step
  function and `iteratedDeriv n` returns junk at the kink $x=t$; the kernel is then defined
  for almost every `t`, and the statement must either use an a.e. equality or compute the
  derivatives of the truncated power by hand; `0 ^ 0 = 1` in Lean makes the case `n = 0`
  agree with $(x-t)_+^0=\mathbf 1_{x\ge t}$. Everything is statable and provable at the pins.
  12.11, 12.12 and 12.13 use it. NASC: `NASC.quadrature_error_eq_peanoKernel` (`sorry`)
  states (i) for point-value rules only (no derivative values), for
  `ContDiffOn ℝ (n + 1) f (Icc a b)`; (ii) is not stated.

* **12.12. Euler–Maclaurin formula.** The **Bernoulli numbers** $B_k$ are
  defined by $z/(e^z-1)=\sum_{k\ge0}B_kz^k/k!$ for $|z|<2\pi$. Let
  $N\in\mathbb N$, $h=(b-a)/N$, and let
  $$T(h)=h\Bigl(\tfrac12f(a)+\sum_{i=1}^{N-1}f(a+ih)+\tfrac12f(b)\Bigr)$$
  be the composite trapezoidal sum. If $m\in\mathbb N_0$ and
  $f\in C^{2m+2}[a,b]$, then for some $\xi\in(a,b)$,
  $$T(h)=\int_a^bf\,dx+\sum_{l=1}^m\frac{B_{2l}}{(2l)!}h^{2l}
  \bigl(f^{(2l-1)}(b)-f^{(2l-1)}(a)\bigr)
  +\frac{B_{2m+2}}{(2m+2)!}h^{2m+2}(b-a)f^{(2m+2)}(\xi).$$
  In particular, if $f$ extends to a $(b-a)$-periodic function of class
  $C^{2m+2}$ on $\mathbb R$, then
  $|T(h)-\int_a^bf|\le|B_{2m+2}|(b-a)\|f^{(2m+2)}\|_\infty h^{2m+2}/(2m+2)!$.

  *Assessment.* Partly covered. TauCeti proves Euler–Maclaurin between
  integer endpoints with an integral remainder involving a periodic Bernoulli
  function, and Mathlib bounds the composite trapezoidal error by a second
  derivative bound, the bound form of the case $m=0$. The mesh form follows
  by an affine change of variable; the mean-value remainder needs the sign of
  the periodic Bernoulli kernel.

  *Scope.* The target includes the composite mesh weights, the derivative
  error formula and the periodic smooth-function estimate.

  *Lean target.* Carriers at the pins: `TauCeti.sum_Icc_eq_eulerMaclaurin` (integer endpoints
  `a ≤ n`, `1 ≤ m`, `ContDiffOn ℝ (2 * m) f (Icc a n)`, remainder with `bernoulliFun` and
  `Int.fract`), `bernoulli` and `bernoulliFun` (Mathlib), `trapezoidal_integral f N a b`,
  `trapezoidal_error`, `trapezoidal_error_le_of_c2`, `exists_eq_const_mul_setIntegral_of_nonneg`
  and `Function.Periodic`. No new definition is needed: `trapezoidal_integral f N a b` is
  $T(h)$. Conjuncts, with `a < b`, `0 < N` and `ContDiffOn ℝ (2 * m + 2) f (Icc a b)`: (i) the
  expansion with `iteratedDerivWithin` on `Icc a b` and some `ξ ∈ Ioo a b`; (ii) if
  `Function.Periodic f (b - a)`, `ContDiff ℝ (2 * m + 2) f` and
  `∀ x, |iteratedDeriv (2 * m + 2) f x| ≤ M`, the error bound with `M` in place of the
  supremum norm. Pitfalls: Mathlib's `bernoulli` has $B_1=-1/2$ and `bernoulli'` has
  $B_1=+1/2$, which agree at every even index used here; `2 * l - 1` is natural subtraction,
  correct for `l ≥ 1`; a supremum norm written as `⨆ x, |…|` is `0` for an unbounded
  derivative, hence the explicit bound `M`; `trapezoidal_integral` with `N = 0` divides by
  zero. Everything is statable and provable at the pins. Depends on 12.10 only through the
  sign argument; 12.13 uses (i). NASC: `NASC.exists_compositeTrapezoid_eulerMaclaurin`
  (`sorry`) states (i) with its own trapezoidal sum, for `ContDiffOn ℝ (2 * m + 2) f (Icc a b)`
  with one-sided endpoint derivatives (`iteratedDerivWithin`); (ii) is not stated.

### Exponentially convergent quadrature

* **12.14. Trapezoidal rule for analytic integrands.**
  - Let $v$ be $2\pi$-periodic on $\mathbb R$, analytic in the strip
    $|\mathrm{Im}\,\theta|<a$ for some $a>0$, with $|v|\le M$ there. Let
    $I=\int_0^{2\pi}v\,d\theta$ and $I_N=(2\pi/N)\sum_{k=1}^Nv(2\pi k/N)$.
    Then for every $N\in\mathbb N$,
    $$|I_N-I|\le\frac{4\pi M}{e^{aN}-1},$$
    and the constant $4\pi$ cannot be reduced. If instead $v$ is analytic
    and bounded by $M$ in the half-plane $\mathrm{Im}\,\theta>-a$, then
    $|I_N-I|\le2\pi M/(e^{aN}-1)$, with $2\pi$ best possible.
  - Let $w$ be analytic in the strip $|\mathrm{Im}\,x|<a$ for some $a>0$,
    with $w(x)\to0$ uniformly as $|x|\to\infty$ in the strip, and with
    $\int_{-\infty}^\infty|w(x+ib)|\,dx\le M$ for all $b\in(-a,a)$. Let
    $I=\int_{-\infty}^\infty w\,dx$. Then for every $h>0$ the sum
    $I_h=h\sum_{k\in\mathbb Z}w(kh)$ exists and
    $$|I_h-I|\le\frac{2M}{e^{2\pi a/h}-1},$$
    and the constant $2M$ cannot be reduced.

  *Assessment.* Mathlib's composite trapezoidal estimate uses a second
  derivative bound, and Mathlib has Cauchy's theorem for rectangles and
  Poisson summation. Exponential convergence needs the contour shift for
  periodic and for decaying analytic functions in a strip, with constants
  depending on the strip width.

  *Lean target.* Carriers at the pins: `AnalyticOnNhd`, `DifferentiableOn`,
  `Function.Periodic`, `intervalIntegral`, `MeasureTheory.Integrable`, `tsum`, `Summable`,
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `fourierCoeffOn`,
  `Real.tsum_eq_tsum_fourier`, `Real.exp`. No new definition is needed. Conjuncts: (i) for
  `v : ℂ → ℂ` analytic on `{z | |z.im| < a}`, bounded by `M` there, with real
  `2 * π`-periodicity, `0 < a` and `0 < N`, the bound `4 * π * M / (Real.exp (a * N) - 1)`;
  (ii) for every `c < 4 * π` some admissible `v`, `a`, `M`, `N` violates the bound with `c`;
  (iii) the half-plane bound with `2 * π` and its sharpness; (iv) for `w` analytic on the
  strip, with uniform decay on the strip and `∫ x, ‖w (x + b * I)‖ ≤ M` together with
  integrability for every `b ∈ Ioo (-a) a`, and `0 < h`, summability of `k ↦ w (k * h)` over
  `ℤ` and the bound `2 * M / (Real.exp (2 * π * a / h) - 1)`; (v) sharpness of `2 * M`.
  Pitfalls: for `N = 0` the step `2 * π / N` is `0` in Lean and the right side divides by
  zero, so `0 < N` is required; a `tsum` of a non-summable family is `0`, so summability is a
  conjunct of (iv), not an assumption; the integral bound needs integrability, or the Bochner
  integral is `0`. Everything is statable at the pins; the proofs need the contour shift for a
  periodic strip function (Fourier coefficient decay $|c_k|\le Me^{-a|k|}$ and aliasing),
  which no library has in this form. NASC: `NASC.norm_trapezoid_sub_integral_le_of_analyticOnStrip`
  (`sorry`) states (i) with nodes $jh$ for $0\le j<N$, which equals the source sum by
  periodicity; (ii)–(v) are not stated.

* **12.15. Gauss and Clenshaw–Curtis quadrature on $[-1,1]$.** Here
  $d\mu=dx$ on $[-1,1]$ and $I=\int_{-1}^1f\,dx$. The $(n+1)$-point
  **Clenshaw–Curtis rule** is the interpolatory rule with nodes the Chebyshev
  points $\cos(j\pi/n)$, $0\le j\le n$; its weights are positive. The
  $(n+1)$-point Gauss rule has as nodes the zeros of the Legendre polynomial
  of degree $n+1$. For $\rho>1$ the **Bernstein ellipse** $E_\rho$ is the
  open region bounded by the image of the circle $|z|=\rho$ under
  $z\mapsto(z+z^{-1})/2$. Let $I_n$ denote either rule with $n+1$ points.
  - If $f$ extends analytically to $E_\rho$ with $|f|\le M$ there, then
    $$|I-I_n|\le\frac{64}{15}\,\frac{M\rho^{1-n}}{\rho^2-1}
    \quad\text{(Clenshaw–Curtis, }n\ge2),\qquad
    |I-I_n|\le\frac{64}{15}\,\frac{M\rho^{-2n}}{\rho^2-1}
    \quad\text{(Gauss, }n\ge1).$$
  - Both rules converge for every $f\in C[-1,1]$. Let $\nu\ge1$, let
    $f,\dots,f^{(\nu-1)}$ be absolutely continuous on $[-1,1]$, and let
    $f^{(\nu)}$ have total variation $V<\infty$. Then
    $$|I-I_n|\le\frac{32}{15}\,\frac{V}{\pi\nu(n-\nu)^\nu}
    \quad\text{(Clenshaw–Curtis, }n>\nu),\qquad
    |I-I_n|\le\frac{32}{15}\,\frac{V}{\pi\nu(2n+1-\nu)^\nu}
    \quad\text{(Gauss, }2n\ge\nu).$$

  *Assessment.* Mathlib has the Chebyshev polynomials and points, the
  Gauss–Chebyshev rule for the Chebyshev measure, and the shifted Legendre
  polynomials without orthogonality; TauCeti has the Chebyshev $L^2$ basis.
  The gap is the positivity of the Clenshaw–Curtis weights and the error
  bounds of both rules for analytic functions and for functions of bounded
  variation, which rest on Chebyshev coefficient decay.

  *Lean target.* Carriers at the pins: `Polynomial.Chebyshev.T`, `Polynomial.shiftedLegendre`
  (a polynomial over `ℤ`, so mapped by `Polynomial.map (Int.castRingHom ℝ)` and composed with
  $(x+1)/2$ to give the Legendre polynomial), `Lagrange.basis`, `AnalyticOnNhd`,
  `eVariationOn`, `AbsolutelyContinuousOnInterval`, `MeasureTheory.volume` restricted to
  `Icc (-1) 1`, `NASC.bernsteinEllipse ρ` (the set `{z | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}` in
  `ℂ`), `NASC.chebyshevNodes n j = Real.cos (j * π / n)`, and `NASC.IsGaussRule`. New
  definitions: the Clenshaw–Curtis weights `Fin (n + 1) → ℝ` as integrals of the Lagrange
  basis. Conjuncts: (i) for `n ≥ 1` the Clenshaw–Curtis weights are positive; (ii) for
  `1 < ρ`, `f : ℂ → ℂ` analytic on `bernsteinEllipse ρ` with `‖f z‖ ≤ M` there, the two
  analytic bounds with their ranges of `n`; (iii) both rules converge for every continuous
  `f`; (iv) the two bounded-variation bounds for `n > ν` and `ν ≤ 2 * n`. ATAP's printed Gauss
  bound (19.10) is false (reference guide of 12.15), so ATAP's comparison theorem 19.5 is not a
  target. Pitfalls: $f^{(\nu)}$ exists only almost
  everywhere, and `deriv` takes the junk value `0` elsewhere, which changes `eVariationOn`; the
  hypothesis is better stated with a function `g` of bounded variation and
  `iteratedDeriv (ν - 1) f x = iteratedDeriv (ν - 1) f (-1) + ∫ t in -1..x, g t`; `(n - ν) ^ ν`
  with natural subtraction is `0` for `n ≤ ν`, so the ranges must be hypotheses; the total
  variation is in `ℝ≥0∞` and must be finite before `toReal`. Everything is statable at the
  pins; the proofs need uniform Chebyshev-series convergence and coefficient bounds (10.10,
  10.11) and the Gauss–Legendre rule for Lebesgue measure (12.1–12.6). Depends on 10.10,
  10.11, 12.5, 12.6 and 12.9. NASC: none; `NASC.norm_chebyshevCoeff_le_of_analyticOnEllipse`
  (10.11, `sorry`) is the coefficient ingredient.

## 13. Discrete Fourier analysis and sparse recovery

[Synopsis](SYNOPSIS.md#13-discrete-fourier-analysis-and-sparse-recovery) · [Coverage inventory](STRUCTURE.md#13-discrete-fourier-analysis-and-sparse-recovery)

The additive-circle and cyclic DFT APIs provide Fourier ingredients. The
selected gaps include matrix normalization, FFT factorization, reconstruction
from samples, nonequispaced transforms, uniform recovery of sparse data by
basis pursuit and greedy methods, and the lower bound on the number of
measurements.

Vectors of length $N$ are indexed from $0$ to $N-1$ in the Fourier part, and
$w_N=e^{-2\pi i/N}$. A function on $\mathbb R$ that is $2\pi$-periodic has the
**Fourier coefficients**
$c_k(f)=\frac1{2\pi}\int_0^{2\pi}f(t)e^{-ikt}\,dt$, $k\in\mathbb Z$, and a
function $f\in L^1(\mathbb R)$ has the **Fourier transform**
$\hat f(\omega)=\int_{\mathbb R}f(x)e^{-ix\omega}\,dx$. $C_0(\mathbb R)$ is the
space of continuous functions on $\mathbb R$ that vanish at infinity, and
$\mathrm{sinc}\,x=(\sin x)/x$ for $x\ne0$, $\mathrm{sinc}\,0=1$. In the sparse
recovery part, $A\in\mathbb K^{m\times N}$ is a measurement matrix,
$[N]=\{1,\dots,N\}$, and for $v\in\mathbb K^N$ and $S\subset[N]$, $v_S$ is the
vector that agrees with $v$ on $S$ and vanishes off $S$, and
$\bar S=[N]\setminus S$.

### The discrete Fourier transform

* **13.1. Fourier matrix and DFT.** Let $N\in\mathbb N$. For every
  $j\in\mathbb Z$,
  $$\sum_{k=0}^{N-1}w_N^{jk}=\begin{cases}N,&j\equiv0\pmod N,\\
  0,&\text{otherwise}.\end{cases}$$
  The **Fourier matrix** is $F_N=(w_N^{jk})_{j,k=0}^{N-1}$, and the **discrete
  Fourier transform** of $a\in\mathbb C^N$ is $\hat a=F_Na$, that is,
  $\hat a_k=\sum_{j=0}^{N-1}a_jw_N^{jk}$. The matrix $F_N$ is symmetric and
  $F_N^*F_N=NI$, so $N^{-1/2}F_N$ is unitary. Hence $F_N$ is invertible with
  $F_N^{-1}=N^{-1}F_N^*$, the **inverse DFT** is
  $$a_j=\frac1N\sum_{k=0}^{N-1}\hat a_kw_N^{-jk},\qquad j=0,\dots,N-1,$$
  and **Parseval's identity** $\langle\hat a,\hat b\rangle=N\langle a,b\rangle$,
  $\|\hat a\|_2^2=N\|a\|_2^2$ holds for all $a,b\in\mathbb C^N$.

  *Assessment.* Partly covered. Mathlib gives finite character orthogonality
  and the DFT with its inverse on cyclic functions. The selected statement
  packages the transform as a scaled unitary matrix with Parseval's
  identities.

  *Scope.* The target is the concrete Fourier matrix, its normalization,
  adjoint and Euclidean inner-product identities.

  *Argument.* Compute the $(j,\ell)$ entry of $F_N^*F_N$ as a sum of the
  character with frequency $\ell-j$. Orthogonality gives $NI$, and transpose
  symmetry follows directly from the entries. The inverse and Parseval
  formulas follow from the Gram identity.

  *Lean target.* Carriers at the pins: `ZMod N` as index type with `[NeZero N]`,
  `ZMod.stdAddChar`, `ZMod.dft` (notation `𝓕`) with `ZMod.dft_apply` and `ZMod.dft_dft`,
  `AddChar.sum_mulShift`, `Matrix.conjTranspose`, `Matrix.mulVec` and `dotProduct` with `star`.
  New definition: `fourierMatrix N : Matrix (ZMod N) (ZMod N) ℂ` with entry
  `ZMod.stdAddChar (-(j * k))`. Conjuncts: (i) the orthogonality sum, stated for `j : ZMod N`
  as `∑ k, stdAddChar (j * k) = if j = 0 then N else 0`; (ii) `(fourierMatrix N)ᵀ =
  fourierMatrix N`; (iii) `(fourierMatrix N)ᴴ * fourierMatrix N = (N : ℂ) • 1`;
  (iv) `fourierMatrix N *ᵥ a = 𝓕 a`; (v) `(fourierMatrix N)⁻¹ = (N : ℂ)⁻¹ • (fourierMatrix N)ᴴ`;
  (vi) `dotProduct (star (𝓕 a)) (𝓕 b) = N * dotProduct (star a) b`. Pitfall: indexing by
  `Fin N` instead of `ZMod N` needs the casts of `Fin.val`; `ZMod 0 = ℤ` is infinite, so
  `[NeZero N]` is required. All statable and provable at the pins; no dependency. NASC:
  `NASC.fourierMatrix_gram_mulVec` (`NASC/DiscreteFourier.lean`) states (iii) and (iv), proved;
  (ii), (v) and (vi) are not stated.

* **13.2. Cyclic convolution.** The **cyclic convolution** of
  $a,b\in\mathbb C^N$ is the vector $a*b$ with
  $(a*b)_n=\sum_{k=0}^{N-1}a_kb_{(n-k)\bmod N}$, and $a\circ b$ is the
  componentwise product. Then
  $$\widehat{a*b}=\hat a\circ\hat b,\qquad N\,\widehat{a\circ b}=\hat a*\hat b .$$
  If $V_N$ is the cyclic forward shift, $(V_Na)_j=a_{(j-1)\bmod N}$, and
  $M_N=\mathrm{diag}(1,w_N,\dots,w_N^{N-1})$, then $F_NV_N=M_NF_N$.

  *Assessment.* The cyclic DFT and finite group operations are available. The
  convolution/product and shift identities are useful for both circulant
  diagonalization and sampling.

  *Argument.* In the transform of a convolution replace the output index $n$
  by $k+j$ modulo $N$ and separate the two sums. Applying the same calculation
  with inverse Fourier signs gives the product formula with its factor of $N$.
  Reindex a single sum to obtain the forward-shift identity.

  *Lean target.* Carriers at the pins: `ZMod.dft`, `ZMod.dft_dft`, pointwise product of
  functions `ZMod N → ℂ`, `Matrix.diagonal`, `Matrix.of`. New definitions: cyclic convolution
  `cyclicConvolution a b : ZMod N → ℂ`, `j ↦ ∑ k, a k * b (j - k)` (Mathlib's discrete
  convolution on monoids is a possible carrier but has a different API), and the shift
  `j ↦ a (j - 1)` as a permutation matrix `Matrix (ZMod N) (ZMod N) ℂ`. Conjuncts: (i)
  `𝓕 (cyclicConvolution a b) = 𝓕 a * 𝓕 b`; (ii) `(N : ℂ) • 𝓕 (a * b) = cyclicConvolution (𝓕 a)
  (𝓕 b)`; (iii) `fourierMatrix N * V = diagonal (fun k ↦ stdAddChar (-k)) * fourierMatrix N`.
  Statable and provable at the pins; depends on 13.1. NASC: `NASC.dft_cyclicConvolution_and_mul`
  (`NASC/DiscreteFourier.lean`) states (i) and (ii), proved; (iii) is not stated.

* **13.3. Circulant matrices.** The **circulant matrix** generated by
  $a\in\mathbb C^N$ is $\mathrm{circ}\,a=(a_{(j-k)\bmod N})_{j,k=0}^{N-1}$, whose
  first column is $a$. Then $(\mathrm{circ}\,a)b=a*b$ for every
  $b\in\mathbb C^N$, and
  $$\mathrm{circ}\,a=F_N^{-1}\,\mathrm{diag}(F_Na)\,F_N .$$
  Hence the eigenvalues of $\mathrm{circ}\,a$, with multiplicity, are the
  entries $\hat a_0,\dots,\hat a_{N-1}$ of $F_Na$, and the $k$-th column of
  $F_N^{-1}$ is an eigenvector for $\hat a_k$. Since
  $\mathrm{circ}\,a=\sum_{k=0}^{N-1}a_kV_N^k$ with $V_N$ as in 13.2, the
  circulant matrices of order $N$ form a commutative algebra.

  *Assessment.* Partly covered. Mathlib defines circulants and proves closure
  under multiplication and commutativity. The selected gap is the explicit
  Fourier diagonalization and eigenvectors.

  *Scope.* The target is the concrete matrix diagonalization and eigenvector
  formula with the stated normalization of the DFT.

  *Argument.* Matrix multiplication by the circulant is cyclic convolution.
  The convolution identity of 13.2 therefore conjugates the circulant to
  multiplication by its Fourier coefficients. Diagonal matrices commute, and
  transforming the coordinate vectors back gives the eigenvectors.

  *Lean target.* Carriers at the pins: `Matrix.circulant` (entry `v (i - j)`, the synopsis
  convention) with `Matrix.circulant_mul` and `Matrix.circulant_mul_comm`, `Matrix.diagonal`,
  `Module.End.HasEigenvector` for `Matrix.toLin'`, `Matrix.charpoly`. Conjuncts: (i)
  `circulant a *ᵥ b = cyclicConvolution a b`; (ii) `fourierMatrix N * circulant a =
  diagonal (𝓕 a) * fourierMatrix N`, which avoids the inverse; (iii) the `k`-th column of
  `(fourierMatrix N)ᴴ` is an eigenvector of `circulant a` for `𝓕 a k`; (iv)
  `(circulant a).charpoly = ∏ k, (X - C (𝓕 a k))`, the multiplicity statement; (v)
  `circulant a = ∑ k, a k • V ^ k.val`. Pitfall: Horn–Johnson's first-row convention is the
  transpose. Statable and provable at the pins; depends on 13.1 and 13.2. NASC:
  `NASC.fourierMatrix_mul_circulant` (`NASC/DiscreteFourier.lean`), with Mathlib's
  `Matrix.circulant`, states (ii), proved; (i), (iii)–(v) are not stated.

* **13.4. Radix-2 fast Fourier transform.** Let $N\ge2$ be even. Let $\Pi_N$ be
  the permutation matrix with
  $\Pi_Nx=(x_0,x_2,\dots,x_{N-2},x_1,x_3,\dots,x_{N-1})^\top$, and let
  $D_N=\mathrm{diag}(I_{N/2},W_{N/2})$ with
  $W_{N/2}=\mathrm{diag}(w_N^j)_{j=0}^{N/2-1}$. Then
  $$F_N=\Pi_N^\top\,(I_2\otimes F_{N/2})\,D_N\,(F_2\otimes I_{N/2}).$$
  If $N=2^t$, applying this factorization recursively writes $F_N$ as a product
  of a permutation matrix (the bit reversal) and $t$ factors of the form
  (diagonal matrix)$\,\times\,(I_{N/2^n}\otimes F_2\otimes I_{2^{n-1}})$, each with
  two nonzero entries in every row. Counting the multiplications by $\pm1$ and
  $\pm i$ as free, the multiplication by a primitive eighth root of unity as
  2 real multiplications and 2 real additions, and any other complex
  multiplication by a twiddle factor as 3 real multiplications and 3 real
  additions, the resulting Cooley–Tukey and Sande–Tukey FFTs compute
  $F_Na$ for $N=2^t$ with $t\ge2$ in
  $$\tfrac32N\log_2N-5N+8\ \text{real multiplications and}\
  \tfrac72N\log_2N-5N+8\ \text{real additions},$$
  in total $5N\log_2N-10N+16$ real operations.

  *Assessment.* Root-of-unity identities and Kronecker products supply the
  matrix ingredients. The gap includes the radix factorization, permutation,
  and operation count under its specific arithmetic conventions.

  *Lean target.* Carriers at the pins: `Matrix.kronecker` (notation `⊗ₖ`, scope `Kronecker`),
  `Matrix.submatrix` along the equivalence `finProdFinEquiv` and permutation matrices,
  `Matrix.fromBlocks`, `Complex.exp`. New definitions: the even–odd permutation of `Fin (2 * n)`,
  the twiddle matrix `D_N`, and an arithmetic-cost model: an inductive type of straight-line
  programs over `ℂ` whose instructions are additions and multiplications by constants, with a cost
  function `ℕ × ℕ` (real multiplications, real additions) that charges `0` for constants `±1, ±i`,
  `(2, 2)` for primitive eighth roots and `(3, 3)` for other unimodular constants. Conjuncts: (i)
  for `N = 2 * n`, `n ≥ 1`, the matrix factorization after reindexing `Fin 2 × Fin n ≃ Fin N`; (ii)
  for `N = 2 ^ t` the recursive transform equals `fourierMatrix N *ᵥ a`; (iii) for `t ≥ 2` the
  program built by the recursion has cost `(3/2 N t - 5 N + 8, 7/2 N t - 5 N + 8)`. Pitfall: at
  `t = 1` the formula gives `(1, 5)` while the program costs `(0, 4)`, so `t ≥ 2` is needed. The
  cost model is infrastructure no library has. Depends on 13.1. NASC:
  `NASC.radixTwoTransform_eq_sum` (`NASC/DiscreteFourier.lean`) states (ii) for the recursion on
  `ℕ → ℂ` at every frequency `j : ℕ`, `sorry`; (i) and (iii) are not stated.

### Fourier coefficients, interpolation and sampling

* **13.5. Aliasing formula.** Let $f$ be continuous and $2\pi$-periodic with
  $\sum_{k\in\mathbb Z}|c_k(f)|<\infty$, let $N\in\mathbb N$, and let
  $$\hat f_k=\frac1N\sum_{j=0}^{N-1}f\Bigl(\frac{2\pi j}N\Bigr)w_N^{jk},
  \qquad k\in\mathbb Z,$$
  the trapezoidal approximation of $c_k(f)$. Then
  $$\hat f_k=\sum_{\ell\in\mathbb Z}c_{k+\ell N}(f)\quad\text{and}\quad
  |\hat f_k-c_k(f)|\le\sum_{\ell\in\mathbb Z\setminus\{0\}}|c_{k+\ell N}(f)|
  \qquad(k\in\mathbb Z).$$
  In particular $\hat f_k=c_k(f)$ for $|k|<N/2$ if $f$ is a trigonometric
  polynomial of degree less than $N/2$.

  *Assessment.* Fourier coefficients and DFT are available. The aliasing
  identity requires interchanging the absolutely summable Fourier series with
  the finite sampling sum.

  *Lean target.* Carriers at the pins: `fourierCoeffOn` on `[0, 2π]` (or `fourierCoeff` on
  `AddCircle (2 * π)`), `hasSum_fourier_series_of_summable`, `Function.Periodic`, `Summable` and
  `tsum` over `ℤ`. Conjuncts, for continuous `f : ℝ → ℂ` with period `2π`, `Summable fun k ↦ ‖c k‖`,
  `N ≥ 1` and `k : ℤ`: (i) `HasSum (fun l : ℤ ↦ c (k + l * N)) (fhat k)`, which records the
  summability that `tsum` would otherwise default to `0`; (ii)
  `‖fhat k - c k‖ ≤ ∑' l, if l = 0 then 0 else ‖c (k + l * N)‖`; (iii) for a trigonometric
  polynomial of degree `d` with `2 * d < N`, `fhat k = c k` for `2 * |k| < N`. Pitfall: the
  normalization `(2π)⁻¹` of `fourierCoeffOn` agrees with the synopsis; Mathlib's `fourierCoeff` on
  `AddCircle T` uses the Haar probability measure and also agrees. Statable at the pins; depends on
  13.1 for the discrete sum. NASC: `NASC.fourierCoeffOn_aliasing` (`NASC/DiscreteFourier.lean`),
  with Mathlib's `fourierCoeffOn` on $[0,2\pi]$, states (i) as an equation with `tsum`, which is
  safe because the series is summable under the hypothesis, `sorry`; (ii) and (iii) are not stated.

* **13.6. Trigonometric interpolation.** Let $N\in\mathbb N$, let
  $x_j=\pi j/N$ for $j=0,\dots,2N-1$, and let
  $S_N=\mathrm{span}\{e^{ikx}:-N\le k\le N-1\}$. For every continuous
  $2\pi$-periodic $u$ there is a unique $I_Nu\in S_N$ with $I_Nu(x_j)=u(x_j)$ for
  all $j$, and its coefficients are
  $\tilde u_k=\frac1{2N}\sum_{j=0}^{2N-1}u(x_j)e^{-ikx_j}$. Let $H^m_p$ be the
  space of $2\pi$-periodic functions whose distributional derivatives up to
  order $m$ lie in $L^2(0,2\pi)$, and let $P_N$ be the orthogonal projection of
  $L^2(0,2\pi)$ onto $S_N$, the truncated Fourier series. For integers $m\ge1$
  and $0\le l\le m$ there is a constant $C$ depending only on $m$ such that for
  all $u\in H^m_p$ and all $N\in\mathbb N$
  $$\|u-P_Nu\|_{H^l(0,2\pi)}+\|u-I_Nu\|_{H^l(0,2\pi)}
  \le C\,N^{l-m}\,\|u^{(m)}\|_{L^2(0,2\pi)} .$$

  *Assessment.* Mathlib supplies the Fourier Hilbert basis and cyclic inverse
  DFT. The missing statement gives interpolation at the specified nodes and
  the periodic Sobolev error estimates.

  *Lean target.* Carriers at the pins: `fourierBasis` and `fourierCoeff` on
  `AddCircle (2 * π)` with `MeasureTheory.Lp ℂ 2`, `tsum_sq_fourierCoeff`, `iteratedDeriv`.
  New definitions: the band `S_N` as the span of `fourier k`, `-N ≤ k ≤ N - 1`; `I_N u` by the
  explicit coefficients; the periodic Sobolev seminorm
  `(∑' k, |k| ^ (2 * l) * ‖fourierCoeff u k‖ ^ 2) ^ (1/2)` valued in `ℝ≥0∞` (it can be
  infinite), with `H^m_p` the set where the `m`-seminorm is finite. Conjuncts: (i) existence and
  uniqueness of `I_N u ∈ S_N` interpolating at `x_j = π j / N`; (ii) the coefficient formula;
  (iii) and (iv) the bounds `‖u - P_N u‖_{H^l} ≤ C m N ^ (l - m) |u|_m` and the same for
  `I_N u`, for integers `1 ≤ m`, `0 ≤ l ≤ m`, `N ≥ 1`, stated with the Fourier seminorm, which
  equals `(2π)^{-1/2} ‖u^{(m)}‖_{L^2}` for integer `m`. Pitfall: the Fourier-side norm avoids
  weak derivatives, which neither library has on the circle. (i)–(ii) are statable now; (iii)
  and (iv) are statable with the Fourier seminorm. No dependency beyond 13.5 for the aliasing
  step. NASC: `NASC.existsUnique_trigonometric_interpolant` (`NASC/DiscreteFourier.lean`)
  states (i) at the level of coefficient vectors, for every `n` (both index types are empty at
  `n = 0`), proved; (ii)–(iv) are not stated.

* **13.8. Shannon sampling theorem.** Let $f\in L^1(\mathbb R)\cap
  C_0(\mathbb R)$ be **bandlimited** on $[-L,L]$ for some $L>0$, that is,
  $\hat f(\omega)=0$ for $|\omega|>L$, and let $M\ge L$. Then
  $$f(x)=\sum_{k\in\mathbb Z}f\Bigl(\frac{k\pi}M\Bigr)\,\mathrm{sinc}(Mx-k\pi)
  \qquad(x\in\mathbb R),$$
  the series converging absolutely and uniformly on $\mathbb R$. In particular
  $f$ is determined by its samples $f(k\pi/M)$, $k\in\mathbb Z$.

  *Assessment.* Fourier inversion is available. Sampling requires the
  bandlimited hypothesis, the sinc representation and the asserted absolute
  and uniform convergence.

  *Lean target.* Carriers at the pins: `MeasureTheory.Integrable`, `Continuous`,
  `Filter.Tendsto ... (Filter.cocompact ℝ) (nhds 0)` for `C_0`, `Real.sinc`, Mathlib's `𝓕`
  with `Real.fourier_real_eq` (kernel `e^{-2πixξ}`; the synopsis transform is `𝓕 f (ω/(2π))`),
  `TendstoUniformly` for uniform convergence of partial sums over `Finset.Icc (-n) n` or
  `Summable` of the sup norms. Conjuncts, for `f` integrable, continuous and vanishing at
  infinity, with the integral `∫ x, f x * exp (-i x ω)` zero for `|ω| > L`, `0 < L ≤ M`:
  (i) `Summable fun k : ℤ ↦ ‖f (k π / M) * sinc (M x - k π)‖` for every `x`; (ii) the sum equals
  `f x`; (iii) the partial sums converge uniformly on `ℝ`. Pitfall: stating the bandlimit with
  Mathlib's `𝓕` changes the cut-off to `L/(2π)`. Statable at the pins; ingredient for (i) is
  Cauchy–Schwarz with `∑ sinc² (M x - kπ) = 1`. NASC: `NASC.tsum_sinc_smul_samples_eq`
  (`NASC/DiscreteFourier.lean`), with the bandlimit stated through Mathlib's `𝓕`
  (`L < 2π|ξ| → 𝓕 f ξ = 0`), states (i) and (ii) without `C_0` (continuity and integrability
  suffice), `sorry`; (iii) is not stated.

### Nonequispaced data and exponential sums

* **13.9. Nonequispaced FFT error bound.** Let $N\in\mathbb N$ be even, let
  $I_N=\{k\in\mathbb Z:-N/2\le k<N/2\}$, and let
  $f(x)=\sum_{k\in I_N}\hat f_ke^{ikx}$ with $\hat f\in\mathbb C^{I_N}$. Let
  $\sigma>1$ with $\sigma N\in\mathbb N$, let $m\in\mathbb N$ with
  $2m\le\sigma N$, and let $\varphi(x)=M_{2m}(\sigma Nx/(2\pi))$, where $M_{2m}$
  is the centred cardinal B-spline of order $2m$ (the $2m$-fold convolution of
  the indicator function of $[-\frac12,\frac12)$). Let
  $\tilde\varphi(x)=\sum_{r\in\mathbb Z}\varphi(x+2\pi r)$, so that
  $c_k(\tilde\varphi)=\hat\varphi(k)/(2\pi)>0$ for $k\in I_N$, and define
  $$g_l=\frac1{\sigma N}\sum_{k\in I_N}\frac{\hat f_k}{c_k(\tilde\varphi)}
  e^{2\pi ikl/(\sigma N)},\qquad
  s(x)=\sum_{l\in I_{\sigma N}}g_l\,\tilde\varphi\Bigl(x-\frac{2\pi l}{\sigma N}
  \Bigr),$$
  where $I_{\sigma N}=\{l\in\mathbb Z:-\sigma N/2\le l<\sigma N/2\}$. Then for
  every $x\in\mathbb R$
  $$|f(x)-s(x)|\le\frac{4}{(2\sigma-1)^{2m}}\,\|\hat f\|_1 .$$
  The coefficients $g_l$ are one inverse DFT of length $\sigma N$, and for each
  $x$ at most $2m+1$ terms of the sum for $s(x)$ are nonzero, so the values
  $s(x_1),\dots,s(x_J)$ at $J$ points cost $O(\sigma N\log(\sigma N)+mJ)$
  operations.

  *Assessment.* Trigonometric polynomials, cardinal B-splines as iterated
  convolutions and Fourier coefficients of periodizations are the ingredients;
  none of them is assembled. The selected result is the aliasing error bound
  of the window method and its operation count.

  *Lean target.* Carriers at the pins: `MeasureTheory.convolution` for the B-spline
  `M_{2m}` (or Mathlib-free: the piecewise polynomial with `Real.sinc` power as Fourier
  transform), `fourierCoeffOn`, `Real.sinc`. New definitions: `cardinalBSpline n : ℝ → ℝ` as
  the `n`-fold convolution of the indicator of `[-1/2, 1/2)`, with its Fourier transform
  `sinc (ω/2) ^ n`; the window `φ`, its periodization, the vector `g` as an inverse DFT of
  length `σN` (with `σ N` given as a natural number `n'` with `N < n'`), and `s(x)`.
  Conjuncts, for even `N ≥ 2`, `n' = σ N` and `1 ≤ m` with `2 m ≤ n'`: (i) `c_k(φ̃) > 0` for
  `k ∈ I_N`; (ii) `‖f x - s x‖ ≤ 4 / (2σ - 1) ^ (2m) * ∑ k, ‖f̂ k‖` for all real `x`; (iii) for
  every `x` at most `2m + 1` summands of `s x` are nonzero. The complexity claim needs a cost
  model as in 13.4 and is left to prose. Pitfall: `σ` is real; keep `σ = n' / N` as a quotient
  of naturals so that `σ N ∈ ℕ` is built in. (i)–(iii) are statable at the pins; depends on
  13.1, 13.5. NASC: none.

* **13.10. Prony's method.** Let $M\in\mathbb N$, let $z_1,\dots,z_M\in
  \mathbb C\setminus\{0\}$ be distinct, let $c_1,\dots,c_M\in\mathbb C$ be
  nonzero, and let $h(k)=\sum_{j=1}^Mc_jz_j^k$ for $k=0,\dots,2M-1$. Let
  $V=(z_k^{j-1})_{j,k=1}^M$ be the Vandermonde matrix. Then the Hankel matrix
  $H=(h(k+l))_{k,l=0}^{M-1}$ factors as $H=V\mathrm{diag}(c)V^\top$ and is
  invertible. The linear system
  $$\sum_{k=0}^{M-1}p_k\,h(k+l)=-h(M+l),\qquad l=0,\dots,M-1,$$
  has a unique solution, and the **Prony polynomial**
  $p(z)=z^M+\sum_{k=0}^{M-1}p_kz^k$ equals $\prod_{j=1}^M(z-z_j)$. The
  coefficients are the unique solution of $Vc=(h(0),\dots,h(M-1))^\top$.
  Consequently an exponential sum $\sum_{j=1}^Mc_je^{\phi_jx}$ with known
  order $M$, nonzero $c_j$, and distinct $\phi_j\in\mathbb C$ with
  $\mathrm{Im}\,\phi_j\in[-\pi,\pi)$ is uniquely determined by its values at
  $x=0,1,\dots,2M-1$.

  *Assessment.* Polynomial roots and Vandermonde matrices are available. The
  missing results identify the exponential frequencies from the data Hankel
  matrix and recover the weights.

  *Lean target.* Carriers at the pins: `Matrix.vandermonde` (rows indexed by nodes, so the
  synopsis `V` is its transpose) with `Matrix.det_vandermonde_ne_zero_iff`, `Matrix.diagonal`,
  `Polynomial.X`, `Polynomial.C`, `Polynomial.monomial`, `Complex.exp`, `Equiv.Perm`.
  Conjuncts, for `M : ℕ`, injective `z : Fin M → ℂ` and nonvanishing `c`: (i) `H = V *
  diagonal c * Vᵀ`; (ii) `H.det ≠ 0`; (iii) unique solvability of the Hankel system; (iv) the
  Prony polynomial equals `∏ j, (X - C (z j))`; (v) unique solvability of `V c = h`; (vi)
  uniqueness of an exponential sum with distinct exponents whose imaginary parts lie in
  `Set.Ico (-π) π` from its values at `0, …, 2M - 1`, up to relabelling. Pitfall: the
  nonvanishing of `z j` is not needed for (i)–(v) (`0 ^ 0 = 1`), only to read off `φ_j = log z_j`.
  All statable and provable at the pins. NASC: `NASC.existsUnique_prony_annihilator` states
  (i)–(v) and `NASC.exists_perm_of_expSum_samples_eq` states (vi) (`NASC/DiscreteFourier.lean`,
  with the helpers `NASC.exp_injOn_im_mem_Ico` and `NASC.exists_perm_of_prod_X_sub_C_eq` in
  `NASC/Support/`), both proved.

### Sparse recovery

* **13.12. Null space property.** The matrix $A\in\mathbb K^{m\times N}$ has the
  **null space property** of order $s$ if
  $\|v_S\|_1<\|v_{\bar S}\|_1$ for every $v\in\ker A\setminus\{0\}$ and every
  $S\subset[N]$ with $\mathrm{card}(S)\le s$. **Basis pursuit** is the problem of
  minimizing $\|z\|_1$ over $z\in\mathbb K^N$ subject to $Az=y$. Every
  $s$-sparse $x\in\mathbb K^N$ is the unique solution of basis pursuit with
  $y=Ax$ if and only if $A$ has the null space property of order $s$. More
  precisely, for a fixed $S$, every $x$ supported on $S$ is the unique
  minimizer if and only if $\|v_S\|_1<\|v_{\bar S}\|_1$ for all
  $v\in\ker A\setminus\{0\}$.

  *Assessment.* Finite vectors and coordinate restrictions can be expressed.
  The missing equivalence identifies exactly when all sparse vectors are
  recovered by the stated ℓ¹ problem.

  *Lean target.* Carriers at the pins: `Matrix (Fin m) (Fin N) 𝕜` with `[RCLike 𝕜]`,
  `Matrix.mulVec`, `LinearMap.ker (Matrix.toLin' A)`, `Finset (Fin N)` with `Finset.card`
  and complement, `Function.support`, `IsMinOn` on the affine set `{z | A *ᵥ z = y}`. New
  definitions: the restricted norm `∑ i ∈ S, ‖v i‖`; `IsSparse s x` as `(Function.support x).ncard
  ≤ s` or as existence of `S` with `S.card ≤ s` outside of which `x` vanishes; the predicate
  `NullSpaceProperty A s`. Conjuncts: (i) the uniform equivalence; (ii) the fixed-support
  equivalence for every `S`. Pitfall: the definition must quantify over `S` with `card ≤ s`, not
  `= s`, or the `s ≥ N` cases change; `ℓ¹` minimality is strict (unique minimizer). Statable
  and provable at the pins; no dependency. NASC: `NASC.HasNullSpaceProperty` and
  `NASC.nullSpaceProperty_iff_basisPursuit_unique` (`NASC/SparseRecovery.lean`, over `RCLike 𝕜`
  with finite index types) state (i), `sorry`; (ii) is not stated.

* **13.13. Robust null space property.** The matrix $A\in\mathbb C^{m\times N}$
  has the **$\ell_2$-robust null space property** of order $s$ with constants
  $0<\rho<1$ and $\tau>0$ if, for every $S\subset[N]$ with
  $\mathrm{card}(S)\le s$ and every $v\in\mathbb C^N$,
  $$\|v_S\|_2\le\frac{\rho}{\sqrt s}\|v_{\bar S}\|_1+\tau\|Av\|_2 .$$
  Then, with $C=(1+\rho)^2/(1-\rho)$ and $D=(3+\rho)\tau/(1-\rho)$, for all
  $x,z\in\mathbb C^N$ and $1\le p\le2$,
  $$\|z-x\|_p\le\frac{C}{s^{1-1/p}}\bigl(\|z\|_1-\|x\|_1+2\sigma_s(x)_1\bigr)
  +Ds^{1/p-1/2}\|A(z-x)\|_2 .$$
  In particular, if $\|Ax-y\|_2\le\eta$ and $x^\sharp$ minimizes $\|z\|_1$
  subject to $\|Az-y\|_2\le\eta$, then
  $$\|x-x^\sharp\|_p\le\frac{2C}{s^{1-1/p}}\sigma_s(x)_1+2Ds^{1/p-1/2}\eta,
  \qquad1\le p\le2 .$$

  *Assessment.* The null-space inequality must quantify the imbalance between
  a chosen support and its complement with the measurement residual. The
  robust recovery bound is the target.

  *Lean target.* Carriers at the pins: as in 13.12, with `EuclideanSpace ℂ (Fin N)` for the
  Euclidean norm, or `‖·‖` on `PiLp p` for `1 ≤ p ≤ 2`, `Real.rpow`. New definitions:
  `HasRobustNullSpaceProperty A s ρ τ`; the best `s`-term error `σ_s(x)_1` as an infimum over the
  finite set of supports of size `≤ s` (a `Finset.inf'` over a nonempty finite set, so no junk
  value). Conjuncts, for `1 ≤ s`, `0 < ρ < 1`, `0 < τ`, `1 ≤ p ≤ 2`: (i) the comparison inequality
  for all `x z`; (ii) the error bound for every minimizer of `‖z‖₁` on `{z | ‖A z - y‖₂ ≤ η}` with
  `‖A x - y‖₂ ≤ η`. Pitfall: `s = 0` makes `ρ / √s` the junk value `0`, so `1 ≤ s` is needed; `p`
  real with `PiLp (ENNReal.ofReal p)`. Statable and provable at the pins; depends on 13.12 for the
  setting. NASC: `NASC.recovery_error_le_of_robustNullSpace` (`NASC/SparseRecovery.lean`, over
  `RCLike 𝕜` with finite index types) states (i) for `p = 2`, with `‖x_{S̄}‖₁` for an arbitrary
  admissible `S` in place of `σ_s(x)_1` (equivalent after minimizing over `S`), `sorry`; general `p`
  and (ii) are not stated.

* **13.14. Restricted isometry property.** The **$s$-th restricted isometry
  constant** $\delta_s=\delta_s(A)$ of $A\in\mathbb C^{m\times N}$ is the
  smallest $\delta\ge0$ with
  $(1-\delta)\|x\|_2^2\le\|Ax\|_2^2\le(1+\delta)\|x\|_2^2$ for all $s$-sparse
  $x$; equivalently $\delta_s=\max_{\mathrm{card}(S)\le s}\|A_S^*A_S-I\|_2$. If
  $$\delta_{2s}<\frac4{\sqrt{41}}\approx0.6246,$$
  then $A$ has the $\ell_2$-robust null space property of order $s$ with
  $$\rho=\frac{\delta_{2s}}{\sqrt{1-\delta_{2s}^2}-\delta_{2s}/4},\qquad
  \tau=\frac{\sqrt{1+\delta_{2s}}}{\sqrt{1-\delta_{2s}^2}-\delta_{2s}/4},$$
  and $\rho<1$. Consequently, for every $x\in\mathbb C^N$ and $y\in\mathbb C^m$
  with $\|Ax-y\|_2\le\eta$, every minimizer $x^\sharp$ of $\|z\|_1$ subject to
  $\|Az-y\|_2\le\eta$ satisfies the bounds of 13.13 with these $\rho,\tau$.
  In particular, with $C'=2(1+\rho)^2/(1-\rho)$ and
  $D'=2(3+\rho)\tau/(1-\rho)$, which depend only on $\delta_{2s}$,
  $$\|x-x^\sharp\|_1\le C'\sigma_s(x)_1+D'\sqrt s\,\eta,\qquad
  \|x-x^\sharp\|_2\le\frac{C'}{\sqrt s}\sigma_s(x)_1+D'\eta .$$
  For $\eta=0$ every $s$-sparse $x$ is recovered exactly.

  *Assessment.* Hermitian norms and coordinate restrictions support the
  restricted isometry predicate. The gap converts the quantitative isometry
  inequality on sparse supports into a uniform reconstruction guarantee.

  *Lean target.* Carriers at the pins: as in 13.13, `Matrix.submatrix` for `A_S`,
  `Matrix.Norms.L2Operator` (scoped `‖·‖` on matrices) for `‖A_S^* A_S - I‖_2`. New
  definitions: `HasRestrictedIsometry A s δ` as the two-sided inequality; the constant
  `δ_s(A)` as a `Finset.sup'` of `‖A_Sᴴ A_S - 1‖` over supports of size `≤ s` (finite, no
  junk). Conjuncts: (i) `δ_s(A)` is the least `δ ≥ 0` with the restricted isometry inequality;
  (ii) for `1 ≤ s` and `δ_{2s} < 4/√41`, the robust null space property with the stated `ρ` and
  `τ`, and `ρ < 1`; (iii) the recovery bounds in `ℓ₁` and `ℓ₂` with `C'`, `D'`. Pitfall: the
  denominator `√(1 - δ²) - δ/4` is positive exactly under the threshold; when `2s > N` the
  restricted isometry over all vectors is meant. Statable and provable at the pins; depends on
  13.13. NASC: `NASC.hasRobustNullSpaceProperty_of_restrictedIsometry`
  (`NASC/SparseRecovery.lean`, over `RCLike 𝕜` with finite index types, also for `s = 0`) states
  (ii) with a bound `δ` on `δ_{2s}` (equivalent by monotonicity), `sorry`; (i) and (iii) are not
  stated.

* **13.15. Gaussian matrices.** Let $A$ be an $m\times N$ matrix with
  independent standard normal real entries, $m<N$, $1\le s\le N$, and
  $\eta,\varepsilon\in(0,1)$. If
  $$m\ge2\eta^{-2}\bigl(s\log(eN/s)+\log(2\varepsilon^{-1})\bigr),$$
  then with probability at least $1-\varepsilon$ the restricted isometry
  constant of $m^{-1/2}A$ satisfies
  $$\delta_s\le2(1+\gamma)\eta+(1+\gamma)^2\eta^2,\qquad
  \gamma=\bigl(2\log(eN/s)\bigr)^{-1/2}.$$
  Since $\gamma\le1/\sqrt2$, it follows that $\delta_s(m^{-1/2}A)\le\delta$ with
  probability at least $1-\varepsilon$ whenever $0<\delta<1$ and
  $m\ge\tilde C\delta^{-2}(s\log(eN/s)+\log(2\varepsilon^{-1}))$, with
  $\tilde C=2\bigl(2(1+2^{-1/2})+(1+2^{-1/2})^2\bigr)^2\approx80.1$. For
  matrices with independent mean-zero, unit-variance subgaussian entries the
  same conclusion holds with a constant $\tilde C$ depending only on the
  subgaussian parameters.

  *Assessment.* Gaussian variables and concentration are available. The
  selected theorem needs a uniform estimate over a union of sparse supports
  with the stated number of measurements.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.gaussianReal 0 1`,
  `MeasureTheory.Measure.pi` for the entry law on `Fin m → Fin N → ℝ`, `Real.log`,
  `Real.sqrt`. New definitions: as in 13.14. Conjuncts, for `1 ≤ s ≤ N`, `m < N`, `η, ε ∈
  (0, 1)`, `m ≥ 2 η⁻² (s log (eN/s) + log (2/ε))`: (i) the law of the matrices whose scaled
  restricted isometry constant exceeds `2(1+γ)η + (1+γ)²η²` has measure `≤ ENNReal.ofReal ε`;
  (ii) the simplified condition with `C̃`. The subgaussian extension is not a target. Missing
  infrastructure: concentration of the extreme singular values of a Gaussian matrix
  (Gordon's inequality or Slepian's lemma, Foucart–Rauhut Theorem 9.26); Gaussian
  concentration for Lipschitz functions is not in either library. Pitfall: `log (eN/s) ≥ 1`
  uses `s ≤ N`; the event should be stated as a set whose measure is bounded, measurability is
  then not needed. NASC: `NASC.gaussianMatrixLaw_not_restrictedIsometry_le`
  (`NASC/SparseRecovery.lean`) states (i) with `NASC.gaussianMatrixLaw m N (1/m)` (entries of
  variance `1/m`, the scaling `m^{-1/2}A`), without the source hypothesis `m < N`, `sorry`.

* **13.16. Coherence.** Let $A\in\mathbb C^{m\times N}$ have columns
  $a_1,\dots,a_N$ with $\|a_i\|_2=1$. Its **coherence** is
  $\mu=\max_{i\ne j}|\langle a_i,a_j\rangle|$, and its **$\ell_1$-coherence
  function** is
  $\mu_1(s)=\max_{i}\max\{\sum_{j\in S}|\langle a_i,a_j\rangle|:
  S\subset[N],\ \mathrm{card}(S)=s,\ i\notin S\}$ for $1\le s\le N-1$, with
  $\mu_1(0)=0$; then $\mu\le\mu_1(s)\le s\mu$. **Orthogonal matching pursuit**
  starts from $S^0=\emptyset$, $x^0=0$, and sets
  $S^{n+1}=S^n\cup\{j_{n+1}\}$ with $j_{n+1}$ maximizing
  $|(A^*(y-Ax^n))_j|$, and $x^{n+1}$ a minimizer of $\|y-Az\|_2$ over $z$
  supported in $S^{n+1}$. If $\mu_1(s)+\mu_1(s-1)<1$, in particular if
  $(2s-1)\mu<1$, then every $s$-sparse $x$ is recovered exactly from $y=Ax$
  both by at most $s$ iterations of orthogonal matching pursuit and by basis
  pursuit.

  *Assessment.* Inner products of columns and least-squares projections are
  available. Missing are the coherence functions, the orthogonal matching
  pursuit iteration, and the recovery theorem for both algorithms.

  *Lean target.* Carriers at the pins: the columns `fun j i ↦ A i j` in
  `EuclideanSpace 𝕜 (Fin m)`, `inner`, `Finset.sup'` over `Finset.powersetCard s` for
  `μ₁(s)` (finite, with the convention `μ₁(0) = 0` built in by an empty sum), and
  `Submodule.starProjection` onto the span of the selected columns for the least-squares
  step. New definitions: `coherence A`, `coherenceFunction A s`, and orthogonal matching
  pursuit as a relation `OMPStep A y (S, x) (S', x')` (any maximizing index; a least-squares
  minimizer supported in `S'`), so that the theorem holds for every run. Conjuncts, for
  columns of norm `1` and `1 ≤ s`: (i) `μ ≤ μ₁(s) ≤ s μ` for `1 ≤ s ≤ N - 1`; (ii) if
  `μ₁(s) + μ₁(s - 1) < 1`, every run of `s` steps from `y = A x`, `x` `s`-sparse, ends at
  `x`; (iii) under the same condition, the null space property of order `s` (13.12), hence
  recovery by basis pursuit. Pitfall: the minimizer in the least-squares step need not be
  unique unless the selected columns are independent, which (ii) proves along the run.
  Statable at the pins; depends on 13.12. NASC: none.

* **13.17. Lower bounds through Gelfand widths.** The **Gelfand $m$-width** of a
  subset $K$ of a normed space $X$ is
  $d^m(K,X)=\inf\{\sup_{x\in K\cap L}\|x\|:L\text{ a subspace of }X,\
  \mathrm{codim}\,L\le m\}$. For $1<p\le2$ and $m<N$ there are constants
  $c_1,c_2>0$ depending only on $p$ such that
  $$c_1\min\Bigl\{1,\frac{\log(eN/m)}m\Bigr\}^{1-1/p}\le
  d^m(B_1^N,\ell_p^N)\le c_2\min\Bigl\{1,\frac{\log(eN/m)}m\Bigr\}^{1-1/p},$$
  where $B_1^N$ is the unit ball of $\ell_1^N$ over $\mathbb R$. Moreover, if
  $A\in\mathbb R^{m\times N}$ is such that every $2s$-sparse $x\in\mathbb R^N$
  is a minimizer of $\|z\|_1$ subject to $Az=Ax$, then
  $$m\ge\frac{s}{\log9}\,\log\frac N{4s} .$$
  When $N/s$ is large this matches, up to a constant factor, the number
  $s\log(eN/s)$ of measurements in 13.15.

  *Assessment.* Gelfand widths are not defined in either library. The selected
  part is the necessary number of measurements for uniform $\ell_1$ recovery,
  which rests on a combinatorial packing lemma and a volume comparison, and
  the lower width bound it implies.

  *Scope.* The selected conclusions are the measurement bound
  $m\ge s\log(N/(4s))/\log 9$ and the lower bound on $d^m(B_1^N,\ell_p^N)$; the
  upper bound, which rests on the random matrices of 13.15, is not selected.

  *Lean target.* Carriers at the pins: `Submodule` of `EuclideanSpace ℝ (Fin N)` with
  `Module.finrank` for codimension, `Metric.closedBall`, `PiLp`, `iSup` and `iInf` valued in
  `ℝ≥0∞` for the width, `MeasureTheory.volume` on `EuclideanSpace` for the volume argument.
  New definitions: `gelfandWidth K m` as an infimum over subspaces of codimension `≤ m` of the
  supremum of norms on `K ∩ L`, in `ℝ≥0∞` so that unbounded sections are not truncated by
  junk values. Conjuncts: (i) for `A : Matrix (Fin m) (Fin N) ℝ` such that every `2s`-sparse
  `x` minimizes `‖z‖₁` on `{z | A z = A x}`, `1 ≤ s`, `m ≥ s / log 9 * log (N / (4 s))`;
  (ii) the lower bound of the width for `1 < p ≤ 2`, `m < N`, with an existential constant
  depending on `p`. Pitfall: (i) is vacuous for `4 s ≥ N` (the right side is `≤ 0`), as it should
  be. (i) is statable at the pins; (ii) needs the width definition. Depends on 13.12. NASC: none.

## 14. Initial value problems: one-step and multistep methods

[Synopsis](SYNOPSIS.md#14-initial-value-problems-one-step-and-multistep-methods) · [Coverage inventory](STRUCTURE.md#14-initial-value-problems-one-step-and-multistep-methods)

Picard–Lindelöf and Grönwall estimates are available for continuous solutions.
The selected results concern numerical consistency, order, convergence and the
algebra of one-step and multistep methods.

The problem is $y'=f(t,y)$, $y(t_0)=y_0$, with
$f:[t_0,T]\times\mathbb R^N\to\mathbb R^N$ (or defined on a subset), and
$\|\cdot\|$ is a norm on $\mathbb R^N$. Stiff problems and stability for
large Lipschitz constants are in Section 15. Finite difference methods for
boundary value problems are in Section 16.

### Existence, uniqueness and continuous dependence

* **14.1. Existence and uniqueness (Picard–Lindelöf).**
  - (Global form.) Let $f:[t_0,T]\times\mathbb R^N\to\mathbb R^N$ be continuous
    and satisfy the **Lipschitz condition** $\|f(t,y)-f(t,z)\|\le L\|y-z\|$
    for all $t\in[t_0,T]$ and $y,z\in\mathbb R^N$. Then the initial value
    problem has a unique solution $y\in C^1([t_0,T];\mathbb R^N)$.
  - (Local form.) Let
    $D=\{(t,y):t_0\le t\le t_0+a,\ \|y-y_0\|\le b\}$ with $a,b>0$, let $f$ be
    continuous on $D$ with $\|f\|\le A$ on $D$, and let $f$ satisfy the
    Lipschitz condition with constant $L$ on $D$. Then the initial value
    problem has a unique solution on $[t_0,t_0+\alpha]$, with
    $\alpha=\min(a,b/A)$, and its graph lies in $D$. For a partition
    $t_0<t_1<\dots<t_n=t_0+\alpha$ the **Euler polygon** is the piecewise
    linear function through the points $(t_j,y_j)$, where
    $y_{j+1}=y_j+(t_{j+1}-t_j)f(t_j,y_j)$; the Euler polygons converge
    uniformly to the solution on $[t_0,t_0+\alpha]$ as the maximal step size
    $\max_j(t_{j+1}-t_j)$ tends to $0$.

  *Assessment.* Partly covered. The libraries give local existence and
  uniqueness and, for autonomous globally Lipschitz fields, global existence
  in their respective ODE frameworks. Uniform convergence of polygonal Euler
  approximants is the selected gap.

  *Scope.* The selected conclusion is convergence of the variable-step Euler
  polygons in the local Lipschitz rectangle.

  *Lean target.* Carriers at the pins: `IsPicardLindelof` with
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` and
  `ODE_solution_unique_of_mem_Icc` for the solution, `Metric.closedBall`, `ContinuousOn` on
  `Set.Icc t₀ (t₀ + a) ×ˢ closedBall y₀ b`, `LipschitzOnWith`, `HasDerivWithinAt`. New
  definitions: a partition as a strictly monotone `t : Fin (n + 1) → ℝ` from `t₀` to
  `t₀ + α`, its mesh `max_i (t (i+1) - t i)`, the Euler values by recursion, and the polygon as
  the function equal on `[t i, t (i+1)]` to the affine interpolant. Conjuncts, in a normed
  space `E` (complete for existence), with `0 < a`, `0 < b`, `0 < A`: (i) the Euler values stay
  in `closedBall y₀ b`; (ii) for every `ε > 0` there is `δ > 0` such that every polygon of mesh
  `≤ δ` is uniformly within `ε` of the solution on `[t₀, t₀ + α]`. Pitfall: `α = min a (b / A)`
  needs `A > 0` (with `A = 0`, `b / A` is the junk value `0`). Statable at the pins; the
  existence half is library material. NASC: `NASC.exists_eulerPolygon_uniform_limit`
  (`NASC/InitialValueProblems.lean`) states (ii) with the solution as part of the conclusion,
  `sorry`; (i) is used inside it but not stated.

### One-step and Runge–Kutta methods

* **14.4. Convergence of one-step methods.** A **one-step method** on the grid
  $t_0<t_1<\dots<t_M=T$, $h_n=t_{n+1}-t_n$, $h=\max_nh_n$, is
  $y_{n+1}=y_n+h_n\Phi(t_n,y_n,h_n)$. Its **local error** at a solution $y$
  is $y(t+h)-y(t)-h\Phi(t,y(t),h)$. Suppose that for some $p\in\mathbb N$ and
  $C\ge0$ the local error satisfies $\|y(t+h)-y(t)-h\Phi(t,y(t),h)\|\le
  Ch^{p+1}$ for $t_0\le t\le t+h\le T$ and $0<h\le h_0$, and that
  $\|\Phi(t,z,h)-\Phi(t,w,h)\|\le\Lambda\|z-w\|$ for all $t$, $z$, $w$ and
  $0<h\le h_0$, with $\Lambda>0$. Then with exact initial value
  $y_0=y(t_0)$ and $h\le h_0$,
  $$\|y(t_M)-y_M\|\le h^p\,\frac{C}{\Lambda}\bigl(e^{\Lambda(t_M-t_0)}-1
  \bigr).$$
  The method has **order** $p$ if its local error is $O(h^{p+1})$ for every
  sufficiently smooth $f$; then, under the Lipschitz condition on $\Phi$, the
  global error is $O(h^p)$. For Euler's method $\Phi=f$, if $f$ is
  differentiable with $\|f\|\le A$, $\|\partial f/\partial y\|\le L$ and
  $\|\partial f/\partial t\|\le M$ in a neighbourhood of the solution, then
  for $h$ sufficiently small the Euler polygon $y_h$ satisfies
  $\|y(t)-y_h(t)\|\le\frac{M+AL}{L}\bigl(e^{L(t-t_0)}-1\bigr)h$.

  *Assessment.* Existing Grönwall estimates apply once the recurrence for the
  accumulated error has been derived. The selected theorem connects a bound on
  the local defect to a global error on a variable step grid.

  *Lean target.* Carriers at the pins: `gronwallBound` with `gronwallBound_of_K_ne_0`,
  `discrete_gronwall_prod_general`, `LipschitzWith`, `Real.exp`. New definitions: the increment
  function `Φ : ℝ → E → ℝ → E`, the numerical sequence of a mesh, the local error (defect).
  Conjuncts, in a normed space `E`, for a strictly monotone grid with steps `≤ h ≤ h₀`,
  `0 ≤ C`, `0 < Λ`, a solution `y` and `y₀ = y t₀`: (i) the global bound
  `‖y t_M - y_M‖ ≤ h ^ p * (C / Λ) * (exp (Λ (t_M - t₀)) - 1)`; (ii) the Euler bound with
  `M + A L`, for `f` differentiable with the three bounds in a neighbourhood of the solution and
  `h` small. The `O(h^p)` reading of order is prose. Pitfall: `Λ > 0` is needed for the closed
  form; `Λ = 0` gives the bound `C h^p (t_M - t₀)`, the limit. Statable and provable at the
  pins. NASC: `NASC.oneStep_final_error_le` (`NASC/InitialValueProblems.lean`) states (i),
  `sorry`; (ii) is not stated.

* **14.5. Runge–Kutta methods.** An $s$-stage **Runge–Kutta method** with
  tableau $(A,b,c)$, $A=(a_{ij})\in\mathbb R^{s\times s}$,
  $b,c\in\mathbb R^s$ and $c_i=\sum_ja_{ij}$, is
  $$Y_i=y_n+h\sum_{j=1}^sa_{ij}f(t_n+c_jh,Y_j)\quad(i=1,\dots,s),\qquad
  y_{n+1}=y_n+h\sum_{i=1}^sb_if(t_n+c_ih,Y_i).$$
  It is **explicit** if $a_{ij}=0$ for $j\ge i$. If $f$ has Lipschitz
  constant $L$ in $y$ and $hL\max_i\sum_j|a_{ij}|<1$, then the stage
  equations have a unique solution.

  *Assessment.* The contraction theorem is available. The selected result
  constructs the implicit stage problem and proves solvability with the stated
  row-sum bound.

  *Argument.* On $E^s$ with the maximum norm the map
  $(Y_i)\mapsto\bigl(y_n+h\sum_ja_{ij}f(t_n+c_jh,Y_j)\bigr)_i$ is Lipschitz with
  constant $|h|L\max_i\sum_j|a_{ij}|<1$, and Banach's fixed point theorem gives
  the unique stage vector.

  *Lean target.* Carriers at the pins: `ContractingWith` with `ContractingWith.fixedPoint` and
  `ContractingWith.fixedPoint_unique`, the sup norm on `Fin s → E`, `Matrix (Fin s) (Fin s) ℝ`.
  New definitions: a structure `ButcherTableau s` (or `RungeKuttaTableau s`) with
  `A : Matrix (Fin s) (Fin s) ℝ`, `b c : Fin s → ℝ`; the predicate `IsStageSolution f t h y Y` and
  the update. Conjuncts, in a complete normed space: (i) unique solvability when
  `|h| L max_i ∑_j |a_ij| < 1` and `f t` is `L`-Lipschitz for every `t`; (ii) the explicit case
  needs no condition. Pitfall: `s = 0` is allowed (the empty stage vector). Statable and
  provable at the pins. NASC: `NASC.RungeKuttaTableau.existsUnique_stages`
  (`NASC/InitialValueProblems.lean`) states (i) with a bound `q < 1` on every row, proved (Banach
  fixed point theorem in the sup norm).

* **14.6. Order conditions by rooted trees.** Let $T$ be the set of rooted
  trees, with $\bullet$ the one-vertex tree and $t=[t_1,\dots,t_m]$ the tree
  obtained by joining the roots of $t_1,\dots,t_m$ to a new root. The
  **order** $|t|$ is the number of vertices. Define recursively
  $$\gamma(\bullet)=1,\qquad
  \gamma([t_1,\dots,t_m])=|t|\,\gamma(t_1)\cdots\gamma(t_m),$$
  and for a tableau $(A,b,c)$ the **elementary weights**
  $\Phi(t)=\sum_jb_j\Phi_j(t)$, where $\Phi_j(\bullet)=1$ and
  $\Phi_j([t_1,\dots,t_m])=\prod_{k=1}^m\bigl(\sum_la_{jl}\Phi_l(t_k)\bigr)$.
  Then the Runge–Kutta method has order $p$ if and only if
  $$\Phi(t)=\frac1{\gamma(t)}\qquad\text{for all }t\in T\text{ with }
  |t|\le p.$$
  The number $\theta_n$ of rooted trees of order $n$ is determined by
  $\sum_{n\ge1}\theta_nx^{n-1}=\prod_{n\ge1}(1-x^n)^{-\theta_n}$; for
  $n=1,\dots,10$ it is $1,1,2,4,9,20,48,115,286,719$, so the numbers of order
  conditions for orders $1,\dots,10$ are
  $1,2,4,8,17,37,85,200,486,1205$.

  *Assessment.* Finite trees and recursively defined products can be
  represented. The gap identifies their weights with Taylor coefficients and
  proves necessity and sufficiency of the order equations.

  *Lean target.* Carriers at the pins: `ContDiff`, `iteratedFDeriv`, `Asymptotics.IsBigO` at
  `nhds 0`, `EuclideanSpace ℝ (Fin n)`, `Multiset` for unordered children. New definitions:
  rooted trees as an inductive type with a `Multiset` (or a list modulo permutation) of
  children; `order`, `density` `γ`, the elementary weights `Φ_j` and `Φ`, the elementary
  differentials `F(t)` through `iteratedFDeriv`, and `HasOrder T p`: for every `n`, every
  `C^{p+1}` field on `ℝ^n` and every solution, the local error along the stage branch through
  the initial value is `O(h^{p+1})`. Conjuncts: (i) the equivalence of `HasOrder T p` with
  `Φ(t) = 1/γ(t)` for `|t| ≤ p`, for tableaux with `c = A 𝟙` (non-autonomous order) or without
  that condition for autonomous problems; (ii) `θ_n` for `n ≤ 10` and the cumulative counts, by
  `decide` on an enumeration. Pitfall: with ordered children the sum over trees needs the
  symmetry factor, so the elementary-weight condition must be stated for every ordered
  representative; the dimension must be arbitrary, since for scalar autonomous problems the
  order conditions differ from order five on. Statable at the pins; the elementary
  differential expansion of the exact flow (Butcher series of the solution) is missing
  infrastructure. Depends on 14.5. NASC: `NASC.RungeKuttaTableau.hasAutonomousOrder_iff_treeWeight`
  (`NASC/InitialValueProblems.lean`) states (i) for autonomous order with ordered trees
  `NASC.RungeKuttaTree`, `sorry`; (ii) is not stated.

* **14.7. Butcher barriers.** Let an explicit $s$-stage Runge–Kutta method
  have order $p$. Then $p\le s$. If $p\ge5$, then $s\ge p+1$. If $p\ge7$, then
  $s\ge p+2$. If $p\ge8$, then $s\ge p+3$. Explicit methods of order $7$ with
  $9$ stages and of order $8$ with $11$ stages exist.

  *Assessment.* The bound $p\le s$ for explicit methods is a short consequence
  of the test equation. The barriers for $p\ge5$, $7$ and $8$ rest on
  Butcher's analysis of the order conditions and are the selected gap.

  *Scope.* The selected conclusions are the three barriers $s\ge p+1$ for
  $p\ge5$, $s\ge p+2$ for $p\ge7$ and $s\ge p+3$ for $p\ge8$; $p\le s$ and the
  existence of the two methods are not selected.

  *Lean target.* Carriers at the pins: those of 14.6. New definitions: `IsExplicit T` as
  `∀ i j, i ≤ j → T.A i j = 0`, and the tree conditions of 14.6 as a predicate
  `OrderConditions T p` (`Φ(t) = 1/γ(t)` for every tree of order `≤ p`). Conjuncts: for
  every explicit tableau with `OrderConditions T p`,
  (i) `5 ≤ p → p + 1 ≤ s`; (ii) `7 ≤ p → p + 2 ≤ s`; (iii) `8 ≤ p → p + 3 ≤ s`. Stating them
  through `OrderConditions` rather than the analytic order makes them independent of 14.6.
  Statable at the pins; the proofs are long algebraic case analyses (HNW II.5). Depends on 14.6
  for the link with order. NASC: none.

* **14.8. Simplifying assumptions.** For a tableau $(A,b,c)$ consider
  $$B(p):\ \sum_ib_ic_i^{q-1}=\frac1q\ (q\le p),\qquad
  C(\eta):\ \sum_ja_{ij}c_j^{q-1}=\frac{c_i^q}q\ (\text{all }i,\ q\le\eta),$$
  $$D(\zeta):\ \sum_ib_ic_i^{q-1}a_{ij}=\frac{b_j(1-c_j^q)}q
  \ (\text{all }j,\ q\le\zeta).$$
  If $B(p)$, $C(\eta)$ and $D(\zeta)$ hold with $p\le\eta+\zeta+1$ and
  $p\le2\eta+2$, then the method has order $p$. The largest $\eta$ with
  $C(\eta)$ is the **stage order**.

  *Assessment.* The tree-order characterization supplies individual order
  equations. These tableau conditions give a sufficient test that avoids
  enumerating all trees up to the claimed order.

  *Lean target.* Carriers and definitions of 14.6. Conjuncts: for natural `p`, `η`, `ζ` with
  `p ≤ η + ζ + 1` and `p ≤ 2η + 2`, `B(p)`, `C(η)` and `D(ζ)` imply `OrderConditions T p`
  and hence `HasOrder T p`. The conditions are indexed `q < p` with exponents `q` and
  denominators `q + 1` to avoid the subtraction `q - 1` on `ℕ`. Pitfall: HNW assumes
  `c = A 𝟙`; `C(1)` implies it, and for `η = 0` the conditions `B(2)` and `D(1)` give the only
  tree condition of order two that involves `A`, so the statement needs no extra hypothesis.
  Statable at the pins; depends on 14.6. NASC:
  `NASC.RungeKuttaTableau.hasAutonomousOrder_of_simplifying` (`NASC/InitialValueProblems.lean`),
  `sorry`.

* **14.9. Collocation methods.** Let $c_1,\dots,c_s\in\mathbb R$ be distinct,
  and let $f$ be continuous and Lipschitz in $y$. For $|h|$ sufficiently small
  there is a unique polynomial $u$ of degree at most $s$, the **collocation
  polynomial**, with $u(t_0)=y_0$ and $u'(t_0+c_ih)=f(t_0+c_ih,u(t_0+c_ih))$
  for $i=1,\dots,s$, and the **collocation method** sets $y_1=u(t_0+h)$.
  - The collocation method is the Runge–Kutta method with
    $a_{ij}=\int_0^{c_i}\ell_j(\tau)\,d\tau$ and
    $b_j=\int_0^1\ell_j(\tau)\,d\tau$, where $\ell_j$ are the Lagrange basis
    polynomials for the nodes $c_1,\dots,c_s$.
  - A Runge–Kutta method with distinct $c_i$ and order at least $s$ is a
    collocation method if and only if $C(s)$ holds.
  - If $M(\tau)=\prod_{i=1}^s(\tau-c_i)$ satisfies
    $\int_0^1M(\tau)\tau^{q-1}\,d\tau=0$ for $q=1,\dots,r$, then the
    collocation method has order at least $s+r$.
  - Consequently the **Gauss methods** ($c_i$ the zeros of the shifted
    Legendre polynomial of degree $s$ on $[0,1]$) have order $2s$, the
    **Radau IIA methods** ($c_i$ the zeros of
    $\frac{d^{s-1}}{d\tau^{s-1}}\bigl(\tau^{s-1}(\tau-1)^s\bigr)$, so
    $c_s=1$) have order $2s-1$, and the **Lobatto IIIA methods** ($c_i$ the
    zeros of $\frac{d^{s-2}}{d\tau^{s-2}}\bigl(\tau^{s-1}(\tau-1)^{s-1}\bigr)$,
    $s\ge2$, so $c_1=0$, $c_s=1$) have order $2s-2$. A Runge–Kutta method
    with $s$ stages has order at most $2s$, and order $2s$ holds exactly for
    the Gauss method.

  *Assessment.* Lagrange interpolation and polynomial exactness are
  ingredients. The selected theorem relates collocation to the Runge–Kutta
  tableau and the quadrature orthogonality condition to order.

  *Lean target.* Carriers at the pins: `Lagrange.basis`, `Polynomial.eval`, `intervalIntegral`,
  `Polynomial.shiftedLegendre` (degree `n` on `[0, 1]`) with its roots, `Polynomial.derivative`
  iterated for the Radau and Lobatto node polynomials. New definitions: `collocationTableau c`
  for injective `c : Fin s → ℝ`, and the collocation polynomial as a polynomial with values in
  `E` (a `Fin (s+1)`-family of coefficients). Conjuncts: (i) for `f` Lipschitz and `|h|` small
  the collocation polynomial exists uniquely and its step is the Runge–Kutta step of
  `collocationTableau c`; (ii) a tableau with injective `c` and `HasOrder T s` is a
  collocation tableau iff `C(s)`; (iii) orthogonality of `M` to degrees `< r` gives
  `HasOrder (collocationTableau c) (s + r)`; (iv) the orders of Gauss, Radau IIA and Lobatto
  IIIA; (v) `HasOrder T p → p ≤ 2 s`, with equality only for the Gauss nodes. Pitfall: the
  existence in (i) is local in `h`; with `HasOrder` defined along the stage branch (14.6) the
  orders do not depend on a global solvability hypothesis. (ii)–(iv) are statable through
  `OrderConditions` without analysis. Depends on 14.5, 14.6, 14.8. NASC:
  `NASC.RungeKuttaTableau.hasAutonomousOrder_of_collocation` (`NASC/InitialValueProblems.lean`)
  states (iii), `sorry`; the others are not stated.

### Linear multistep methods

* **14.10. Linear multistep methods and their order.** A **linear $k$-step
  method** is
  $$\sum_{j=0}^k\alpha_jy_{n+j}=h\sum_{j=0}^k\beta_jf(t_{n+j},y_{n+j}),
  \qquad\alpha_k\ne0,\quad|\alpha_0|+|\beta_0|>0,$$
  with $\rho(\zeta)=\sum_j\alpha_j\zeta^j$ and
  $\sigma(\zeta)=\sum_j\beta_j\zeta^j$. It is **explicit** if $\beta_k=0$.
  It has **order** $p$ if
  $L(y,t,h)=\sum_j\bigl(\alpha_jy(t+jh)-h\beta_jy'(t+jh)\bigr)=O(h^{p+1})$
  for every smooth $y$. The following are equivalent:
  - the method has order $p$;
  - $\sum_j\alpha_j=0$ and $\sum_j\alpha_jj^q=q\sum_j\beta_jj^{q-1}$ for
    $q=1,\dots,p$;
  - $\rho(e^h)-h\sigma(e^h)=O(h^{p+1})$ as $h\to0$;
  - $\rho(\zeta)/\log\zeta-\sigma(\zeta)=O((\zeta-1)^p)$ as $\zeta\to1$.

  If the order is exactly $p$, then $L(y,t,h)=C_{p+1}h^{p+1}y^{(p+1)}(t)+
  O(h^{p+2})$ with
  $C_{p+1}=\frac1{(p+1)!}\bigl(\sum_j\alpha_jj^{p+1}-(p+1)\sum_j\beta_jj^p
  \bigr)$, and the **error constant** is $C=C_{p+1}/\sigma(1)$. The method is
  **consistent** if $p\ge1$, that is, $\rho(1)=0$ and $\rho'(1)=\sigma(1)$.

  *Assessment.* The selected equivalences need the local multistep error
  functional and its moment conditions, including the generating-polynomial
  characterization.

  *Scope.* The target is the multistep order test, including the first nonzero
  defect coefficient, the error constant and the consistency conditions.

  *Lean target.* Carriers at the pins: `Polynomial ℂ` or `ℝ[X]` for `ρ` and `σ`,
  `Polynomial.derivative`, `Polynomial.eval`, `Asymptotics.IsBigO` at `nhds 0` and at
  `nhds 1`, `ContDiff`, `taylor_mean_remainder_lagrange`, `Real.log`. New definitions: a
  structure `LinearMultistepMethod k` with `α β : Fin (k + 1) → ℝ`, `α (Fin.last k) ≠ 0`; the
  defect functional; `HasOrder` by the moment conditions. Conjuncts: (i)–(iii) the
  equivalence of the moment conditions with the `O(h^{p+1})` defect for every `C^{p+1}`
  function and with `ρ(e^h) - hσ(e^h) = O(h^{p+1})`; (iv) the `ρ / log − σ` form, with
  `Real.log` near `1` only (it is `0` at `0`, a junk value outside the neighbourhood);
  (v) the leading coefficient `C_{p+1}` when the order is exactly `p`; (vi) consistency as
  `ρ 1 = 0 ∧ ρ' 1 = σ 1`. Pitfall: the error constant divides by `σ(1)`, which is `0` for an
  inconsistent method; define it only under consistency. Statable and provable at the pins.
  NASC: `NASC.multistepHasOrder_iff_defect_isBigO` (`NASC/InitialValueProblems.lean`) states
  (i) for scalar functions, `sorry`; (ii)–(vi) are not stated.

* **14.11. Root condition and the Dahlquist equivalence theorem.** The method
  is **zero-stable** (satisfies the **root condition**) if every zero of
  $\rho$ lies in $\{|\zeta|\le1\}$ and the zeros with $|\zeta|=1$ are simple.
  The method is **convergent** if for every problem with $f$ sufficiently
  smooth and Lipschitz in $y$, and all starting values with
  $y_j(h)\to y_0$ ($j=0,\dots,k-1$) as $h\to0$, the solution with constant
  step $h$ satisfies $y_n\to y(t)$ as $h\to0$ with $t_n=t_0+nh=t$ fixed.
  Then:
  - the method is convergent if and only if it is zero-stable and
    consistent;
  - if it is zero-stable and has order $p$, and the starting errors are
    $O(h^p)$, then $\|y(t_n)-y_n\|=O(h^p)$ uniformly for
    $t_0\le t_n\le T$.

  *Assessment.* The location and multiplicity of characteristic roots control
  solutions of a linear recurrence. The equivalence theorem must connect this
  stability criterion with consistency and uniform convergence for the
  nonlinear initial value problem.

  *Lean target.* Carriers at the pins: `Polynomial.roots`, `Polynomial.rootMultiplicity`,
  `LinearRecurrence` with `LinearRecurrence.solSpace`, `LipschitzWith`, `Filter.Tendsto`.
  New definitions: `IsZeroStable ρ` (roots in the closed disc, roots on the circle simple),
  the multistep sequence with starting values, and `IsConvergent` quantified over all
  `C^1` (or Lipschitz and continuous) fields, all starting values tending to `y₀`, and
  `t = t₀ + n h` fixed with `h = (t - t₀)/n`. Conjuncts: (i) the root condition is equivalent
  to uniform boundedness of the solutions of `∑ α_j u_{n+j} = 0` with bounded initial
  values; (ii) `IsConvergent ↔ IsZeroStable ρ ∧ consistent`; (iii) zero-stability, order `p`
  and `O(h^p)` starting errors give `O(h^p)` global error uniformly on `[t₀, T]`. Pitfall: the
  root condition requires `ρ ≠ 0` (guaranteed by `α_k ≠ 0`); convergence must be stated with
  `n → ∞` and `h = (t - t₀)/n`, not as a limit in `h` over all reals. Statable at the pins.
  Depends on 14.10. NASC: `NASC.isZeroStable_iff_bounded_recurrence`
  (`NASC/InitialValueProblems.lean`) states (i), `sorry`; (ii) and (iii) are not stated.

* **14.12. First Dahlquist barrier.** A zero-stable linear $k$-step method has
  order $p\le k+2$ if $k$ is even and $p\le k+1$ if $k$ is odd. If
  $\beta_k/\alpha_k\le0$, in particular if the method is explicit, then
  $p\le k$.

  *Assessment.* The gap is the sharp order restriction under the root
  condition, with the separate explicit-method bound.

  *Lean target.* Carriers and definitions of 14.10 and 14.11. Conjuncts, for `0 < k`,
  `α_k ≠ 0`, the root condition and order `p`: (i) `p ≤ k + 2` for even `k` and `p ≤ k + 1`
  for odd `k`; (ii) `β_k / α_k ≤ 0 → p ≤ k`. Pitfall: the statement is about order at least
  `p` (the moment conditions), so it bounds every `p` for which they hold; common factors of
  `ρ` and `σ` need no exclusion. Statable at the pins; the proof uses the transformation
  `ζ = (1 + w)/(1 - w)` and the sign pattern of the transformed coefficients. NASC:
  `NASC.multistep_order_le_dahlquist` (`NASC/InitialValueProblems.lean`), `sorry`.

* **14.13. Backward differentiation formulas.** The **$k$-step BDF method**
  has $\sigma(\zeta)=\zeta^k$ and
  $$\rho(\zeta)=\sum_{j=1}^k\frac1j\,\zeta^{k-j}(\zeta-1)^j.$$
  It has order $k$, and it is zero-stable if and only if $1\le k\le6$; so it
  is convergent of order $k$ exactly for $k\le6$.

  *Assessment.* The order computation and the exact root locations for BDF
  zero-stability are missing. The general equivalence theorem then supplies
  the convergence classification.

  *Lean target.* Carriers of 14.10–14.11. New definition: the BDF polynomial
  `∑_{j=1}^k (1/j) X^{k-j} (X - 1)^j`. Conjuncts, for `1 ≤ k`: (i) order exactly `k`; (ii)
  `IsZeroStable ↔ k ≤ 6`; (iii) convergence of order `k` exactly for `k ≤ 6`, from (ii) and
  14.11. Pitfall: (ii) for `k ≥ 7` is an infinite family; Cryer's proof (or the sign of
  `Re ρ` on the circle) is needed, while `k ≤ 6` is a finite computation with certified root
  bounds. Statable at the pins; depends on 14.11 for (iii). NASC:
  `NASC.isZeroStable_bdfPolynomial_iff` (`NASC/InitialValueProblems.lean`) states (ii), `sorry`.

### Error expansions, extrapolation and B-series

* **14.14. Asymptotic error expansion and extrapolation.** Let a one-step
  method of order $p$ with sufficiently differentiable $\Phi$ and $f$ be
  applied with constant step size $h$. Then for every $N\ge p$ there are
  functions $e_p,\dots,e_N$, independent of $h$ and solving linear
  inhomogeneous differential equations with $e_j(t_0)=0$, such that at the
  grid points $t=t_0+nh\in[t_0,T]$
  $$y(t)-y_h(t)=e_p(t)h^p+e_{p+1}(t)h^{p+1}+\dots+e_N(t)h^N+E_h(t)h^{N+1},$$
  with $E_h(t)$ bounded for $t\in[t_0,T]$ and $0<h\le h_0$. If the method is
  **symmetric** (equal to its adjoint), only even powers of $h$ occur.
  **Extrapolation:** given $H>0$ and integers $n_1<n_2<\cdots$, let
  $T_{i,1}=y_{h_i}(t_0+H)$ with $h_i=H/n_i$, and let $T_{j,k}=P(0)$, where
  $P(h)=Y-\sum_{q=p}^{p+k-2}d_qh^q$ is the function of this form with
  $P(h_i)=T_{i,1}$ for $i=j-k+1,\dots,j$. Then $T_{j,k}$, as a one-step
  method with step $H$, has order $p+k-1$.

  *Assessment.* The selected results are the existence of the asymptotic
  expansion of the global error of a one-step method, its restriction to even
  powers for symmetric methods, and the order of the extrapolated values.

  *Lean target.* Carriers at the pins: `ContDiff`, `Asymptotics.IsBigO` (uniformly in `t` over
  the grid), `IsPicardLindelof` for the variational equations, `Lagrange.basis` or Neville's
  recursion for the extrapolation table. New definitions: the adjoint method
  `Φ*_h = Φ_{-h}⁻¹`, symmetry, the extrapolation tableau `T j k`. Conjuncts: (i) for every
  `N ≥ p` there are functions `e_j`, solving the stated linear equations with `e_j t₀ = 0`,
  and a constant `C` with `‖y t - y_h t - ∑ e_j t h^j‖ ≤ C h^{N+1}` for grid points `t` and
  `0 < h ≤ h₀`; (ii) for symmetric methods `e_j = 0` for odd `j`; (iii) `T j k` has order
  `p + k - 1`. Pitfall: grid points `t = t₀ + n h` must be part of the quantification;
  `E_h(t)` bounded means one constant for all such `t` and `h`. Needs the smooth dependence
  of the numerical flow on parameters; statable at the pins. Depends on 14.4. NASC: none.

* **14.16. B-series and their composition.** Let $f$ be smooth and autonomous,
  let $F(t)$ be the **elementary differentials**
  ($F(\bullet)(y)=f(y)$, $F([t_1,\dots,t_m])(y)=
  f^{(m)}(y)(F(t_1)(y),\dots,F(t_m)(y))$), and let $\alpha(t)$ be the number
  of monotonic labellings of $t$. For $a:T\cup\{\emptyset\}\to\mathbb R$
  the (formal) **B-series** is
  $$B(a,y)=a(\emptyset)y+\sum_{t\in T}\frac{h^{|t|}}{|t|!}\alpha(t)a(t)
  F(t)(y).$$
  The exact flow is $B(e,y_0)$ with $e\equiv1$, and one step of a Runge–Kutta
  method is $B(a,y_0)$ with $a(\emptyset)=1$ and $a(t)=\gamma(t)\Phi(t)$. If
  $a(\emptyset)=1$, then $B(b,B(a,y))=B(ab,y)$ for an explicitly given
  product $ab$, and the set $\{a:a(\emptyset)=1\}$ with this product is a
  non-commutative group (the **Butcher group**). All identities hold as
  formal power series in $h$, or modulo $O(h^{k+1})$ when $f$ is only
  $C^k$.

  *Assessment.* The recursive weights in the order theory are ingredients. The
  gap needs the B-series composition law and its forest combinatorics.

  *Lean target.* Carriers at the pins: `iteratedFDeriv`, `FormalMultilinearSeries` or
  `PowerSeries` in `h` for formal identities, `Asymptotics.IsBigO` for truncated ones, `Group`
  for the Butcher group. New definitions: trees and elementary differentials as in 14.6; the
  B-series as a formal power series in `h` with coefficients in the space of maps `E → E`;
  the composition product `a b` through ordered subtrees (cuts), with the monotonic-labelling
  count `α(t)`. Conjuncts: (i) the exact flow is `B(e, y₀)` up to `O(h^{k+1})` for `C^k`
  fields; (ii) a Runge–Kutta step is `B(γ Φ, y₀)` up to `O(h^{k+1})`; (iii) the composition law
  `B(b, B(a, y)) = B(a b, y)` as formal series; (iv) the characters with `a(∅) = 1` form a
  group, non-commutative. Pitfall: the normalization with `α(t)/|t|!` and unlabelled trees
  equals HNW's labelled sums; a version over ordered trees divides by the ordered weight
  instead. Missing infrastructure: formal series of vector fields and the Connes–Kreimer
  coproduct. Depends on 14.6. NASC: `NASC.RungeKuttaTableau.exists_update_bSeries`
  (`NASC/InitialValueProblems.lean`) states (ii) over ordered trees with `orderedWeight`,
  `sorry`; (i), (iii) and (iv) are not stated.

## 15. Stiff problems, differential-algebraic equations, and geometric integration

[Synopsis](SYNOPSIS.md#15-stiff-problems-differential-algebraic-equations-and-geometric-integration) · [Coverage inventory](STRUCTURE.md#15-stiff-problems-differential-algebraic-equations-and-geometric-integration)

The gap between general continuous dynamics and the numerical results lies in
the stability function, method-specific error recurrences and the preservation
of geometric structure by discrete maps.

Notation for
Runge–Kutta and linear multistep methods is that of Section 14;
$\mathbb 1=(1,\dots,1)^\top\in\mathbb R^s$, $\mathbb C^-=\{z:\mathrm{Re}\,z
\le0\}$, and $\langle\cdot,\cdot\rangle$ is an inner product on
$\mathbb C^N$ with norm $\|\cdot\|$. A Runge–Kutta method is
**non-confluent** if $c_1,\dots,c_s$ are distinct.

### Linear stability

* **15.1. Stability function.** Applied to the **Dahlquist test equation**
  $y'=\lambda y$, a Runge–Kutta method gives, whenever $I-h\lambda A$ is
  invertible, a unique stage vector and $y_{n+1}=R(h\lambda)y_n$, where the
  **stability function** is
  $$R(z)=1+zb^\top(I-zA)^{-1}\mathbb 1=
  \frac{\det(I-zA+z\mathbb 1b^\top)}{\det(I-zA)},$$
  a rational function with numerator and denominator of degree at most $s$.
  For an explicit method $R$ is a polynomial of degree at most $s$. If the
  method has order $p$, then $R(z)=e^z+O(z^{p+1})$ as $z\to0$. The
  **stability domain** is $S=\{z\in\mathbb C:|R(z)|\le1\}$.

  *Assessment.* The matrix inverse and determinant lemmas are available. The
  selected assertion derives the test-equation stability function from the
  stage system and connects its expansion to method order.

  *Lean target.* Carriers at the pins: `Matrix (Fin s) (Fin s) ℂ` with `Matrix.map
  Complex.ofReal`, `Matrix.det`, `Matrix.inv` (`⁻¹`), `Matrix.vecMulVec`,
  `Matrix.det_add_replicateCol_mul_replicateRow`, `Polynomial`, `Asymptotics.IsBigO`. New
  definitions: the tableau of 14.5; `stabilityFunction T z = 1 + z * b ⬝ᵥ (1 - z A)⁻¹ *ᵥ 𝟙`;
  numerator and denominator polynomials `det (1 - X A + X 𝟙 bᵀ)` and `det (1 - X A)` in `ℂ[X]`.
  Conjuncts: (i) for `det (1 - h λ A) ≠ 0` the stage system of `y' = λ y` has a unique solution
  and the step is `R(hλ) y_n`; (ii) where `det (1 - z A) ≠ 0`, the determinant quotient; (iii)
  numerator and denominator have `natDegree ≤ s`, and the denominator is `1` for explicit
  tableaux; (iv) order `p` (14.6) implies `R(z) - exp z = O(z^{p+1})` at `0`. Pitfall:
  Mathlib's `M⁻¹ = 0` for singular `M` makes the first formula equal `1` there, so every
  statement carries `det (1 - z A) ≠ 0` or works with the polynomial quotient; the stability
  domain should exclude the zeros of the denominator. Statable and provable at the pins;
  (iv) depends on 14.6. NASC: the definition `NASC.RungeKuttaTableau.stabilityFunction` and
  `NASC.RungeKuttaTableau.stabilityFunction_eq_detRatio` (`NASC/StiffAndGeometric.lean`) state
  (ii), proved; (i), (iii), (iv) are not stated.

* **15.3. Padé approximations and the Ehle conjecture.** For
  $k,j\in\mathbb N_0$ the **$(k,j)$ Padé approximation** to $e^z$ is
  $R_{kj}=P_{kj}/Q_{kj}$ with
  $$P_{kj}(z)=\sum_{m=0}^k\frac{k!\,(j+k-m)!}{(j+k)!\,m!\,(k-m)!}z^m,
  \qquad Q_{kj}(z)=P_{jk}(-z).$$
  It is the unique rational function with numerator degree at most $k$ and
  denominator degree at most $j$ such that $R_{kj}(z)-e^z=O(z^{k+j+1})$.
  The function $R_{kj}$ is A-stable (bounded by $1$ in modulus on
  $\mathbb C^-$) if and only if $k\le j\le k+2$.

  *Assessment.* The Padé table identities give algebraic ingredients. The
  half-plane modulus bound and its exact degree classification require the
  rational-function stability analysis.

  *Lean target.* Carriers at the pins: `Polynomial ℂ` with `Polynomial.monomial`,
  `Polynomial.eval`, `Polynomial.comp` with `-X`, `Nat.factorial`, `Complex.exp`,
  `Asymptotics.IsBigO` at `nhds 0`. New definition: `expPadeNumerator k j : ℂ[X]` and
  `Q k j = (expPadeNumerator j k).comp (-X)`. Conjuncts: (i) `P(z) - e^z Q(z) =
  O(z^{k+j+1})`; (ii) uniqueness among numerator degree `≤ k`, denominator degree `≤ j` with
  `Q(0) = 1`; (iii) A-stability, stated as `Q(z) ≠ 0` and `‖P(z)/Q(z)‖ ≤ 1` for `Re z ≤ 0`,
  iff `k ≤ j ≤ k + 2`. Pitfall: in (iii) the nonvanishing of `Q` must be a conjunct, since
  `x / 0 = 0` would make the modulus bound hold at a pole. (i) and (ii) are statable and
  provable at the pins; (iii) needs order stars or the Ehle–Wanner–Hairer–Nørsett argument (the
  argument principle on Mathlib's winding numbers is not available in this form). NASC:
  `NASC.expPade_isAStable_iff`, with `NASC.IsAStable P Q` (the conjunct form of (iii): `Q z ≠ 0`
  and `‖P z / Q z‖ ≤ 1` for `re z ≤ 0`) (`NASC/StiffAndGeometric.lean`), states (iii), `sorry`;
  (i) and (ii) are not stated.

* **15.4. A-stable implicit Runge–Kutta methods.** For every $s\in\mathbb N$:
  - the $s$-stage Gauss method has order $2s$ and $R=R_{ss}$, and it is
    A-stable;
  - the $s$-stage Radau IA and Radau IIA methods have order $2s-1$ and
    $R=R_{s-1,s}$, and they are A-stable and L-stable;
  - for $s\ge2$, the $s$-stage Lobatto IIIA, IIIB and IIIC methods have
    order $2s-2$; $R=R_{s-1,s-1}$ for IIIA and IIIB and $R=R_{s-2,s}$ for
    IIIC; all are A-stable, and IIIC is L-stable.

  *Assessment.* The stability functions of the Gauss, Radau and Lobatto
  families are identified with Padé approximants, and their A- and L-stability
  follows from 15.3.

  *Lean target.* Carriers at the pins: those of 15.1, 15.3, 14.9 (`Polynomial.shiftedLegendre`
  for the Gauss nodes). New definitions: the six tableau families for every `s` (Gauss, Radau
  IA, Radau IIA, Lobatto IIIA, IIIB, IIIC), each given by nodes and the defining simplifying
  assumptions (`B`, `C`, `D` of 14.8). Conjuncts, for every `s ≥ 1` (`s ≥ 2` for Lobatto): (i)
  the orders `2s`, `2s - 1`, `2s - 2`; (ii) `R = R_{ss}`, `R_{s-1,s}`, `R_{s-1,s-1}`,
  `R_{s-2,s}` as rational functions (equality of numerator and denominator polynomials up to a
  common scalar); (iii) A-stability, and L-stability of Radau IA, Radau IIA and Lobatto IIIC.
  Pitfall: L-stability as `‖R z‖ → 0` along `Filter.cocompact ℂ` needs numerator degree less
  than denominator degree, a polynomial statement. Statable at the pins; (iii) depends on 15.3,
  (i) on 14.8–14.9. NASC: none.

* **15.5. Stability domain of multistep methods and the second Dahlquist
  barrier.** For a linear multistep method the **stability domain** is the
  set of $\mu\in\mathbb C$ such that every root of
  $\rho(\zeta)-\mu\sigma(\zeta)=0$ satisfies $|\zeta|\le1$ and the roots with
  $|\zeta|=1$ are simple; the method is **A-stable** if this set contains
  $\mathbb C^-$. An A-stable linear multistep method has order $p\le2$. If
  $p=2$, its error constant (14.10) satisfies $C\le-\frac1{12}$, and the
  trapezoidal rule $y_{n+1}=y_n+\frac h2(f_n+f_{n+1})$ is the only A-stable
  method of order $2$ with $C=-\frac1{12}$. The BDF methods with $k=1,2$
  are A-stable.

  *Assessment.* Root multiplicity and generating polynomials are available.
  The selected result connects the stability region of a multistep formula to
  the order barrier and extremal error constant.

  *Lean target.* Carriers of 14.10–14.11. New definitions: the stability domain of a
  multistep method as the set of `μ : ℂ` with `IsZeroStable (ρ - C μ * σ)`, and A-stability as
  containment of `{μ | μ.re ≤ 0}` (NASC's `IsMultistepAStable a b`: the root condition for
  `ρ - μσ` for every `μ` with `re μ ≤ 0`). Conjuncts: (i) A-stability and order `p` give `p ≤ 2`;
  (ii) for `p = 2` the error constant satisfies `C ≤ -1/12`; (iii) equality holds only for the
  trapezoidal rule, up to the normalization `α_k = 1` and common factors of `ρ` and `σ`;
  (iv) BDF1 and BDF2 are A-stable. Pitfall: at `μ = α_k/β_k` the degree of `ρ - μσ` drops, and a
  definition through the root condition of the lower-degree polynomial differs from HW's at that
  point; for (i) this is harmless because nearby `μ` with `Re μ < 0` already fail. (iii) needs
  the normalization made explicit. Statable at the pins; depends on 14.10–14.11. NASC:
  `NASC.multistep_order_le_two_of_isMultistepAStable` (`NASC/StiffAndGeometric.lean`) states (i),
  `sorry`; (ii)–(iv) are not stated.

### Nonlinear stability

* **15.7. B-stability, AN-stability and algebraic stability.** A Runge–Kutta
  method is **B-stable** if for every $f$ with
  $\mathrm{Re}\,\langle f(t,y)-f(t,z),y-z\rangle\le0$ for all $t,y,z$, every
  $h\ge0$ and every pair of initial values $y_0,\hat y_0$, one step gives
  $\|\hat y_1-y_1\|\le\|\hat y_0-y_0\|$. It is **AN-stable** if
  $|1+b^\top Z(I-AZ)^{-1}\mathbb 1|\le1$ for all diagonal
  $Z=\mathrm{diag}(z_1,\dots,z_s)$ with $\mathrm{Re}\,z_j\le0$ and $z_j=z_k$
  whenever $c_j=c_k$. It is **algebraically stable** if $b_i\ge0$ for all
  $i$ and the matrix
  $$M=\bigl(b_ia_{ij}+b_ja_{ji}-b_ib_j\bigr)_{i,j=1}^s$$
  is positive semidefinite. Then:
  - algebraically stable $\Rightarrow$ B-stable $\Rightarrow$ AN-stable
    $\Rightarrow$ A-stable, where A-stability is that of the rational
    function $R$ of 15.1;
  - for non-confluent methods the three properties algebraic stability,
    B-stability and AN-stability are equivalent;
  - the Gauss, Radau IA, Radau IIA and Lobatto IIIC methods are
    algebraically stable, and the Lobatto IIIA and IIIB methods are not
    AN-stable, hence not B-stable.

  *Assessment.* The inner-product API can express dissipativity and positive
  semidefiniteness. The numerical theorem links these to the one-step
  contraction and the stated algebraic-stability criteria.

  *Lean target.* Carriers at the pins: `InnerProductSpace ℝ H` (or `ℂ` with `RCLike.re`),
  `Matrix.PosSemidef`, `Matrix.diagonal`, `Matrix.inv`. New definitions: `IsBStable T`
  (quantified over all real inner product spaces of a fixed universe, all dissipative `f`,
  `h ≥ 0` and pairs of stage solutions), `IsANStable T` (with the confluence restriction on
  `Z`), `IsAlgebraicallyStable T`. Conjuncts: (i) algebraically stable implies the contraction
  for every pair of stage solutions; (ii) B-stable implies AN-stable implies A-stable; (iii) for
  injective `c` the three are equivalent; (iv) Gauss, Radau IA, Radau IIA, Lobatto IIIC are
  algebraically stable, Lobatto IIIA and IIIB are not AN-stable. Pitfall: B-stability must not
  presuppose existence of the stages (state it for every pair of stage solutions); the
  AN-stability determinant `det (1 - A Z)` must be nonzero where `R(Z)` is evaluated; with
  A-stability stated by the determinant quotient, (ii) needs `det (1 - z • A) ≠ 0` on `re z ≤ 0`
  (reducible counterexample `A = diag(1, -1)`, `b = (1, 0)`). (i) is
  statable and provable at the pins; (ii)–(iii) need the construction of test problems from `Z`
  (Burrage–Butcher). Depends on 15.1, 15.4. NASC:
  `NASC.RungeKuttaTableau.norm_update_sub_le_of_algebraicStability`
  (`NASC/StiffAndGeometric.lean`) states (i), `sorry`.

### Differential-algebraic equations and exponential integrators

* **15.9. Linear constant-coefficient DAEs.** Let $A,B\in\mathbb C^{n\times n}$
  and let the pencil $A+\lambda B$ be **regular**, that is,
  $\det(A+\lambda B)\not\equiv0$. Then there are invertible $P,Q$ with
  $$PAQ=\begin{pmatrix}C&0\\0&I\end{pmatrix},\qquad
  PBQ=\begin{pmatrix}I&0\\0&N\end{pmatrix},$$
  where $N=\mathrm{blockdiag}(N_1,\dots,N_k)$, each $N_i$ is the $m_i\times
  m_i$ matrix with ones on the superdiagonal and zeros elsewhere, and $C$ may
  be taken in Jordan form (**Weierstrass–Kronecker form**). With
  $u=Q(y,z)$ the system $Bu'+Au=d(t)$ decouples into $y'+Cy=\eta(t)$ and
  $Nz'+z=\delta(t)$, where $Pd=(\eta,\delta)$; the last component of each
  block of $z$ is determined algebraically and the others by up to $m_i-1$
  differentiations of $\delta$. The **index of nilpotency** is $\max_im_i$,
  and $0$ when there is no nilpotent block, that is, when $B$ is invertible;
  it does not depend on the choice of $P,Q$.
  The **differentiation index** of $F(u',u)=0$ is the least $m$ such that
  $F=0$ and its first $m$ derivatives with respect to $t$ allow one to
  extract by algebraic manipulation an explicit system $u'=\varphi(u)$. For
  $Bu'+Au=d$ with a regular pencil it equals the index of nilpotency.

  *Assessment.* The library has matrix Jordan infrastructure in individual
  settings. The gap is the regular matrix pencil decomposition, its nilpotent
  blocks and the index of the resulting differential-algebraic system.

  *Lean target.* Carriers at the pins: `Matrix.fromBlocks`, `Matrix.submatrix` along an
  equivalence `Fin r ⊕ Fin q ≃ Fin n`, `Matrix.det`, `IsNilpotent` with `nilpotencyClass`,
  `Matrix.blockDiagonal'` for the Jordan blocks, `HasDerivAt` for the decoupled systems. New
  definitions: regularity `∃ λ, det (A + λ B) ≠ 0`; the index of nilpotency as
  `nilpotencyClass N` (`0` for the empty block); the differentiation index (prose or a
  predicate on derivative arrays). Conjuncts: (i) existence of `P`, `Q` invertible, `C`, `N`
  nilpotent with the block forms; (ii) the shift-matrix block structure of `N`; (iii)
  independence of `nilpotencyClass N` from the choice; (iv) the solution formula
  `z = ∑_{i<ν} (-N)^i δ^{(i)}` for `N z' + z = δ` with `δ` of class `C^ν`; (v) the
  differentiation index equals the index of nilpotency. Pitfall: `n = 0` and `B` invertible
  give `q = 0`, the index `0`. (i)–(iv) are statable and provable at the pins ((ii) needs the
  Jordan form of a nilpotent matrix, which Mathlib does not state in matrix form); (v) needs a
  definition of the differentiation index. NASC: `NASC.exists_weierstrassDecomposition`
  (`NASC/StiffAndGeometric.lean`) states (i), `sorry`.

* **15.10. Runge–Kutta and multistep methods for index-1 problems.** Consider
  the **semi-explicit** system $y'=f(y,z)$, $0=g(y,z)$, with
  $\partial g/\partial z$ invertible in a neighbourhood of the exact solution
  (**index 1**) and consistent initial values $g(y_0,z_0)=0$.
  - (Runge–Kutta.) Let the method have invertible $A$, order $p$ and stage
    order $q$, and compute the stages from $Y_i=y_n+h\sum_ja_{ij}
    f(Y_j,Z_j)$, $0=g(Y_i,Z_i)$, with $y_{n+1}=y_n+h\sum_ib_if(Y_i,Z_i)$ and
    $z_{n+1}=(1-b^\top A^{-1}\mathbb 1)z_n+b^\top A^{-1}(Z_1,\dots,Z_s)^\top$.
    Then $y_n-y(t_n)=O(h^p)$ and $z_n-z(t_n)=O(h^r)$ on bounded intervals,
    where $r=p$ if $a_{si}=b_i$ for all $i$ (**stiffly accurate**),
    $r=\min(p,q+1)$ if $-1\le R(\infty)<1$, and $r=\min(p-1,q)$ if
    $R(\infty)=1$; if $|R(\infty)|>1$ the numerical solution diverges.
  - (Multistep.) Let a linear multistep method of order $p$ have $0$ in its
    stability domain and be stable at $\infty$, that is, $\beta_k\ne0$ and
    the roots of $\sigma$ satisfy the root condition, and apply it as
    $\sum_j\alpha_jy_{n+j}=h\sum_j\beta_jf(y_{n+j},z_{n+j})$,
    $0=\sum_j\beta_jg(y_{n+j},z_{n+j})$. If the starting errors are
    $O(h^p)$, then $y_n-y(t_n)=O(h^p)$ and $z_n-z(t_n)=O(h^p)$ for
    $t_n-t_0\le\mathrm{const}$. This applies to the BDF methods with
    $k\le6$.

  *Assessment.* The results are the convergence orders of Runge–Kutta and
  multistep methods applied to semi-explicit index-1 systems, with the
  dependence of the algebraic-component order on $R(\infty)$.

  *Lean target.* Carriers at the pins: `HasFDerivAt` and `ContinuousLinearMap.inverse` or
  `IsUnit` of `fderiv ℝ (g y) z` for the index-1 condition, the implicit function theorem
  (`ImplicitFunctionData`, `HasStrictFDerivAt.implicitFunction`), `Asymptotics.IsBigO`
  uniformly in `n` with `n h ≤ T`. New definitions: the semi-explicit system with `f g` of
  class `C^{p+1}`, the Runge–Kutta method of the synopsis with invertible `A` and the update
  for `z`, `R(∞) = 1 - bᵀ A⁻¹ 𝟙`, stiff accuracy. Conjuncts: (i) `y_n - y(t_n) = O(h^p)`; (ii)
  `z_n - z(t_n) = O(h^r)` with `r` by the three cases; (iii) divergence for `|R(∞)| > 1`; (iv)
  the multistep result, with `β k ≠ 0` and the root condition for `σ`. Pitfall: `A⁻¹` is Mathlib's
  junk inverse unless `IsUnit A.det` is a hypothesis; the stage order is the largest `q` with `C(q)`
  (14.8). Statable at the pins; depends on 14.8, 15.1 and on 14.11 for (iv). NASC: none.

* **15.11. Exponential Euler method.** Let $X$ be a Banach space and let $-A$
  generate an analytic semigroup on $X$; after replacing $A$ by $A+\omega I$
  and $g$ by $g+\omega u$, assume that the fractional powers $A^\gamma$ are
  defined and $\|e^{-tA}\|+t^\gamma\|A^\gamma e^{-tA}\|\le C(\gamma)$ for
  all $\gamma,t\ge0$. Let $V=D(A^\alpha)$ with norm $\|A^\alpha v\|$, where
  $0\le\alpha<1$, and let
  $g:[0,T]\times V\to X$ be locally Lipschitz in a strip along the exact
  solution of $u'+Au=g(t,u)$, $u(0)=u_0$. The **exponential Euler method**
  is
  $$u_{n+1}=e^{-hA}u_n+h\varphi_1(-hA)g(t_n,u_n),\qquad
  \varphi_1(z)=\frac{e^z-1}z.$$
  If $F(t)=g(t,u(t))$ is differentiable and $A^{\beta-1}F'\in
  L^\infty(0,T;V)$ for some $\beta\in(0,1]$, then
  $$\|u_n-u(t_n)\|_V\le Ch\sup_{0\le t\le t_n}\|A^{\beta-1}F'(t)\|_V$$
  for $0\le nh\le T$ and $0<h\le h_0$, with $C$ and $h_0$ depending on $T$
  (and $h_0$ on the strip of local Lipschitz continuity) but not on $n$ or
  $h$; the step restriction keeps the numerical solution in the strip.

  *Assessment.* TauCeti has strongly continuous and contraction semigroups,
  mild solutions and the Duhamel integral. The exponential Euler convergence
  theorem needs analytic semigroups, fractional powers, the quadrature defect
  and the stiffness-uniform bounds in the specified spaces.

  *Lean target.* Carriers at the pins: `TauCeti.Semigroups.StronglyContinuousSemigroup` with
  its generator domain `StronglyContinuousSemigroup.domain`, `IsForcedMildSolution` and
  `StronglyContinuousSemigroup.duhamel`, `ContinuousLinearMap`, `intervalIntegral`. New
  definitions: analytic semigroups (sectorial generators) with the bound
  `‖t^γ A^γ e^{-tA}‖ ≤ C(γ)`, fractional powers `A^α` and the space `V = D(A^α)` with the graph
  norm, `φ₁(-hA)` as `h⁻¹ ∫₀^h e^{-(h-s)A} ds`, which avoids dividing by an operator. Conjuncts:
  (i) for `0 ≤ α < 1`, `0 < β ≤ 1`, `g` locally Lipschitz `V → X` in a strip, `F` differentiable
  with `A^{β-1} F'` bounded in `V`: `‖u_n - u(t_n)‖_V ≤ C h sup ‖A^{β-1}F'‖_V` for `nh ≤ T` and
  `h ≤ h₀`, with `C` quantified before the data bound and `h₀` after it. Pitfall: the constant must
  be quantified before `h` and `n`; the supremum of an unbounded family is a junk `0` in `ℝ`, so
  state boundedness as a hypothesis with an explicit bound `K`. A contraction-semigroup version with
  globally Lipschitz `g` and Lipschitz `F` (rate `M h/(2L)(e^{Lnh} - 1)`) is statable now; the
  parabolic version needs analytic semigroups and fractional powers. NASC:
  `NASC.exponentialEuler_error_le` (`NASC/StiffAndGeometric.lean`) states that contraction-semigroup
  version (with `α = 0`, `β = 1`), `sorry`.

### Geometric integration

* **15.13. Quadratic invariants and symplectic Runge–Kutta methods.** A
  **quadratic invariant** of $y'=f(y)$ is $Q(y)=y^\top Cy$ with $C$
  symmetric and $y^\top Cf(y)=0$ for all $y$.
  - If $b_ia_{ij}+b_ja_{ji}=b_ib_j$ for all $i,j$ (that is, $M=0$ in 15.7),
    then the Runge–Kutta method conserves every quadratic invariant and is
    symplectic. The Gauss methods satisfy this condition.
  - Conversely, an irreducible symplectic Runge–Kutta method satisfies
    $M=0$.
  - For $n\ge3$ no consistent Runge–Kutta method ($\sum_ib_i=1$) conserves
    every polynomial invariant of degree $n$ (the method with $b=0$ is the
    identity map and conserves everything). The obstruction is $\det Y$, a polynomial invariant of
    degree $n$ of $Y'=AY$, $Y\in\mathbb R^{n\times n}$, whenever
    $\mathrm{tr}\,A=0$.

  *Assessment.* TauCeti proves preservation of the symplectic form by exact
  Hamiltonian flows. The gap concerns the discrete Runge–Kutta coefficients,
  quadratic invariants and the induced step map.

  *Lean target.* Carriers at the pins: `LinearMap.BilinForm ℝ E` (or `E →ₗ[ℝ] E →ₗ[ℝ] ℝ`),
  `TauCeti.SymplecticForm` with `TauCeti.SymplecticForm.hamiltonianVectorField` and
  `TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_add`, `HasStrictFDerivAt` with the
  inverse function theorem for the differentiability of the step map, `Matrix.det`. New
  definitions: irreducibility of a tableau (no equivalent tableau with fewer stages), the
  step map of a tableau with the stage branch. Conjuncts: (i) Cooper: `M = 0` and
  `B (f u) u + B u (f u) = 0` give `B y₁ y₁ = B y₀ y₀` for every stage solution; (ii)
  symplecticity of the step map for `M = 0` and `|h| L max_i ∑_j |a_ij| < 1`; (iii) Gauss
  tableaux satisfy `M = 0`; (iv) irreducible symplectic tableaux satisfy `M = 0`; (v) for
  `n ≥ 3` no tableau with `∑ i, b i = 1` preserves `det Y` for every `Y' = A Y` with `tr A = 0`.
  Pitfall: (i) does not need symmetry of `B` if the invariant is written
  `B (f u) u + B u (f u) = 0`; (iv) needs irreducibility, otherwise a tableau with duplicated stages
  is a counterexample. (i)–(iii) are statable and provable at the pins, (iv)–(v) are statable.
  Depends on 15.7 for `M`. NASC: `NASC.RungeKuttaTableau.quadratic_update_eq`
  (`NASC/StiffAndGeometric.lean`) states (i) for symmetric `B` with `B x (f x) = 0`, proved.

* **15.15. Backward error analysis.** For a one-step method
  $y_{n+1}=\Phi_h(y_n)$ applied to $y'=f(y)$, the **modified equation** is
  the formal series $\tilde y'=f(\tilde y)+hf_2(\tilde y)+h^2f_3(\tilde y)
  +\cdots$ whose time-$h$ flow equals $\Phi_h$ as a formal series in $h$;
  for a method of order $p$, $f_2=\dots=f_p=0$. Let $f$ be analytic and
  bounded by $M$ on the complex ball $B_{2R}(y_0)$, and let the Taylor
  coefficients of $\Phi_h(y)=y+hf(y)+h^2d_2(y)+\cdots$ satisfy
  $\|d_j(y)\|\le\mu M(2\kappa M/R)^{j-1}$ on $B_R(y_0)$ for some $\mu\ge1$
  (for a consistent Runge–Kutta method this holds with $\mu=\sum_i|b_i|\ge1$ and
  $\kappa=\max_i\sum_j|a_{ij}|$). Put $\eta=2\max(\kappa,\mu/(2\log2-1))$,
  $h_0=R/(e\eta M)$ and $\gamma=e(2+1.65\eta+\mu)$. If $h\le h_0/4$ and
  $N$ is the largest integer with $hN\le h_0$, then the time-$h$ flow
  $\tilde\varphi_{N,h}$ of the modified equation truncated after the term
  $h^{N-1}f_N$ satisfies
  $$\|\Phi_h(y_0)-\tilde\varphi_{N,h}(y_0)\|\le h\gamma Me^{-h_0/h}.$$

  *Assessment.* Formal series and local flow theory supply ingredients. The
  missing result constructs the modified vector field and turns an optimally
  truncated expansion into a quantitative small-defect estimate.

  *Lean target.* Carriers at the pins: `Metric.closedBall` in `EuclideanSpace ℂ (Fin d)` or
  `Fin d → ℂ`, `DifferentiableOn ℂ` (analyticity), `norm_deriv_le_of_forall_mem_sphere_norm_le` and
  the Cauchy estimates, `IsPicardLindelof` for the flow of the truncated equation, `Nat.floor` for
  `N`. New definitions: the coefficients `f_j` of the modified equation by the recursion of HLW
  (IX.1.4), the truncation `F_N`, its time-`h` flow. Conjuncts: (i) the formal identity, stated as
  `Φ_h(y) - φ_{N,h}(y) = O(h^{N+1})` for each fixed `N` and smooth `f`; (ii) `f_2 = ⋯ = f_p = 0` for
  order `p`; (iii) the bounds (7.5) for Runge–Kutta methods with `μ`, `κ`; (iv) the exponentially
  small estimate for `h ≤ h₀/4` with `N = ⌊h₀/h⌋`, under the hypothesis `1 ≤ μ`. Pitfall: `N` must
  be the largest integer with `hN ≤ h₀`, i.e. `Nat.floor (h₀ / h)`, which needs `h > 0`; the
  constants are real numbers, not asymptotic. (i)–(iii) are statable at the pins; (iv) needs
  complex-analytic flows on balls. Depends on 14.6 or 14.16 for the series. NASC:
  `NASC.modifiedField_firstCorrection_eq` (`NASC/StiffAndGeometric.lean`) states only the
  identification of `f_2` from second-order expansions, proved; (i)–(iv) are not stated.

* **15.16. Long-time energy conservation.** Let $H:D\to\mathbb R$ be analytic
  on an open $D\subset\mathbb R^{2d}$, and apply a symplectic method of order
  $p$ satisfying the analytic bounds of 15.15. If the numerical solution
  stays in a compact set $K\subset D$, then there are $h_0>0$ and a modified
  Hamiltonian $\tilde H=H+h^pH_{p+1}+\dots+h^{N-1}H_N$ with $N=N(h)$ as in
  15.15 such that
  $$\tilde H(y_n)=\tilde H(y_0)+O(e^{-h_0/(2h)}),\qquad
  H(y_n)=H(y_0)+O(h^p)\qquad\text{for }nh\le e^{h_0/(2h)}.$$

  *Assessment.* Exact Hamiltonian conservation and the previous
  modified-equation estimates are ingredients. The selected theorem bounds the
  accumulated energy drift of the numerical trajectory over the stated time
  scale.

  *Lean target.* Carriers at the pins: those of 15.15, `TauCeti.SymplecticForm` and the
  Hamiltonian vector field, `IsCompact`, `AnalyticOnNhd ℝ H D`. New definitions: the modified
  Hamiltonian `H̃` as a finite sum `H + ∑ h^{j-1} H_j` for `j ≤ N(h)`. Conjuncts: (i) existence
  of `H_j` with `f_j = J⁻¹ ∇ H_j` for symplectic methods (the modified equation is
  Hamiltonian); (ii) `|H̃(y_n) - H̃(y_0)| ≤ C n h e^{-h₀/h}`; (iii) `|H(y_n) - H(y_0)| ≤ C h^p`
  for `n h ≤ e^{h₀/(2h)}`, with the constants independent of `n` and `h ≤ h₁`. Pitfall: the
  hypothesis "numerical solution stays in `K`" is a hypothesis on the whole orbit up to `n`;
  the `O`-terms must be explicit constants. (i) is statable at the pins; (ii)–(iii) depend on
  15.15. NASC: `NASC.energy_error_le_of_modifiedEnergy` (`NASC/StiffAndGeometric.lean`) states
  the final triangle-inequality step from (ii) and a bound `|H̃ - H| ≤ C h^p`, proved.

* **15.17. Splitting methods.** Let $y'=f^{[1]}(y)+f^{[2]}(y)$ with flows
  $\varphi^{[1]}_t,\varphi^{[2]}_t$ of the two parts. The **Lie–Trotter
  splitting** $\varphi^{[1]}_h\circ\varphi^{[2]}_h$ has order $1$, and the
  **Strang splitting** $\varphi^{[1]}_{h/2}\circ\varphi^{[2]}_h\circ
  \varphi^{[1]}_{h/2}$ is symmetric and has order $2$. For matrices,
  $$e^{tA/2}e^{tB}e^{tA/2}=\exp\Bigl(t(A+B)+t^3\bigl(-\tfrac1{24}
  [A,[A,B]]+\tfrac1{12}[B,[B,A]]\bigr)+O(t^5)\Bigr),$$
  with $[A,B]=AB-BA$. If both parts are Hamiltonian, the splittings are
  symplectic.

  *Assessment.* TauCeti's Trotter product limit supplies related flow theory.
  The finite-step order, symmetry and cubic matrix commutator expansion are
  separate numerical results.

  *Lean target.* Carriers at the pins: `NormedSpace.exp` on `Matrix (Fin n) (Fin n) ℝ` with the
  scoped norm `Matrix.Norms.L2Operator` (any norm works for `O`), `NormedSpace.exp_add_of_commute`,
  `Asymptotics.IsBigO` at `nhds 0`, `IsPicardLindelof` for the flows of the parts, the
  Hamiltonian flows of TauCeti for symplecticity. New definitions: the Lie–Trotter and Strang
  compositions of two flows, the adjoint of a one-step map. Conjuncts: (i) Lie–Trotter has local
  error `O(h²)`, Strang `O(h³)`, for `C²` and `C³` fields with flows; (ii) Strang is symmetric;
  (iii) the matrix identity with `O(t⁵)`; (iv) compositions of symplectic flows are symplectic.
  Pitfall: (iii) compares with `exp` of a perturbed exponent; a logarithm formulation would
  need `NormedSpace.log`, defined only near `1`. All statable at the pins; (iv) follows from
  the TauCeti flow theorem. NASC: `NASC.strang_exp_sub_corrected_exp_isBigO`
  (`NASC/StiffAndGeometric.lean`) states (iii) in a complete normed real algebra, `sorry`.

## 16. Finite difference methods for differential equations

[Synopsis](SYNOPSIS.md#16-finite-difference-methods-for-differential-equations) · [Coverage inventory](STRUCTURE.md#16-finite-difference-methods-for-differential-equations)

Normed-operator and spectral results supply ingredients for stability. The
selected gaps specify the actual discrete operators and their approximation
behavior.

For a grid
function $v=(v_j)_{j\in\mathbb Z}$ with spacing $\Delta x$ the discrete norms
are $\|v\|_{\Delta,p}=(\Delta x\sum_j|v_j|^p)^{1/p}$ for $p=1,2$ and
$\|v\|_{\Delta,\infty}=\sup_j|v_j|$. The **Courant number** for the
advection equation $u_t+au_x=0$ with constant $a\in\mathbb R$ is
$\nu=a\Delta t/\Delta x$. Inequalities between vectors and matrices are
entrywise.

### Boundary value problems

* **16.2. Eigenvalues of the discrete Laplacian.** The $d\times d$ symmetric
  tridiagonal Toeplitz matrix with diagonal $\alpha$ and off-diagonal
  entries $\beta$ has eigenvalues $\alpha+2\beta\cos\frac{\pi j}{d+1}$ with
  orthogonal eigenvectors $(\sin\frac{\pi j\ell}{d+1})_{\ell=1}^d$,
  $j=1,\dots,d$. Hence for $h=1/(d+1)$ the matrix
  $h^{-2}\,\mathrm{tridiag}(-1,2,-1)$ has eigenvalues
  $4h^{-2}\sin^2(j\pi h/2)$. On the unit square with $h=1/N$ and the
  $(N-1)^2$ interior grid points, the five-point matrix $L_h$ of 16.3 has
  the eigenvalues
  $$\lambda_{jk}=4h^{-2}\Bigl(\sin^2\frac{j\pi h}2+\sin^2\frac{k\pi h}2
  \Bigr),\qquad1\le j,k\le N-1,$$
  with orthonormal eigenvectors $2h\sin(j\pi x)\sin(k\pi y)$ at the grid
  points (orthonormal in the Euclidean inner product). So $L_h$ is
  symmetric positive definite with $\lambda_{\min}=8h^{-2}\sin^2(\pi h/2)$,
  $\lambda_{\max}=8h^{-2}\cos^2(\pi h/2)$, and
  $\kappa_2(L_h)=\cot^2(\pi h/2)$.

  *Assessment.* Mathlib has the finite Hermitian spectral theorem. The
  selected identities identify the explicit sine eigenbasis and extremal
  eigenvalues of the one- and two-dimensional difference operators.

  *Lean target.* Carriers at the pins: `Matrix (Fin n) (Fin n) ℝ`, `Matrix.IsHermitian` with
  `Matrix.IsHermitian.eigenvalues` and Mathlib's `spectral_theorem`, `Matrix.PosDef`, the scoped
  `Matrix.Norms.L2Operator` operator norm, and `Matrix.kronecker` for the two-dimensional matrix
  $L_h=h^{-2}(T\otimes I+I\otimes T)$ on `Fin (N - 1) × Fin (N - 1)`, with $T$ the project's
  `NASC.tridiagonalToeplitz (N - 1) 2 (-1)`. Conjuncts: (i) for $n\ge1$ and each $j$ the sine vector
  is a nonzero eigenvector with eigenvalue $\alpha+2\beta\cos(\pi(j+1)/(n+1))$, with `Fin n` indices
  shifted by one; (ii) the sine vectors are pairwise orthogonal with squared norm $(n+1)/2$; (iii)
  the eigenpairs of $L_h$ with the orthonormal vectors $2h\sin\sin$; (iv) $\lambda_{\min}$,
  $\lambda_{\max}$, and $\|L_h\|\,\|L_h^{-1}\|=\cot^2(\pi h/2)$ for $N\ge2$. Pitfall: for $N=1$ the
  matrix is empty and every norm is $0$; Mathlib's inverse is $0$ for a singular matrix, so (iv)
  must come after positive definiteness. Everything is statable at the pins. NASC:
  `NASC.tridiagonalToeplitz_mulVec_sine` (`NASC/FiniteDifferences.lean`) states (i), `sorry`;
  (ii)–(iv) have no declaration.

* **16.3. Five-point Laplacian and the discrete maximum principle.** Let
  $\Omega=(0,1)^2$, $h=1/N$, let $\Omega_h$ be the interior grid points and
  $\partial\Omega_h$ the grid points on the boundary, and define
  $$(\Delta_hv)_{ij}=\frac{v_{i+1,j}+v_{i-1,j}+v_{i,j+1}+v_{i,j-1}-4v_{ij}}
  {h^2}.$$
  - If $u\in C^4(\bar\Omega)$, then
    $|(\Delta_hu)(x)-\Delta u(x)|\le\frac{h^2}{12}(M_{xxxx}+M_{yyyy})$ at
    every $x\in\Omega_h$, where $M_{xxxx}=\max|\partial_x^4u|$ and
    $M_{yyyy}=\max|\partial_y^4u|$ over $\bar\Omega$.
  - (**Discrete maximum principle.**) If $\Delta_hv\ge0$ on $\Omega_h$, then
    $\max_{\Omega_h}v\le\max_{\partial\Omega_h}v$.
  - The matrix $L_h$ of $-\Delta_h$ on $\Omega_h$ (with zero boundary
    values) is symmetric, irreducibly diagonally dominant, positive definite
    and has nonpositive off-diagonal entries; hence it is a nonsingular
    **M-matrix** (a **Stieltjes matrix**) and $L_h^{-1}>0$.

  *Assessment.* Nonnegative and diagonally dominant matrices are available.
  The missing result proves the stencil truncation error and the discrete
  boundary maximum principle, including the sign and inverse properties of the
  interior matrix.

  *Lean target.* Carriers: grid functions `ℕ → ℕ → ℝ` with the project's
  `NASC.fivePointLaplacian h v i j` and `NASC.GridBoundaryNonpos n v`; Mathlib
  `taylor_mean_remainder_lagrange` for the truncation error; for the matrix part
  `Matrix (Fin (N - 1) × Fin (N - 1)) ℝ`, `Matrix.PosDef` and Gershgorin's
  `det_ne_zero_of_sum_row_lt_diag`, which needs strict dominance and so does not apply directly. New
  definition: a predicate `IsNonsingularMMatrix A` on a real square matrix, nonpositive off-diagonal
  entries, invertible, and entrywise nonnegative inverse. Conjuncts: (i) for $u$ with
  `ContDiffOn ℝ 4` on the closed square and bounds $M_{xxxx}$, $M_{yyyy}$ given as hypotheses (not
  as `sSup`, which is junk for an unbounded set), the stencil estimate at interior points; (ii) the
  maximum principle, in the form "nonpositive boundary values and $\Delta_hv\ge0$ give $v\le0$",
  from which the max form follows by subtracting the boundary maximum; (iii) $L_h$ is symmetric
  positive definite and a nonsingular M-matrix, with entrywise positive inverse. Pitfall: `ℕ`
  subtraction makes `v (i - 1) j` equal `v i j` at $i=0$, so every interior statement needs $0<i<N$
  explicitly. Statable at the pins. NASC: `NASC.fivePoint_nonpos_of_boundary_nonpos`
  (`NASC/FiniteDifferences.lean`) states (ii) and is proved; (i) and (iii) have no declaration.

* **16.4. Convergence of the five-point scheme.** Let $u\in C^4(\bar\Omega)$
  solve $-\Delta u=f$ in $\Omega=(0,1)^2$, $u=g$ on $\partial\Omega$, and let
  $U$ solve $-\Delta_hU=f$ on $\Omega_h$, $U=g$ on $\partial\Omega_h$. Then
  $$\max_{\Omega_h}|u-U|\le\frac{h^2}{96}(M_{xxxx}+M_{yyyy}).$$
  In the scaled Euclidean norm
  $\|e\|_h=h\bigl(\sum_{\Omega_h}|e_{ij}|^2\bigr)^{1/2}$ the error is also
  $O(h^2)$.

  *Assessment.* The previous stencil estimate and discrete maximum principle
  are the main ingredients. The gap is the explicit maximum-norm bound on the
  grid with exact boundary values.

  *Argument.* By 16.3 the absolute interior defect is bounded by
  $B=h^2(M_{xxxx}+M_{yyyy})/12$. Compare both signs of the error with $B\phi$
  for $\phi(x,y)=\tfrac14(x(1-x)+y(1-y))$. This barrier has $-\Delta_h\phi=1$
  and $0\le\phi\le1/8$. Apply the discrete maximum principle of 16.3. The
  scaled Euclidean estimate follows by bounding the scaled number of grid
  points.

  *Lean target.* Carriers as in 16.3. Conjuncts: (i) if $u$ is `ContDiffOn ℝ 4` on the closed square
  with fourth-derivative bounds $M_{xxxx},M_{yyyy}$, $-\Delta u=f$ inside, and $U$ is a grid
  function with $-\Delta_hU=f$ at the interior points and $U=u$ on the boundary points, then
  $|u-U|\le h^2(M_{xxxx}+M_{yyyy})/96$ at every grid point; (ii) the scaled Euclidean error is at
  most the same bound, since $h^2(N-1)^2\le1$. The existence of $U$ is the invertibility in
  16.3(iii) and is a separate conjunct, not a hypothesis hidden in a junk inverse. Depends on
  16.3(i) and (ii). Statable at the pins. NASC: `NASC.fivePoint_error_le_of_defect`
  (`NASC/FiniteDifferences.lean`) is the comparison step, from an interior defect bound $h^2M/12$ to
  the error bound $h^2M/96$ with $M=M_{xxxx}+M_{yyyy}$, proved; the composition with 16.3(i) and
  part (ii) have no declaration.

### Stability and convergence for evolution problems

* **16.5. Lax–Richtmyer theory.** Let $V$ be a Banach space and $L$ a linear
  operator, and consider $u'(t)=Lu(t)$, $0\le t\le T$, $u(0)=u_0$. The
  problem is **well posed** if there is a dense subspace $V_0\subset V$ such
  that for every $u_0\in V_0$ there is a unique solution, and
  $\sup_{0\le t\le T}\|u(t)-\tilde u(t)\|\le c_0\|u_0-\tilde u_0\|$ for
  solutions with data $u_0,\tilde u_0\in V_0$. The solution operators
  $S(t)$ then extend to bounded operators on $V$. A **difference method** is
  a family of bounded linear operators $C(\Delta t)$ on $V$,
  $0<\Delta t\le\Delta_0$, with $\sup_{0<\Delta t\le\Delta_0}
  \|C(\Delta t)\|<\infty$ and with approximations $C(\Delta t)^mu_0$ at
  $t=m\Delta t$. It is
  - **consistent** if there is a dense subspace $V_c$ such that for every
    $u_0\in V_c$ the solution satisfies
    $\frac1{\Delta t}\|C(\Delta t)u(t)-u(t+\Delta t)\|\to0$ uniformly in
    $0\le t\le T-\Delta t$;
  - **stable** if there is $M_0$ with $\|C(\Delta t)^m\|\le M_0$ whenever
    $0<\Delta t\le\Delta_0$ and $m\Delta t\le T$;
  - **convergent** if $\|(C(\Delta t_i)^{m_i}-S(t))u_0\|\to0$ for every
    $t\in[0,T]$, every $u_0\in V$, and all sequences $\Delta t_i\to0$ and
    $m_i\in\mathbb N_0$ with $m_i\Delta t_i\le T$ and $m_i\Delta t_i\to t$.

  **Lax equivalence theorem:** for a well-posed problem and a consistent
  difference method, stability is equivalent to convergence.

  *Assessment.* Uniform boundedness and Banach-space limits are available. The
  gap relates the precise finite-time stability and consistency hypotheses for
  the operator family to strong convergence.

  *Lean target.* Carriers: a real Banach space $E$, `E →L[ℝ] E` with its operator norm, `Dense`,
  Mathlib `banach_steinhaus` for the converse, and for strongly continuous solution operators
  TauCeti's `TauCeti.Semigroups.StronglyContinuousSemigroup`. No definition beyond the three
  predicates is needed; they are best inlined as in the project's statement. Conjuncts: (i)
  consistency on a dense set and stability give convergence; (ii) convergence gives stability.
  Hypotheses: $S(0)=1$, $\sup_{t\le T}\|S(t)\|<\infty$, $\sup_{\Delta t}\|C(\Delta t)\|<\infty$,
  $T>0$. Pitfall: the synopsis defines convergence along sequences with $m_i\Delta t_i\to t$, which
  is equivalent to the uniform comparison of $C(\Delta t)^m$ with $S(m\Delta t)$ only when $S$ is
  strongly continuous; the uniform form needs no continuity and is the one to state. Statable at the
  pins. The theorem for Tau Ceti semigroups is in the open roadmap PR #3214
  (LaxEquivalenceAndFiniteDifferenceSchemes, Layer 1, sections 1.2–1.5). NASC:
  `NASC.stable_iff_convergent_of_consistent` (`NASC/FiniteDifferences.lean`), uniform form, `sorry`.

* **16.6. Von Neumann analysis.** Consider the two-level scheme
  $\sum_{k=-\gamma}^{\delta}b_k(\mu)u^{n+1}_{\ell+k}=
  \sum_{k=-\alpha}^{\beta}c_k(\mu)u^n_{\ell+k}$, $\ell\in\mathbb Z$, for a
  scalar equation on $\mathbb R$ with constant coefficients, with a fixed
  ratio $\mu$ of the mesh sizes, and its **amplification factor**
  $$\tilde a(z,\mu)=\frac{\sum_kc_k(\mu)z^k}{\sum_kb_k(\mu)z^k},\qquad
  |z|=1,$$
  assuming the denominator does not vanish on $|z|=1$. The scheme is stable
  in $\|\cdot\|_{\Delta,2}$ (the powers of the one-step operator on
  $\ell^2(\mathbb Z)$ are uniformly bounded) if and only if
  $|\tilde a(e^{i\theta},\mu)|\le1$ for all $\theta\in[0,2\pi]$. If the
  one-step operator is a normal matrix $B_{\Delta x}$ (for example a
  circulant, from periodic boundary conditions), then
  $\|B_{\Delta x}^n\|_2=\rho(B_{\Delta x})^n$, so the **von Neumann
  condition** $\rho(B_{\Delta x})\le1+K\Delta t$, with $K$ independent of
  $\Delta x$ and $\Delta t$, is sufficient for stability on bounded time
  intervals. Likewise, for a semi-discretization $w'=P_{\Delta x}w$ with
  $P_{\Delta x}$ normal and $\mathrm{Re}\,\lambda\le\eta$ for all
  $\lambda\in\Lambda(P_{\Delta x})$, with $\eta$ independent of $\Delta x$,
  one has $\|e^{tP_{\Delta x}}\|_2\le e^{\eta t}$.

  *Assessment.* Fourier transformation and the spectral theorem are available.
  The selected result uses the transformed stencil on the infinite grid and
  the uniform-in-mesh power bound on normal finite-grid matrices.

  *Lean target.* Carriers: Mathlib `ZMod.dft`, `Matrix.circulant`, the scoped
  `Matrix.Norms.L2Operator` norm, `spectralRadius`, `NormedSpace.exp`; for the infinite grid
  `lp (fun _ : ℤ => ℂ) 2` and the Fourier Hilbert basis `fourierBasis` on `AddCircle`. New
  definitions: a stencil as a finitely supported coefficient function `ℤ →₀ ℂ`, its symbol
  $\rho_c(\theta)=\sum_kc_ke^{ik\theta}$, and its convolution operator on `lp` and circulant matrix
  on `ZMod N`. Conjuncts: (i) on $\ell^2(\mathbb Z)$, if $\rho_b$ has no zero on the circle, the
  powers of $B^{-1}C$ are uniformly bounded if and only if $|\rho_c|\le|\rho_b|$ everywhere; (ii)
  for a normal matrix $\|B^n\|_2=\rho(B)^n$, so $\rho(B_{\Delta x})\le1+K\Delta t$ gives $\|B^n\|\le
  e^{KT}$ for $n\Delta t\le T$; (iii) for normal $P$ with spectral abscissa at most $\eta$,
  $\|\exp(tP)\|_2\le e^{\eta t}$. Pitfall: without the nonvanishing hypothesis Mathlib's inverse of
  the singular circulant is $0$ and the criterion fails (checked in PR #3214, section 2.3). Statable
  at the pins. The periodic criterion over all grid sizes is in the open roadmap PR #3214, sections
  2.2–2.3; (i) on $\ell^2(\mathbb Z)$, (ii) and (iii) are not. NASC:
  `NASC.vonNeumann_power_bounded_iff` (`NASC/FiniteDifferences.lean`) states the fixed-$N$ periodic
  criterion, `sorry`.

* **16.7. The CFL condition.** The **numerical domain of dependence** of a
  grid value is the set of initial grid points on which it depends. A
  difference method can be convergent only if, in the limit
  $\Delta t,\Delta x\to0$, its numerical domain of dependence contains the
  domain of dependence of the differential equation. For an explicit
  three-point scheme for $u_t+au_x=0$ with fixed $\Delta t/\Delta x$ this
  is the **CFL condition** $|\nu|\le1$. The condition is necessary but not
  sufficient for stability.

  *Assessment.* The stencil and its repeated domain of dependence must be
  related to limits of PDE solutions. The Courant condition comes from this
  propagation comparison.

  *Lean target.* Carriers: schemes as maps `ℕ → (ℤ → ℝ) → (ℤ → ℝ)` (level $n$ uses $\Delta
  t=T/(n+1)$ and $\Delta x=\Delta t/\mu$), `ContDiff ℝ ∞`, `Filter.Tendsto`. New definition: a
  scheme is local with radius $r$ if a new value at $i$ depends only on the old values at $|j-i|\le
  r$; no linearity is needed. Conjuncts: (i) if a local scheme converges at one point for all smooth
  data to the exact solution $f(x-at)$, then $|a\mu|\le r$; for three-point schemes this is
  $|\nu|\le1$; (ii) the condition is not sufficient: the forward Euler centred scheme of 16.8
  satisfies it and is unstable. The proof of (i) takes data that vanish on the numerical domain of
  dependence and equal $1$ at $-aT$. Statable at the pins. NASC:
  `NASC.cfl_of_threePoint_convergence` (`NASC/FiniteDifferences.lean`) states (i) for $r=1$,
  `sorry`; (ii) depends on 16.8 and has no declaration.

* **16.9. The θ-method for the heat equation.** Let $A$ be the matrix
  $dh^{-2}\,\mathrm{tridiag}(1,-2,1)$ of the central semi-discretization
  of $u_t=du_{xx}$ ($d>0$) on $(0,1)$ with homogeneous Dirichlet conditions,
  and $w_{n+1}=w_n+\tau A\bigl((1-\theta)w_n+\theta w_{n+1}\bigr)$,
  $0\le\theta\le1$, so $w_{n+1}=R(\tau A)w_n$ with
  $R(z)=(1+(1-\theta)z)/(1-\theta z)$. If $\theta\ge\frac12$, then
  $\|R(\tau A)^n\|_2\le1$ for all $\tau>0$ and $n$. If $0\le\theta<\frac12$,
  then $\|R(\tau A)^n\|_2\le1$ for all $n$ provided
  $$\frac{d\tau}{h^2}\le\frac1{2-4\theta}.$$
  For $\theta=0$ (explicit Euler) this is $d\tau/h^2\le\frac12$.

  *Assessment.* Normal-matrix spectral calculus is available. The missing step
  is the exact contractivity range for the rational time-stepping function on
  the discrete heat spectrum.

  *Lean target.* Carriers: the project's `NASC.tridiagonalToeplitz n (-2) 1`, the scoped
  `Matrix.Norms.L2Operator` norm, `Matrix.IsHermitian` and the spectral theorem. Conjuncts: (i) for
  $\theta\in[\frac12,1]$, $d,\tau,h>0$, $\|R(\tau A)^n\|_2\le1$; (ii) for $\theta\in[0,\frac12)$ and
  $d\tau/h^2\le1/(2-4\theta)$, the same; the step matrix is $(I-\theta\tau A)^{-1}(I+(1-\theta)\tau
  A)$. Only the spectral bounds $-4\le\lambda\le0$ of $\mathrm{tridiag}(1,-2,1)$ are used, so $h$
  need not equal $1/(n+1)$. Pitfalls: invertibility of $I-\theta\tau A$ must be proved (negative
  semidefinite $A$), not assumed through Mathlib's junk inverse; at $\theta=\frac12$ the expression
  $1/(2-4\theta)$ is junk $0$ in Lean, so the two cases stay separate. Depends on 16.2. Statable at
  the pins. The periodic analogue is in the open roadmap PR #3214, section 2.4. NASC:
  `NASC.norm_heatThetaMatrix_pow_le_one` (`NASC/FiniteDifferences.lean`), `sorry`.

### Stability tools for the method of lines

* **16.10. Kreiss matrix theorem.** Let $\|\cdot\|$ be a vector norm on
  $\mathbb C^N$ and the matrix norm it induces. For
  $A\in\mathbb C^{N\times N}$ let the **Kreiss constant** be
  $\mathcal K(A)=\sup_{|z|>1}(|z|-1)\|(zI-A)^{-1}\|$. Then
  $$\mathcal K(A)\le\sup_{k\ge0}\|A^k\|\le eN\mathcal K(A).$$
  So a family of $N\times N$ matrices with fixed $N$ is uniformly power
  bounded if and only if its Kreiss constants are uniformly bounded.

  *Assessment.* TauCeti has semigroup resolvent bounds. The selected
  finite-dimensional Kreiss result uses the resolvent outside the unit disk
  and gives the stated dimension-dependent power bound.

  *Lean target.* Carriers: `Matrix (Fin N) (Fin N) ℂ` with the scoped `Matrix.Norms.L2Operator`
  norm, `spectrum ℂ`, `ℝ≥0∞`; for a general vector norm, a finite-dimensional complex normed space
  $E$ with `T : E →L[ℂ] E` and `Module.finrank ℂ E = N`. New definition: the Kreiss constant as a
  supremum in `ℝ≥0∞` over $|z|>1$, equal to $\top$ when $z$ is in the spectrum, since Mathlib's
  inverse of a singular matrix is $0$ and would otherwise give a finite junk value. Conjuncts: (i)
  $\mathcal K(A)\le\sup_k\|A^k\|$; (ii) $\sup_k\|A^k\|\le eN\mathcal K(A)$, both in `ℝ≥0∞` with
  $N\ge1$; (iii) the family statement for fixed $N$. Statable at the pins. The Ritt and Kreiss
  resolvent conditions are distinguished, but the matrix theorem is not stated, in the
  BanachAlgebras roadmap on main, section 2.2. NASC: `NASC.kreissConstant` and
  `NASC.kreissConstant_le_iSup_pow_and_le` (`NASC/FiniteDifferences.lean`), $\ell^2$ norm only,
  `sorry`.

* **16.11. Logarithmic norm.** For a norm on $\mathbb C^m$ and
  $A\in\mathbb C^{m\times m}$ the **logarithmic norm** is
  $\mu(A)=\lim_{\tau\downarrow0}(\|I+\tau A\|-1)/\tau$; the limit exists and
  $-\|A\|\le\mu(A)\le\|A\|$. For $\omega\in\mathbb R$:
  - $\mu(A)\le\omega$ if and only if $\|e^{tA}\|\le e^{t\omega}$ for all
    $t\ge0$;
  - $\mu(A)\le\omega$ if and only if $\|(I-\tau A)^{-1}\|\le1/(1-\tau\omega)$
    for all $\tau>0$ with $\tau\omega<1$;
  - $\mu_2(A)=\max\{\lambda:\lambda\in\Lambda(\frac12(A+A^*))\}
    =\max_{v\ne0}\mathrm{Re}\,\langle Av,v\rangle/\langle v,v\rangle$,
    $\mu_1(A)=\max_j\bigl(\mathrm{Re}\,a_{jj}+\sum_{i\ne j}|a_{ij}|\bigr)$
    and $\mu_\infty(A)=\max_i\bigl(\mathrm{Re}\,a_{ii}+\sum_{j\ne i}|a_{ij}|
    \bigr)$.

  *Assessment.* Mathlib has the matrix exponential and operator norms, and
  TauCeti the Lumer–Phillips characterization of contraction semigroups on
  real Banach spaces. The logarithmic norm, the existence of its one-sided
  limit and its exponential, resolvent and entrywise characterizations are
  missing.

  *Lean target.* Carriers: `Matrix (Fin m) (Fin m) ℂ` with a chosen operator norm (the scoped
  `Matrix.Norms.L2Operator`, `Matrix.linftyOpNormedAddCommGroup` or an arbitrary norm on `Fin m → ℂ`
  through `E →L[ℂ] E`), `NormedSpace.exp`, `Matrix.IsHermitian.eigenvalues`, `Filter.Tendsto` along
  `𝓝[>] 0`. New definition: the logarithmic norm $\mu(A)$ as the limit of the difference quotient,
  together with the theorem that the quotient is monotone in $\tau$, so the limit exists and equals
  the infimum over $\tau>0$ (this avoids the junk value of `limUnder`). Conjuncts: (i) existence and
  $-\|A\|\le\mu(A)\le\|A\|$; (ii) $\mu(A)\le\omega$ if and only if $\|\exp(tA)\|\le e^{t\omega}$ for
  all $t\ge0$; (iii) the resolvent characterization for $\tau\omega<1$; (iv) the three explicit
  formulas, each for its own norm, with $\mu_2$ the largest eigenvalue of the Hermitian part.
  Pitfall: the formulas for $\mu_1$ and $\mu_\infty$ hold for the induced $\ell^1$ and $\ell^\infty$
  operator norms only, so each needs its local instance. Statable at the pins. TauCeti's
  `TauCeti.Semigroups.exists_contractionSemigroup_generator_eq_iff` is the generator form of (ii) at
  $\omega=0$ on real Banach spaces, not this matrix statement. NASC: no declaration.

* **16.14. Strong stability preserving time stepping.** Let $F$ satisfy
  $v+\tau F(t,v)\ge0$ for all $t\ge0$, $v\ge0$ and $0<\alpha\tau\le1$ (so
  forward Euler is positive for $\tau\le1/\alpha$), and for implicit stages
  also that $u=v+\tau F(t,u)$ has, for all $v\ge0$, $t\ge0$ and $\tau>0$, a
  unique solution depending continuously on $\tau$ and $v$. A diagonally
  implicit Runge–Kutta method written in the **Shu–Osher form**
  $$v_0=w_n,\quad v_i=\sum_{j=0}^{i-1}\bigl(p_{ij}v_j+q_{ij}\tau
  F(t_n+\tilde c_j\tau,v_j)\bigr)+q_i\tau F(t_n+\tilde c_i\tau,v_i),\quad
  w_{n+1}=v_s,$$
  with $\sum_jp_{ij}=1$ and all $p_{ij},q_{ij},q_i\ge0$, is positive under
  the step size restriction
  $$\alpha\tau\le\min_{0\le j<i\le s}\frac{p_{ij}}{q_{ij}}
  \qquad(p_{ij}/0=+\infty).$$
  For explicit methods ($q_i=0$) the condition on implicit solvability is not
  needed. The same convex-combination argument shows that if forward Euler
  is total variation diminishing for a spatial discretization under
  $\tau\le\tau_0$, then the two-stage method $w^*=w_n+\tau F(w_n)$,
  $w^{**}=w^*+\tau F(w^*)$, $w_{n+1}=\frac12(w_n+w^{**})$ is total variation
  diminishing under the same restriction.

  *Assessment.* Convexity and positivity lemmas are available. The selected
  theorem connects forward-Euler stability to stage-by-stage stability for the
  given Shu–Osher coefficients.

  *Lean target.* Carriers: vectors `Fin n → ℝ` with the Pi order, `Finset.sum` over earlier stages,
  `Set.Icc`. No definition is needed; the Shu–Osher coefficients are arrays
  `Fin (s + 1) → Fin (s + 1) → ℝ`. Conjuncts: (i) explicit methods: if forward Euler is positive for
  steps in $[0,1/\alpha]$, $\sum_{j<i}p_{ij}=1$, $p_{ij},q_{ij}\ge0$ and $\alpha\tau q_{ij}\le
  p_{ij}$, then every stage is nonnegative; (ii) diagonally implicit methods under the solvability
  hypothesis, as an existence-and-positivity statement for the implicit stages; (iii) the two-stage
  TVD statement for a seminorm or convex functional in place of positivity. Pitfall: the Pi order
  makes `0 ≤ v` entrywise, as intended, but `0 < v` would mean "nonnegative and somewhere positive",
  so strict statements must be entrywise. Statable at the pins. NASC: `NASC.shuOsher_nonneg`
  (`NASC/FiniteDifferences.lean`) states (i) with the stages given explicitly and without the
  row-sum condition $\sum_{j<i}p_{ij}=1$, proved; (ii) and (iii) have no declaration.

### Monotone schemes for viscosity solutions

* **16.15. Barles–Souganidis convergence theorem.** Let $\Omega$ be a bounded
  open subset of $\mathbb R^d$ and consider a continuous, degenerate elliptic
  equation $F(D^2u,Du,u,x)=0$ on $\bar\Omega$, with any boundary conditions
  incorporated into the viscosity problem. Assume comparison on $\bar\Omega$
  between bounded upper semicontinuous viscosity subsolutions and bounded
  lower semicontinuous viscosity supersolutions. Let
  $S(h,x,r,w)$ be a scheme defined for $h>0$, $x\in\bar\Omega$,
  $r\in\mathbb R$ and bounded functions $w$ on $\bar\Omega$. Suppose that:
  - $S(h,x,r,w)\le S(h,x,r,v)$ whenever $w\ge v$ pointwise (**monotonicity**);
  - for each sufficiently small $h>0$ there is a solution $u_h$ of
    $S(h,x,u_h(x),u_h)=0$ on $\bar\Omega$, with $\|u_h\|_\infty$ bounded
    independently of $h$ (**stability**);
  - for every smooth test function $\phi$ and each $x\in\bar\Omega$,
    $$\lim_{\substack{h\downarrow0,\ y\to x\\ \xi\to0}}
    \frac{S(h,y,\phi(y)+\xi,\phi+\xi)}h
    =F(D^2\phi(x),D\phi(x),\phi(x),x)\qquad(y\in\bar\Omega)$$
    (**consistency**).

  Then $u_h$ converges locally uniformly to the unique continuous viscosity
  solution. The theorem also has a form with upper and lower consistency
  limits using the corresponding semicontinuous envelopes of $F$.

  *Assessment.* TauCeti has viscosity notions for a continuous Monge–Ampère
  equation. The missing result needs a monotone scheme, consistency at moving
  test points, and a comparison argument for upper and lower limits.

  *Lean target.* Carriers: `UpperSemicontinuousOn`, `LowerSemicontinuousOn`, `IsLocalMaxOn`,
  `TendstoUniformlyOn`, `ContDiff ℝ ∞` test functions on a finite-dimensional inner product space,
  and the project's `NASC.IsDegenerateElliptic`, `NASC.IsViscositySubsolution` and
  `NASC.IsViscositySupersolution` (`NASC/ViscositySolutions.lean`), which take the operator as
  `F x r p X` (point, value, gradient, Hessian), so that it is local by construction. TauCeti's
  viscosity notions at the pin are for the Monge–Ampère equation only. Conjuncts: (i) under
  monotonicity, stability and consistency, the half-relaxed limits are a viscosity sub- and
  supersolution; (ii) with comparison they coincide and the convergence is uniform on $\bar\Omega$;
  (iii) the form with semicontinuous envelopes. Hypotheses: $\bar\Omega$ compact, comparison for
  bounded semicontinuous sub- and supersolutions, $u_h$ bounded uniformly, the consistency limit
  over $h\downarrow0$, $y\to x$ in $\bar\Omega$ and $\xi\to0$. Pitfall: the division by $h$ in the
  consistency limit fixes the scaling of $S$; a scheme scaled differently must be rescaled before
  the theorem applies. Statable at the pins; boundary conditions in the viscosity sense need no
  further infrastructure because they are part of $F$ on $\bar\Omega$. The open roadmap PR #2801
  (HamiltonJacobiAndConservationLaws, Layer 4) owns first-order viscosity solutions, not this scheme
  theorem. NASC: `NASC.exists_uniformLimit_of_monotoneScheme` (`NASC/ViscositySolutions.lean`)
  states (i)–(ii) for continuous degenerate elliptic `F`, `sorry`.

## 17. Hyperbolic conservation laws and finite volume methods

[Synopsis](SYNOPSIS.md#17-hyperbolic-conservation-laws-and-finite-volume-methods) · [Coverage inventory](STRUCTURE.md#17-hyperbolic-conservation-laws-and-finite-volume-methods)

The selected statements start from weak and entropy formulations, then concern
conservative approximation and wave interactions. Distribution and
bounded-variation results provide analytic ingredients.

A **scalar conservation law** is
$$\partial_t u+\nabla\cdot f(u)=0\quad\text{in }\mathbb R^d\times(0,\infty),
\qquad u(\cdot,0)=u_0,$$
with flux $f\colon\mathbb R\to\mathbb R^d$ locally Lipschitz and
$u_0\in L^\infty(\mathbb R^d)$; schemes are stated for $d=1$. A **system** is
$\partial_t u+\partial_x f(u)=0$ with $u(x,t)\in\mathbb R^m$ and $f$ smooth on an
open set of states. For a function of one variable, $\mathrm{TV}$ is its total
variation. Jumps are $[g]=g(u_R)-g(u_L)$ for left state $u_L$ and right state
$u_R$. A scheme uses a uniform grid with cells of width $\Delta x$, time step
$\Delta t=\lambda\Delta x$ with $\lambda>0$ fixed, and cell values $v^n_j$.
Linear finite difference theory, including the Lax equivalence theorem and
von Neumann analysis, is in section 16.

### Scalar conservation laws

* **17.1. Weak solutions and the Rankine–Hugoniot condition.** A **weak
  solution** is a $u\in L^\infty(\mathbb R^d\times(0,\infty))$ such that
  $$\int_0^\infty\!\!\int_{\mathbb R^d}\bigl(u\,\partial_t\varphi
  +f(u)\cdot\nabla\varphi\bigr)\,dx\,dt+\int_{\mathbb R^d}u_0\,\varphi(\cdot,0)
  \,dx=0$$
  for every $\varphi\in C^1_c(\mathbb R^d\times[0,\infty))$. In one space
  dimension, a function equal to the constants $u_L$ for $x<st$ and $u_R$ for
  $x>st$ is a weak solution if and only if the **Rankine–Hugoniot condition**
  $$f(u_R)-f(u_L)=s\,(u_R-u_L)$$
  holds; the same holds for systems, with vector-valued states. Weak
  solutions are not unique: for Burgers' equation, $f(u)=u^2/2$, with $u_0=0$
  on $x<0$ and $u_0=1$ on $x>0$, both the rarefaction wave ($u=0$ for $x<0$,
  $u=x/t$ for $0\le x\le t$, $u=1$ for $x>t$) and the jump with speed
  $s=1/2$ are weak solutions.

  *Assessment.* Distributional calculus is available. The gap connects the
  space-time weak formulation for a piecewise smooth solution to the jump
  condition on a moving interface.

  *Lean target.* Carriers: the project's `NASC.IsConservationTest` and
  `NASC.IsWeakConservationLaw f u₀ u` (space-time tests on `ℝ × ℝ` of class $C^1$ with compact
  support, Bochner integrals over $t>0$, values in a Banach space $E$ so that systems are included);
  Mathlib `HasCompactSupport`, `integral_prod`, and `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
  for the converse direction. For $d\ge2$ the space variable is `EuclideanSpace ℝ (Fin d)` and the
  flux takes values in `Fin d → E`. Conjuncts: (i) a single jump with speed $s$ is a weak solution
  if and only if $f(u_R)-f(u_L)=s(u_R-u_L)$; (ii) for Burgers' equation the rarefaction and the jump
  of speed $\frac12$ are both weak solutions. Pitfall: a Bochner integral of a non-integrable
  function is $0$; `NASC.IsWeakConservationLaw` therefore requires local integrability of $u$ and
  $f\circ u$ on $[0,\infty)\times\mathbb R$ and of $u_0$, and the candidates of (ii) must be
  shown to have it. Statable at the pins. The open roadmap PR
  #2801 (HamiltonJacobiAndConservationLaws, section 5.1) owns the scalar case with $C^1$ curves and
  these Burgers checks. NASC: `NASC.isWeakConservationLaw_singleJump_iff`
  (`NASC/ConservationLaws.lean`) states (i), `sorry`.

* **17.3. Kružkov's theorem.** Let $f$ be Lipschitz and
  $u_0\in L^\infty(\mathbb R^d)$. There is exactly one entropy solution
  $u\in L^\infty(\mathbb R^d\times(0,\infty))$, and it satisfies:
  - the **maximum principle**
    $\mathop{\mathrm{ess\,inf}}u_0\le u\le\mathop{\mathrm{ess\,sup}}u_0$;
  - **order preservation**: if $u_0\ge v_0$ a.e., then $u\ge v$ a.e. for the
    corresponding entropy solutions;
  - **$L^1$ contraction**: if $u_0-v_0\in L^1$, then
    $\|u(t)-v(t)\|_{L^1}\le\|u_0-v_0\|_{L^1}$ for all $t>0$;
  - for $d=1$ and $u_0\in L^1\cap BV$, **TV non-increase**
    $\mathrm{TV}(u(t))\le\mathrm{TV}(u_0)$; if moreover $f$ is piecewise
    $C^2$, the time continuity
    $\|u(t)-u(s)\|_{L^1}\le\|f\|_{\mathrm{Lip}}\,\mathrm{TV}(u_0)\,|t-s|$.

  For $d=1$, if $u$ and $v$ are the entropy solutions with Lipschitz,
  piecewise $C^2$ fluxes $f$ and $g$ and data $u_0,v_0\in L^1\cap BV$, then
  $$\|u(t)-v(t)\|_{L^1}\le\|u_0-v_0\|_{L^1}
  +t\,\min\{\mathrm{TV}(u_0),\mathrm{TV}(v_0)\}\,\|f-g\|_{\mathrm{Lip}}.$$

  *Assessment.* TauCeti develops bounded variation and distributional
  approximation. The existence, uniqueness, contraction and initial-data
  dependence of the scalar entropy solution remain gaps.

  *Lean target.* Carriers: the project's `NASC.IsScalarEntropySolution f u₀ u` ($d=1$: bounded
  jointly measurable $u$, initial values a.e., continuity of $t\mapsto\int_{-R}^R|u(t)-u(s)|$, the
  weak law and the Kružkov inequalities for nonnegative tests); Mathlib `LipschitzWith`,
  `MeasureTheory.essSup` and `MeasureTheory.essInf`, `eVariationOn`, `∫⁻`. Conjuncts: (i) existence
  and uniqueness for `LipschitzWith K f` and bounded measurable $u_0$; (ii) the maximum principle
  with `essInf` and `essSup` of $u_0$; (iii) order preservation; (iv) the $L^1$ contraction as an
  inequality of lower Lebesgue integrals, which needs no integrability hypothesis; (v) for $u_0\in
  L^1\cap BV$, the total variation bound; (vi) for $f$ piecewise $C^2$, the time continuity; (vii)
  the flux-stability estimate. Pitfalls: `essSup` on `ℝ` is a junk value for unbounded data, so
  boundedness of $u_0$ stays a hypothesis; `eVariationOn` sees a representative, so (v) is stated
  for the right-continuous representative of $u(t)$ or with the infimum over representatives.
  Statable at the pins for $d=1$; $d\ge2$ needs only the space variable of 17.1. The open roadmap PR
  #2801, Layer 6 (sections 6.1–6.4), owns (i)–(iv) in every dimension for locally Lipschitz flux;
  (v)–(vii) are not there. NASC: `NASC.exists_scalarEntropySolution_and_contraction`
  (`NASC/ConservationLaws.lean`) states existence and (iv), hence uniqueness, for locally
  Lipschitz $f$, `sorry`.

* **17.4. The scalar Riemann problem.** Let $d=1$ and let $u_0$ equal $u_L$
  on $x<0$ and $u_R$ on $x>0$. If $f\in C^2$ with $f''>0$, the entropy
  solution is self-similar, $u=w(x/t)$:
  - if $u_L>u_R$, it is the **shock** with speed
    $s=(f(u_L)-f(u_R))/(u_L-u_R)$;
  - if $u_L<u_R$, it is the **rarefaction wave**
    $w(\xi)=(f')^{-1}(\xi)$ for $f'(u_L)\le\xi\le f'(u_R)$, with $w=u_L$
    to the left and $w=u_R$ to the right of that fan.

  *Assessment.* The strict-convexity part uses the characteristic speed and
  its inverse along a rarefaction, together with the Rankine–Hugoniot speed
  and entropy condition for a shock.

  *Scope.* The selected Riemann solver is for strictly convex flux, with the
  shock speed and rarefaction profile.

  *Lean target.* Carriers: `NASC.IsScalarEntropySolution`, `ContDiff ℝ 2`, `StrictMono (deriv f)`
  for strict convexity, `Function.invFun (deriv f)` for the fan. Conjuncts: (i) for $u_L>u_R$ the
  jump at the Rankine–Hugoniot speed is the entropy solution; (ii) for $u_L<u_R$ the rarefaction
  $w(\xi)=(f')^{-1}(\xi)$ is the entropy solution; (iii) uniqueness, from 17.3. Pitfall:
  `Function.invFun` returns an arbitrary value off the range of $f'$, so the fan formula must be
  used only for $f'(u_L)\le x/t\le f'(u_R)$, as in the project's statement. Depends on 17.3 for the
  identification with the entropy solution. Statable at the pins. The open roadmap PR #2801, section
  5.4, owns this for uniformly convex $f$. NASC: `NASC.isScalarEntropySolution_rarefaction` and
  `NASC.isScalarEntropySolution_riemann_shock` (`NASC/ConservationLaws.lean`), the latter for convex
  $f$, both `sorry`.

### Conservative schemes

* **17.5. The Lax–Wendroff theorem.** A **conservative scheme** has the
  form
  $$v^{n+1}_j=v^n_j-\lambda\bigl(g_{j+1/2}-g_{j-1/2}\bigr),\qquad
  g_{j+1/2}=g(v^n_{j-p+1},\dots,v^n_{j+p}),$$
  with a locally Lipschitz **numerical flux** $g$ that is **consistent**,
  $g(u,\dots,u)=f(u)$. The same form is used for systems. Let
  $v_{\Delta x}$ be the piecewise constant function with values $v^n_j$, with
  $v^0_j$ the cell averages of $u_0$. Suppose that $v_{\Delta x}$ is bounded
  in $L^\infty$ uniformly in $\Delta x$ and that $v_{\Delta x}\to u$ in
  $L^1_{\mathrm{loc}}$ along a sequence $\Delta x\to0$. Then $u$ is a weak
  solution. If moreover the scheme satisfies a **discrete entropy
  inequality**
  $$\eta(v^{n+1}_j)\le\eta(v^n_j)-\lambda\bigl(G_{j+1/2}-G_{j-1/2}\bigr)$$
  with a consistent numerical entropy flux, $G(u,\dots,u)=q(u)$, then $u$
  satisfies the entropy inequality for $(\eta,q)$.

  *Assessment.* A weak formulation and integration by parts are ingredients.
  The selected result passes from a conservative discrete balance and its
  entropy analogue to the limit equation.

  *Lean target.* Carriers: the project's `NASC.conservativeUpdate g ν a b c` (three-point form),
  `NASC.finiteVolumeReconstruction dt dx V t x` (piecewise constant in space and time through
  `Nat.floor` and `Int.floor`) and `NASC.IsWeakConservationLaw`; Mathlib interval integrals. New
  definition for the general form: a $(2p)$-point flux `(Fin (2 * p) → ℝ) → ℝ` with consistency
  $g(u,\dots,u)=f(u)$ and local Lipschitz continuity. Conjuncts: (i) bounded approximations
  converging in $L^1_{\mathrm{loc}}$, with initial values converging in $L^1_{\mathrm{loc}}$, have a
  weak-solution limit; (ii) with a discrete entropy inequality and a consistent numerical entropy
  flux, the limit satisfies the entropy inequality. Hypotheses: $\Delta t/\Delta x=\lambda$ fixed or
  bounded, $\Delta x\to0$, a uniform $L^\infty$ bound. Statable at the pins. NASC:
  `NASC.isWeakConservationLaw_of_finiteVolume_limit` (`NASC/ConservationLaws.lean`) states (i) for
  three-point fluxes, `sorry`; (ii) has no declaration.

* **17.7. Convergence of monotone schemes.** Let $f$ be Lipschitz,
  $u_0\in L^1\cap BV(\mathbb R)$, and let a conservative consistent
  monotone scheme with Lipschitz numerical flux be run with
  $\Delta t=\lambda\Delta x$, under the CFL-type condition that keeps it
  monotone. Let $u$ be the Kružkov entropy solution of 17.3. For each $T>0$
  and every compact interval $K\subset\mathbb R$, the whole family satisfies
  $$\sup_{0\le t\le T}\|v_{\Delta x}(\cdot,t)-u(\cdot,t)\|_{L^1(K)}
  \longrightarrow 0\qquad(\Delta x\to0).$$

  *Assessment.* The continuum entropy theory and discrete variation and
  monotonicity estimates give prerequisites. The selected theorem proves
  uniform-in-time local convergence for the full mesh family.

  *Lean target.* Carriers: `NASC.conservativeUpdate`, `NASC.finiteVolumeReconstruction`,
  `NASC.IsScalarEntropySolution`, `eVariationOn`, `Integrable`. Conjuncts: (i) the Crandall–Majda
  cell entropy inequality for a monotone conservative update with the numerical Kružkov flux; (ii)
  $L^1$ contraction, TV bound and $L^1$ time continuity of the discrete solutions, giving
  compactness by Helly's theorem; (iii) every limit is the entropy solution (by 17.5 with (i) and
  uniqueness in 17.3), so the whole family converges in $\sup_{t\le T}L^1(K)$. Hypotheses: $f$
  Lipschitz, $u_0\in L^1\cap BV$, monotonicity of the update on the range of the data (the CFL-type
  condition). Infrastructure: Helly's selection theorem in $L^1_{\mathrm{loc}}$ for functions of
  uniformly bounded variation, absent from both libraries. Depends on 17.3, 17.5 and 17.6. NASC:
  `NASC.monotoneUpdate_entropy_inequality` (`NASC/ConservationLaws.lean`) states (i), the main
  ingredient rather than the theorem, proved; (ii)–(iii) have no declaration.

* **17.8. Order barriers for monotone and positive schemes.** Two
  results state that the accuracy of monotone schemes is limited.
  - (Harten–Hyman–Lax) If a conservative consistent scheme is monotone and
    its numerical flux $g$ is $C^3$, then it is at most first order
    accurate: on smooth solutions, with $\lambda=\Delta t/\Delta x$ fixed, the
    one-step defect is
    $$u(x,t+\Delta t)-H\bigl(u(x-p\Delta x,t),\dots,u(x+p\Delta x,t)\bigr)
    =-\tfrac12\Delta x^2\,\partial_x\bigl(\beta(u)\,\partial_xu\bigr)
    +O(\Delta x^3),$$
    where $\beta(u)=\sum_kk^2\,\partial_kH(u,\dots,u)-\lambda^2f'(u)^2$, the
    sum over the arguments $k=-p,\dots,p$ of $H$. Here $\beta\ge0$, and
    $\beta>0$ unless only one $\partial_kH(u,\dots,u)$ is nonzero, in which
    case the scheme is an exact translation and $f$ is linear.
  - (Godunov) For $u_t+au_x=0$ with $a\ne0$, consider a linear
    semi-discretization
    $$w_j'(t)=\frac ah\sum_{k=-r}^{s}\gamma_k\,w_{j+k}(t)$$
    with order conditions $\sum_k\gamma_k=0$, $\sum_kk\gamma_k=-1$, and
    $\sum_kk^i\gamma_k=0$ for $2\le i\le q$. If it is **positive**,
    $a\gamma_k\ge0$ for all $k\ne0$, then $q\le1$. If $q=1$, then
    $|\sum_kk^2\gamma_k|\ge1$; first-order upwind attains equality.

  For first-order upwind with $a>0$, $\gamma_{-1}=1$ and $\gamma_0=-1$ give
  $\sum k\gamma_k=-1$ and $\sum k^2\gamma_k=1$.

  *Assessment.* Both order barriers require analyzing consistency and
  positivity of the discrete update. The gap identifies quantitative limits on
  the order of the schemes.

  *Lean target.* Carriers: `ContDiff ℝ 3` for the flux, `Finset ℤ` stencils with real weights.
  Conjuncts: (i) Harten–Hyman–Lax: for a monotone conservative scheme with $C^3$ flux, the one-step
  defect on smooth solutions has the stated leading term with
  $\beta=\sum_kk^2\partial_kH(u,\dots,u)-\lambda^2f'(u)^2\ge0$, and $\beta>0$ unless the scheme is a
  translation; (ii) Godunov, semi-discrete: positive weights and $\sum_kk^i\gamma_k=0$ for $i=2$
  contradict $\sum_kk\gamma_k=-1$, so $q\le1$; (iii) $|\sum_kk^2\gamma_k|\ge1$ when $q=1$. For (i)
  the leading term is best stated as an algebraic identity for the Taylor coefficients (the
  Cauchy–Schwarz inequality for $\beta$ and the translation case), with the defect expansion as a
  separate statement with an explicit $O(\Delta x^3)$ bound under bounds on the third derivatives.
  Statable at the pins. NASC: `NASC.exists_int_eq_of_positive_stencil_secondMoment`
  (`NASC/ConservationLaws.lean`) states the fully discrete analogue (a nonnegative stencil with the
  first two moments of a shift by $\nu$ is that shift), proved; (i)–(iii) as stated have no
  declaration.

* **17.9. Harten's lemma.** Suppose that the new values can be written in
  **incremental form**
  $$v^{n+1}_j=v^n_j-A_{j-1/2}\,(v^n_j-v^n_{j-1})
  +B_{j+1/2}\,(v^n_{j+1}-v^n_j)$$
  with coefficients that may depend on $v^n$. If $A_{j+1/2}\ge0$,
  $B_{j+1/2}\ge0$ and $A_{j+1/2}+B_{j+1/2}\le1$ for all $j$, then
  $\mathrm{TV}(v^{n+1})\le\mathrm{TV}(v^n)$. If $A_{j-1/2}\ge0$,
  $B_{j+1/2}\ge0$ and $A_{j-1/2}+B_{j+1/2}\le1$ for all $j$, then
  $\min_kv^n_k\le v^{n+1}_j\le\max_kv^n_k$. Every TVD scheme is
  monotonicity preserving (17.6), and a linear monotonicity preserving
  scheme is monotone (Godunov), so a linear TVD scheme is at most first
  order; second-order TVD schemes, such as flux-limiter schemes, are
  nonlinear.

  *Assessment.* Total variation of functions is available in Mathlib. The
  incremental-form criterion is a finite summation argument on grid
  sequences, and it is the standard tool behind every TVD and flux-limiter
  scheme; it is missing.

  *Lean target.* Carriers: sequences `ℤ → ℝ`, total variation $\sum_j|v_{j+1}-v_j|$ as a `tsum` in
  `ℝ≥0∞` (or Mathlib's `eVariationOn` of the sequence on `ℤ`), `iSup` and `iInf` over `ℤ`.
  Conjuncts: (i) under $A_{j+1/2},B_{j+1/2}\ge0$ and $A_{j+1/2}+B_{j+1/2}\le1$, the total variation
  does not increase, stated in `ℝ≥0∞` so that infinite variation needs no hypothesis; (ii) under the
  shifted conditions, $\inf_kv^n_k\le v^{n+1}_j\le\sup_kv^n_k$ for bounded $v^n$; (iii) a TVD scheme
  is monotonicity preserving. Pitfalls: real `⨆` over `ℤ` is junk $0$ for an unbounded sequence, so
  (ii) carries a boundedness hypothesis or is stated in `EReal`; the two index conventions of the
  source (half-integer and integer) must be fixed once. Statable at the pins; no infrastructure.
  NASC: no declaration.

* **17.10. Error estimates: Kuznetsov's lemma.** Let $d=1$. Let $\mathcal K$
  be the class of maps $t\mapsto u(t)$ into $L^1_{\mathrm{loc}}\cap BV$ that
  are right continuous with one-sided limits and satisfy
  $\|u(t)\|_{L^\infty}\le\|u(0)\|_{L^\infty}$ and
  $\mathrm{TV}(u(t))\le\mathrm{TV}(u(0))$. Let $\nu(u,\varepsilon_0)$ be the
  supremum over $0\le t\le T$ and $|\tau|\le\varepsilon_0$ of
  $\|u(t+\tau)-u(t)\|_{L^1}$. Let $\Lambda_{\varepsilon,\varepsilon_0}(u,v)$ be
  the Kružkov form of $u$, with $k$ replaced by $v(x',s')$, tested with a
  product of mollifiers of widths $\varepsilon$ in space and $\varepsilon_0$
  in time and integrated in $(x',s')$; it is nonnegative when $u$ is an
  entropy solution. If $u\in\mathcal K$, $v$ is the entropy solution, and
  $0<\varepsilon_0<T$ and $\varepsilon>0$, then
  $$\|u(T^-)-v(T)\|_{L^1}\le\|u_0-v_0\|_{L^1}
  +\mathrm{TV}(v_0)\bigl(2\varepsilon+\varepsilon_0\|f\|_{\mathrm{Lip}}\bigr)
  +\nu(u,\varepsilon_0)-\Lambda_{\varepsilon,\varepsilon_0}(u,v).$$
  Consequences:
  - for the viscous approximation with viscosity $\delta$, the $L^1$ error at
    time $T$ is at most $2\,\mathrm{TV}(u_0)\sqrt{T\delta}$;
  - for a conservative consistent monotone scheme with cell-average data and
    $u_0\in L^1\cap BV$, $\|v_{\Delta x}(T)-u(T)\|_{L^1}\le C\sqrt{\Delta x}$,
    with $C$ depending on $T$, $\mathrm{TV}(u_0)$, $f$ and the numerical
    flux;
  - **front tracking**: if $f_\delta$ is piecewise linear and $u_{0,\delta}$
    is a step function, the entropy solution $u_\delta$ for $(f_\delta,u_{0,\delta})$
    is piecewise constant with finitely many jumps and finitely many
    interactions, and by 17.3
    $\|u(t)-u_\delta(t)\|_{L^1}\le\|u_0-u_{0,\delta}\|_{L^1}
    +t\,\mathrm{TV}(u_0)\,\|f-f_\delta\|_{\mathrm{Lip}}$.

  *Assessment.* Weak entropy inequalities and bounded variation provide
  ingredients. Doubling variables and controlling the discrete residual in the
  mollified functional yield the numerical error bound.

  *Lean target.* Carriers: `eVariationOn`, `∫⁻`, interval integrals, mollifiers from Mathlib's
  `ContDiffBump`, and the right-continuous maps $t\mapsto u(t)$ into `MeasureTheory.Lp ℝ 1` on
  bounded intervals, with the left limit $u(T^-)$ as a `Filter.Tendsto` along `𝓝[<] T`. New
  definitions: the class $\mathcal K$, the modulus $\nu(u,\varepsilon_0)$ in `ℝ≥0∞`, and the doubled
  Kružkov form $\Lambda_{\varepsilon,\varepsilon_0}(u,v)$ as a real number for bounded $u,v$ of
  bounded variation. Conjuncts: (i) Kuznetsov's inequality; (ii) the viscous rate
  $2\,\mathrm{TV}(u_0)\sqrt{T\delta}$; (iii) the $\sqrt{\Delta x}$ rate for monotone schemes; (iv)
  the front-tracking estimate. Pitfall: all four sides can be infinite unless the variation is
  finite, so they are stated in `ℝ≥0∞` or under $\mathrm{TV}(u_0)<\infty$. Depends on 17.3 and 17.7.
  Statable at the pins, with the viscous equation needing the existence theory that PR #2801,
  section 6.3, owns. NASC: `NASC.upwind_L1_error_le_sqrt_mesh` (`NASC/ConservationLaws.lean`) states
  (iii) for the upwind scheme for $u_t+au_x=0$, $a>0$, against the exact translate, `sorry`.

* **17.11. Entropy-conservative and entropy-stable fluxes (Tadmor).** Let
  $\eta$ be strictly convex, let $w=\eta'(u)$ be the **entropy variable**,
  let $\psi=wf(u)-q(u)$ be the **entropy flux potential**, and write
  $\Delta a_{j+1/2}=a_{j+1}-a_j$. Consider the semi-discrete conservative
  scheme
  $$\frac{d}{dt}u_j=-\frac1{\Delta x}\bigl(g_{j+1/2}-g_{j-1/2}\bigr)$$
  with a consistent flux. It is **entropy conservative** (it satisfies a
  discrete entropy equality with a consistent numerical entropy flux) if
  $$\Delta w_{j+1/2}\,g_{j+1/2}=\Delta\psi_{j+1/2}\quad\text{for all }j,$$
  and **entropy stable** (discrete entropy inequality) if
  $\Delta w_{j+1/2}\,g_{j+1/2}\le\Delta\psi_{j+1/2}$ for all $j$; for
  three-point schemes these conditions are also necessary. In the scalar
  case the unique entropy-conservative flux is
  $$g^*_{j+1/2}=\frac{\Delta\psi_{j+1/2}}{\Delta w_{j+1/2}}
  =\int_0^1f\bigl(u(w_j+\xi\,\Delta w_{j+1/2})\bigr)\,d\xi ,$$
  and a flux written as $g=g^*-\frac12Q\,\Delta w$ is entropy stable if and
  only if $Q\ge0$. For Burgers' equation, $\eta=u^2/2$ gives
  $g^*=(u_j^2+u_ju_{j+1}+u_{j+1}^2)/6$, and $\eta=-\log u$ on $u>0$ gives
  $g^*=u_ju_{j+1}/2$. The same conditions, with inner products, hold for
  systems with an entropy pair as in 17.12.

  *Assessment.* Convex entropy and entropy variables are expressible with
  existing calculus. The flux identities and their consequences for the
  discrete entropy inequality need a conservative scheme API.

  *Lean target.* Carriers: real functions $w=\eta'$, $\psi$, two-point fluxes `ℝ → ℝ → ℝ`, `deriv`,
  interval integrals for $g^*(a,b)=\int_0^1f(w^{-1}(w_a+s(w_b-w_a)))\,ds$. Conjuncts: (i) the scheme
  is entropy conservative if and only if $(w_b-w_a)g(a,b)=\psi(b)-\psi(a)$, with numerical entropy
  flux $\frac12(w_a+w_b)g-\frac12(\psi_a+\psi_b)$; (ii) the inequality version gives the cell
  entropy inequality (entropy stability); (iii) the viscosity form: $g=g^*-\frac12 Q\Delta w$ with
  $Q\ge0$ is entropy stable; (iv) the explicit fluxes for Burgers with $\eta=u^2/2$ and with
  $\eta=-\log u$. Pitfall: for (iii) $w$ must be strictly increasing, so $\eta$ strictly convex with
  $\eta''>0$, not only convex. Statable at the pins. NASC: `NASC.tadmor_cell_entropy_le`
  (`NASC/ConservationLaws.lean`) states the algebraic core of (ii) for a single cell, proved.

### Systems in one space dimension

* **17.14. Lax's theorem on the Riemann problem.** Let $f\in C^2$ be
  strictly hyperbolic near $u_L$, and let each field be genuinely nonlinear
  or linearly degenerate. There is a neighborhood $U$ of $u_L$ such that for
  every $u_R\in U$ the Riemann problem has a self-similar weak solution
  consisting of at most $m$ elementary waves: rarefactions, Lax shocks and
  contact discontinuities, separating at most $m+1$ constant states. It is
  unique among solutions of this form with states in $U$. The
  intermediate states are obtained by composing the $k$-wave curves for
  $k=1,\dots,m$; the $k$-wave curve through a state is tangent there to
  $r_k$.

  *Assessment.* The implicit function theorem can support local wave curves.
  The selected theorem constructs the Riemann solution and resolves the
  ordered wave strengths under the field hypotheses.

  *Lean target.* Carriers: states `Fin n → ℝ`, the project's `NASC.IsHyperbolicOn f U speed field`
  (ordered real eigenvalues with eigenvectors, each field genuinely nonlinear or linearly degenerate
  on all of $U$), `fderiv`, the implicit function theorem `HasStrictFDerivAt.implicitFunction`,
  `eVariationOn`, and `NASC.IsWeakConservationLaw`. New definitions: the $k$-rarefaction and
  $k$-Hugoniot curves through a state, the Lax shock predicate, and the $k$-wave curve as a $C^1$
  map of the wave strength. Conjuncts: (i) each $k$-wave curve is $C^1$ and tangent to $r_k$; (ii)
  existence of a self-similar weak solution of at most $m$ waves with Lax-admissible shocks and
  states in $U$; (iii) uniqueness among such solutions. Pitfall: eigenvectors are determined only up
  to scale, so genuine nonlinearity is stated for the given field and must be invariant under
  rescaling. Statable at the pins. NASC: `NASC.exists_selfSimilar_riemann_solution`
  (`NASC/ConservationLaws.lean`) states a weak self-similar solution with small variation, without
  the wave structure, the admissibility or the uniqueness of (ii)–(iii), `sorry`.

* **17.15. Existence and stability for small total variation.** Let the
  system be as in 17.14 near a state $\bar u$. There is $\delta>0$ such that
  for $u_0$ with $\|u_0-\bar u\|_{L^\infty}$ and $\mathrm{TV}(u_0)$ smaller than
  $\delta$ there is a global weak solution, obtained as the limit of front
  tracking approximations, with uniformly bounded total variation (Glimm's
  random choice method gives the same existence result). At isolated jumps
  it satisfies the Lax conditions. The solutions so obtained are unique and
  form an $L^1$-Lipschitz semigroup:
  $\|u(t)-v(t)\|_{L^1}\le C\,\|u_0-v_0\|_{L^1}$, with $C$ independent of
  $t$, $u_0$ and $v_0$.

  *Assessment.* The gap is global small-variation existence, admissibility and
  semigroup stability from front tracking. The proof needs quantitative wave
  interaction estimates.

  *Scope.* The selected claim is small-total-variation existence and stability
  of the entropy solution semigroup.

  *Lean target.* Carriers: as in 17.14, with `eVariationOn` on `ℝ → Fin n → ℝ` and `∫⁻` for $L^1$
  distances. Conjuncts: (i) for small $\mathrm{TV}(u_0)$ and $\|u_0-\bar u\|_\infty$, a global weak
  solution with bounded total variation, Lax conditions at isolated jumps; (ii) a semigroup on a
  domain containing these data with the $L^1$-Lipschitz bound, $C$ independent of $t$; (iii)
  uniqueness among entropy solutions in the sense of Holden–Risebro's conditions (A)–(C).
  Infrastructure: front tracking (wave interaction potentials and Glimm functionals) exists in
  neither library. Pitfall: the semigroup acts on functions, and `=ᵐ[volume]` identities are needed
  for the semigroup law, because pointwise values of $L^1$ data are not determined. Depends on
  17.14. NASC: `NASC.exists_smallVariation_conservation_semigroup` (`NASC/ConservationLaws.lean`)
  states (i)–(ii) without the Lax conditions, `sorry`; (iii) has no declaration.

## 18. Galerkin and finite element methods for elliptic problems

[Synopsis](SYNOPSIS.md#18-galerkin-and-finite-element-methods-for-elliptic-problems) · [Coverage inventory](STRUCTURE.md#18-galerkin-and-finite-element-methods-for-elliptic-problems)

Coercive Hilbert-space solvability, Sobolev results and weak elliptic theory
supply continuous foundations. These gaps focus on stable discretizations and
the approximation estimates needed to turn well-posedness into numerical error
bounds.

Spaces are real. For a
bounded bilinear form $a$ on $V\times W$,
$\|a\|=\sup a(v,w)/(\|v\|_V\|w\|_W)$ over nonzero $v$ and $w$. A
**mesh** $\mathcal T_h$ of a polyhedral domain $\Omega$ is a matching
partition into closed simplices $K$ with diameter $h_K$, inradius $\rho_K$,
and $h=\max_Kh_K$. A family of meshes is **shape regular** if
$h_K/\rho_K\le\sigma$ for all $K$ and all $h$, and **quasi-uniform** if, in
addition, $h_K\ge c\,h$ with $c>0$ fixed. The **Lagrange space** of degree
$k\in\mathbb N$ is
$V_h=\{v\in C(\overline\Omega):v|_K\in\mathbb P_k\text{ for all }K\}$, and
$V_{h,0}=V_h\cap H^1_0(\Omega)$. The length scale $\ell_\Omega$ is the
diameter of $\Omega$. Constants depend on the reference element, $d$, the
Sobolev indices and $\sigma$ unless stated. Time-dependent problems,
spectral and adaptive methods and eigenvalue approximation are in
section 19, multilevel solvers in section 20, and boundary elements in
section 21.

### Abstract Galerkin theory

* **18.1. The Banach–Nečas–Babuška theorem.**
  Let $V$ be a Banach space, $W$ a reflexive Banach space, $a$ a bounded
  bilinear form on $V\times W$ and $\ell\in W'$. The problem of finding
  $u\in V$ with $a(u,w)=\ell(w)$ for all $w\in W$ is **well posed** (has a
  unique solution for every $\ell$) if and only if
  - (inf-sup) $\displaystyle\alpha:=\inf_{v\ne0}\sup_{w\ne0}
    \frac{a(v,w)}{\|v\|_V\|w\|_W}>0$, and
  - (injectivity of the adjoint) if $w\in W$ and $a(v,w)=0$ for all $v\in V$,
    then $w=0$.

  Then $\|u\|_V\le\|\ell\|_{W'}/\alpha$.

  *Assessment.* Partly covered. Mathlib has Lax–Milgram with its inverse
  bound. The Banach trial and reflexive test space equivalence under the two
  inf-sup conditions is the selected result.

  *Scope.* The target is the Banach–Nečas–Babuška equivalence for the Banach
  trial space and reflexive Banach test space in the statement.

  *Lean target.* Carriers: bounded bilinear forms as `A : V →L[ℝ] StrongDual ℝ W` with $V,W$ real
  Banach spaces (`CompleteSpace`), reflexivity of $W$ as surjectivity of
  `NormedSpace.inclusionInDoubleDual ℝ W`, and for the coercive case Mathlib's `IsCoercive` with
  `IsCoercive.continuousLinearEquivOfBilin`, `IsCoercive.bounded_below`. Conjuncts: (i) $A$ is
  bijective if and only if $\alpha\|v\|\le\|Av\|$ for some $\alpha>0$ and the adjoint is injective;
  (ii) then $\|A^{-1}\ell\|\le\|\ell\|/\alpha$; (iii) coercivity on a Hilbert space gives both
  conditions with the same $\alpha$. Pitfall: the inf-sup constant as a real `⨅` of a `⨆` is junk on
  the trivial space and for unbounded quotients; state it as the existence of $\alpha>0$ with the
  inequality. Statable at the pins; (iii) is Mathlib's Lax–Milgram. NASC:
  `NASC.bijective_iff_infSup_of_reflexive` (`NASC/Galerkin.lean`) states (i), `sorry`; (ii) has no
  declaration.

* **18.2. Discrete well-posedness and Fortin's criterion.** Let
  $V_h\subset V$ and $W_h\subset W$ be finite-dimensional, and let $u_h\in
  V_h$ satisfy $a(u_h,w_h)=\ell(w_h)$ for all $w_h\in W_h$. This discrete
  problem is well posed if and only if $\dim V_h=\dim W_h$ and
  $$\alpha_h:=\inf_{v_h\ne0}\sup_{w_h\ne0}
  \frac{a(v_h,w_h)}{\|v_h\|_V\|w_h\|_W}>0 .$$
  If $V_h=W_h$ and $a$ is coercive on $V=W$, then $\alpha_h\ge\alpha$. Let
  $V$ and $W$ be Hilbert spaces satisfying the conditions of 18.1. If
  there is a **Fortin operator** $\Pi_h\colon W\to W_h$ with
  $a(v_h,\Pi_hw-w)=0$ for all $v_h\in V_h$ and $w\in W$ and with
  $\gamma_h\|\Pi_hw\|_W\le\|w\|_W$ for all $w$, then
  $\alpha_h\ge\gamma_h\alpha$. Conversely, if $\alpha_h>0$, there is a linear
  idempotent Fortin operator with $\gamma_h=\alpha_h/\|a\|$.

  *Assessment.* Finite-dimensional duality and rank identities are available.
  The numerical gap is the equivalence with discrete inf-sup stability and the
  Fortin operator criterion.

  *Lean target.* Carriers: `A : V →L[ℝ] StrongDual ℝ W`, finite-dimensional `Submodule ℝ V` and
  `Submodule ℝ W` with `FiniteDimensional`, `Module.finrank`, and the restricted form
  `(A v).comp Y.subtypeL`. Conjuncts: (i) the discrete problem is well posed if and only if $\dim
  V_h=\dim W_h$ and $\alpha_h>0$; (ii) coercivity on $V=W$ gives $\alpha_h\ge\alpha$; (iii) a Fortin
  operator gives $\alpha_h\ge\gamma_h\alpha$; (iv) conversely, $\alpha_h>0$ gives a linear
  idempotent Fortin operator with $\gamma_h=\alpha_h/\|a\|$ on Hilbert spaces. Pitfall:
  $\alpha_h/\|a\|$ is junk $0$ for $a=0$, but then $\alpha_h=0$ and (iv) is vacuous. Statable at the
  pins. NASC: `NASC.norm_restrict_ge_of_fortin` (`NASC/Galerkin.lean`) states (iii) and is proved;
  (i), (ii) and (iv) have no declaration.

* **18.3. Quasi-optimality: Céa, Babuška, Xu–Zikatanov.** In the setting of
  18.2, with $u$ the exact solution and $\alpha_h>0$, **Galerkin
  orthogonality** $a(u-u_h,w_h)=0$ holds for all $w_h\in W_h$, and
  $$\|u-u_h\|_V\le\Bigl(1+\frac{\|a\|}{\alpha_h}\Bigr)
  \inf_{v_h\in V_h}\|u-v_h\|_V \qquad\text{(Babuška).}$$
  If $V$ and $W$ are Hilbert spaces and $\{0\}\ne V_h\ne V$, the factor improves to
  $\|a\|/\alpha_h$ (Xu–Zikatanov). If $V=W$ is a Hilbert space, $V_h=W_h$
  and $a$ is coercive with constant $\alpha$, the factor is $\|a\|/\alpha$
  (Céa), and it is $(\|a\|/\alpha)^{1/2}$ if moreover $a$ is symmetric.

  *Assessment.* Partly covered. Orthogonal projection gives the inner-product
  instance. The selected bounds concern the general coercive or inf-sup-stable
  bilinear forms, including the sharp Hilbert-space variants.

  *Scope.* The target is quasi-optimality with a discrete inf-sup constant,
  including the sharpened Hilbert-space bound and the coercive case.

  *Lean target.* Carriers as in 18.2, with the project's `NASC.bestApproximationError` (an infimum
  of distances, nonnegative and finite for a nonempty set) and Mathlib's
  `Submodule.HasOrthogonalProjection` for the Hilbert case. Conjuncts: (i) Galerkin orthogonality;
  (ii) Babuška's bound $1+\|a\|/\alpha_h$; (iii) Xu–Zikatanov's $\|a\|/\alpha_h$ when $V$ and $W$
  are Hilbert spaces and $\{0\}\ne V_h\ne V$; (iv) Céa's $\|a\|/\alpha$ and the symmetric
  $(\|a\|/\alpha)^{1/2}$ in the energy norm. Pitfall: the condition $V_h\ne\{0\}$ in (iii) is
  needed: for $V_h=\{0\}$ the stability hypothesis holds for every $\alpha_h$, while the error is
  $\|u\|$. Statable at the pins. NASC: `NASC.norm_galerkinError_le_of_infSup` (`NASC/Galerkin.lean`)
  states (ii) and is proved; `NASC.norm_galerkinError_le_of_infSup_hilbert` states (iii) with
  $V_h\ne\{0\}$ and a Banach $W$, `sorry`; (iv) has no declaration here (the energy-norm bound is
  part of 18.13).

* **18.4. Strang's lemmas.** Let $u_h\in V_h$ satisfy
  $a_h(u_h,w_h)=\ell_h(w_h)$ for all $w_h\in W_h$, with a bilinear form
  $a_h$ on $V_h\times W_h$ whose discrete inf-sup constant (as in 18.2) is
  $\alpha_h>0$.
  - (First lemma) If $V_h\subset V$ and $W_h\subset W$, then
    $$\|u-u_h\|_V\le\inf_{v_h\in V_h}\Bigl[\Bigl(1+\frac{\|a\|}{\alpha_h}
    \Bigr)\|u-v_h\|_V+\frac1{\alpha_h}\sup_{w_h\ne0}
    \frac{|(\ell_h-\ell)(w_h)+(a-a_h)(v_h,w_h)|}{\|w_h\|_W}\Bigr].$$
  - (Second lemma) If $V_h\not\subset V$, suppose that the error is
    measured in a norm on $V+V_h$ whose restriction to $V_h$ is the
    stability norm, and that $a_h$ extends to a bounded form $a^\sharp$ on
    $(V+V_h)\times W_h$. Then
    $$\|u-u_h\|\le\Bigl(1+\frac{\|a^\sharp\|}{\alpha_h}\Bigr)
    \inf_{v_h\in V_h}\|u-v_h\|+\frac1{\alpha_h}\sup_{w_h\ne0}
    \frac{|\ell_h(w_h)-a^\sharp(u,w_h)|}{\|w_h\|_W}.$$
    The last term is the **consistency error**. It vanishes if
    $\ell_h=\ell$ and $a^\sharp(u,w_h)=a(u,w_h)$ for all $w_h\in W_h$.
    For conforming spaces with exact forms and loads the estimate recovers
    Babuška's bound.

  If $a_h$ is symmetric and positive definite on $V+V_h$ and agrees with
  $a$ on $V$, then in the energy norm $\|v\|_h=a_h(v,v)^{1/2}$,
  $\|u-u_h\|_h\le\inf_{v\in V_h}\|u-v\|_h+\sup_{w\in V_h\setminus\{0\}}
  |a_h(u-u_h,w)|/\|w\|_h$.

  *Assessment.* The gap is a variational approximation theory with perturbed
  forms or nonconforming spaces. It needs quantitative control of both best
  approximation and consistency under the stated stability assumptions.
  TauCeti's continuous-dependence estimate for the weak Dirichlet problem is
  the continuous analogue of the first lemma.

  *Lean target.* Carriers: as in 18.2, with the discrete form `Ah : X →L[ℝ] StrongDual ℝ Y` on the
  discrete spaces and, for the second lemma, a normed space containing $V+V_h$ with an extension of
  $a_h$. Conjuncts: (i) the first lemma for conforming spaces; (ii) the second lemma with the
  consistency error; (iii) the energy-norm form for symmetric positive definite $a_h$. Pitfall:
  $V+V_h$ is not a subspace of $V$ in the nonconforming case, so (ii) needs an ambient space and two
  norms that agree on $V_h$; stating it with a single norm on $V_h$ loses the content. Statable at
  the pins. TauCeti's
  `TauCeti.PDE.norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq` is the continuous
  analogue for the Dirichlet problem, not a Galerkin estimate. NASC:
  `NASC.norm_galerkinError_le_strang` (`NASC/Galerkin.lean`) states (i) at a fixed $v_h$ and is
  proved; (ii) and (iii) have no declaration.

### Sobolev space tools

* **18.6. The onto trace from $H^1(\Omega)$.** For a bounded Lipschitz
  domain $\Omega$, the value trace is a bounded surjection
  $$\gamma:H^1(\Omega)\longrightarrow H^{1/2}(\partial\Omega)$$
  with kernel $H^1_0(\Omega)$. For functions in $H^1(\Omega)$ continuous on
  $\overline\Omega$, $\gamma$ agrees with restriction to $\partial\Omega$.

  *Assessment.* Partly covered. TauCeti gives the global trace
  $W^{1,p}(\Omega)\to L^p(\partial\Omega)$ for $p<\infty$ on bounded Lipschitz
  domains, its agreement with restriction for functions continuous up to the
  boundary, and its kernel $W^{1,p}_0(\Omega)$. The selected result is the
  range: surjectivity onto the fractional boundary space, which has no carrier.

  *Scope.* The target is the onto trace theorem at first order with the
  boundary Sobolev space as codomain.

  *Lean target.* Carriers at the pins: `TauCeti.W1p.frontierTrace` on a bounded set with
  `IsLipschitzDomainWith`, valued in `Lp ℝ p` for the restricted Hausdorff measure
  `μHE[finrank ℝ E]` on the frontier, with `TauCeti.W1p.ker_frontierTrace` and
  `TauCeti.W1p.frontierTrace_ae_eq_of_continuousOn`. New definition: the boundary space
  $H^{1/2}(\partial\Omega)$, as the elements of `Lp ℝ 2` of the surface measure with finite
  Slobodeckij energy $\iint|g(x)-g(y)|^2|x-y|^{-d}$, a lower integral in `ℝ≥0∞` so that a divergent
  integral is excluded rather than set to a junk value. Conjuncts: (i) the range of the trace on
  $H^1$ is exactly that set; (ii) the trace is bounded into it, with the energy at most
  $C\|u\|^2_{H^1}$; (iii) a bounded right inverse (lifting). Infrastructure: fractional Sobolev
  spaces on Lipschitz boundaries exist in neither library, and the lifting needs boundary charts
  with a partition of unity, which TauCeti has for the trace. NASC: `NASC.fractionalBoundaryEnergy`,
  `NASC.frontierMeasure`, `NASC.range_frontierTrace_eq_setOf_fractionalBoundaryEnergy_lt_top` and
  `NASC.exists_frontierTrace_fractionalBound` (`NASC/FiniteElements.lean`) state (i) and (ii),
  `sorry`; (iii) has no declaration.

* **18.7. Elliptic regularity on convex and polygonal domains.** Let $A$
  be a Lipschitz, symmetric, uniformly positive definite matrix field and
  $f\in L^2(\Omega)$.
  - If $\Omega$ is convex, the weak solution of $-\nabla\cdot(A\nabla u)=f$
    with $u=0$ on $\partial\Omega$ is in $H^2(\Omega)$.
  - If $\Omega\subset\mathbb R^2$ is a polygon and $A=I$, there is
    $s_0\in(\frac12,1]$, with $s_0=1$ if $\Omega$ is convex, such that the
    solution of the Dirichlet problem with $u=0$ on $\partial\Omega$ is in
    $H^{1+s}(\Omega)$ for all $s\in[0,s_0]$.

  By the closed graph theorem the solution map is then bounded:
  $\|u\|_{H^{1+s}(\Omega)}\le C\|f\|_{L^2(\Omega)}$.

  *Assessment.* TauCeti has local and flat-boundary Hessian estimates and
  qualitative $H^2$ regularity up to a $C^2$ graph boundary. The selected gap
  is global regularity and a solution bound for the homogeneous Dirichlet
  problem on convex or polygonal domains, which are neither smooth nor flat.

  *Scope.* The selected regularity estimates use homogeneous Dirichlet data on
  convex domains and, for the Laplacian, on planar polygons.

  *Lean target.* Carriers: `TauCeti.Wkp`, `TauCeti.W1p0`, `TauCeti.PDE.IsWeakSolutionDirichlet`,
  `LipschitzOnWith` for the coefficient field `EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ`,
  `Matrix.IsHermitian`, `Convex`. Conjuncts: (i) on a bounded convex domain, the Dirichlet solution
  is in $H^2$ with $\|u\|_{H^2}\le C\|f\|_{L^2}$; (ii) the Neumann and Robin cases when well posed;
  (iii) on a plane polygon, $H^{1+s}$ for $s\le s_0$; (iv) the L-shaped example. Infrastructure:
  (iii) and (iv) need fractional Sobolev spaces $H^{1+s}$ on domains and polygon geometry, absent
  from both libraries; (i) needs approximation of a convex domain by smooth convex domains together
  with global $H^2$ estimates, of which TauCeti has the $C^2$ graph case
  `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph` without the uniform
  bound. NASC: `NASC.exists_Wkp_two_of_convex_weakDirichlet` (`NASC/FiniteElements.lean`) states
  (i), `sorry`.

### Conforming finite elements

* **18.9. The Bramble–Hilbert (Deny–Lions) lemma.** Let $S\subset\mathbb
  R^d$ be a Lipschitz domain, $p\in[1,\infty]$ and $k\in\mathbb N_0$. There is
  $c$, depending on $k$, $p$ and $S$, such that
  $$\inf_{q\in\mathbb P_k}\|v-q\|_{W^{k+1,p}(S)}\le c\,|v|_{W^{k+1,p}(S)}
  \qquad\text{for all }v\in W^{k+1,p}(S).$$
  If $S$ is star-shaped with respect to a ball of radius $\rho$, $\rho$ larger
  than half the radius of the largest such ball, and $Q^mv$ is the
  averaged Taylor polynomial of degree $m-1$ of $v\in W^{m,p}(S)$, then for
  $0\le j\le m$
  $$|v-Q^mv|_{W^{j,p}(S)}\le C\,(\mathop{\mathrm{diam}}S)^{m-j}
  |v|_{W^{m,p}(S)},$$
  with $C$ depending only on $m$, $d$ and the **chunkiness**
  $\mathop{\mathrm{diam}}S/\rho_{\max}$.

  *Assessment.* Poincaré and polynomial-space ingredients exist. The
  Bramble–Hilbert estimate quotienting by polynomials and its geometric
  uniformity are needed for interpolation errors.

  *Lean target.* Carriers: `TauCeti.Wkp μ Ω p (k + 1)` with `TauCeti.Wkp.iteratedGradient k`, the
  top weak derivative, `MvPolynomial (Fin d) ℝ` with `MvPolynomial.totalDegree`, `Convex`,
  `IsLipschitzDomainWith`. New definitions for the second part: star-shapedness with respect to a
  ball and the averaged Taylor polynomial $Q^mv$, an integral of Taylor polynomials against a
  cutoff. Conjuncts: (i) the quotient estimate on a bounded connected Lipschitz domain, $p<\infty$
  (by compactness); (ii) the averaged Taylor estimate for every $p\in[1,\infty]$ with the chunkiness
  constant; (iii) for $p=\infty$ on a Lipschitz domain, (i) from (ii) by covering. Pitfall: the
  infimum over polynomials is a real `⨅` over a nonempty set bounded below by $0$, so it is safe,
  but the polynomial must be identified with a Sobolev class through an a.e. equality. Statable at
  the pins. The main-branch roadmap SobolevPolynomialApproximation owns (ii) (Layer 3 and section
  4.1) and the compactness form (section 4.4). NASC: `NASC.exists_poly_sobolev_error_le_of_convex`
  (`NASC/FiniteElements.lean`) states (i) on bounded convex domains for $p=2$, `sorry`.

* **18.10. Interpolation error estimates.** Let the mesh family be shape
  regular and let each element be affine equivalent to a reference element
  with $\mathbb P_k\subset\hat P$. Let $p\in[1,\infty]$ and let $l\in\mathbb
  N_0$ be such that the degrees of freedom are bounded on $W^{l,p}(\hat K)$,
  for instance $l>d/p$ (or $l\ge d$ if $p=1$) for Lagrange elements. For
  integers $r$ with $l\le r\le k+1$ and $0\le m\le r$,
  $$|v-I_Kv|_{W^{m,p}(K)}\le C\,h_K^{r-m}|v|_{W^{r,p}(K)}
  \qquad\text{for all }v\in W^{r,p}(K)\text{ and all }K,$$
  with $C$ independent of $K$, $h$ and $v$. Summing over $K$, the global
  interpolant $I_h$ satisfies
  $(\sum_K\|v-I_hv\|^p_{W^{m,p}(K)})^{1/p}\le Ch^{r-m}|v|_{W^{r,p}(\Omega)}$.
  For $\mathbb P_1$ Lagrange elements in $d=2$ and $p=2$, this requires
  $r=2$: nodal interpolation is not defined on $H^1$.

  *Assessment.* Polynomial approximation and Sobolev estimates provide
  ingredients. The missing theorem also needs a reference-to-cell map, shape
  regularity and a nodal interpolation operator.

  *Lean target.* Carriers: `TauCeti.Wkp`, `MvPolynomial`, Mathlib `AffineEquiv` and
  `Lagrange.interpolate` in one dimension. New definitions: a simplex as an affine image of the
  reference simplex with $h_K$ and $\rho_K$; a Ciarlet element (18.8) as a finite-dimensional space
  of polynomials with a basis of linear forms; the local interpolant; a mesh as a finite family of
  simplices with matching faces, and shape regularity. Conjuncts: (i) the scaled local estimate on
  one affine cell; (ii) the global estimate on a shape-regular mesh; (iii) the $\mathbb P_1$, $d=2$,
  $p=2$ restriction $r=2$. Infrastructure: simplicial meshes, affine pullback of Sobolev classes
  with the scaling of seminorms, and point values of $W^{l,p}$ functions for $l>d/p$, which TauCeti
  has as continuous representatives on Lipschitz domains for $d<lp$. Depends on 18.8 and 18.9.
  SobolevPolynomialApproximation on main owns the affine scaling of seminorms (section 2.2). NASC:
  `NASC.exists_scaled_lagrange_derivative_bound` (`NASC/FiniteElements.lean`) states the
  one-dimensional case for $C^r$ functions in the supremum norm, `sorry`.

* **18.11. Quasi-interpolation.** On a shape-regular family there are
  linear **quasi-interpolation operators** (Clément, Scott–Zhang) onto the
  Lagrange space that are defined on functions too rough for nodal
  interpolation; the Scott–Zhang operator is the identity on $V_h$. For
  the Scott–Zhang operator $I_h$ with elements containing $\mathbb P_{m-1}$,
  $p\in[1,\infty]$, and integers $1\le k\le m$ and $0\le s\le k$,
  $$\Bigl(\sum_Kh_K^{p(s-k)}\|v-I_hv\|^p_{W^{s,p}(K)}\Bigr)^{1/p}
  \le C\,|v|_{W^{k,p}(\Omega)} ,$$
  and in particular $(\sum_K\|I_hv\|^p_{W^{k,p}(K)})^{1/p}\le
  C\|v\|_{W^{k,p}(\Omega)}$. Thus $I_h$ is stable in $H^1$ and gives the
  optimal rate for functions of low smoothness, where nodal interpolation
  is undefined. Averaging
  operators give the same local estimates, with $|v|$ on the right taken
  over a patch of elements around $K$.

  *Assessment.* The selected theorem uses local averaging to construct an
  interpolation operator for Sobolev functions without point evaluations, with
  the specified mesh-local estimates.

  *Lean target.* Carriers: `TauCeti.W1p`, `TauCeti.Wkp`, the mesh and element definitions of 18.10.
  New definition: the Scott–Zhang operator through dual bases of the face moments. Conjuncts: (i)
  projection onto $V_h$; (ii) the weighted local estimate for $0\le s\le k\le m$; (iii) stability in
  $W^{k,p}$; (iv) the patch-local averaged form. Infrastructure: simplicial meshes and traces on
  faces of cells, which TauCeti has only as the global boundary trace. Pitfall: the patch estimates
  need mesh hypotheses beyond conformity and shape regularity: on a pinched (bowtie) vertex star the
  Scott–Zhang estimate fails, so state connected vertex stars; for $d\ge2$ these give local
  quasi-uniformity $h_K\le Ch_{K'}$ for cells sharing a vertex (EG I, Proposition 11.6, p. 125); for
  $d=1$ Proposition 11.6 is false (cells $[0,1]$, $[1,1+\varepsilon]$) but the operator is then
  nodal interpolation, which is local. Depends on 18.9 and 18.10. NASC:
  `NASC.exists_uniform_interval_quasiInterpolator` (`NASC/FiniteElements.lean`) states the
  one-dimensional uniform-mesh $\mathbb P_1$ case with explicit cell moments, $H^1$ stability and
  the $L^2$ estimate, `sorry`.

* **18.12. Inverse estimates.** Let $P_K$ be the local polynomial space.
  There is $C$ such that for integers $0\le m\le l$, all
  $p,q\in[1,\infty]$, all $K$ and all $v\in P_K$,
  $$|v|_{W^{l,p}(K)}\le C\,h_K^{m-l+d(1/p-1/q)}|v|_{W^{m,q}(K)},\qquad
  \|v\|_{L^p(F)}\le C\,h_K^{-1/p+d(1/p-1/q)}\|v\|_{L^q(K)}$$
  for each face $F$ of $K$. On a quasi-uniform family the global form is
  $(\sum_K\|v\|^p_{W^{l,p}(K)})^{1/p}\le Ch^{m-l+\min(0,d/p-d/q)}
  (\sum_K\|v\|^q_{W^{m,q}(K)})^{1/q}$ for piecewise polynomial $v$. For
  $v(x)=x$ on $K=[0,h]$, $|v|_{1,K}=\sqrt3\,h^{-1}\|v\|_{0,K}$; for
  $v(x)=x-h/2$ the ratio is $2\sqrt3\,h^{-1}$, the largest over $\mathbb P_1$.

  *Assessment.* Equivalence of norms on finite-dimensional spaces gives the
  reference-element constant. The scaling to a cell with explicit powers of
  $h_K$ and the face inequality need affine cell maps and surface measure on
  faces, which are missing; the discrete trace inequality is the stability
  input of 18.17.

  *Lean target.* Carriers: `MvPolynomial (Fin d) ℝ` restricted to a simplex, `eLpNorm` on the
  simplex and on its faces (the Hausdorff measure `μH[d - 1]` restricted to a face), Mathlib's
  equivalence of norms on finite-dimensional spaces. Conjuncts: (i) the local inverse estimate on an
  affine cell with the explicit power of $h_K$; (ii) the discrete trace inequality on a face; (iii)
  the global form on quasi-uniform meshes; (iv) the one-dimensional examples. Pitfall: the powers
  $h_K^{d(1/p-1/q)}$ involve `ENNReal.toReal` of $1/p$; at $p=\infty$ the exponent must be read with
  $1/\infty=0$, which `ENNReal.toReal` gives, but a real exponent written as $1/p.toReal$ would be
  junk. Statable at the pins for (i), (ii) and (iv) on a single simplex; (iii) needs the mesh of
  18.10. A dependency of 18.17. NASC: no declaration.

* **18.13. Energy norm error estimate.** Let $a(v,w)=\int_\Omega
  (A\nabla v)\cdot\nabla w\,dx$ with $A$ bounded and uniformly positive
  definite, let $u\in H^1_0(\Omega)$ solve $a(u,v)=(f,v)$ for all $v\in
  H^1_0(\Omega)$, and let $u_h\in V_{h,0}$ be the Galerkin solution for the
  Lagrange space of degree $k$. Then
  $\|\nabla(u-u_h)\|_{0,\Omega}\le(\|a\|/\alpha)
  \inf_{v_h\in V_{h,0}}\|\nabla(u-v_h)\|_{0,\Omega}$, the error tends to
  zero as $h\to0$, and if $u\in H^{1+r}(\Omega)$ with $0<r\le k$, then
  $$\|\nabla(u-u_h)\|_{0,\Omega}\le C\Bigl(\sum_Kh_K^{2r}
  |u|^2_{1+r,K}\Bigr)^{1/2}\le Ch^r|u|_{1+r,\Omega}.$$

  *Assessment.* Lax–Milgram and projection supply well-posedness and the
  energy-space framework. The selected estimate also needs finite-element
  interpolation at the given order and the shape-regular mesh structure.

  *Lean target.* Carriers: `TauCeti.W1p0 μ Ω 2`, `TauCeti.PDE.energyFormH1`,
  `TauCeti.PDE.IsWeakSolutionDirichlet`, and the Lagrange spaces of 18.10 as finite-dimensional
  submodules. Conjuncts: (i) the energy best-approximation bound; (ii) convergence as $h\to0$ for a
  family whose spaces approximate $H^1_0$; (iii) the rate $h^r$ for $u\in H^{1+r}$. Pitfall:
  non-integer $r$ needs fractional Sobolev spaces; the integer case $r\in\{1,\dots,k\}$ is the
  statable one. Depends on 18.3 and 18.10. NASC: `NASC.galerkin_energy_error_le`
  (`NASC/Galerkin.lean`) states the abstract energy-norm best approximation for a symmetric positive
  semidefinite form, in squared form (no square roots), proved; (ii) and (iii) need the mesh
  infrastructure of 18.10 and have no declaration.

* **18.14. The Aubin–Nitsche duality argument.** In the setting of 18.13,
  suppose that the adjoint problem has the **smoothing property**: for every
  $g\in L^2(\Omega)$ the solution $z_g\in H^1_0(\Omega)$ of $a(v,z_g)=(v,g)$
  for all $v$ satisfies $\|z_g\|_{1+s,\Omega}\le C\ell_\Omega^2\|g\|_{0,\Omega}$
  for some $s\in(0,1]$. Then
  $$\|u-u_h\|_{0,\Omega}\le C\,h^s\ell_\Omega^{1-s}
  \|\nabla(u-u_h)\|_{0,\Omega},$$
  with $C$ depending linearly on $\|a\|/(\alpha C_{\mathrm{PF}})$. On a
  convex domain ($s=1$) and with $u\in H^{k+1}(\Omega)$ this gives
  $\|u-u_h\|_{0,\Omega}\le Ch^{k+1}|u|_{k+1,\Omega}$. In general the
  Galerkin solution is not quasi-optimal in $L^2$.

  *Assessment.* The dual weak problem is expressible with existing elliptic
  theory. The selected bound combines its smoothing estimate and Galerkin
  orthogonality to gain an order in the weaker norm.

  *Lean target.* Carriers: as in 18.13, with `Lp ℝ 2` and the inclusion of $H^1_0$ in $L^2$
  (`TauCeti.W1p0.valueL`). Conjuncts: (i) the abstract duality estimate from Galerkin orthogonality
  and an approximation property of the dual solutions; (ii) the rate $h^s$ under the smoothing
  property; (iii) the convex case $h^{k+1}$, from 18.7(i). Depends on 18.7 and 18.13. NASC:
  `NASC.norm_weak_galerkinError_le_of_dualApproximation` (`NASC/Galerkin.lean`) states (i) and is
  proved; (ii) and (iii) have no declaration.

### Nonconforming and discontinuous Galerkin methods

* **18.17. Symmetric interior penalty.** Let $V_h$ be the broken space of
  piecewise $\mathbb P_k$ functions, $k\ge1$. Let $\mathcal F_h$ be the set
  of all faces, with jumps $[v]$ and averages $\{v\}$ (on a boundary face,
  the trace), and let $\eta_0>0$. The **SIPG form** is
  $$a_h(v,w)=\sum_K\int_K\nabla v\cdot\nabla w
  -\sum_{F\in\mathcal F_h}\int_F\bigl(\{\nabla v\}\cdot n_F[w]
  +\{\nabla w\}\cdot n_F[v]\bigr)
  +\sum_{F\in\mathcal F_h}\frac{\eta_0}{h_F}\int_F[v][w],$$
  with norm $\|v\|_h^2=\|\nabla_hv\|_{0,\Omega}^2+\sum_Fh_F^{-1}
  \|[v]\|^2_{0,F}$. Let $c_{\mathrm{tr}}$ be the constant in the discrete
  trace inequality $\|n_F\cdot\nabla v|_K\|_{0,F}\le c_{\mathrm{tr}}h_F^{-1/2}
  \|\nabla v\|_{0,K}$, and let $n_\partial$ bound the number of faces of a
  cell ($n_\partial=d+1$ for simplices). If $\eta_0>n_\partial c_{\mathrm{tr}}^2$,
  then
  $$a_h(v,v)\ge\frac{\eta_0-n_\partial c_{\mathrm{tr}}^2}{1+\eta_0}\,
  \|v\|_h^2\qquad\text{for all }v\in V_h ,$$
  and the discrete problem $a_h(u_h,w)=(f,w)$ for all $w\in V_h$ is well
  posed. If, in addition, $u\in H^{1+r}(\Omega)$ with $r>\frac12$ and
  $t=\min(k,r)$, then in the norm $\|\cdot\|_h$ augmented by
  $\sum_Kh_K\|\nabla v|_K\|^2_{0,\partial K}$,
  $$\|u-u_h\|\le C\Bigl(\sum_Kh_K^{2t}|u|^2_{1+t,K}\Bigr)^{1/2},$$
  and, under the smoothing property of 18.14 with $s\in(\frac12,1]$,
  $\|u-u_h\|_{0,\Omega}\le Ch^s\ell_\Omega^{1-s}\|u-u_h\|$, with the
  augmented norm on the right. Here $C$ depends on $\eta_0$ as well.

  *Assessment.* The missing SIPG analysis needs broken traces, face jumps,
  penalty coercivity and a discrete method with consistency and approximation
  bounds.

  *Lean target.* Carriers: a Hilbert space for the broken space, the mesh of 18.10, and for face
  integrals the Hausdorff measure on faces. New definitions: the broken space of piecewise
  polynomials on a mesh, face jumps and averages, the SIPG form and its norm. Conjuncts: (i)
  coercivity with the constant $(\eta_0-n_\partial c_{\mathrm{tr}}^2)/(1+\eta_0)$; (ii) well
  posedness; (iii) the energy error bound; (iv) the $L^2$ bound under smoothing. Pitfall: the
  penalty condition is strict, $\eta_0>n_\partial c_{\mathrm{tr}}^2$, and the constant in (i) is $0$
  at equality. Infrastructure: meshes with faces and the discrete trace inequality of 18.12. NASC:
  `NASC.sipgForm` and `NASC.half_add_le_sipgForm` (`NASC/Galerkin.lean`) state an abstract
  coercivity inequality for the SIPG form under a trace bound and a penalty condition, over a
  finite set of faces, proved; (i)–(iv) as stated have no declaration.

### Mixed methods

* **18.18. Saddle point problems: the Babuška–Brezzi theorem.** Let $V$
  and $Q$ be reflexive Banach spaces, let $a$ on $V\times V$ and $b$ on
  $V\times Q$ be bounded bilinear forms, and let $K=\{v\in V:b(v,q)=0\text{
  for all }q\in Q\}$. The problem: find $(u,p)\in V\times Q$ with
  $$a(u,v)+b(v,p)=f(v),\qquad b(u,q)=g(q)\qquad\text{for all }(v,q),$$
  is well posed for all $f\in V'$, $g\in Q'$ if and only if $a$ satisfies
  the two conditions of 18.1 on $K\times K$, with constant $\alpha$, and
  $$\beta:=\inf_{q\ne0}\sup_{v\ne0}\frac{b(v,q)}{\|v\|_V\|q\|_Q}>0$$
  (the **Babuška–Brezzi** or **inf-sup** condition). Then
  $\|u\|_V\le\frac1\alpha\|f\|+\frac1\beta(1+\frac{\|a\|}\alpha)\|g\|$ and
  $\|p\|_Q\le\frac1\beta(1+\frac{\|a\|}\alpha)\|f\|
  +\frac{\|a\|}{\beta^2}(1+\frac{\|a\|}\alpha)\|g\|$.

  *Assessment.* Lax–Milgram addresses the coercive component. The selected
  saddle-point theorem needs stability on the constraint kernel and the
  inf-sup condition for the multiplier.

  *Lean target.* Carriers: `A : V →L[ℝ] StrongDual ℝ V`, `B : V →L[ℝ] StrongDual ℝ Q`, reflexivity
  through `NormedSpace.inclusionInDoubleDual`, the kernel `LinearMap.ker` of $v\mapsto B v$, and the
  project's `NASC.IsMixedSolution`. Conjuncts: (i) well posedness if and only if $a$ satisfies the
  two conditions of 18.1 on $K$ and $\beta>0$; (ii) the two a priori bounds. Pitfall: the
  restriction of $a$ to $K$ must be a form on the closed subspace $K$ with its own dual, not on $V$.
  Depends on 18.1. NASC: `NASC.existsUnique_mixedSolution_of_infSup` (`NASC/Galerkin.lean`) states
  the sufficiency half for $a$ coercive on $K$, `sorry`; (ii) has no declaration.

* **18.19. Mixed Galerkin approximation.** Let $V_h\subset V$ and
  $Q_h\subset Q$ be finite-dimensional and
  $K_h=\{v_h\in V_h:b(v_h,q_h)=0\text{ for all }q_h\in Q_h\}$. The discrete
  problem is well posed if and only if the inf-sup constant $\alpha_h$ of $a$
  on $K_h\times K_h$ and the discrete Babuška–Brezzi constant $\beta_h$ of $b$
  on $V_h\times Q_h$ are positive. A coercive $a$ guarantees $\alpha_h>0$,
  but coercivity of $a$ on $K$ alone does not, since $K_h\not\subset K$ in
  general. Then
  $$\|u-u_h\|_V\le\Bigl(1+\frac{\|a\|}{\alpha_h}\Bigr)\inf_{v_h\in Z_h}
  \|u-v_h\|_V+c_h\inf_{q_h\in Q_h}\|p-q_h\|_Q,$$
  where $Z_h=\{v_h\in V_h:b(v_h,q_h)=b(u,q_h)\text{ for all }q_h\}$, and
  $c_h=0$ if $K_h\subset K$ and $c_h=\|b\|/\alpha_h$ otherwise. The
  pressure error is bounded by $(1+\|a\|/\alpha_h)\|a\|/\beta_h$ times the
  first infimum plus
  $(1+\|b\|/\beta_h+c_h\|a\|/\beta_h)$ times the second. Moreover
  $\inf_{v_h\in Z_h}\|u-v_h\|_V\le(1+\|b\|/\beta_h)\inf_{v_h\in V_h}
  \|u-v_h\|_V$. Hence, if $\alpha_h\ge\alpha_0>0$ and $\beta_h\ge\beta_0>0$
  uniformly in $h$, the method is quasi-optimal in both variables.

  *Assessment.* Subspace and bilinear-form results provide the algebraic
  setting. The gap is discrete saddle-point stability together with the
  coupled velocity and multiplier estimates, including the possibility that
  the discrete kernel is larger than the continuous one.

  *Lean target.* Carriers: as in 18.18, with finite-dimensional submodules and
  `NASC.bestApproximationError`. Conjuncts: (i) discrete well posedness if and only if
  $\alpha_h,\beta_h>0$; (ii) the velocity bound with $c_h$; (iii) the pressure bound; (iv) the
  estimate of $\inf_{Z_h}$ by $\inf_{V_h}$; (v) quasi-optimality under uniform constants. Pitfall:
  $Z_h$ may be empty only if $\beta_h=0$, so (iv) needs $\beta_h>0$ before taking an infimum over
  it. Depends on 18.18. NASC: `NASC.exists_mixed_quasi_optimal_constant` (`NASC/Galerkin.lean`)
  states (v) with a constant depending only on $a$, $b$, $\alpha$ and $\beta$, `sorry`.

* **18.20. Raviart–Thomas elements and the mixed Poisson problem.** The
  **Raviart–Thomas** space of degree $k\in\mathbb N_0$ on a simplex is
  $\mathrm{RT}_k=\mathbb P_k^d+x\,\mathbb P_k$. With normal-moment degrees of
  freedom it is unisolvent, its global space $V_h$ is $H(\mathrm{div})$
  conforming, $\nabla\cdot\mathrm{RT}_k\subset\mathbb P_k$, and the canonical
  interpolant $I^{\mathrm{d}}_K$ satisfies the commuting property
  $\nabla\cdot I^{\mathrm{d}}_Kv=\Pi_K(\nabla\cdot v)$, with $\Pi_K$ the
  $L^2$ projection onto $\mathbb P_k$. For the mixed form of
  $-\nabla\cdot(A\nabla p)=g$, $p=0$ on $\partial\Omega$, with
  $\sigma=-A\nabla p\in H(\mathrm{div};\Omega)$ and $p\in L^2(\Omega)$,
  take $V_h$ and the broken space $Q_h$ of piecewise $\mathbb P_k$
  functions. Then $K_h\subset K$, and the discrete Babuška–Brezzi constant in
  $H(\mathrm{div})\times L^2$ is bounded below by $\beta_\Omega/\ell_\Omega$,
  uniformly in $h$. The errors satisfy
  $\|\sigma-\sigma_h\|_{0,\Omega}\le C\inf\|\sigma-\varsigma_h\|_{0,\Omega}$
  over $\varsigma_h\in V_h$ with $\nabla\cdot\varsigma_h=\Pi_hg$, and
  $\|\nabla\cdot(\sigma-\sigma_h)\|_{0,\Omega}=\|\nabla\cdot\sigma-\Pi_hg\|
  _{0,\Omega}$. For $0<r\le k+1$ and sufficiently smooth $\sigma$, $p$,
  $$\|\sigma-\sigma_h\|_{0,\Omega}+\|\nabla\cdot(\sigma-\sigma_h)\|_{0,\Omega}
  +\|p-p_h\|_{0,\Omega}\le Ch^r\bigl(|\sigma|_{r}+|\nabla\cdot\sigma|_{r}
  +|p|_{r}\bigr),$$
  with the seminorms taken elementwise or over element patches and $C$
  depending on the bounds of $A$ and on $\ell_\Omega$.

  *Assessment.* Polynomial and weak divergence APIs are ingredients. The gap
  is the Raviart–Thomas element with unisolvence, a divergence-commuting
  interpolation and the mixed Poisson error estimate.

  *Lean target.* Carriers: `MvPolynomial (Fin d) ℝ` with `MvPolynomial.totalDegree` and
  `MvPolynomial.pderiv`, and for the global space a weak divergence on `Lp ℝ 2`. New definitions:
  $\mathrm{RT}_k$ as a submodule of `Fin d → MvPolynomial (Fin d) ℝ`, its normal-moment degrees of
  freedom on a simplex, the global space with continuous normal components, and $H(\mathrm{div})$.
  Conjuncts: (i) $\nabla\cdot\mathrm{RT}_k=\mathbb P_k$; (ii) unisolvence; (iii) the commuting
  property; (iv) the discrete inf-sup bound; (v) the error estimates. Infrastructure:
  $H(\mathrm{div};\Omega)$ (the degree $d-1$ case of the SobolevDifferentialForms roadmap on main,
  section 3.6, not yet in TauCeti), meshes, and normal traces on faces. Depends on 18.19. NASC:
  `NASC.exists_raviartThomas_div_eq` (`NASC/FiniteElements.lean`) states (i) on the reference
  space, written as $\mathbb P_k^d+x\,q$ with $q$ homogeneous of degree $k$ (the same space as
  $\mathbb P_k^d+x\,\mathbb P_k$), over a field of characteristic zero, `sorry`.

* **18.21. Stable pairs for the Stokes problem.** For the Stokes problem,
  $V=H^1_0(\Omega)^d$, $Q=L^2_0(\Omega)$ (mean zero) and
  $b(v,q)=-\int_\Omega q\,\nabla\cdot v$; the continuous inf-sup condition
  holds on Lipschitz domains. On shape-regular simplicial families:
  - the **MINI element**, continuous $\mathbb P_1$ velocities enriched by
    one bubble of degree $d+1$ per cell and continuous $\mathbb P_1$
    pressures, satisfies the
    discrete inf-sup condition with $\beta_h\ge\beta_0>0$ independent of
    $h$;
  - the **Taylor–Hood element**, continuous $\mathbb P_2$ velocities and
    continuous $\mathbb P_1$ pressures, satisfies it uniformly in $h$ when
    $d\in\{2,3\}$ and the edges of each cell that are not contained in
    $\partial\Omega$ span $\mathbb R^d$ (in $d=2$: no triangle with two edges
    on $\partial\Omega$; in $d=3$, "at most one face on $\partial\Omega$" does
    not suffice, since the internal edges may be those of one face). For $d=2$
    and smooth solutions, $\|u-u_h\|_{1,\Omega}+\|p-p_h\|_{0,\Omega}\le Ch^s
    (\|u\|_{s+1,\Omega}+\|p\|_{s,\Omega})$ for $0\le s\le2$.

  By 18.19 both pairs are then quasi-optimal.

  *Assessment.* The Stokes form and pressure–velocity pairing can be developed
  from the Sobolev API. The named mesh-dependent pairs need uniform inf-sup
  constants and stability analyses.

  *Lean target.* Carriers: `TauCeti.W1p0 μ Ω 2` componentwise, `Lp ℝ 2` with mean zero,
  `TauCeti.W1p.gradient` for the divergence, `IsLipschitzDomain`, `IsConnected`. Conjuncts: (i) the
  continuous inf-sup condition on bounded connected Lipschitz domains; (ii) MINI is uniformly
  stable; (iii) Taylor–Hood is uniformly stable when the internal edges of each cell span $\mathbb
  R^d$; (iv) the Taylor–Hood error estimate. Infrastructure: (i) needs a right inverse of the
  divergence (Bogovskiĭ's operator), which the SobolevDifferentialForms roadmap on main leaves out
  and no library has; (ii)–(iv) need meshes, bubbles and macroelement arguments. Depends on 18.19.
  NASC: `NASC.exists_divergence_test_of_meanZero` (`NASC/FiniteElements.lean`) states (i), `sorry`.

### Structure-preserving discretization

* **18.22. Finite element de Rham complexes and commuting projections.**
  Let $\Omega\subset\mathbb R^3$ be a Lipschitz domain that is simply
  connected with connected boundary. The **de Rham complex**
  $$\mathbb R\to H^1(\Omega)\xrightarrow{\nabla}H(\mathrm{curl};\Omega)
  \xrightarrow{\nabla\times}H(\mathrm{div};\Omega)\xrightarrow{\nabla\cdot}
  L^2(\Omega)\to0$$
  is exact. On a simplex, the polynomial complex
  $\mathbb R\to\mathbb P_{k+1}\to\mathrm N_k\to\mathrm{RT}_k\to\mathbb P_k\to0$,
  with the Nédélec space $\mathrm N_k$ of the first kind, is exact, and the
  canonical interpolants of the four spaces commute with $\nabla$,
  $\nabla\times$ and $\nabla\cdot$ on sufficiently smooth functions. The
  canonical interpolants are not bounded on the spaces of the complex. On a
  shape-regular family, however, there are operators $J_h$ onto the global
  finite element spaces (Lagrange, Nédélec, Raviart–Thomas, broken
  $\mathbb P_k$), also with boundary conditions, that are projections,
  bounded in $L^p$ uniformly in $h$ for every $p\in[1,\infty]$, quasi-optimal
  in $L^p$, and commute with $\nabla$, $\nabla\times$ and $\nabla\cdot$.
  These **bounded commuting cochain projections** transfer the stability of
  the continuous complex to the discrete one.

  *Assessment.* Differential forms and cochain complexes are available
  separately. The finite-element spaces, subcomplex and bounded commuting
  projection are the missing numerical structure.

  *Lean target.* Carriers: `MvPolynomial (Fin 3) ℝ` with `MvPolynomial.pderiv` for the polynomial
  complex; for the Sobolev complex, the SobolevDifferentialForms roadmap on main (weak exterior
  derivative, the spaces $W^p\Lambda^k$, abstract Hilbert complexes, sections 2–6), none of which is
  in TauCeti at the pin. New definitions: $\mathrm N_k$ as $\mathbb P_k^3$ plus homogeneous fields
  of degree $k+1$ orthogonal to $x$, the canonical interpolants by moments. Conjuncts: (i) exactness
  of the continuous complex on a simply connected Lipschitz domain with connected boundary; (ii)
  exactness of the polynomial complex; (iii) the commuting diagram; (iv) bounded commuting
  projections. Infrastructure: meshes, tangential and normal traces on faces, and the Sobolev de
  Rham complex. NASC: `NASC.exists_gradient_of_curlFree_edgePolynomial` (`NASC/FiniteElements.lean`)
  states exactness of (ii) at $\mathrm N_k$, `sorry`.

## 19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation

[Synopsis](SYNOPSIS.md#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation) · [Coverage inventory](STRUCTURE.md#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation)

The existing weak parabolic theory and continuous compact spectral theory
supply the starting point. The numerical gaps require approximation spaces,
discrete evolution and quantitative error indicators.

Throughout, $(\cdot,\cdot)$ and $\|\cdot\|$ denote the inner product and norm of
$L^2$ on the domain in question, and $\|\cdot\|_s$ the norm of $H^s$. In
items 19.2–19.5 the letter $k$ denotes a time step and $r$ an order of
spatial accuracy.

### Parabolic problems

* **19.2. Ritz projection and semidiscrete Galerkin method.** The **Ritz** (or
  elliptic) **projection** $R_h:H^1_0(\Omega)\to S_h$ is defined by
  $(\nabla R_hw,\nabla\chi)=(\nabla w,\nabla\chi)$ for all $\chi\in S_h$. It
  satisfies $\|\nabla R_hw\|\le\|\nabla w\|$ and
  $$\|R_hw-w\|+h\|\nabla(R_hw-w)\|\le Ch^s\|w\|_s,\qquad
  w\in H^s\cap H^1_0,\ 1\le s\le r .$$
  The **semidiscrete Galerkin approximation** is the function
  $u_h:[0,\infty)\to S_h$ with $u_h(0)=v_h\in S_h$ and
  $(u_{h,t},\chi)+(\nabla u_h,\nabla\chi)=(f,\chi)$ for all $\chi\in S_h$ and
  $t>0$. If $v=0$ on $\partial\Omega$, then for all $t\ge0$
  $$\|u_h(t)-u(t)\|\le\|v_h-v\|+Ch^r\Bigl(\|v\|_r+\int_0^t\|u_t\|_r\,ds\Bigr).$$
  With $v_h=R_hv$ or $v_h$ the $L^2$ projection of $v$ onto $S_h$, the first
  term is at most $Ch^r\|v\|_r$, so the error is $O(h^r)$ uniformly on bounded
  time intervals.

  *Assessment.* Partly covered. TauCeti proves that the finite-dimensional
  autonomous semidiscrete problem is uniquely solvable for continuous forcing,
  and the continuous weak theory of 19.1. The Ritz projection and its
  estimates, and the spatial error bound, are the selected gap.

  *Scope.* The targets are the Ritz estimate and the time-dependent error in
  the spatial $L^2$ norm.

  *Lean target.* Carriers at the pins: `TauCeti.W1p0 μ Ω 2` for
  $H^1_0(\Omega)$, `TauCeti.Wkp μ Ω 2 s` for $H^s(\Omega)$, the Gelfand triple
  through `ContinuousLinearMap.gelfandDual`, and
  `TauCeti.PDE.existsUnique_galerkinSolution` for the semidiscrete solution.
  New definitions: an approximation family (for each $h\in(0,1)$ a
  finite-dimensional submodule $S_h$ of `W1p0` with the order-$r$ approximation
  inequality as a hypothesis, not a construction); the Ritz projection $R_h$,
  the orthogonal projection onto $S_h$ for the Dirichlet inner product
  $(\nabla\cdot,\nabla\cdot)$ (`Submodule.starProjection` once `W1p0` carries
  that inner product). Conjuncts: (i) $\|\nabla R_hw\|\le \|\nabla w\|$; (ii)
  the Ritz estimate for $1\le s\le r$, which needs the Aubin–Nitsche duality
  and $H^2$ regularity on a smooth domain as hypotheses; (iii) the $L^2$ error
  bound at every $t\ge0$, with $u$ a strong solution whose $u_t$ is integrable
  with values in $H^r$. Pitfall: the time integral $\int_0^t\|u_t\|_r$ must be
  a lower Lebesgue integral in $\mathbb R_{\ge0} \cup\{\infty\}$, or carry an
  integrability hypothesis, since a Bochner integral of a non-integrable
  function is $0$. Statable at the pins with the approximation property,
  elliptic regularity and the solution regularity as hypotheses; the finite
  element spaces that satisfy them are missing. NASC: `ritz_parabolic_error_le`
  (TimeDependentGalerkin.lean) states the semidiscrete error bound
  $\|u_h(T)-u(T)\|\le\|u_h(0)-u(0)\|+\|\rho(0)\|+\|\rho(T)\|+\int_0^T\|\rho'\|$ with
  $\rho=R_hu-u$, for the solution equation $u'+Au=F$, a Galerkin solution in $S_h$ and the Ritz
  condition, under a positive operator and without rates; it is proved from the energy lemma
  `norm_le_add_integral_of_inner_le`, which is `sorry`.

* **19.3. Backward Euler and Crank–Nicolson Galerkin methods.** Let $k>0$ be
  a time step, $t_n=nk$, $\bar\partial U^n=(U^n-U^{n-1})/k$, and $U^0=v_h$.
  The **backward Euler Galerkin method** seeks $U^n\in S_h$ with
  $(\bar\partial U^n,\chi)+(\nabla U^n,\nabla\chi)=(f(t_n),\chi)$ for all
  $\chi\in S_h$, $n\ge1$. The **Crank–Nicolson Galerkin method** seeks
  $U^n\in S_h$ with $(\bar\partial U^n,\chi)+(\nabla\hat U^n,\nabla\chi)
  =(f(t_{n-1/2}),\chi)$, where $\hat U^n=\tfrac12(U^n+U^{n-1})$ and
  $t_{n-1/2}=(n-\tfrac12)k$. Both schemes have a unique solution for every
  $k>0$. Assume $v=0$ on $\partial\Omega$ and $\|v_h-v\|\le Ch^r\|v\|_r$. Then
  for all $n\ge0$ the backward Euler solution satisfies
  $$\|U^n-u(t_n)\|\le Ch^r\Bigl(\|v\|_r+\int_0^{t_n}\|u_t\|_r\,ds\Bigr)
  +k\int_0^{t_n}\|u_{tt}\|\,ds ,$$
  and the Crank–Nicolson solution satisfies
  $$\|U^n-u(t_n)\|\le Ch^r\Bigl(\|v\|_r+\int_0^{t_n}\|u_t\|_r\,ds\Bigr)
  +Ck^2\int_0^{t_n}\bigl(\|u_{ttt}\|+\|\Delta u_{tt}\|\bigr)\,ds .$$
  No relation between $k$ and $h$ is required.

  *Assessment.* The elliptic and semidiscrete estimates of 19.2 are
  prerequisites. The gap controls the interaction of spatial projection error
  and the temporal error of the two fully discrete schemes.

  *Lean target.* Carriers: those of 19.2, with the step sequence
  $U:\mathbb N\to S_h$. New definitions: the backward Euler and Crank–Nicolson
  recursions as predicates on $U$ (a $\theta$-scheme with
  $\theta\in\{1,\tfrac12\}$), and existence and uniqueness of each step by
  positivity of $I+\theta k A_h$ on $S_h$. Conjuncts: (i) unique solvability
  for every $k>0$; (ii) the backward Euler bound, whose time term
  $k\int_0^{t_n}\|u_{tt}\|$ carries no constant; (iii) the Crank–Nicolson
  bound; both for all $n\ge0$, under $\|v_h-v\|\le Ch^r\|v\|_r$, with no
  relation between $k$ and $h$. Every time integral is a lower Lebesgue
  integral or carries integrability. Depends on 19.2. NASC:
  `parabolic_timeStepping_error_le` (TimeDependentGalerkin.lean), sorry; it
  states the accumulation of a uniform local defect $\delta$ into $n\delta$ for
  a positive operator and every $\theta\in[\tfrac12,1]$, an abstract ingredient only.

* **19.4. Nonsmooth initial data.** Let $f=0$, $v\in L^2(\Omega)$, and let
  $u_h$ be the semidiscrete approximation of 19.2 with $v_h=P_hv$, the
  $L^2$-orthogonal projection of $v$ onto $S_h$. Then
  $$\|u_h(t)-u(t)\|\le Ch^rt^{-r/2}\|v\|\qquad\text{for all }t>0,$$
  and $t$ may be replaced by $t+h^2$ on the right. For piecewise linear
  elements ($r=2$) this is $\|u_h(t)-u(t)\|\le Ch^2t^{-1}\|v\|$: the method
  converges with full order for every $t>0$ although $v$ has no smoothness.

  *Assessment.* The weak heat solution and semigroup regularization give the
  analytic setting. The selected bound compares smoothing of the exact and
  discrete semigroups for rough initial data.

  *Lean target.* Carriers: `TauCeti.PDE.dirichletEigenvalue` and its Hilbert
  basis of eigenfunctions give the solution operator $E(t)$ of the Dirichlet
  heat equation as a spectral series on $L^2(\Omega)$; the discrete operator
  $E_h(t)=\exp(-tA_h)P_h$ is `NormedSpace.exp` on the finite-dimensional $S_h$.
  Conjunct: for $v\in L^2(\Omega)$, $t>0$ and $v_h=P_hv$, $\|u_h(t)- u(t)\|\le
  Ch^rt^{-r/2}\|v\|$, with $C$ independent of $v$, $h$, $t$. The hypotheses are
  those of 19.2 together with the $L^2$ projection $P_h$. Pitfall: the factor
  $t^{-r/2}$ must not be written as a real power at $t=0$; quantify over $t>0$.
  Depends on 19.2. NASC: `exists_parabolic_smoothing_constant`
  (TimeDependentGalerkin.lean), sorry; it is a finite-dimensional surrogate
  bounding the semigroup difference by $C/t$ times the difference of the
  inverse operators, which is the operator form of the proof (Thomée's Lemma
  3.3), not the theorem.

* **19.5. Discontinuous Galerkin time stepping.** Let $\mathcal H$ be a real
  Hilbert space and $A$ a self-adjoint positive definite operator on
  $\mathcal H$ with compact inverse; write $|w|_s=\|A^{s/2}w\|$ and
  $\mathcal D=\mathcal D(A^{1/2})$. Consider $u'+Au=f$, $u(0)=v$. Let
  $0=t_0<t_1<\cdots$, $J_n=(t_{n-1},t_n]$, $k_n=t_n-t_{n-1}$, and let $q\ge1$.
  Let $\mathcal S_k$ be the space of functions $X:[0,\infty)\to\mathcal H$ whose
  restriction to each $J_n$ is a polynomial of degree at most $q-1$ in $t$
  with coefficients in $\mathcal D$; write $X^n=X(t_n)$ and $X^n_+$ for the
  limit from above at $t_n$. The **discontinuous Galerkin method** seeks
  $U\in\mathcal S_k$ with $U^0=v$ and, for each $n\ge1$,
  $$\int_{J_n}\bigl((U',X)+(A^{1/2}U,A^{1/2}X)\bigr)\,dt+(U^{n-1}_+,X^{n-1}_+)
  =(U^{n-1},X^{n-1}_+)+\int_{J_n}(f,X)\,dt$$
  for all $X$ in the restriction of $\mathcal S_k$ to $J_n$. This problem has
  a unique solution. For $q=1$ it is the scheme
  $(I+k_nA)U^n=U^{n-1}+\int_{J_n}f\,dt$, and for $q=2$ and $f=0$ it is
  $U^n=r(k_nA)U^{n-1}$ with $r$ the $(2,1)$ Padé approximant of $e^{-\lambda}$
  (subdiagonal, numerator of degree $1$). The nodal errors satisfy
  $$\|U^N-u(t_N)\|\le C\Bigl(\sum_{n=1}^Nk_n^{2q}\int_{J_n}|u^{(q)}|_1^2\,dt
  \Bigr)^{1/2},$$
  and for $q\ge2$, with $k=\max_nk_n$, the superconvergence estimate
  $$\|U^N-u(t_N)\|\le Ck^{q-1}\Bigl(\sum_{n=1}^Nk_n^{2q}\int_{J_n}
  |u^{(q)}|_{2q-1}^2\,dt\Bigr)^{1/2}$$
  holds; thus the nodal error is $O(k^{2q-1})$ for constant steps and smooth
  compatible solutions.

  *Assessment.* Parabolic weak solvability covers the continuum problem. The
  selected theorem constructs the discontinuous time approximation, including
  jump terms and the resulting error bounds.

  *Lean target.* Carriers: a real Hilbert space $\mathcal H$ and a self-adjoint
  positive operator with compact inverse, given through a Hilbert basis of
  eigenvectors with eigenvalues $\lambda_j\to\infty$ (as in
  `IsCoercive.formSolutionOperator`), which turns the scheme into decoupled
  scalar problems. New definitions: the space $\mathcal S_k$ of piecewise
  polynomials in time of degree $<q$ with values in $\mathcal D(A^{1/2})$, and
  the DG predicate. Conjuncts: (i) unique solvability; (ii) the reductions for
  $q=1$ and for $q=2$, $f=0$, with $r(\lambda)=(1-\lambda/3)/(1+2\lambda/3+
  \lambda^2/6)$; (iii) the nodal error bound; (iv) the superconvergence bound
  for $q\ge2$. Pitfall: $|w|_s$ is infinite off $\mathcal D(A^{s/2})$, so the
  norms in (iii)–(iv) take values in $\mathbb R_{\ge0}\cup\{\infty\}$. NASC:
  `IsDGHeatStep` and `exists_dgHeatStep_error_le_pow`
  (TimeDependentGalerkin.lean), sorry; they state only the scalar step on
  $[0,1]$ for $z\in[0,1]$, with local error $O(z^{2q})$, the ingredient behind
  (iv).

### Spectral methods

For items 19.7–19.11, $I=(-1,1)$ and, for $\alpha,\beta>-1$,
$\omega^{\alpha,\beta}(x)=(1-x)^\alpha(1+x)^\beta$; $\|\cdot\|_{\omega}$ is the
norm of $L^2_\omega(I)$, and $\mathbb P_N$ the polynomials of degree at most
$N\ge1$. The Legendre case is $\alpha=\beta=0$ and the Chebyshev case
$\alpha=\beta=-\tfrac12$. The **non-uniformly weighted Sobolev space**
$B^m_{\alpha,\beta}(I)$ consists of the $u$ with
$\partial_x^ju\in L^2_{\omega^{\alpha+j,\beta+j}}(I)$ for $0\le j\le m$.
The **Legendre–Gauss–Lobatto (LGL) nodes** are $x_0=-1<x_1<\cdots<x_N=1$,
the interior ones being the zeros of $L_N'$; with the associated weights
$w_j>0$ the quadrature $\sum_jw_j\varphi(x_j)$ is exact on
$\mathbb P_{2N-1}$ (section 12), and $\langle u,v\rangle_N=\sum_{j=0}^N
u(x_j)v(x_j)w_j$ is the **discrete inner product**. $I_N$ denotes
polynomial interpolation in $\mathbb P_N$ at the nodes indicated.

* **19.6. Fourier approximation.** Let $X_N=\mathrm{span}\{e^{ijx}:|j|\le N\}$
  on $(0,2\pi)$, let $P_N$ be the $L^2$-orthogonal projection onto $X_N$ (the
  truncated Fourier series), and let $H^m_p$ be the periodic Sobolev space
  with norm $\|u\|_m=(\sum_j(1+j^2)^m|\hat u_j|^2)^{1/2}$ and seminorm
  $|u|_m=(\sum_j|j|^{2m}|\hat u_j|^2)^{1/2}$ (real $m\ge0$).
  - (Bernstein inverse inequality.) $\|\varphi^{(r)}\|\le N^r\|\varphi\|$ for
    all $\varphi\in X_N$ and integers $r\ge1$.
  - (Projection.) For $u\in H^m_p$ and $0\le\mu\le m$,
    $\|P_Nu-u\|_\mu\le CN^{\mu-m}|u|_m$, with $C$ depending only on $\mu$; and
    if $m>\tfrac12$, $\max_x|(P_Nu-u)(x)|\le\sqrt{2/(2m-1)}\,N^{1/2-m}|u|_m$.
  - (Interpolation.) Let $I_Nu$ be the trigonometric interpolant of $u$ at
    $x_j=\pi j/N$, $0\le j\le 2N-1$, in the space spanned by $e^{ijx}$,
    $|j|<N$, and $\cos Nx$. If $u\in H^m_p$ with $m>\tfrac12$, then
    $\|\partial_x^l(I_Nu-u)\|\le CN^{l-m}|u|_m$ for $0\le l\le m$, with $C$
    depending only on $l$ and $m$.

  *Assessment.* Mathlib has the Fourier Hilbert basis and Parseval's identity
  on the additive circle. The selected rates need finite frequency cutoffs,
  inverse and interpolation bounds in periodic Sobolev norms.

  *Lean target.* Carriers at the pins: `fourierBasis`, `fourierCoeff`,
  `hasSum_sq_fourierCoeff` on `AddCircle (2 * π)`. New definitions: the
  periodic Sobolev norm $\|u\|_{H^m_p}^2=\sum_j(1+j^2)^m|\hat u_j|^2$ as an
  extended nonnegative sum, the truncation $P_N$, and the interpolant $I_N$ at
  $2N$ equispaced nodes with $\tilde u_N=\tilde u_{-N}$. Conjuncts: (i) the
  Bernstein inequality on $X_N$; (ii) $\|P_Nu-u\|_\mu\le CN^{\mu-m}|u|_m$ for
  $0\le\mu\le m$; (iii) the maximum-norm bound with the corrected constant
  $\sqrt{2/(2m-1)}$, for $m>1/2$; (iv) the interpolation estimate for $m>1/2$.
  Pitfall: for $u\notin H^m_p$ the right-hand sides are infinite; use `ENNReal`
  sums, or state the hypothesis as summability. Statable and provable at the
  pins. NASC: `fourier_tail_sobolev_sq_le` (TimeDependentGalerkin.lean), proved;
  it is the coefficient form of the tail estimate behind (ii).

* **19.8. Orthogonal projection errors.** Let $\pi_N^{\alpha,\beta}$ be the
  $L^2_{\omega^{\alpha,\beta}}$-orthogonal projection onto $\mathbb P_N$ (the
  truncated Jacobi series).
  - For integers $0\le l\le m$ there is $C$, depending only on $\alpha$,
    $\beta$ and $m$, such that for all $N\ge m-1$ and $u\in B^m_{\alpha,\beta}(I)$
    $$\|\partial_x^l(\pi_N^{\alpha,\beta}u-u)\|_{\omega^{\alpha+l,\beta+l}}\le
    CN^{l-m}\|\partial_x^mu\|_{\omega^{\alpha+m,\beta+m}} .$$
    In particular (Legendre and Chebyshev) $\|u-\pi_Nu\|_\omega\le
    CN^{-m}\|u^{(m)}\|_{\omega}$ for $u\in H^m_\omega(I)$, $N\ge m-1$.
  - In the unweighted Legendre case the truncation error in $H^l$, $l\ge1$, is
    not of optimal order: $\|u-\pi_Nu\|_{H^l}\le CN^{2l-1/2-m}\|u^{(m)}\|$ for
    $1\le l\le m\le N+1$, and the exponent cannot be improved to $l-m$ in
    general (for $u=L_{N+1}-L_{N-1}$, $\|\partial_x(\pi_Nu-u)\|\ge
    c\sqrt N\|\partial_xu\|$).
  - Optimal $H^1$ approximation with boundary conditions: let
    $\mathbb P_N^0=\{\varphi\in\mathbb P_N:\varphi(\pm1)=0\}$ and let
    $P^{1,0}_N$ be the orthogonal projection of $H^1_0(I)$ onto $\mathbb P^0_N$
    for the inner product $\int_Iu'v'\,dx$. For $u\in H^m(I)\cap H^1_0(I)$,
    $m\ge1$, $N\ge m-1$ and $k\in\{0,1\}$,
    $\|u-P^{1,0}_Nu\|_{H^k}\le CN^{k-m}\|u^{(m)}\|$.

  *Assessment.* Not covered. Mathlib has the shifted Legendre polynomials and
  the Chebyshev polynomials as algebraic objects, but not their orthogonality
  in weighted $L^2$, the Jacobi polynomials, or projection errors. The Jacobi
  projection estimate is the approximation result on which the spectral
  Galerkin estimates 19.9–19.11 rest.

  *Scope.* The targets are the weighted Jacobi projection estimate (first
  claim) and the $H^1_0$ projection estimate (third claim); the suboptimality
  example is a check.

  *Lean target.* Carriers at the pins: `Polynomial.shiftedLegendre`,
  `Polynomial.Chebyshev.T`, `Polynomial.derivative`, and `MeasureTheory.Lp` for
  the weighted measure `volume.withDensity` of $\omega^{\alpha,\beta}=
  (1-x)^\alpha(1+x)^\beta$ on $(-1,1)$. New definitions: the Jacobi polynomials
  (left by the general orthogonal-polynomial roadmap to a sibling roadmap), the
  weighted space $B^m_{\alpha,\beta}(I)$ as the functions whose derivatives up
  to order $m$ lie in the shifted-weight $L^2$ spaces, and
  $\pi_N^{\alpha,\beta}$ as `Submodule.starProjection` onto $\mathbb P_N$ in
  $L^2_{\omega^{\alpha, \beta}}$. Conjuncts: (i) for $0\le l\le m$ and
  $N\ge m-1$ the bound $CN^{l-m}$ with $C=C(\alpha,\beta,m)$; (ii) the $H^1_0$
  projection estimate for $k\in\{0,1\}$. Hypotheses $\alpha,\beta>-1$. Pitfall:
  the weighted norms are infinite off $B^m_{\alpha,\beta}$; use lower Lebesgue
  integrals. Statable at the pins once the Jacobi family exists; no NASC
  declaration.

* **19.10. Legendre–Galerkin method.** Let $\alpha\ge0$, $f$ continuous on
  $[-1,1]$, and let $u\in H^1_0(I)$ be the weak solution of $-u''+\alpha u=f$,
  $u(\pm1)=0$. The **Legendre–Galerkin approximation** is the
  $u_N\in\mathbb P^0_N$ with
  $\int_Iu_N'v'\,dx+\alpha\int_Iu_Nv\,dx=\int_I(I_Nf)v\,dx$ for all
  $v\in\mathbb P^0_N$, where $I_N$ is LGL interpolation. If
  $\partial_xu\in B^{m-1}_{0,0}(I)$ and $f\in B^k_{-1,-1}(I)$ for fixed
  $m,k\ge1$ and $N\ge\max(m,k)-1$, then
  $$\|u-u_N\|_1\le c\sqrt{\tfrac{(N-m+1)!}{N!}}(N+m)^{\frac{1-m}2}
  \|\partial_x^mu\|_{\omega^{m-1,m-1}}+c\sqrt{\tfrac{(N-k+1)!}{N!}}
  (N+k)^{-\frac{k+1}2}\|\partial_x^kf\|_{\omega^{k-1,k-1}},$$
  with $c$ depending on $m$ and $k$ but not on $N$, $f$ and $u$. For fixed $m$ and $k$
  the right-hand side is $O(N^{1-m}+N^{-k})$: the convergence rate is limited
  only by the regularity of $u$ and $f$.

  *Assessment.* The orthogonal polynomial and coercive form APIs supply
  ingredients. The missing result constructs the space with zero endpoint
  values and proves its spectral Galerkin error estimate.

  *Lean target.* Carriers: `Polynomial` of degree at most $N$ with
  $\varphi(\pm1)=0$, interval integrals for the forms, `Lagrange.interpolate`
  at the LGL nodes for $I_Nf$. New definitions: the LGL nodes (zeros of
  $(1-x^2)L_N'$) and the Legendre polynomials on $[-1,1]$ (a rescaling of
  `Polynomial.shiftedLegendre`). Conjuncts: (i) existence and uniqueness of
  $u_N$ for $\alpha\ge0$; (ii) the $H^1$ error bound with the factorial factor
  and the weighted norms of 19.8; (iii) the bound on the factor from Remark
  4.14. Depends on 19.8 and 19.9 (the LGL interpolation estimate) and on the
  first Strang lemma. Pitfall: the weighted derivative norms are infinite for
  nonsmooth data; quantify over $u\in B^m$. NASC:
  `existsUnique_legendreGalerkin` and `exists_legendreGalerkin_sobolev_error_bound`
  with `legendre` (from `Polynomial.shiftedLegendre`) (TimeDependentGalerkin.lean), sorry; the error
  bound is the case $m=2$, $k=2$ only.

### Eigenvalue approximation

* **19.13. Variational eigenvalue problems and the min–max principle.** Let
  $V\subset H$ be real Hilbert spaces, let $a$ be a symmetric bounded bilinear
  form on $V$ with $a(v,v)\ge\alpha\|v\|_V^2$ ($\alpha>0$), and let $b$ be a
  symmetric bounded bilinear form that is an inner product on $H$. Let
  $T:H\to H$ be the solution operator, $Tf\in V$ and $a(Tf,v)=b(f,v)$ for all
  $v\in V$, and assume $T$ compact. The eigenvalues of
  $$a(u,v)=\lambda\,b(u,v)\quad\text{for all }v\in V,\qquad u\in V\setminus\{0\},$$
  are the reciprocals of the positive eigenvalues of $T$; they are positive
  with finite multiplicities and are listed with multiplicity as
  $\lambda^{(1)}\le\lambda^{(2)}\le\cdots$, with $b$-orthonormal
  eigenfunctions $u^{(k)}$. The **min–max principle** holds:
  $$\lambda^{(k)}=\min_{E\subset V,\ \dim E=k}\ \max_{v\in E\setminus\{0\}}
  \frac{a(v,v)}{b(v,v)} .$$
  For a finite-dimensional $V_h\subset V$, the **Galerkin eigenvalues**
  $\lambda_h^{(1)}\le\cdots\le\lambda_h^{(\dim V_h)}$ of $a(u_h,v)=\lambda_h
  b(u_h,v)$, $v\in V_h$, satisfy the same formula with $V$ replaced by $V_h$.
  Consequently a conforming Galerkin method approximates every eigenvalue
  from above: $\lambda^{(k)}\le\lambda_h^{(k)}$ for $1\le k\le\dim V_h$.

  *Assessment.* Partly covered. TauCeti gives the compact variational
  eigenproblem through the form solution operator, the concrete Dirichlet
  min–max theorem and finite-dimensional Courant–Fischer. The selected claims
  are the general variational min–max on the energy space and the conforming
  discrete upper bounds.

  *Scope.* The target is the variational characterization for the energy
  eigenproblem and its use with conforming finite-dimensional subspaces.

  *Lean target.* Carriers at the pins: `IsCoercive` and
  `IsCoercive.formSolutionOperator` with
  `hasEigenvalue_formSolutionOperator_iff`, the pattern of
  `TauCeti.PDE.isLeast_dirichletEigenvalue`, and
  `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` for the discrete
  problem. Conjuncts: (i) the eigenvalues are the reciprocals of the positive
  eigenvalues of $T$, positive, of finite multiplicity, with $b$-orthonormal
  eigenfunctions; (ii) the min–max formula over $k$-dimensional $E\le V$; (iii)
  the same formula on a finite-dimensional $V_h\le V$; (iv)
  $\lambda^{(k)}\le\lambda^{(k)}_h$ for $1\le k\le\dim V_h$. The pivot inner
  product $b$ is a hypothesis on a bilinear form, so $H$ carries two inner
  products; the cleanest carrier takes $H$ with the inner product $b$. Pitfall:
  when $V_h$ has dimension less than $k$ the discrete min–max is over an empty
  family, and a real infimum gives $0$, which would make (iii) false; restrict
  to $k\le\dim V_h$. Statable and largely provable at the pins. NASC:
  `exists_variationalEigenvalue_minmax` (VariationalEigenproblems.lean), sorry;
  it states (ii) only.

* **19.14. Convergence and absence of spurious modes.** In the setting of
  19.13 let $T_h:H\to H$ be the discrete solution operator, $T_hf\in V_h$ and
  $a(T_hf,v)=b(f,v)$ for $v\in V_h$; so $T_h=P_hT$ with $P_h$ the
  $a$-orthogonal projection onto $V_h$. For $k\ge1$ let $m(k)$ be the
  dimension of the span of the first $k$ distinct eigenspaces, and use the
  **gap** $\hat\delta(E,F)=\max(\delta(E,F),\delta(F,E))$,
  $\delta(E,F)=\sup_{u\in E,\|u\|_H=1}\inf_{v\in F}\|u-v\|_H$. Say the
  discrete problem **converges** if for every $\varepsilon>0$ and $k$ there is
  $h_0$ such that for $h<h_0$, $\max_{i\le m(k)}|\lambda^{(i)}-\lambda_h^{(i)}|
  \le\varepsilon$ and the gap between $\bigoplus_{i\le m(k)}E^{(i)}$ and
  $\bigoplus_{i\le m(k)}E^{(i)}_h$ is at most $\varepsilon$.
  - The discrete problem converges if and only if $\|T-T_h\|_{\mathcal L(H)}
    \to0$ as $h\to0$.
  - If $T$ is compact from $H$ to $V$ and $P_hw\to w$ in $H$ for every $w\in V$,
    then $\|T-T_h\|_{\mathcal L(H)}\to0$.
  - More generally, let $T$ and $T_h$ be compact operators on a Hilbert space
    with $\|T-T_h\|\to0$. Then every compact subset of the resolvent set of $T$
    lies in the resolvent set of $T_h$ for small $h$ (no spurious modes); each
    nonzero eigenvalue $\mu$ of $T$ of algebraic multiplicity $m$ is the limit
    of exactly $m$ eigenvalues of $T_h$ counted with algebraic multiplicity;
    and the gap between the corresponding generalized eigenspaces tends to $0$.

  *Assessment.* Not covered. Compactness, strong-to-norm convergence after
  composition with a compact operator, and spectral perturbation ingredients
  are available. The missing approximation theorem controls the discrete
  eigenspaces and excludes spurious modes.

  *Lean target.* Carriers at the pins: `IsCompactOperator`,
  `ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator` and
  `banach_steinhaus` (for Proposition 7.6), `spectrum`, and
  `Submodule.starProjection` for the gap between eigenspaces. New definitions:
  the gap $\hat\delta(E,F)$ between closed subspaces, and "convergence of the
  discrete eigenvalue problem" as the conjunction of convergence of eigenvalues
  with multiplicity, convergence of eigenspaces in gap, and absence of spurious
  eigenvalues. Conjuncts: (i) convergence holds if and only if $\|T-T_h\|\to0$;
  (ii) compactness of $T$ into $V$ and strong convergence of $P_h$ on $V$ imply
  $\|T-T_h\|\to0$; (iii) for compact $T$, $T_h$ with $\|T-T_h\|\to0$: no
  spurious modes on compact subsets of the resolvent set, conservation of
  algebraic multiplicity, and convergence of generalized eigenspaces in gap,
  which needs Riesz projections by contour integrals. Pitfall: the $k$-th
  discrete eigenvalue does not exist for $k>\dim V_h$; state (i) eventually in
  $h$. Depends on 19.13. NASC: `exists_eigenvector_of_isCompactOperator_of_tendsto`
  (VariationalEigenproblems.lean), proved; it gives only that a nonzero limit
  of discrete eigenvalues is an eigenvalue of $T$.

* **19.15. Rates: the double order for eigenvalues.** In the setting of 19.13
  assume $\|T-T_h\|_{\mathcal L(H)}\to0$, and let $E$ be the eigenspace of
  $\lambda=\lambda^{(k)}$, of multiplicity $m$. Then for $h$ small
  $$\lambda^{(k)}\le\lambda^{(k)}_h\le\lambda^{(k)}+C\sup_{u\in E,\|u\|_V=1}
  \inf_{v\in V_h}\|u-v\|_V^2 ,$$
  and for each unit $u\in E$ there is $w_h$ in the span of the discrete
  eigenfunctions of the $m$ eigenvalues converging to $\lambda$ with
  $\|u-w_h\|_V\le C\sup_{u\in E,\|u\|_V=1}\inf_{v\in V_h}\|u-v\|_V$. For the
  Dirichlet Laplacian ($V=H^1_0(\Omega)$, $H=L^2(\Omega)$, $\Omega$ Lipschitz)
  with $V_h$ satisfying $\inf_{v\in V_h}\|w-v\|_{H^1}\le Ch^{\min\{k,r-1\}}
  \|w\|_{H^r}$ and $\inf_{v\in V_h}\|w-v\|\le Ch^{\min\{k+1,r\}}\|w\|_{H^r}$
  (as for continuous piecewise polynomials of degree $k$), if $E\subset H^r$
  and $t=\min\{k,r-1\}$, then
  $$\lambda\le\lambda_h\le\lambda+Ch^{2t}$$
  for each discrete eigenvalue $\lambda_h\to\lambda$, and for each unit
  $u\in E$ there are $u_h$ in the span of the discrete eigenfunctions of the
  $m$ eigenvalues converging to $\lambda$ with $\|u-u_h\|_{H^1}\le Ch^t$ and
  (possibly another such $u_h$) $\|u-u_h\|\le Ch^{1+t}$. With eigenfunctions
  in $H^{k+1}$ the eigenvalue error is $O(h^{2k})$, twice the order of the
  energy error.

  *Assessment.* Not covered. The variational eigenproblem and a spectral gap
  are ingredients. The numerical estimate distinguishes the first-order
  eigenspace error from the squared eigenvalue error.

  *Lean target.* Carriers: those of 19.13–19.14, and `TauCeti.PDE.energyFormH1`
  with `TauCeti.W1p0` for the Laplace case. Conjuncts: (i) the two-sided
  eigenvalue bound with the squared best-approximation error of $E$ in $V$;
  (ii) the eigenvector bound in $V$; (iii) for the Dirichlet Laplacian with
  $E\subset H^r$ and $t=\min\{k,r-1\}$, the rates $h^{2t}$, $h^t$ in $H^1$ and
  $h^{1+t}$ in $L^2$. The two approximation inequalities on $V_h$ are
  hypotheses. Pitfall: the supremum over the unit sphere of $E$ is over a
  finite-dimensional sphere and attained, but stated with a real `⨆` it is junk
  $0$ when $E=\{0\}$; $E\ne0$ holds because $\lambda$ is an eigenvalue. Depends
  on 19.13, 19.14, and on the Bramble–Hilbert estimates of
  SobolevPolynomialApproximation. NASC: `rayleigh_error_eq_quadratic`
  (VariationalEigenproblems.lean), proved; it is the Rayleigh-quotient identity
  behind (ii).

### A posteriori error estimation and adaptivity

For items 19.17–19.18, $\Omega\subset\mathbb R^d$ is a Lipschitz polyhedron,
$\mathbf d$ a symmetric matrix field whose eigenvalues lie in
$[\lambda_\flat,\lambda^\sharp]$ with $\lambda_\flat>0$, $f\in L^2(\Omega)$,
and $u\in H^1_0(\Omega)$ solves $\int(\mathbf d\nabla u)\cdot\nabla w=\int fw$
for all $w\in H^1_0$. $(\mathcal T_h)$ is a shape-regular family of
matching simplicial meshes, $V_h\subset H^1_0$ the continuous piecewise
polynomials of degree $k\ge1$, and $u_h\in V_h$ the Galerkin solution.

* **19.17. Residual estimator: reliability and local efficiency.** The
  **residual** $\rho(u_h)\in H^{-1}(\Omega)$,
  $\langle\rho(u_h),\varphi\rangle=\int f\varphi-\int(\mathbf d\nabla u_h)\cdot
  \nabla\varphi$, satisfies
  $$\frac1{\lambda^\sharp}\|\rho(u_h)\|_{H^{-1}}\le\|\nabla(u-u_h)\|\le
  \frac1{\lambda_\flat}\|\rho(u_h)\|_{H^{-1}},$$
  where $\|\eta\|_{H^{-1}}=\sup_\varphi\langle\eta,\varphi\rangle/\|\nabla\varphi\|$.
  Assume $\mathbf d$ is smooth on each cell, so that
  $r_v=f+\nabla\cdot(\mathbf d\nabla u_h)\in L^2(K)$ on each cell $K$; let
  $r_s=[\![\mathbf d\nabla u_h]\!]\cdot n_F$ be the normal flux jump on each
  interior face $F$. Define the cell indicators
  $\eta_K=\bigl(h_K^2\|r_v\|_{L^2(K)}^2+h_K\sum_{F\subset\partial K,\,F\not\subset
  \partial\Omega}\|r_s\|_{L^2(F)}^2\bigr)^{1/2}$.
  - (Reliability.) $\lambda_\flat\|\nabla(u-u_h)\|\le C_{\rm rel}
    \bigl(\sum_K\eta_K^2\bigr)^{1/2}$, with $C_{\rm rel}$ depending only on
    $d$ and the shape regularity of the mesh family (explicitly through local
    Poincaré and trace constants on vertex patches). No regularity of $u$ is
    required.
  - (Local efficiency.) Fix integers $l_v,l_s\ge0$, let $\bar r_v$, $\bar r_s$
    be the $L^2$ projections of $r_v$, $r_s$ onto polynomials of degree $l_v$
    on $K$ and $l_s$ on $F$, and define the **oscillation**
    $\mathrm{osc}_K=h_K\|r_v-\bar r_v\|_{L^2(K)}$,
    $\mathrm{osc}_F=h_F^{1/2}\|r_s-\bar r_s\|_{L^2(F)}$. Let $D_K$ be the union
    of $K$ and the cells sharing a face with $K$. Then
    $$\eta_K\le c\Bigl(\|\mathbf d\|_{L^\infty(D_K)}\|\nabla(u-u_h)\|_{L^2(D_K)}
    +\sum_{K'\subset D_K}\mathrm{osc}_{K'}+\sum_{F\subset\partial K}\mathrm{osc}_F
    \Bigr),$$
    with $c$ depending only on the shape regularity, $k$, $l_v$ and $l_s$. When
    $\mathbf d$ and $f$ are piecewise polynomials and $l_v$, $l_s$ are large
    enough, the oscillation vanishes and the estimator is equivalent to the
    error.

  *Assessment.* Not covered. Weak elliptic solvability is present. The missing
  estimator theory involves mesh residuals, jumps, patchwise efficiency and
  data oscillation.

  *Lean target.* Carriers: `TauCeti.W1p0` and
  `TauCeti.PDE.IsWeakSolutionDirichlet` for the continuous problem. New
  definitions: a simplicial mesh of a polyhedral domain with its faces, patches
  and shape-regularity constant, the conforming $\mathbb P_k$ space, the
  residual as an element of the dual of `W1p0`, the cell and face indicators,
  and the oscillation. Conjuncts: (i) the residual–error equivalence with
  constants $\lambda_\flat$, $\lambda^\sharp$; (ii) global reliability with
  $C_{\rm GUB}$ depending only on shape regularity; (iii) local efficiency with
  oscillation. Pitfall: face jumps require traces of piecewise smooth
  functions, which must be taken from the polynomial pieces, not from a Sobolev
  trace, to avoid a.e. ambiguity. The mesh infrastructure is missing at the
  pins. NASC: `norm_error_le_of_weighted_residuals`
  (VariationalEigenproblems.lean), proved; it is the abstract reliability step
  from a residual representation and interpolation bounds.

* **19.18. Prager–Synge identity and equilibrated fluxes.** Let $u\in
  H^1_0(\Omega)$ solve $-\Delta u=f\in L^2(\Omega)$. For every $u_h\in
  H^1_0(\Omega)$ and every $\sigma^*\in H(\mathrm{div};\Omega)$ with
  $\nabla\cdot\sigma^*=f$,
  $$\|\nabla(u-u_h)\|^2+\|\nabla u+\sigma^*\|^2=\|\nabla u_h+\sigma^*\|^2 ,$$
  so $\|\nabla u_h+\sigma^*\|$ is a guaranteed upper bound of the error. For
  the problem of 19.17 with $\sigma_h=-\mathbf d\nabla u_h$, any
  $u_h\in H^1_0(\Omega)$ satisfies
  $$\lambda_\flat\|\nabla(u-u_h)\|\le\inf_{\sigma^*\in H(\mathrm{div}),\
  \nabla\cdot\sigma^*=f}\|\sigma^*-\sigma_h\|\le\lambda^\sharp
  \|\nabla(u-u_h)\| ,$$
  and if $\sigma^*\in H(\mathrm{div};\Omega)$ only satisfies
  $\int_K\nabla\cdot\sigma^*=\int_Kf$ on every cell $K$, then
  $$\lambda_\flat\|\nabla(u-u_h)\|\le\Bigl(\sum_K\bigl(\|\sigma^*-\sigma_h\|_{L^2(K)}
  +\tfrac{h_K}{\pi}\|f-\nabla\cdot\sigma^*\|_{L^2(K)}\bigr)^2\Bigr)^{1/2}.$$
  For the Galerkin solution $u_h$, a flux $\sigma_h^*$ in a Raviart–Thomas
  space of degree $l\ge0$ with this property (indeed with
  $\int_K(\nabla\cdot\sigma_h^*-f)q=0$ for all $q\in\mathbb P_l$) can be
  computed by independent local mixed problems on vertex patches; if
  $\mathbf d$ is piecewise constant and $l\ge k-1$, it is also locally
  efficient: $\|\sigma^*_h-\sigma_h\|_{L^2(K)}$ is bounded by a constant times
  the energy error and data oscillation on the cells sharing a vertex with
  $K$.

  *Assessment.* Not covered. The selected hypercircle identity uses the weak
  equation and normal-flux integration by parts. It gives a guaranteed energy
  bound whenever a flux with the required divergence is available.

  *Scope.* The selected claim is the Poisson hypercircle identity and the
  guaranteed energy error bound from an equilibrated flux.

  *Argument.* The cross term between $\nabla(u_h-u)$ and $\nabla u+\sigma^*$ is
  zero by the weak equation and integration by parts. Expanding the square of
  their sum gives the identity.

  *Lean target.* Carriers at the pins: `TauCeti.W1p0`, `TauCeti.W1p.gradient`,
  `TauCeti.PDE.IsWeakSolutionDirichlet`, and `TauCeti.PDE.energyFormH1_one_zero_zero_eq_inner`. New
  definition: the flux space $\{\sigma^*\in L^2(\Omega)^d:\nabla\cdot\sigma^*=f\}$, with the weak
  divergence tested against `W1p0`. Conjuncts: (i) the identity $\|\nabla(u-u_h)\|^2+\|\nabla
  u+\sigma^*\|^2=\|\nabla u_h+\sigma^*\|^2$; (ii) the guaranteed bound $\|\nabla(u-u_h)\|\le\|\nabla
  u_h+\sigma^*\|$. Pitfall: the sign convention $\sigma=-\nabla u$ must match the divergence
  condition. Statable and provable at the pins. NASC:
  `norm_sub_sq_add_norm_add_sq_eq_of_equilibrated` (VariationalEigenproblems.lean), proved; the
  remaining work is the upstream statement and the bound (ii), a one-line corollary.

* **19.19. Convergence and optimality of adaptive finite elements.** Let
  $\Omega\subset\mathbb R^n$, $n\ge2$, be a polyhedron, $\alpha$ a Lipschitz
  function with $0<\alpha_0\le\alpha\le\alpha_1$, $f\in L^2(\Omega)$, and
  $u\in H^1_0$ the solution of $\int\alpha\nabla u\cdot\nabla v=\int fv$, with
  energy norm $\|v\|_E^2=\int\alpha|\nabla v|^2$. An adaptive loop
  SOLVE–ESTIMATE–MARK–REFINE produces nested non-degenerate triangulations
  $\mathcal T_j$ and Galerkin solutions $u_j$ of degree $k$. With
  $R_j=f+\nabla\cdot(\alpha\nabla u_j)$ on each cell, the face indicators are
  $E_e(u_j)^2=\sum_{T\supset e}h_T^2\|R_j\|_{L^2(T)}^2+h_e\|[\alpha\nabla u_j
  \cdot n_e]\|_{L^2(e)}^2$ for interior faces $e$. MARK selects faces carrying
  at least the fraction $\theta_1^2$ of $\sum_eE_e(u_j)^2$ (**Dörfler
  marking**, $0<\theta_1<1$), and cells
  carrying at least the fraction $\theta_2^2$ of the squared oscillation
  $\mathrm{osc}_j(\Omega)^2=\sum_T h_T^2\|R_j-Q_jR_j\|_{L^2(T)}^2$, where
  $Q_j$ is the $L^2$ projection onto
  discontinuous piecewise polynomials of degree $k-1$. REFINE keeps the
  family non-degenerate, creates a new node in the interior of each marked
  face and of each cell containing it, with children satisfying
  $h_{T'}\ge\gamma_1h_T$, and reduces the size of each oscillation-marked
  cell's children to $h_{T'}\le\gamma_2h_T$, $\gamma_2<1$.
  - (Contraction.) There are $\theta\in(0,1)$ and $\eta>0$, depending only on
    $\alpha$, the shape regularity, $\gamma_1,\gamma_2,\theta_1,\theta_2$, such
    that
    $$\|u-u_{j+1}\|_E^2+\eta\,\mathrm{osc}_{j+1}(\Omega)^2\le\theta\bigl(
    \|u-u_j\|_E^2+\eta\,\mathrm{osc}_j(\Omega)^2\bigr).$$
    In particular $u_j\to u$ in $H^1$ with a geometric rate in $j$.
  - (Optimality.) For the Poisson problem with $f$ piecewise polynomial on
    $\mathcal T_0$, newest-vertex bisection with a suitable initial labelling,
    and Dörfler marking with $\theta$ sufficiently small and a marked set of
    cardinality at most a constant times the minimal one: if $u$ belongs to
    the approximation class $\mathcal A_s$, i.e.
    $|u|_{\mathcal A_s}=\sup_{N>0}N^s\inf\{\|\nabla(u-v)\|:v\in V(\mathcal T),
    \ \mathcal T\text{ a refinement of }\mathcal T_0,\ \#\mathcal T-\#\mathcal T_0
    \le N\}<\infty$, then $\|\nabla(u-u_n)\|\le c|u|_{\mathcal A_s}
    (\#\mathcal T_n-\#\mathcal T_0)^{-s}$ for all $n\ge1$: the adaptive meshes
    achieve the best possible convergence rate in terms of the number of
    cells.

  *Assessment.* Not covered. The selected result combines discrete reliability,
  marking, refinement, a contraction and complexity relative to an
  approximation class.

  *Lean target.* New definitions: newest-vertex bisection on a conforming
  initial mesh with its refinement relation, Dörfler marking with parameter
  $\theta$, the sequence produced by SOLVE–ESTIMATE–MARK–REFINE, and the
  approximation class $\mathbb A_s$ with its quasi-norm defined by an infimum
  over meshes with at most $N$ more elements. Conjuncts: (i) the contraction of
  $\|u-u_j\|_E^2+\eta\,\mathrm{osc}_j^2$ with $\theta$, $\eta$ depending only
  on the listed data; (ii) for $u\in\mathcal A_s$, $\|\nabla(u-u_n)\|\le
  c|u|_{\mathcal A_s}(\#\mathcal T_n-\#\mathcal T_0)^{-s}$ for $n\ge1$.
  Pitfall: at $n$ with $\#\mathcal T_n=\#\mathcal T_0$ the real power of $0$ is
  junk; REFINE makes $\#\mathcal T_n>\#\mathcal T_0$ for $n\ge1$, which must be
  proved or assumed. The class quasi-norm is a supremum over $N$ that can be
  infinite; take it in $\mathbb R_{\ge0} \cup\{\infty\}$. Depends on 19.17 and
  on the mesh closure estimate of Binev–Dahmen–DeVore, which is missing. NASC:
  `exists_adaptive_error_contraction` (VariationalEigenproblems.lean), proved;
  it is the abstract step (i) from estimator reduction, reliability and
  quasi-orthogonality.

### Nonlinear problems

* **19.20. Obstacle problem and $\Gamma$-convergence.**
  - (Falk-type estimate.) Let $X$ be a Banach space, $a$ a bounded coercive
    bilinear form on $X$ with constants $M$, $\alpha$, $\ell\in X'$,
    $K\subset X$ and $K_h\subset X_h\subset X$ nonempty closed convex sets, and
    let $u\in K$, $u_h\in K_h$ solve $a(u,v-u)\ge\ell(v-u)$ for $v\in K$ and
    $a(u_h,v_h-u_h)\ge\ell(v_h-u_h)$ for $v_h\in K_h$ (with $K_h\not\subset K$
    allowed). With $\langle Au,w\rangle=a(u,w)$,
    $$\frac\alpha2\|u-u_h\|_X^2\le\inf_{v\in K,\ v_h\in K_h}\Bigl(\|Au-\ell\|_{X'}
    \bigl(\|u_h-v\|_X+\|u-v_h\|_X\bigr)+\frac{M^2}{2\alpha}\|u-v_h\|_X^2\Bigr),$$
    and if $X$ is continuously embedded in a Hilbert space $H$ whose inner
    product represents the pairing ($\langle\varphi,v\rangle=(\varphi,v)_H$
    for $\varphi\in H$) and $Au-\ell\in H$, the same bound holds with
    $\|Au-\ell\|_H(\|u_h-v\|_H+\|u-v_h\|_H)$ as first term. For the
    obstacle problem on a bounded polyhedral Lipschitz domain
    $\Omega\subset\mathbb R^d$, $d\in\{2,3\}$, with
    $\Gamma_D\subset\partial\Omega$ closed of positive surface measure,
    homogeneous Neumann data on $\partial\Omega\setminus\Gamma_D$,
    $f\in L^2(\Omega)$, $\chi\in C(\bar\Omega)$ with $\chi\le0$ on
    $\Gamma_D$, $K=\{v\in H^1_D(\Omega):v\ge\chi\}$, $a(u,v)=(\nabla u,\nabla v)$,
    $\ell(v)=(f,v)$, continuous piecewise linear elements on a regular family
    of triangulations, $I_h$ nodal interpolation and
    $K_h=\{v_h\in S^1_D(\mathcal T_h):v_h\ge I_h\chi\}$: if $\chi,u\in H^2(\Omega)$, then
    $$\|\nabla(u-u_h)\|^2\le ch^2\|\Delta u+f\|\bigl(\|D^2\chi\|+\|D^2u\|\bigr)
    +ch^2\|D^2u\|^2 ,$$
    so $\|\nabla(u-u_h)\|=O(h)$.
  - ($\Gamma$-convergence.) Let $X$ be a Banach space, $X_h\subset X$ subspaces
    with $\bigcup_h X_h$ approximating every $u\in X$ strongly
    ($\inf_{v\in X_h}\|u-v\|\to0$), and $I:X\to\mathbb R$ weakly
    lower semicontinuous and strongly continuous. Let $I_h=I$ on $X_h$ and
    $I_h=+\infty$ off $X_h$. Then $I_h$ **$\Gamma$-converges** to $I$ for the
    weak topology: $\liminf_hI_h(u_h)\ge I(u)$ whenever $u_h\rightharpoonup u$,
    and every $u$ has a recovery sequence $u_h\rightharpoonup u$ with
    $I_h(u_h)\to I(u)$. Consequently, if $I_h(u_h)\le\inf I_h+\varepsilon_h$
    with $\varepsilon_h\to0$ and $u_h\rightharpoonup u$, then $u$ minimizes
    $I$ and $I_h(u_h)\to I(u)$.

  *Assessment.* Not covered. TauCeti has Γ-convergence with convergence of
  infima and of minimizers under equicoercivity. The obstacle problem requires
  admissible sets on the meshes, discrete compactness and recovery, and
  convergence of the computed minimizers.

  *Lean target.* Carriers at the pins: `TauCeti.TendstoGamma`,
  `TauCeti.Equicoercive`, `TauCeti.TendstoGamma.isMinOn_of_tendsto` and
  `TauCeti.TendstoGamma.tendsto_iInf` (functionals with values in `EReal`),
  `TauCeti.W1p0` and `TauCeti.PDE.energyFormH1`. New definitions: the
  admissible sets $K$ and $K_h$ and the energies with value $\top$ off them.
  Conjuncts: (i) Falk's estimate in $X'$; (ii) its variant in $H$; (iii) the
  $O(h)$ bound for the obstacle problem with $\chi,u\in H^2$, which needs
  `TauCeti.Wkp` and mixed boundary conditions; (iv) Γ-convergence for the weak
  topology and the convergence of almost-minimizers. `TendstoGamma` is
  sequential on any topological space, so it applies to `WeakSpace` with no
  first countability. Pitfall: functionals with value $\top$ off $K$ must use
  `EReal` or `ℝ≥0∞`, not real values with junk outside. NASC:
  `falk_obstacle_error_le` (VariationalEigenproblems.lean), proved; it is the
  abstract form of (i).

## 20. Multilevel and domain decomposition methods

[Synopsis](SYNOPSIS.md#20-multilevel-and-domain-decomposition-methods) · [Coverage inventory](STRUCTURE.md#20-multilevel-and-domain-decomposition-methods)

The existing projection and spectral norm APIs supply algebraic ingredients.
The selected results control smoothing, coarse-grid approximation and
decomposition in the energy norm.

For a symmetric positive
definite operator $A$ on a finite-dimensional real inner product space,
$(u,v)_A=(Au,v)$ and $\|v\|_A=(Av,v)^{1/2}$; for an operator $T$ that is
self-adjoint and positive definite with respect to $(\cdot,\cdot)_A$,
$\kappa(T)=\lambda_{\max}(T)/\lambda_{\min}(T)$. For Hermitian matrices,
$X\le Y$ means that $Y-X$ is positive semidefinite. Mesh-dependent statements
concern families of finite element discretizations; the constants $C$ are
independent of the mesh sizes $h$ and $H$, the number of levels and the number
of subdomains, unless stated otherwise.

### Multigrid

* **20.1. Two-grid convergence from smoothing and approximation properties.**
  Let levels $\ell=0,1,2,\dots$ carry invertible matrices
  $A_\ell\in\mathbb K^{n_\ell\times n_\ell}$, prolongations
  $p:\mathbb K^{n_{\ell-1}}\to\mathbb K^{n_\ell}$, restrictions
  $r:\mathbb K^{n_\ell}\to\mathbb K^{n_{\ell-1}}$, and consistent smoothing
  iterations for $A_\ell$ with iteration matrices $S_\ell$. The **two-grid iteration** with
  $\nu$ presmoothing steps applies $\nu$ smoothing steps and then the
  coarse-grid correction $x\mapsto x-pA_{\ell-1}^{-1}r(A_\ell x-b)$; its
  iteration matrix is
  $$M^{\mathrm{TG}}_\ell(\nu)=(I-pA_{\ell-1}^{-1}rA_\ell)S_\ell^\nu
  =(A_\ell^{-1}-pA_{\ell-1}^{-1}r)\,A_\ell S_\ell^\nu.$$
  The **smoothing property** holds if there is a function $\eta$ with
  $\eta(\nu)\to0$ as $\nu\to\infty$ and
  $\|A_\ell S_\ell^\nu\|_2\le\eta(\nu)\|A_\ell\|_2$ for all $\nu\ge0$ and
  $\ell\ge1$. The **approximation property** holds if
  $\|A_\ell^{-1}-pA_{\ell-1}^{-1}r\|_2\le C_A/\|A_\ell\|_2$ for all $\ell\ge1$.
  Under both properties,
  $$\|M^{\mathrm{TG}}_\ell(\nu)\|_2\le C_A\,\eta(\nu)\qquad
  (\nu\ge0,\ \ell\ge1),$$
  so for every $\zeta\in(0,1)$ there is $\underline\nu$, independent of $\ell$,
  with $\|M^{\mathrm{TG}}_\ell(\nu)\|_2\le\zeta$ for all $\nu\ge\underline\nu$.
  For $A_\ell$ Hermitian positive definite, the damped Richardson smoother
  $S_\ell=I-A_\ell/\|A_\ell\|_2$ has the smoothing property with
  $$\eta(\nu)=\eta_0(\nu)=\frac{\nu^\nu}{(\nu+1)^{\nu+1}}
  =\frac1{e\nu}+O(\nu^{-2}).$$

  *Assessment.* Not covered. The two-grid estimate joins a smoother and a
  coarse-space correction. Its convergence factor requires the stated smoothing
  and approximation inequalities, and the Richardson constant $\eta_0$ a
  spectral computation.

  *Lean target.* Carriers at the pins: `Matrix` over `RCLike 𝕜` with the
  $\ell^2$ operator norm from the scoped instances of `Matrix.Norms.L2Operator`
  (not the default $\ell^\infty$ operator norm), or
  `EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)` with its operator
  norm. New definitions: a level hierarchy (sizes $n_\ell$, $A_\ell$, $p$, $r$,
  $S_\ell$) and the two-grid matrix. Conjuncts: (i) the factorization of
  $M^{\rm TG}_\ell(\nu)$; (ii) $\|M^{\rm TG}_\ell (\nu)\|_2\le C_A\eta(\nu)$;
  (iii) the uniform $\underline\nu$ for each $\zeta\in(0,1)$; (iv) the
  Richardson smoothing function $\eta_0(\nu)=\nu^\nu/ (\nu+1)^{\nu+1}$ for
  Hermitian positive definite $A_\ell$. Pitfall: at $\nu=0$,
  $\eta_0(0)=0^0/1=1$ needs Lean's convention $0^0=1$, which holds for
  `Monoid.npow`. Statable and provable at the pins. NASC: `norm_twoGrid_le`
  (Multilevel.lean), proved; it is (ii) for one level with the inverse
  approximation written $\|A^{-1}-B\|$.

* **20.2. Multigrid W-cycle.** The **multigrid iteration** with cycle index
  $\gamma\in\mathbb N$ on level $\ell\ge1$ replaces the exact coarse solve by
  $\gamma$ steps of the multigrid iteration on level $\ell-1$ started at zero,
  with an exact solve on level $0$. With $\nu$ presmoothing steps, its
  iteration matrices satisfy $M_0=O$ and
  $$M_\ell=M^{\mathrm{TG}}_\ell(\nu)+p\,M_{\ell-1}^{\gamma}A_{\ell-1}^{-1}rA_\ell
  S_\ell^\nu\qquad(\ell\ge1).$$
  Assume the smoothing and approximation properties of 20.1, and in addition
  $\|S_\ell^\nu\|_2\le C_S$ for all $\ell\ge1$, $\nu\ge1$, and
  $C_p^{-1}\|x\|_2\le\|px\|_2\le\bar C_p\|x\|_2$ for all coarse vectors $x$ and
  all $\ell$. If $\gamma\ge2$, then for every $\zeta'\in(0,1)$ there is
  $\underline\nu$, independent of $\ell$, such that $\|M_\ell\|_2\le\zeta'$ for
  all $\nu\ge\underline\nu$ and all $\ell\ge0$.

  *Assessment.* Not covered. The missing result constructs the multilevel
  recursion and bounds its error operator uniformly in the number of levels
  under the W-cycle conditions.

  *Lean target.* Carriers: those of 20.1. New definition: the multigrid
  iteration matrix $M_\ell$ by recursion on $\ell$ with $M_0=0$. Conjuncts: (i)
  the recursion formula; (ii) for $\gamma\ge2$ and every $\zeta'\in(0,1)$ a
  uniform $\underline\nu$ with $\|M_\ell\|_2\le\zeta'$ for all $\ell$, under
  the bounds $C_S$, $C_p$, $\bar C_p$. Depends on 20.1. NASC:
  `exists_wCycle_uniform_bound` (Multilevel.lean), proved; it is the scalar
  recurrence $M_{k+1}\le\eta+CM_k^\gamma$ behind (ii).

* **20.3. Symmetric two-grid and V-cycle convergence.** In the setting of
  20.1, assume in addition that $r=p^*$, that $A_{\ell-1}=rA_\ell p$ (Galerkin
  coarse matrices), that $A_\ell$ is Hermitian positive definite, and that the
  smoother is $S_\ell=I-W_\ell^{-1}A_\ell$ with $W_\ell$ Hermitian and
  $A_\ell\le W_\ell$, applied $\nu/2$ times before and $\nu/2$ times after the
  coarse-grid correction, $\nu\ge2$ even. Assume the approximation property in
  the form
  $\|W_\ell^{1/2}(A_\ell^{-1}-pA_{\ell-1}^{-1}r)W_\ell^{1/2}\|_2\le C_A$ for
  all $\ell\ge1$. Then the two-grid iteration matrix $M^{\mathrm{TG}}_\ell$
  satisfies
  $$\rho(M^{\mathrm{TG}}_\ell)=\|M^{\mathrm{TG}}_\ell\|_A\le
  \begin{cases}C_A\,\eta_0(\nu),&C_A\le1+\nu,\\
  (1-1/C_A)^\nu,&C_A>1+\nu,\end{cases}$$
  which is less than $1$, and the multigrid V-cycle ($\gamma=1$) satisfies, on
  every level $\ell$,
  $$\rho(M^{V}_\ell)=\|M^{V}_\ell\|_A\le\frac{C_A}{C_A+\nu}.$$
  In particular, the V-cycle converges for every $\nu\ge2$ with a contraction
  number independent of $\ell$.

  *Assessment.* Not covered. The symmetric smoother and spectral estimates are
  ingredients. The selected result needs the energy-norm contraction and the
  recursive V-cycle comparison.

  *Lean target.* Carriers: `Matrix.PosDef`, `Matrix.IsHermitian` with the
  Loewner order on Hermitian matrices, the square root `CFC.sqrt`, and
  `spectralRadius`. Conjuncts: (i) $\rho(M^{\rm TG}_\ell)=\|M^{\rm
  TG}_\ell\|_A$; (ii) the two-case bound; (iii) the V-cycle bound
  $C_A/(C_A+\nu)$ on every level. Hypotheses: $r=p^*$, Galerkin coarse
  matrices, $A_\ell\le W_\ell$, $\nu\ge2$ even. Pitfall: `spectralRadius` takes
  values in `ℝ≥0∞`; compare after `ENNReal.ofReal` of the norm. Depends on
  20.1. NASC: `norm_symmetricTwoGrid_le` (Multilevel.lean), sorry; it is an
  energy-norm surrogate with an orthogonal coarse projection, bounding
  $\|S^m(1-P_V)S^m\|$ by $C\eta_0(2m)$.

* **20.4. Finite element multigrid for a model problem.** Let
  $\Omega\subset\mathbb R^2$ be a convex polygon, $a(u,v)=\int_\Omega(\alpha
  \nabla u\cdot\nabla v+\beta uv)\,dx$ with smooth $\alpha,\beta$,
  $0<\alpha_0\le\alpha\le\alpha_1$ and $0\le\beta\le\beta_1$, and let $V_k\subset
  H^1_0(\Omega)$ be the continuous piecewise linear functions on triangulations
  $\mathcal T_k$, where $\mathcal T_{k+1}$ is obtained from $\mathcal T_k$ by
  joining edge midpoints. Let $(v,w)_k=h_k^2\sum_pv(p)w(p)$, summed over the
  interior vertices $p$ of $\mathcal T_k$, and define $A_k:V_k\to V_k$ by
  $(A_kv,w)_k=a(v,w)$ for all $w\in V_k$. Let the $k$-th level iteration solve
  exactly on level $1$ and, on level $k\ge2$, use $m$ Richardson smoothing
  steps $z\mapsto z+\Lambda_k^{-1}(g-A_kz)$, where $\Lambda_k\ge\rho(A_k)$ and
  $\Lambda_k\le Ch_k^{-2}$, with prolongation the inclusion $V_{k-1}\subset V_k$
  and restriction its adjoint with respect to $(\cdot,\cdot)_{k-1}$ and
  $(\cdot,\cdot)_k$, and write $\|v\|_E=a(v,v)^{1/2}$. Then:
  - (two-grid) $\|e_{\mathrm{TG}}\|_E\le Cm^{-1/2}\|e_0\|_E$ for the one-sided
    two-grid method with $m$ presmoothing steps;
  - (W-cycle) for every $\zeta\in(0,1)$ there is $m_0$ such that, for
    $m\ge m_0$, the one-sided W-cycle reduces the energy error by the factor
    $\zeta$ on every level $k$;
  - (V-cycle) with $m$ pre- and $m$ postsmoothing steps, the V-cycle satisfies
    $\|z-MG(k,z_0,g)\|_E\le\frac{C_*}{m+C_*}\|z-z_0\|_E$ for every $m\ge1$
    and every $k$, with $C_*$ independent of $k$ and $m$;
  - (full multigrid) if the $k$-th level iteration is a contraction in
    $\|\cdot\|_E$ with a contraction number $\zeta$ independent of $k$, and
    $r$ iterations are performed on each level with $2\zeta^r<1$, starting
    from the interpolated result of the previous level, then the full
    multigrid approximation $\hat u_k$ satisfies
    $\|u_k-\hat u_k\|_E\le Ch_k|u|_{H^2(\Omega)}$, where $u_k$ is the Galerkin
    solution and $u$ the exact solution.

  *Assessment.* Not covered. Finite element approximation properties give
  ingredients. The missing theorem quantifies mesh-independent contraction and
  the work-to-accuracy relation on a hierarchy.

  *Lean target.* Carriers: `TauCeti.W1p0` on a polygon and
  `TauCeti.PDE.energyFormH1` for $a$. New definitions: the nested uniformly
  refined triangulations, the $P_1$ spaces $V_k$, the mesh-dependent inner
  product $(\cdot,\cdot)_k$ and $A_k$, the $k$-th level iteration and the full
  multigrid algorithm. Conjuncts: (i) the two-grid bound $Cm^{-1/2}$; (ii) the
  W-cycle contraction; (iii) the V-cycle bound $C_*/(m+C_*)$; (iv) the full
  multigrid bound $Ch_k|u|_{H^2}$. Hypotheses: convex polygon ($H^2$
  regularity), $\Lambda_k\ge\rho(A_k)$, $\Lambda_k\le Ch_k^{-2}$, $2\zeta^r<1$.
  Depends on 20.1–20.3 and on the finite element interpolation and $H^2$
  regularity, which are missing at the pins. NASC:
  `fullMultigrid_dyadic_error_le` (Multilevel.lean), proved; it is the scalar
  recursion behind (iv).

### Subspace correction

* **20.5. Parallel subspace correction and the lemma of Lions.** Let $A$ be
  symmetric positive definite on a finite-dimensional space $V$. Let $V_j$,
  $0\le j\le J$, be finite-dimensional spaces with linear maps $I_j:V_j\to V$
  such that $V=\sum_jI_jV_j$, and let $B_j$ be symmetric positive definite on
  $V_j$. The **additive (parallel subspace correction) preconditioner** is
  $B=\sum_{j=0}^JI_jB_j^{-1}I_j^\top$. Then $B$ is symmetric positive definite,
  $$(B^{-1}v,v)=\min\Bigl\{\sum_{j=0}^J(B_jv_j,v_j):\ v_j\in V_j,\
  v=\sum_jI_jv_j\Bigr\},$$
  the minimum being attained only at $v_j=B_j^{-1}I_j^\top B^{-1}v$, and the
  eigenvalues of $BA$ are positive with
  $$\lambda_{\max}(BA)=\max_{v\ne0}\frac{(Av,v)}{(B^{-1}v,v)},\qquad
  \lambda_{\min}(BA)=\min_{v\ne0}\frac{(Av,v)}{(B^{-1}v,v)}.$$
  Consequently, if every $v\in V$ has a decomposition $v=\sum_jI_jv_j$ with
  $\sum_j(B_jv_j,v_j)\le K_0(Av,v)$ (a **stable decomposition**), then
  $\lambda_{\min}(BA)\ge1/K_0$; and if $(Av,v)\le K_1\sum_j(B_jv_j,v_j)$ for
  every decomposition, then $\lambda_{\max}(BA)\le K_1$ and
  $\kappa(BA)\le K_0K_1$.

  *Assessment.* Not covered. Orthogonal projections and finite-dimensional
  adjoints exist. The gap connects a decomposition into subspaces with the
  spectrum of the additive preconditioner.

  *Lean target.* Carriers: finite-dimensional real inner product spaces $V$,
  $V_j$, `ContinuousLinearMap.adjoint` for $I_j^\top$, `LinearMap.IsSymmetric`,
  and `IsLeast` for the minimum. Conjuncts: (i) $B$ is symmetric positive
  definite; (ii) the minimum formula for $(B^{-1}v,v)$ with the unique
  minimizer; (iii) the Rayleigh formulas for $\lambda_{\max}(BA)$ and
  $\lambda_{\min}(BA)$, with $BA$ self-adjoint for $(\cdot,\cdot)_{B^{-1}}$;
  (iv) the consequences of stable decomposition. Pitfall: the eigenvalues of
  $BA$ must be taken for the inner product $(B^{-1}\cdot,\cdot)$ or through
  `Matrix.IsHermitian.eigenvalues` of $B^{1/2}AB^{1/2}$; $BA$ is not symmetric
  for the original inner product. Statable and provable at the pins. NASC:
  `exists_additiveInverse_isLeast_energy` (Multilevel.lean), sorry; it states
  (i) and the minimum in (ii), without uniqueness of the minimizer.

* **20.6. The Xu–Zikatanov identity.** Let $A$ be symmetric positive definite
  on $V$, let $V_1,\dots,V_J$ be subspaces with $V=V_1+\cdots+V_J$, and let
  $P_i$ be the $(\cdot,\cdot)_A$-orthogonal projection onto $V_i$. The
  **successive subspace correction** method with exact subspace solves has
  error propagation operator $E=(I-P_J)(I-P_{J-1})\cdots(I-P_1)$, and
  $$\|E\|_A^2=1-\frac1{1+c_0},\qquad
  c_0=\sup_{\|v\|_A=1}\ \inf_{\substack{v_i\in V_i\\ \sum_iv_i=v}}\
  \sum_{i=1}^J\Bigl\|P_i\sum_{j=i+1}^Jv_j\Bigr\|_A^2.$$
  In particular $\|E\|_A<1$.

  *Assessment.* Not covered. The finite product of projection corrections is
  expressible. The selected identity gives its exact energy-norm contraction in
  terms of an extremal decomposition constant.

  *Lean target.* Carriers: a finite-dimensional real inner product space
  carrying the energy inner product, `Submodule.starProjection`, and a
  `List.foldl` product for $E$. Conjuncts: (i) $\|E\|_A^2=1-1/(1+c_0)$; (ii)
  $\|E\|_A<1$. Pitfall: $c_0$ is a real `sSup` of `sInf`s; the inner sets are
  nonempty because the $V_i$ span and bounded below by $0$, the outer set is
  bounded because the infimum is attained and bounded by a fixed decomposition,
  and on the trivial space the `sSup` of the empty set is $0$, consistent with
  $E=0$. Statable and provable at the pins. NASC: `projectionSweep` and
  `norm_projectionSweep_sq_eq_xuZikatanov` (Multilevel.lean), sorry; they state
  (i).

* **20.7. Two-level convergence identity and optimal coarse spaces.** Let $A$
  be symmetric positive definite on $V=\mathbb R^n$, and let $R$ be a smoother
  whose symmetrization $\bar R=R^\top+R-R^\top AR$ is symmetric positive
  definite (equivalently, $\|I-RA\|_A<1$). For a coarse space $V_c\subsetneq V$,
  let $\Pi_c$ be the $(\cdot,\cdot)_A$-orthogonal projection onto $V_c$; the
  two-level method with exact coarse solve and postsmoothing has error
  operator $E=(I-RA)(I-\Pi_c)$. Then
  $$\|E\|_A^2=1-\frac1{K(V_c)},\qquad
  K(V_c)=\max_{v\ne0}\ \min_{v_c\in V_c}\
  \frac{(\bar R^{-1}(v-v_c),v-v_c)}{\|v\|_A^2}.$$
  If $\mu_1\le\cdots\le\mu_n$ are the eigenvalues of $\bar RA$ with
  eigenvectors $\zeta_1,\dots,\zeta_n$ orthogonal in the $\bar R^{-1}$-inner
  product, then for $0\le n_c<n$,
  $\min\{\|E\|_A^2:\dim V_c=n_c\}=1-\mu_{n_c+1}$, attained by
  $V_c=\mathrm{span}\{\zeta_1,\dots,\zeta_{n_c}\}$.

  *Assessment.* Not covered. Matrix eigendecomposition and variational
  characterizations are available. The missing result identifies the exact
  two-level norm and optimizes the coarse space.

  *Lean target.* Carriers: `Matrix.PosDef`, `Matrix.IsHermitian.eigenvalues`
  and `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` for the
  optimization over $n_c$-dimensional subspaces. Conjuncts: (i) the identity
  $\|E\|_A^2=1-1/K(V_c)$ for $V_c\ne V$; (ii) the minimum over $\dim V_c=n_c$
  equals $1-\mu_{n_c+1}$, attained at the span of the first $n_c$ eigenvectors.
  Pitfall: for $V_c=V$, $K(V_c)=0$ and Lean's $0^{-1}=0$ turns the right side
  into $1$ while $E=0$; the hypothesis $V_c\ne V$ is necessary. Statable and
  provable at the pins. NASC: `norm_twoLevel_sq_eq_coarseOptimization`
  (Multilevel.lean), sorry; it states (i) after the change of variables $A=I$,
  with the hypothesis $V\ne\top$.

### Abstract Schwarz theory and domain decomposition

* **20.8. Abstract Schwarz framework.** Let $a(\cdot,\cdot)$ be symmetric and
  positive definite on a finite-dimensional space $V$. Let $V_i$, $0\le i\le
  N$, be finite-dimensional spaces with linear maps $R_i^\top:V_i\to V$ such
  that $V=\sum_{i=0}^NR_i^\top V_i$, and with symmetric positive definite
  bilinear forms $\tilde a_i$ on $V_i$. Define $\tilde P_i:V\to V_i$ by
  $\tilde a_i(\tilde P_iu,v_i)=a(u,R_i^\top v_i)$ for all $v_i\in V_i$, and
  $P_i=R_i^\top\tilde P_i$. The **additive Schwarz operator** is
  $P_{\mathrm{ad}}=\sum_{i=0}^NP_i$, and the **multiplicative Schwarz** error
  propagation operator is $E_{\mathrm{mu}}=(I-P_N)\cdots(I-P_1)(I-P_0)$.
  Each $P_i$ is self-adjoint with respect to $a(\cdot,\cdot)$. Consider:
  - (stable decomposition) there is $C_0>0$ such that every $u\in V$ has a
    decomposition $u=\sum_{i=0}^NR_i^\top u_i$ with
    $\sum_{i=0}^N\tilde a_i(u_i,u_i)\le C_0^2\,a(u,u)$;
  - (strengthened Cauchy–Schwarz inequalities) there are
    $\epsilon_{ij}\in[0,1]$, $1\le i,j\le N$, with
    $|a(R_i^\top u_i,R_j^\top u_j)|\le\epsilon_{ij}\,
    a(R_i^\top u_i,R_i^\top u_i)^{1/2}a(R_j^\top u_j,R_j^\top u_j)^{1/2}$ for
    all $u_i\in V_i$, $u_j\in V_j$; write $\rho(\mathcal E)$ for the spectral
    radius of $\mathcal E=(\epsilon_{ij})$;
  - (local stability) there is $\omega>0$ with
    $a(R_i^\top u_i,R_i^\top u_i)\le\omega\,\tilde a_i(u_i,u_i)$ for all
    $u_i\in\mathrm{range}(\tilde P_i)$, $0\le i\le N$.

  Under the first assumption $a(P_{\mathrm{ad}}u,u)\ge C_0^{-2}a(u,u)$; under
  the second and third, $a(P_{\mathrm{ad}}u,u)\le\omega(\rho(\mathcal E)+1)
  a(u,u)$. Under all three,
  $$\kappa(P_{\mathrm{ad}})\le C_0^2\,\omega\,(\rho(\mathcal E)+1),$$
  and if moreover $\omega\in(0,2)$, then with $\tilde\omega=\max(1,\omega)$,
  $$\|E_{\mathrm{mu}}\|_a^2\le1-\frac{2-\omega}{(2\tilde\omega^2\rho(\mathcal
  E)^2+1)\,C_0^2}<1.$$

  *Assessment.* Not covered. Schur complement and projection results are
  ingredients. The selected theorem connects stable decomposition, local
  stability and strengthened Cauchy–Schwarz inequalities to the spectrum of the
  additive Schwarz operator and the multiplicative contraction.

  *Lean target.* Carriers: finite-dimensional real inner product spaces, and
  $\rho(\mathcal E)$ through the bound $\sum_{ij}\epsilon_{ij}x_ix_j\le
  \rho(\mathcal E)\|x\|^2$ for the symmetric nonnegative $\mathcal E$, with
  $\rho(\mathcal E)$ the largest of `Matrix.IsHermitian.eigenvalues`; the
  $\epsilon_{ij}$ need not be symmetric in the source, so symmetrize first.
  Conjuncts: (i) the lower bound $C_0^{-2}$; (ii) the upper bound
  $\omega(\rho(\mathcal E)+1)$; (iii) the condition number bound; (iv) the
  multiplicative bound for $\omega\in(0,2)$. Pitfall: $\kappa(P_{\rm ad})$ is a
  ratio of extreme eigenvalues of an operator self-adjoint only for
  $a(\cdot,\cdot)$; state (iii) as the two Rayleigh bounds. Depends on 20.5.
  Statable and provable at the pins. NASC: `schwarz_rayleigh_bounds`
  (Multilevel.lean), proved; it states (i)–(ii) for orthogonal projections, with
  an overlap constant $D$ in place of $\omega(\rho(\mathcal E)+1)$.

* **20.9. Two-level overlapping Schwarz.** Let $\Omega\subset\mathbb R^d$,
  $d=2,3$, be a polygon or polyhedron, $a(u,v)=\int_\Omega\nabla u\cdot\nabla
  v\,dx$ on the continuous piecewise linear functions on a shape-regular
  triangulation vanishing on $\partial\Omega$. Let $\{\Omega_i'\}_{i=1}^N$ be
  overlapping subdomains that are unions of elements, of diameters $H_i$, such
  that, for some $\delta_i>0$, every $x\in\Omega_i'$ lies in some
  $\Omega_j'$ with
  $\mathrm{dist}(x,\partial\Omega_j'\setminus\partial\Omega)\ge\delta_i$,
  and such that the $\Omega_i'$ can be coloured with at most $N_c$ colours so
  that subdomains of the same colour are disjoint. Let $H/\delta=\max_iH_i/
  \delta_i$, let the local spaces be the finite element functions vanishing
  outside $\Omega_i'$, and let the coarse space be a piecewise linear space on
  a shape-regular coarse mesh whose elements meeting $\Omega_i'$ have diameter
  at most $CH_i$, interpolated onto the fine mesh. With exact local and coarse
  solvers, the additive Schwarz operator satisfies
  $$\kappa(P_{\mathrm{ad}})\le C\Bigl(1+\frac H\delta\Bigr),$$
  where $C$ depends on $N_c$ (and the shape-regularity constants) but not on
  $h$, $H$ or $\delta$, and the linear dependence on $H/\delta$ is sharp. The
  multiplicative and hybrid variants then converge at rates bounded through
  20.8.

  *Assessment.* Not covered. The gap needs a mesh partition, overlap and coarse
  interpolation estimates before the abstract Schwarz bounds yield the stated
  condition number.

  *Lean target.* Carriers: `TauCeti.W1p0` and the energy form on a polygon or
  polyhedron. New definitions: shape-regular fine and coarse triangulations,
  overlapping subdomains as unions of elements with overlap $\delta_i$, the
  colouring constant $N_c$, the local spaces and the coarse interpolant.
  Conjuncts: (i) $\kappa(P_{\rm ad})\le C(1+H/\delta)$ with $C$ depending on
  $N_c$ and shape regularity; (ii) the sharpness of the linear dependence on
  $H/\delta$, as a family of examples. Depends on 20.8 and on a discrete
  Poincaré inequality in a boundary strip of width $\delta$, which is missing.
  NASC: `schwarz_condition_bound_of_overlap_decomposition` (Multilevel.lean),
  proved as a corollary of `schwarz_rayleigh_bounds`; it is the abstract step from a stable
  decomposition with constant $C(1+H/\delta)$ and a colouring bound.

* **20.11. Polylogarithmic bounds for nonoverlapping methods.** Let $\Omega$
  be partitioned into nonoverlapping, shape-regular subdomains of diameter
  about $H$, with a quasi-uniform finite element mesh of size $h$ aligned with
  the subdomain boundaries, and let the problem be reduced to the Schur
  complement $S_h$ on the interface. For the model problem of 20.10 in two
  dimensions:
  - the Bramble–Pasciak–Schatz, Neumann–Neumann (with coarse space) and BDDC
    preconditioners $B$ satisfy $\kappa(BS_h)\le C(1+\log(H/h))^2$, with $C$
    independent of $h$, $H$ and the number of subdomains;
  - these three bounds are sharp in their dependence on $H/h$.

  For $-\nabla\cdot(\rho\nabla u)$ in three dimensions, with $\rho$ a positive
  constant $\rho_i$ on each subdomain, the balancing Neumann–Neumann method,
  provided no subdomain boundary meets the Dirichlet boundary in only one or
  a few points, and the FETI-DP method with the Dirichlet preconditioner whose
  primal constraints are the subdomain vertex values and the averages over
  all edges and faces satisfy the condition number bound $C(1+\log(H/h))^2$,
  with $C$ independent of $h$, $H$ and the values $\rho_i$. In two
  dimensions, FETI-DP with the Dirichlet preconditioner and primal vertex
  values satisfies a bound of the same form. Apart from the eigenvalue
  $1$, the preconditioned BDDC and FETI-DP operators with corresponding
  primal constraints have the same spectrum.

  *Assessment.* Not covered. The interface operators can use Schur complements.
  The selected result is the polylogarithmic conditioning bound under the
  geometric and discrete constraints on primal and dual degrees of freedom.

  *Lean target.* Carriers: the block identities of
  `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` (for example
  `Matrix.det_fromBlocks₁₁`) and `TauCeti/Analysis/Matrix/SchurComplement.lean`
  for $S_h$. New definitions: the subdomain partition, interface, vertex, edge
  and face sets, the BPS, Neumann–Neumann, BDDC and FETI-DP preconditioners.
  Conjuncts: (i) the 2D bound $C(1+\log(H/h))^2$ for the three preconditioners;
  (ii) its sharpness; (iii) the 3D bounds for balancing Neumann–Neumann and
  FETI-DP with the stated primal constraints, uniform in the $\rho_i$; (iv) the
  2D FETI-DP bound; (v) the equality of the BDDC and FETI-DP spectra apart from
  $1$. Depends on 20.8 and on discrete harmonic extension and the $\log(H/h)$
  discrete Sobolev inequality, which are missing. NASC:
  `bddc_averaging_spectral_bounds` (Multilevel.lean), proved; it is the abstract
  step from a bound on the averaging operator to the spectral bounds.

## 21. Integral equations and boundary element methods

[Synopsis](SYNOPSIS.md#21-integral-equations-and-boundary-element-methods) · [Coverage inventory](STRUCTURE.md#21-integral-equations-and-boundary-element-methods)

The Fredholm and resolvent libraries cover substantial continuous operator
theory. The gaps concern kernels, approximation by finite operators, and
boundary discretization.

Spaces are complex normed spaces unless stated otherwise. Let
$G\subset\mathbb R^m$ be a nonempty compact Jordan measurable set equal to the
closure of its interior. A kernel $K$ on $G\times G$ is **weakly singular** if
it is continuous for $x\ne y$ and $|K(x,y)|\le M|x-y|^{\alpha-m}$ for some
$M>0$ and $\alpha\in(0,m]$. For the Laplace equation in $\mathbb R^m$,
$m=2,3$, the fundamental solution is
$$\Phi(x,y)=\frac1{2\pi}\log\frac1{|x-y|}\ (m=2),\qquad
\Phi(x,y)=\frac1{4\pi|x-y|}\ (m=3).$$

### Second-kind equations with compact operators

* **21.1. Riesz theory.** Integral operators $(A\varphi)(x)=\int_GK(x,y)
  \varphi(y)\,dy$ with continuous or weakly singular kernels are compact on
  $C(G)$; with continuous kernels they are also compact on $L^2(G)$. Let $A$ be
  a compact linear operator on a normed space $X$. Then:
  - the nullspace $N(I-A)$ is finite-dimensional and the range $(I-A)(X)$ is
    closed;
  - $I-A$ is injective if and only if it is surjective, and in that case
    $(I-A)^{-1}$ is bounded;
  - if $X$ is infinite-dimensional, then $0\in\sigma(A)$, and
    $\sigma(A)\setminus\{0\}$ consists of at most countably many eigenvalues,
    each of finite geometric multiplicity, with no accumulation point except
    possibly $0$.

  In particular, if $\varphi-A\varphi=0$ has only the trivial solution, then
  $\varphi-A\varphi=f$ has a unique solution for every $f\in X$, depending
  continuously on $f$. A compact operator from an infinite-dimensional normed
  space has no bounded inverse.

  *Assessment.* Partly covered. Mathlib and TauCeti give the abstract
  compact-operator Riesz assertions on Banach spaces: finite-dimensional
  nullspace, closed range, the Fredholm alternative for eigenvalues, countable
  spectrum accumulating only at $0$. The selected gap proves compactness for
  the integral operators under their kernel hypotheses.

  *Scope.* The selected claim is compactness for the indicated integral kernels
  in the two function-space settings.

  *Lean target.* Carriers at the pins: `C(G, ℂ)` with $G$ a compact metric
  space, `MeasureTheory.Lp ℂ 2 μ`, `IsCompactOperator`, and the Arzelà–Ascoli
  theorem `BoundedContinuousFunction.arzela_ascoli`. Conjuncts: (i) a
  continuous kernel gives a compact operator on `C(G, ℂ)` for every finite
  measure; (ii) a weakly singular kernel ($|K(x,y)|\le M|x-y|^{\alpha-m}$,
  $0<\alpha\le m$, continuous off the diagonal) gives a compact operator on
  $C(G)$ for $G\subset\mathbb R^m$ compact, Jordan measurable, the closure of
  its interior; (iii) a continuous kernel gives a compact operator on $L^2(G)$
  (Hilbert–Schmidt). Pitfall: for (ii) the integral
  $\int K(x,y) \varphi(y)\,dy$ is a Bochner integral that is $0$ when not
  integrable; integrability at each $x$ must be proved from $\alpha>0$ before
  the operator is defined. Statable and provable at the pins. NASC:
  `isCompactOperator_of_continuousKernel` and
  `isCompactOperator_of_small_diagonal_tails` (IntegralEquations.lean), sorry;
  they state (i) and a form of (ii) with uniformly small diagonal tails, over `RCLike 𝕜`.

* **21.2. Fredholm alternative.** A **dual system** $\langle X,Y\rangle$ is a
  pair of normed spaces with a nondegenerate bilinear form
  $\langle\cdot,\cdot\rangle$ on $X\times Y$; operators $A:X\to X$ and
  $B:Y\to Y$ are **adjoint** if $\langle A\varphi,\psi\rangle=\langle\varphi,
  B\psi\rangle$ for all $\varphi,\psi$. Let $A$ and $B$ be compact and adjoint.
  Then either $I-A$ and $I-B$ are both bijective, or both have nontrivial
  nullspaces with
  $$\dim N(I-A)=\dim N(I-B)<\infty,$$
  and then
  $(I-A)(X)=\{f\in X:\langle f,\psi\rangle=0\ \text{for all}\ \psi\in N(I-B)\}$
  and $(I-B)(Y)=\{g\in Y:\langle\varphi,g\rangle=0\ \text{for all}\
  \varphi\in N(I-A)\}$.

  *Assessment.* Partly covered. The compact index-zero and continuous-transpose
  results are available. The selected alternative uses a possibly different
  nondegenerate normed dual system and identifies solvability on both sides.

  *Scope.* The target is the normed-space dual Fredholm alternative and the
  compatibility condition for the inhomogeneous problem.

  *Lean target.* Carriers at the pins: pairings `X →ₗ[ℂ] Y →ₗ[ℂ] ℂ` (built with
  `LinearMap.mk₂`), `IsCompactOperator`, `TauCeti.isFredholm_one_sub`, and
  `TauCeti/Analysis/Fredholm/Transpose.lean`. Conjuncts: (i) the dichotomy;
  (ii) $\dim N(I-A)=\dim N(I-B)<\infty$; (iii) the range of $I-A$ is the
  annihilator of $N(I-B)$; (iv) symmetrically for $I-B$. The pairing need not
  be continuous; Kress's proof is by biorthogonal systems, not by the Banach
  transpose. Pitfall: `Module.finrank` of an infinite-dimensional space is $0$,
  so (ii) must carry `FiniteDimensional` explicitly, not only the equality of
  `finrank`. Statable and provable at the pins. NASC:
  `exists_fredholm_solution_iff_pairing` (IntegralEquations.lean), sorry; it
  states (iii) for Banach spaces over `RCLike 𝕜`.

### Projection and Nyström methods

* **21.5. Projection methods for second-kind equations.** Let $X$ be a Banach
  space, $K:X\to X$ bounded, $\lambda\ne0$ with $\lambda-K$ bijective, and
  $P_n:X\to X_n$ bounded projections with $\|K-P_nK\|\to0$; this holds when
  $K$ is compact and $P_nx\to x$ for all $x$. Then for $n\ge N$ the operators
  $\lambda-P_nK$ have inverses bounded uniformly in $n$, the solution $x_n\in
  X_n$ of $(\lambda-P_nK)x_n=P_ny$ satisfies
  $x-x_n=\lambda(\lambda-P_nK)^{-1}(x-P_nx)$, and
  $$\frac{|\lambda|}{\|\lambda-P_nK\|}\,\|x-P_nx\|\le\|x-x_n\|\le|\lambda|\,
  \|(\lambda-P_nK)^{-1}\|\,\|x-P_nx\|.$$
  Thus $x_n\to x$ at exactly the rate of the best approximation $P_nx\to x$.
  When $P_n$ is the orthogonal projection onto $X_n$ in a Hilbert space this is
  the **Galerkin method**, and when $P_n$ is interpolation at nodes in $X_n$
  it is the **collocation method**. Collocation with continuous piecewise linear
  interpolation on $[a,b]$ converges for every uniquely solvable second-kind
  equation with a continuous or weakly singular kernel.

  *Assessment.* Not covered. The Riesz theory excludes nontrivial homogeneous
  solutions, and the finite-section estimate (21.4) is a Hilbert-basis special
  case of the quasi-optimality. The missing approximation result proves
  eventual discrete solvability and the two-sided projection error for
  second-kind equations.

  *Lean target.* Carriers at the pins: `ContinuousLinearMap` with
  `IsCompactOperator`, the perturbation bound `norm_inverse_add_le`, and
  `ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator` with
  `banach_steinhaus` for the step from strong convergence of $P_n$ to
  $\|K-P_nK\|\to0$. Conjuncts: (i) eventual invertibility of $\lambda-P_nK$
  with uniformly bounded inverses; (ii) the identity $x-x_n=\lambda(\lambda-
  P_nK)^{-1}(x-P_nx)$; (iii) the two-sided bound; (iv) the sufficient condition
  for compact $K$; (v) convergence of collocation with piecewise linear
  interpolation for continuous and weakly singular kernels. Pitfall: the
  inverse of $\lambda-P_nK$ on $X$ must be `Ring.inverse` or a
  `ContinuousLinearEquiv`; `Ring.inverse` is $0$ when not invertible, so (iii)
  needs the invertibility in (i) as a conjunct for the same $n$. Depends on
  21.1. NASC: `exists_projection_secondKind_bounds` (IntegralEquations.lean),
  sorry; it states (i)–(iii) with unnamed constants, over `RCLike 𝕜`.

* **21.7. Collectively compact approximation.** A set of linear operators
  $\mathcal A$ from $X$ to $Y$ is **collectively compact** if
  $\{A\varphi:\varphi\in U,\ A\in\mathcal A\}$ is relatively compact for every
  bounded $U\subset X$. Let $X$ be a Banach space, $A:X\to X$ compact with
  $I-A$ injective, and $(A_n)$ collectively compact with $A_n\varphi\to
  A\varphi$ for all $\varphi$. Then $\|(A_n-A)A_n\|\to0$, and for all $n$ with
  $\|(I-A)^{-1}(A_n-A)A_n\|<1$ the inverse $(I-A_n)^{-1}$ exists, with
  $$\|(I-A_n)^{-1}\|\le\frac{1+\|(I-A)^{-1}A_n\|}
  {1-\|(I-A)^{-1}(A_n-A)A_n\|},$$
  and the solutions of $\varphi-A\varphi=f$ and $\varphi_n-A_n\varphi_n=f_n$
  satisfy
  $$\|\varphi_n-\varphi\|\le\frac{1+\|(I-A)^{-1}A_n\|}
  {1-\|(I-A)^{-1}(A_n-A)A_n\|}\bigl(\|(A_n-A)\varphi\|+\|f_n-f\|\bigr).$$
  Since $\|(I-A)^{-1}A_n\|\le\|(I-A)^{-1}\|\,\|A_n\|$, the bounds also hold
  with that product in the numerators.

  *Assessment.* Not covered. The theory of individual compact operators is
  available. The gap uses collective compactness and pointwise approximation to
  control inverse operators uniformly.

  *Lean target.* Carriers: `IsCompactOperator`, `ContinuousLinearEquiv` for the
  inverses, and `banach_steinhaus` for the uniform bound on $\|A_n\|$. New
  definition: collective compactness of a family as relative compactness of the
  union of the images of the unit ball. Conjuncts: (i) $\|(A_n-A)A_n\|\to 0$;
  (ii) the inverse bound with numerator $1+\|(I-A)^{-1}A_n\|$ wherever
  $\|(I-A)^{-1}(A_n-A)A_n\|<1$; (iii) the error bound. Pitfall: the denominator
  $1-\|(I-A)^{-1}(A_n-A)A_n\|$ is nonpositive for small $n$, and real division
  by it gives junk; quantify over the $n$ with the strict inequality. Depends
  on 21.1. NASC: `eventually_secondKind_boundedInverse`
  (IntegralEquations.lean), sorry; it states the eventual uniform inverse bound
  without the explicit constants.

* **21.8. Nyström method.** Let $K$ be continuous on $G\times G$ and let
  $Q_n(g)=\sum_{k=1}^n\alpha_k^{(n)}g(x_k^{(n)})$ be quadrature rules with
  $Q_n(g)\to\int_Gg\,dy$ for every $g\in C(G)$. The **Nyström operators**
  $(A_n\varphi)(x)=\sum_k\alpha_k^{(n)}K(x,x_k^{(n)})\varphi(x_k^{(n)})$ are
  collectively compact and converge pointwise to $A$ on $C(G)$, though not in
  norm unless $K=0$. Solving $\varphi_n-A_n\varphi_n=f$ is equivalent to solving the linear
  system for the nodal values $\varphi_n(x_j)$ and then using the
  Nyström interpolation formula
  $\varphi_n(x)=f(x)+\sum_k\alpha_kK(x,x_k)\varphi_n(x_k)$. If
  $\varphi-A\varphi=f$ is uniquely solvable, then for $n\ge N$ the Nyström
  equations are uniquely solvable, $\|(I-A_n)^{-1}\|_\infty$ is bounded
  uniformly in $n$, and
  $$\|\varphi-\varphi_n\|_\infty\le c\,\|(A-A_n)\varphi\|_\infty,$$
  so the error is of the order of the quadrature error for the integrands
  $K(x,\cdot)\varphi$.

  *Assessment.* Not covered. The missing result converts converging quadrature
  into pointwise and collectively compact operator approximation and a Nyström
  error estimate.

  *Lean target.* Carriers: `C(G, ℂ)` for a compact metric space $G$ with a
  finite measure, finite weighted sums for $Q_n$. Conjuncts: (i) collective
  compactness and pointwise convergence of the Nyström operators; (ii) the
  failure of norm convergence unless $K=0$; (iii) the equivalence of the
  operator equation with the nodal system and the interpolation formula; (iv)
  eventual unique solvability with $\sup_n\|(I-A_n)^{-1}\|_\infty<\infty$; (v)
  $\|\varphi-\varphi_n\|_\infty\le c\|(A-A_n)\varphi\|_\infty$. Pitfall: (ii)
  needs $G$ without isolated points, or a measure without atoms; for a Dirac
  measure $A_n=A$ is possible. Depends on 21.7. NASC:
  `exists_nystrom_convergence` (IntegralEquations.lean), sorry; it states
  (iii)–(iv) and convergence over `RCLike 𝕜`, without the rate (v).

### Volterra equations

* **21.9. Volterra equations of the second kind.** Let $I=[0,T]$,
  $D=\{(t,s):0\le s\le t\le T\}$, and $K\in C(D)$. There is a unique
  **resolvent kernel** $R\in C(D)$, satisfying
  $R(t,s)=K(t,s)+\int_s^tK(t,v)R(v,s)\,dv$ on $D$, and for every $g\in C(I)$
  the equation
  $$y(t)=g(t)+\int_0^tK(t,s)y(s)\,ds,\qquad t\in I,$$
  has a unique solution $y\in C(I)$, given by
  $y(t)=g(t)+\int_0^tR(t,s)g(s)\,ds$.
  For the weakly singular kernel $(t-s)^{-\alpha}K(t,s)$ with $0<\alpha<1$
  and $K\in C(D)$, the equation again has a unique solution in $C(I)$ for
  every $g\in C(I)$, and the resolvent kernel has the form
  $(t-s)^{-\alpha}Q(t,s)$ for $0\le s<t\le T$.

  *Assessment.* Not covered. Existing resolvent and integration theory supplies
  ingredients, and TauCeti has a half-line Volterra existence theorem with an
  explicit bound. Volterra equations need iterated triangular-kernel estimates
  that give convergence of the Neumann series without a smallness condition.

  *Lean target.* Carriers: interval integrals on $[0,T]$, `ContinuousOn` on the
  triangle $D$, and `TauCeti.exists_volterra_solution` as a model. Conjuncts:
  (i) existence and uniqueness of $R\in C(D)$ with the resolvent equation; (ii)
  unique solvability in $C(I)$ with the resolvent representation; (iii) the
  weakly singular case, with the resolvent of the form $(t-s)^{-\alpha}Q(t,s)$.
  Pitfall: $(t-s)^{-\alpha}$ at $t=s$ is the real power $0^{-\alpha}=0$ in Lean
  (`Real.rpow`), so the kernel must be specified on $s<t$ and integrated over
  $(0,t)$. Statable and provable at the pins. NASC: `exists_volterra_resolvent`
  (IntegralEquations.lean), sorry; it states (i)–(ii).

* **21.10. Piecewise polynomial collocation for Volterra equations.** Let
  $0=t_0<t_1<\dots<t_N=T$, $h_n=t_{n+1}-t_n$, $h=\max_nh_n$, and
  $0\le c_1<\dots<c_m\le1$. The **collocation solution** $u_h$ is the
  function that is a polynomial of degree at most $m-1$ on each
  $(t_n,t_{n+1}]$, possibly discontinuous at the mesh points, and satisfies
  the equation of 21.9 at the points $t_n+c_ih_n$. Let $g\in C^m(I)$ and
  $K\in C^m(D)$. There is $\bar h>0$ such that for $h<\bar h$ the collocation
  solution exists, is unique, and satisfies
  $$\max_{t\in I}|y(t)-u_h(t)|\le Ch^m,$$
  with $C$ depending on the $c_i$ but not on the mesh. Let
  $J_\nu=\int_0^1s^\nu\prod_i(s-c_i)\,ds$, assume $J_\nu=0$ for
  $0\le\nu<\kappa$ and $J_\kappa\ne0$ with $1\le\kappa\le m$, and let
  $g\in C^{m+\kappa}(I)$, $K\in C^{m+\kappa}(D)$. Then the **iterated
  collocation solution** $u_h^{\mathrm{it}}=g+\int_0^tK(t,s)u_h(s)\,ds$
  satisfies $\max_{1\le n\le N}|y(t_n)-u_h^{\mathrm{it}}(t_n)|\le Ch^{m+\kappa}$;
  if moreover $c_m=1$, then $u_h$ itself satisfies
  $\max_{1\le n\le N}|y(t_n)-u_h(t_n)|\le Ch^{m+\kappa}$, and then $\kappa\le
  m-1$. In particular the Gauss points ($\kappa=m$) give order $2m$ for
  $u_h^{\mathrm{it}}$ at the mesh points while $u_h$ is only of order $m$
  there, and the Radau II points ($\kappa=m-1$, $c_m=1$) give order $2m-1$ for
  $u_h$ at the mesh points.

  *Assessment.* Not covered. Interpolation and the stability of causal Volterra
  recursions are ingredients. The gap is the collocation recurrence and its
  uniform and nodal convergence orders.

  *Lean target.* Carriers: `Polynomial ℝ` pieces on the mesh intervals,
  interval integrals, `ContDiff ℝ m` on a neighbourhood of $D$. New definition:
  the collocation predicate. Conjuncts: (i) existence and uniqueness for
  $h<\bar h$; (ii) the global bound $Ch^m$; (iii) the nodal superconvergence of
  the iterated solution under the orthogonality condition $J_\nu=0$,
  $\nu<\kappa$; (iv) the nodal bound for $u_h$ when $c_m=1$, with
  $\kappa\le m-1$; (v) the Gauss and Radau II cases. Pitfall: $C^m(D)$ on a
  closed triangle must be stated as `ContDiffOn` on the triangle or `ContDiff`
  of an extension. Depends on 21.9. NASC: `IsVolterraCollocation` and
  `exists_volterraCollocation_error_le` (IntegralEquations.lean), sorry; they
  state (i)–(ii).

* **21.11. Graded meshes for weakly singular Volterra equations.** Consider
  $y(t)=g(t)+\int_0^t(t-s)^{-\alpha}K(t,s)y(s)\,ds$ with $0<\alpha<1$,
  $g\in C^m(I)$, $K\in C^m(D)$; its solution is in general not differentiable
  at $t=0$. Let $t_n=(n/N)^rT$ be the **graded mesh** with grading exponent
  $r=\mu/(1-\alpha)\ge1$, and $h=T/N$. Then for $h<\bar h$ the collocation
  solution of 21.10 (for any $0\le c_1<\dots<c_m\le1$) satisfies
  $$\max_{t\in I}|y(t)-u_h(t)|\le C(r)\begin{cases}h^\mu,&1-\alpha\le\mu\le
  m,\\ h^m,&\mu\ge m,\end{cases}$$
  so the grading $r=m/(1-\alpha)$ restores the order $m$, whereas the
  uniform mesh ($r=1$) gives only order $1-\alpha$.

  *Assessment.* Not covered. The kernel singularity and limited solution
  smoothness require graded-mesh consistency estimates. The selected result
  specifies the convergence rate as a function of the grading.

  *Lean target.* Carriers: those of 21.10. Conjuncts: (i) the bound
  $C(r)h^{\min\{\mu,m\}}$ for the graded mesh with $r=\mu/(1-\alpha)\ge1$; (ii)
  the corollaries for $r=m/(1-\alpha)$ and $r=1$. Pitfall: as in 21.9, the
  singular kernel is undefined at $s=t$, and the junk value of `Real.rpow` must
  not enter the integral. Depends on 21.9 (weakly singular case) and 21.10.
  NASC: `exists_graded_volterraCollocation_error_le` (IntegralEquations.lean),
  sorry; it states (i) in the form $C(T/n)^{\min\{m,r(1-\alpha)\}}$ for every
  $r\ge1$.

### Potentials and boundary element methods

* **21.12. Layer potentials and jump relations.** Let $D\subset\mathbb R^m$,
  $m=2,3$, be a bounded domain with boundary $\partial D$ of class $C^2$ and
  outward unit normal $\nu$. For $\varphi\in C(\partial D)$ the
  **single-layer** and **double-layer potentials** are
  $$u(x)=\int_{\partial D}\varphi(y)\Phi(x,y)\,ds(y),\qquad
  v(x)=\int_{\partial D}\varphi(y)\frac{\partial\Phi(x,y)}{\partial\nu(y)}
  \,ds(y),\qquad x\notin\partial D;$$
  they are harmonic in $D$ and in $\mathbb R^m\setminus\bar D$. Write
  $w_\pm(x)=\lim_{h\to+0}w(x\pm h\nu(x))$. Then $u$ is continuous on
  $\mathbb R^m$, and, uniformly on $\partial D$,
  $$v_\pm=K\varphi\pm\tfrac12\varphi,\qquad
  \frac{\partial u_\pm}{\partial\nu}=K'\varphi\mp\tfrac12\varphi,$$
  where $(K\varphi)(x)=\int_{\partial D}\varphi(y)\,\partial\Phi(x,y)/
  \partial\nu(y)\,ds(y)$ and $(K'\varphi)(x)=\int_{\partial D}\varphi(y)\,
  \partial\Phi(x,y)/\partial\nu(x)\,ds(y)$ are improper integrals with
  weakly singular kernels. The normal derivative of $v$ has no jump:
  $\nu\cdot(\nabla v(x+h\nu(x))-\nabla v(x-h\nu(x)))\to0$ uniformly. (Some
  texts define $K$ and $K'$ with a factor $2$, so that $2v_\pm=K\varphi\pm
  \varphi$ and $2\,\partial u_\pm/\partial\nu=K'\varphi\mp\varphi$.)

  *Assessment.* Not covered. The Laplace fundamental solutions and their
  harmonicity away from the pole are available. The missing results are the
  layer potentials, their harmonicity and the jump relations.

  *Lean target.* Carriers at the pins: `TauCeti.newtonianKernel` and
  `TauCeti.planarNewtonianKernel` (with the normalization of $\Phi$ to be
  checked against the item), the surface measure `μHE[m - 1]` restricted to
  $\partial D$, and `Set.IsLipschitzDomainWith` for the domain; a $C^2$
  boundary needs a new definition. New definitions: the outward normal, the
  single- and double-layer potentials, and $K$, $K'$. Conjuncts: (i)
  harmonicity off $\partial D$; (ii) continuity of $u$ on $\mathbb R^m$; (iii)
  the two jump relations, uniformly on $\partial D$; (iv) the continuity of the
  normal derivative of $v$. Pitfall: the kernels are weakly singular on
  $\partial D$; the Bochner integral is $0$ when not integrable, so
  integrability against the surface measure must be proved first. NASC:
  `circleSingleLayer` and `exists_circleSingleLayer_normal_jump`
  (BoundaryElements.lean), sorry; they state the radial jump of the single
  layer on a circle, a special case of (iii).

* **21.13. Mapping properties on Lipschitz boundaries.** Let
  $\Omega\subset\mathbb R^3$ be a bounded Lipschitz domain with boundary
  $\Gamma$, and let $S$, $D$ be the single- and double-layer potentials of an
  elliptic operator $-\mathrm{div}(A\nabla u)+2b\cdot\nabla u+cu$ with
  constant coefficients ($A$ symmetric positive definite), defined through its
  fundamental solution. Let $\gamma_0^\pm$ and $\gamma_1^\pm$ be the exterior
  ($+$) and interior ($-$) traces and conormal derivatives on $\Gamma$, and
  define the boundary integral operators $V=\gamma_0S$, $K_\pm=\gamma_0^\pm D$,
  $K'_\pm=\gamma_1^\pm S$ and $W=-\gamma_1D$. For $|s|<\frac12$ the following
  maps are continuous:
  $$V:H^{-1/2+s}(\Gamma)\to H^{1/2+s}(\Gamma),\quad
  K_\pm:H^{1/2+s}(\Gamma)\to H^{1/2+s}(\Gamma),$$
  $$K'_\pm:H^{-1/2+s}(\Gamma)\to H^{-1/2+s}(\Gamma),\quad
  W:H^{1/2+s}(\Gamma)\to H^{-1/2+s}(\Gamma),$$
  and $S:H^{-1/2+s}(\Gamma)\to H^{1+s}_{\mathrm{loc}}(\mathbb R^3)$. With
  $[w]$ the exterior minus the interior trace, the jump relations
  $$[S\varphi]=0,\quad[\gamma_1S\varphi]=-\varphi,\quad[D\psi]=\psi,\quad
  [\gamma_1D\psi]=0$$
  hold for all $\varphi\in H^{-1/2}(\Gamma)$ and $\psi\in H^{1/2}(\Gamma)$.

  *Assessment.* Not covered. The Sobolev API supplies ingredients for traces on
  Lipschitz domains. The layer operators must be defined and bounded on the
  boundary Sobolev spaces with the stated dualities.

  *Lean target.* Carriers: `TauCeti.W1p`, the traces of
  `TauCeti/Analysis/Sobolev/LipschitzDomain/Trace`, `Set.IsLipschitzDomainWith`
  and `μHE[2]` on $\Gamma\subset\mathbb R^3$. New definitions: $H^s(\Gamma)$
  for $|s|\le1$ (Slobodeckij norm for $0<s<1$, duality for $s<0$), the conormal
  derivative, the potentials $S$, $D$ for constant coefficients, and $V$,
  $K_\pm$, $K'_\pm$, $W$. Conjuncts: (i) the four boundary mappings for
  $|s|<\frac12$; (ii) $S:H^{-1/2+s}\to H^{1+s}_{\rm loc}$; (iii) the four jump
  relations. Pitfall: a dual norm defined as a real `⨆` over an unbounded or
  empty set is junk; define it in `ℝ≥0∞` or on the dual space. The fundamental
  solution of the general constant-coefficient operator is missing. NASC:
  `newtonSingleLayer`, `boundaryHhalfNormSq`, `boundaryHminusHalfNorm` and
  `exists_newtonSingleLayer_trace_bound` (BoundaryElements.lean), sorry; they
  state (i) for $V$ of the Laplacian at $s=0$ on continuous densities, with
  norms in `ℝ≥0∞`.

* **21.14. Ellipticity of the single-layer operator.** For the Laplace
  operator in $\mathbb R^3$ and a bounded Lipschitz domain, there is a
  constant $c_V>0$ such that
  $$\langle V\varphi,\varphi\rangle\ge c_V\|\varphi\|^2_{H^{-1/2}(\Gamma)}
  \qquad(\varphi\in H^{-1/2}(\Gamma)),$$
  and if moreover $\Gamma$ is connected, there is a constant $c_W>0$ such that
  $$\langle W\psi,\psi\rangle\ge c_W\|\psi\|^2_{H^{1/2}(\Gamma)/\mathbb K}
  \qquad(\psi\in H^{1/2}(\Gamma)).$$
  Hence the first-kind equation $V\varphi=g$ has a unique solution
  $\varphi\in H^{-1/2}(\Gamma)$ for every $g\in H^{1/2}(\Gamma)$, and its
  Galerkin approximations in any closed subspace are quasi-optimal (Céa's
  lemma).

  *Assessment.* Not covered. The gap comprises the ellipticity of $V$ and $W$
  in the boundary energy norms and the resulting unique solvability and
  quasi-optimality.

  *Lean target.* Carriers: those of 21.13, `IsCoercive` for the form of $V$,
  and Céa's lemma (section 18). Conjuncts: (i) $\langle V\varphi,\varphi
  \rangle\ge c_V\|\varphi\|^2_{H^{-1/2}}$; (ii) for connected $\Gamma$, the ellipticity of $W$
  on the quotient by constants; (iii) unique solvability of $V\varphi=g$; (iv)
  quasi-optimality of Galerkin approximations in closed subspaces. Pitfall: a
  statement with `ENNReal.toReal` of the $H^{-1/2}$ norm is vacuous where the
  norm is $\top$; state (i) on the completed space, or carry finiteness.
  Depends on 21.13. NASC: `exists_newtonSingleLayer_elliptic_bound`
  (BoundaryElements.lean), sorry; it states (i) on continuous densities as an
  inequality in `ℝ≥0∞`, so the conclusion also gives finiteness of the
  $H^{-1/2}$ norm.

* **21.15. Galerkin boundary element methods under a Gårding inequality.**
  Let $H$ be a Hilbert space, $(S_\ell)$ finite-dimensional subspaces with
  $\inf_{v\in S_\ell}\|u-v\|_H\to0$ for every $u\in H$, $a$ a bounded
  sesquilinear form with $|a(u,u)|\ge\alpha\|u\|_H^2$ for some $\alpha>0$, and
  $t$ a bounded sesquilinear form whose associated operator $H\to H'$ is
  compact. Assume that $a(u,v)+t(u,v)=0$ for all $v\in H$ implies $u=0$. Then
  for every $F\in H'$ the problem $a(u,v)+t(u,v)=F(v)$ for all $v\in H$ has a
  unique solution $u\in H$; there is $\ell_0$ such that for $\ell\ge\ell_0$
  the Galerkin equations in $S_\ell$ have a unique solution $u_\ell$, and
  $$\|u-u_\ell\|_H\le C\min_{v\in S_\ell}\|u-v\|_H$$
  with $C$ independent of $\ell$.

  *Assessment.* Partly covered. TauCeti gives unique solvability for compact
  perturbations of coercive real forms under injectivity. The selected
  conclusions are eventual discrete well-posedness and uniform
  quasi-optimality.

  *Scope.* The selected claims are eventual discrete well-posedness and
  quasi-optimality uniformly over the approximation spaces.

  *Lean target.* Carriers at the pins:
  `existsUnique_forall_apply_eq_of_garding` (real Hilbert spaces),
  `IsCompactOperator`, and `Submodule` for $S_\ell$. Conjuncts: (i) eventual
  unique solvability of the Galerkin equations; (ii) $\|u-u_\ell\|\le
  C\min_{v\in S_\ell}\|u-v\|$ with $C$ independent of $\ell$. The continuous
  solvability, already covered in the real case, is needed for sesquilinear
  forms. Pitfall: the minimum over $S_\ell$ is attained because $S_\ell$ is
  finite-dimensional; as a real `⨅` it is correct, but `Metric.infDist` is the
  cleaner carrier. NASC: `eventually_galerkin_wellPosed_compactPerturbation`
  (BoundaryElements.lean), sorry; it states (i)–(ii) with the NASC
  `bestApproximationError`.

* **21.17. Boundary value problems by layer potentials.** Let $D\subset
  \mathbb R^m$, $m=2,3$, be a bounded domain of class $C^2$ with connected
  boundary, and let $K$, $K'$ be the operators of 21.12 on $C(\partial D)$,
  which are adjoint for the pairing $\langle\varphi,\psi\rangle=\int_{\partial
  D}\varphi\psi\,ds$.
  - The operators $\tfrac12I-K$ and $\tfrac12I-K'$ are injective, hence
    bijective on $C(\partial D)$ by 21.1. The nullspace of $\tfrac12I+K$ is
    spanned by the constant $1$, and that of $\tfrac12I+K'$ by a function
    $\psi_0$ with $\int_{\partial D}\psi_0\,ds=1$ (the **natural charge**),
    whose single-layer potential is constant in $D$.
  - (Interior Dirichlet problem.) For $f\in C(\partial D)$ let $\varphi$ solve
    $\tfrac12\varphi-K\varphi=-f$. The double-layer potential $v$ with density
    $\varphi$, restricted to $D$, extends continuously to $\bar D$ with
    boundary values $f$; it is the unique function harmonic in $D$,
    continuous on $\bar D$ and equal to $f$ on $\partial D$.
  - (Interior Neumann problem.) For $g\in C(\partial D)$ the equation
    $\tfrac12\psi+K'\psi=g$ is solvable if and only if $\int_{\partial D}
    g\,ds=0$, and then the single-layer potential $u$ with density $\psi$
    satisfies $\partial u_-/\partial\nu=g$ uniformly on $\partial D$. Hence
    the interior Neumann problem is solvable exactly when $\int_{\partial
    D}g\,ds=0$.

  For the unit circle, $\partial\Phi(x,y)/\partial\nu(y)=\partial\Phi(x,y)/
  \partial\nu(x)=-1/(4\pi)$ for $x\ne y$ on the circle, so $K\varphi=K'\varphi=
  -\frac1{4\pi}\int\varphi\,ds$, $\psi_0=1/(2\pi)$, and $\tfrac12I-K$ is
  injective while $\tfrac12I+K$ annihilates the constants.

  *Assessment.* Not covered. The Fredholm alternative of 21.2 and the jump
  relations of 21.12 are the ingredients. The gap is the identification of the
  nullspaces of $\tfrac12I\pm K$, $\tfrac12I\pm K'$ by the uniqueness theorems
  for the Dirichlet and Neumann problems, and the resulting existence theorems.

  *Lean target.* Carriers: those of 21.12, `C(∂D, ℝ)` with the pairing
  $\int\varphi\psi\,ds$, and the maximum principle of
  `TauCeti/Analysis/PDE/MaximumPrinciple` for uniqueness of the interior
  Dirichlet problem. Conjuncts: (i) injectivity, hence bijectivity, of
  $\tfrac12I-K$ and $\tfrac12I-K'$; (ii) the nullspaces of $\tfrac12I+K$ and
  $\tfrac12I+K'$ and the natural charge; (iii) existence and uniqueness for the
  interior Dirichlet problem; (iv) the solvability criterion for the interior
  Neumann problem. Hypotheses: $\partial D$ connected and of class $C^2$.
  Depends on 21.1, 21.2 and 21.12. No NASC declaration.

## 22. Inverse problems and regularization

[Synopsis](SYNOPSIS.md#22-inverse-problems-and-regularization) · [Coverage inventory](STRUCTURE.md#22-inverse-problems-and-regularization)

The compact singular expansion, finite-dimensional pseudoinverse and posterior
kernels give reusable foundations. The selected results control regularization
and conditional inference in their numerical and infinite-dimensional
settings.

Unless stated otherwise, $X$ and $Y$ are Hilbert spaces over $\mathbb K$ with
inner products $(\cdot,\cdot)$, $K:X\to Y$ is a bounded linear operator with
adjoint $K^*$, null space $N(K)$ and range $R(K)=K(X)$. Exact data are
$y\in Y$, and noisy data $y^\delta\in Y$ satisfy $\|y^\delta-y\|\le\delta$
with **noise level** $\delta>0$. The regularization parameter is $\alpha>0$,
or an integer $m$ for iterative methods. For a compact $K$ with infinitely
many nonzero singular values the system $(\sigma_n,e_n,g_n)$ of 22.2 is
indexed by $n\in\mathbb N$; for finite rank the sums below are finite.

### Ill-posedness and the singular value decomposition

* **22.3. Picard criterion.** Let $K:X\to Y$ be compact with singular system
  $(\sigma_n,e_n,g_n)$. The equation $Kx=y$ has a solution if and only if
  $y\in N(K^*)^\perp$ and
  $$\sum_n\frac{|(y,g_n)|^2}{\sigma_n^2}<\infty .$$
  In that case $x=\sum_n\sigma_n^{-1}(y,g_n)e_n$ is a solution, and it is the
  solution in $N(K)^\perp$.

  *Assessment.* TauCeti's compact rank-one expansion supplies a singular
  system. The gap characterizes the exact operator range by a weighted square
  summability condition and gives the minimal-norm solution series.

  *Lean target.* Carriers at the pins: `ContinuousLinearMap.adjoint`, `Orthonormal`, `Summable` and
  `tsum`; TauCeti's `IsCompactOperator.exists_orthonormal_hasSum_rankOne` supplies a singular system
  for a compact $K$. No new definition is needed if the singular system enters as hypotheses:
  orthonormal $e$ and $g$, $\sigma_n>0$, $Ke_n=\sigma_ng_n$, $K^*g_n=\sigma_ne_n$, and completeness
  in the form that $v\perp g_n$ for all $n$ holds exactly when $K^*v=0$. Conjuncts: (i)
  $(\exists x,\ Kx=y)$ if and only if $y$ is orthogonal to the kernel of $K^*$ and
  $n\mapsto(y,g_n)^2/\sigma_n^2$ is summable; (ii) in that case $x=\sum_n\sigma_n^{-1}(y,g_n)e_n$
  satisfies $Kx=y$; (iii) this $x$ lies in the orthogonal complement of the kernel of $K$. Pitfall:
  `tsum` of a non-summable family is $0$, so (ii) must sit under the summability conjunct, and the
  coefficient divides by $\sigma_n$, which needs $\sigma_n>0$. Statable and provable at the pins.
  NASC: `NASC.exists_eq_image_iff_picard` (`NASC/Regularization.lean`), sorry; it states (i) and
  (ii) and omits (iii).

* **22.4. Moore–Penrose generalized inverse.** Let $K:X\to Y$ be bounded and
  linear. An element $\hat x\in X$ is a **best approximate solution** of
  $Kx=y$ if $\|K\hat x-y\|\le\|Kx-y\|$ for all $x\in X$, and a
  **minimal norm solution** if moreover $\|\hat x\|\le\|x\|$ for every best
  approximate solution $x$.
  - A best approximate solution exists if and only if $y$ lies in
    $D(K^\dagger)=R(K)\oplus R(K)^\perp$, a dense subspace of $Y$. For such
    $y$ the best approximate solutions are the solutions of the normal
    equation $K^*Kx=K^*y$; they form the affine subspace $x^\dagger+N(K)$,
    where $x^\dagger$ is the unique minimal norm solution, the unique
    best approximate solution in $N(K)^\perp$.
  - The **Moore–Penrose generalized inverse** $K^\dagger:D(K^\dagger)\to X$,
    $K^\dagger y=x^\dagger$, is linear with closed graph. It is bounded if and
    only if $R(K)$ is closed, and then $D(K^\dagger)=Y$.
  - If $K$ is compact with singular system $(\sigma_n,e_n,g_n)$, then
    $D(K^\dagger)=\{y\in Y:\sum_n\sigma_n^{-2}|(y,g_n)|^2<\infty\}$ and
    $K^\dagger y=\sum_n\sigma_n^{-1}(y,g_n)e_n$. In particular $R(K)$ is
    closed, and $K^\dagger$ bounded, if and only if $K$ has finite rank.

  *Assessment.* Partly covered. TauCeti constructs the finite-dimensional
  Moore–Penrose inverse in singular coordinates. The general dense domain,
  closed graph, boundedness criterion and compact-operator formula remain
  gaps.

  *Scope.* The target is the closed, densely defined generalized inverse for
  bounded operators between Hilbert spaces, including the case of nonclosed
  range.

  *Lean target.* Carriers at the pins: `LinearPMap` with `LinearPMap.IsClosed`,
  `Submodule.orthogonal`, `LinearMap.range`, `Submodule.starProjection` onto the closure of the
  range, and TauCeti's finite-dimensional `LinearMap.moorePenroseInverse`. New definition: the
  generalized inverse of a bounded $K:X\to Y$, a linear partial map from $Y$ to $X$ whose domain is
  the range of $K$ plus its orthogonal complement and whose value is the element of the orthogonal
  complement of the kernel mapped to the projection of $y$ onto the closed range. Conjuncts: (i) a
  best approximate solution exists exactly for $y$ in the domain, and the domain is dense; (ii) for
  such $y$ the best approximate solutions are the solutions of $K^*Kx=K^*y$, they form
  $x^\dagger+N(K)$, and $x^\dagger$ is the unique one of minimal norm; (iii) the graph is closed;
  (iv) the map is continuous on its domain if and only if the range is closed, and then the domain
  is all of $Y$; (v) for compact $K$ with a singular system, the domain and value are the Picard
  series of 22.3, and the range is closed exactly when $K$ has finite rank. Pitfall: continuity of a
  partial map is continuity on the domain subtype, not of an extension by zero. Depends on 22.3 for
  (v). Statable at the pins. NASC: `NASC.generalizedInverseDomain` and
  `NASC.exists_generalizedInverse_closedGraph` (`NASC/Regularization.lean`), sorry; they state
  density, the closed graph, the normal equation with minimality, and the boundedness criterion, but
  not the existence characterization of (i), the affine set of (ii), or (v).

### Linear regularization

* **22.5. Regularization schemes and parameter choice.** Let $K:X\to Y$ be
  bounded, linear and injective. A family of bounded linear operators
  $R_\alpha:Y\to X$, $\alpha>0$, is a **regularization scheme** if
  $R_\alpha Kx\to x$ as $\alpha\to0$ for every $x\in X$. A **parameter choice**
  $\alpha=\alpha(\delta,y^\delta)$ is **regular** if
  $R_{\alpha(\delta,y^\delta)}y^\delta\to K^{-1}y$ as $\delta\to0$ for every
  $y\in R(K)$ and all $y^\delta$ with $\|y^\delta-y\|\le\delta$; it is
  **a priori** if it depends on $\delta$ only. For every regularization
  scheme
  $$\|R_\alpha y^\delta-K^{-1}y\|\le\delta\|R_\alpha\|+\|R_\alpha Kx-x\|,
  \qquad x=K^{-1}y .$$
  - If $K$ is compact and $X$ is infinite dimensional, then
    $\sup_{\alpha>0}\|R_\alpha\|=\infty$, and $R_\alpha K$ does not converge to
    $I$ in operator norm.
  - (Spectral filters.) Let $K$ be compact and injective with singular system
    $(\sigma_n,e_n,g_n)$. Let $q:(0,\infty)\times(0,\|K\|]\to\mathbb R$ be
    bounded, with $|q(\alpha,\sigma)|\le c(\alpha)\sigma$ for some
    $c(\alpha)>0$ and $\lim_{\alpha\to0}q(\alpha,\sigma)=1$ for each
    $\sigma\in(0,\|K\|]$. Then
    $R_\alpha y=\sum_n\sigma_n^{-1}q(\alpha,\sigma_n)(y,g_n)e_n$ defines a
    regularization scheme with $\|R_\alpha\|\le c(\alpha)$.
  - (Spectral cut-off.) For $K$ as above, $R_my=\sum_{\sigma_n\ge\sigma_m}
    \sigma_n^{-1}(y,g_n)e_n$ is a regularization scheme as $m\to\infty$, with
    $\|R_m\|=1/\sigma_m$.
  - (**Bakushinskii's theorem**.) If some regularization scheme admits a
    regular parameter choice $\alpha=\alpha(y^\delta)$ that does not depend on
    $\delta$, then $K^{-1}:R(K)\to X$ is bounded. Hence for an ill-posed
    equation every regular parameter choice uses the noise level.

  *Assessment.* The spectral calculus is a prerequisite. The selected theorem relates approximation
  on the exact range and noise amplification to a convergent parameter choice, with spectral cutoff
  as a model, and Bakushinskii's theorem shows that a regular choice must use the noise level.

  *Lean target.* Carriers at the pins: `Filter.Tendsto` along `nhdsWithin 0 (Set.Ioi 0)`, the
  operator norm, `Function.Injective`, `IsCompactOperator`, and `BddAbove`. New definitions: a
  regularization scheme for an injective $K$, a family of bounded operators $R_\alpha$ with
  $R_\alpha Kx\to x$ as $\alpha\to0^+$ for every $x$; and a regular parameter choice, a function of
  $(\delta,y^\delta)$ with positive values such that for every $x$ and every $\varepsilon>0$ there
  is $\delta_0>0$ with $\|R_{\alpha(\delta,y^\delta)}y^\delta-x\|<\varepsilon$ whenever
  $0<\delta<\delta_0$ and $\|y^\delta-Kx\|\le\delta$. Conjuncts: (i) the error splitting; (ii) for
  compact $K$ and infinite-dimensional $X$ the norms $\|R_\alpha\|$ are unbounded and $R_\alpha K$
  does not tend to the identity in operator norm; (iii) the spectral filter gives a scheme with
  $\|R_\alpha\|\le c(\alpha)$; (iv) the cut-off has $\|R_m\|=1/\sigma_m$ for antitone $\sigma$; (v)
  (Bakushinskii) if a regular choice does not depend on $\delta$, then there is $C$ with
  $\|x\|\le C\|Kx\|$ for all $x$. Pitfall: the convergence in the definition is uniform over the
  noisy data, which a plain `Tendsto` of one data path does not express. The singular system enters
  as in 22.3. Statable at the pins. NASC: `NASC.regularization_tendsto_of_noise_control`
  (`NASC/Regularization.lean`), proved; it is the a priori convergence for one data path under
  $\delta\|R_{\alpha(\delta)}\|\to0$. Conjuncts (ii)–(v) have no NASC declaration.

* **22.6. Tikhonov regularization.** Let $K:X\to Y$ be bounded and linear,
  and $\alpha>0$.
  - For every $y\in Y$ the **Tikhonov functional**
    $\|Kx-y\|^2+\alpha\|x\|^2$ has a unique minimizer $x_\alpha$ on $X$. It is
    the unique solution of the normal equation
    $$\alpha x_\alpha+K^*Kx_\alpha=K^*y,$$
    so $x_\alpha=R_\alpha y$ with $R_\alpha=(\alpha I+K^*K)^{-1}K^*$, and
    $x_\alpha$ depends continuously on $y$.
  - If $K$ is injective, then $(R_\alpha)$ is a regularization scheme and
    $\|R_\alpha\|\le\|K\|/\alpha$. If $K$ is compact and injective, then
    $\|R_\alpha\|\le1/(2\sqrt\alpha)$, and
    $R_\alpha y=\sum_n\sigma_n(\alpha+\sigma_n^2)^{-1}(y,g_n)e_n$.
  - (A priori convergence.) Let $K$ be compact and injective, $y\in R(K)$,
    and let $\alpha(\delta)\to0$ and $\delta^2/\alpha(\delta)\to0$ as
    $\delta\to0$. Then $R_{\alpha(\delta)}y^\delta\to K^{-1}y$ as $\delta\to0$,
    uniformly over all $y^\delta$ with $\|y^\delta-y\|\le\delta$.

  *Assessment.* A coercive linear solve supports the normal equation. The gap
  comprises the singular filter formula, uniform noise bound and convergence
  under the parameter condition.

  *Lean target.* Carriers at the pins: `IsCoercive.continuousLinearEquivOfBilin` (Lax–Milgram),
  `ContinuousLinearMap.adjoint`, and `Real.sqrt`. No new definition is needed. Conjuncts: (i) for
  $\alpha>0$ there is a bounded $R_\alpha$ with $\alpha R_\alpha y+K^*KR_\alpha y=K^*y$, and
  $R_\alpha y$ is the unique minimizer of the Tikhonov functional; (ii)
  $\|R_\alpha\|\le\|K\|/\alpha$, and $(R_\alpha)$ is a regularization scheme when $K$ is injective;
  (iii) $\|R_\alpha\|\le1/(2\sqrt\alpha)$ and, for compact injective $K$ with a singular system, the
  filter series; (iv) the a priori convergence, uniform over noisy data, when $\alpha(\delta)\to0$
  and $\delta^2/\alpha(\delta)\to0$. The bound in (iii) holds for every bounded $K$, so the Lean
  form need not assume compactness there. Depends on 22.5 for the definition of a scheme. NASC:
  `NASC.exists_tikhonov_normal_solve` (`NASC/Regularization.lean`, with the operator
  `NASC.tikhonovNormalOp`), proved, gives (i) with the bound
  $1/(2\sqrt\alpha)$; the helpers `NASC.tikhonov_normal_inner`, `NASC.norm_le_of_tikhonov_normal`,
  `NASC.tikhonov_objective_eq_add_error` and `NASC.norm_tikhonov_exactData_le` are proved. The
  scheme property, the series and (iv) are open.

* **22.7. Tikhonov convergence rates and saturation.** Let $K:X\to Y$ be
  compact and injective, $y=Kx^\dagger$, and $x_\alpha=R_\alpha y$ the
  Tikhonov solution for exact data.
  - (Source condition.) If $x^\dagger=(K^*K)^\nu w$ with $0<\nu\le1$ and
    $w\in X$, then $\|x_\alpha-x^\dagger\|\le\alpha^\nu\|w\|$ for all
    $\alpha>0$. For noisy data,
    $$\|R_\alpha y^\delta-x^\dagger\|\le\frac{\delta}{2\sqrt\alpha}
    +\alpha^\nu\|w\|,$$
    and the choice $\alpha=(\delta/\|w\|)^{2/(2\nu+1)}$, for $w\ne0$, gives
    $\|R_\alpha y^\delta-x^\dagger\|\le\frac32\|w\|^{1/(2\nu+1)}
    \delta^{2\nu/(2\nu+1)}$.
  - (Characterization at $\nu=1$.) $\|x_\alpha-x^\dagger\|=O(\alpha)$ as
    $\alpha\to0$ if and only if $x^\dagger\in R(K^*K)$, that is,
    $y\in R(KK^*K)$.
  - (Saturation.) If $\|x_\alpha-x^\dagger\|=o(\alpha)$ as $\alpha\to0$, then
    $x^\dagger=0$. So no source condition with $\nu>1$ improves the rate
    $O(\alpha)$.

  *Assessment.* The compact spectral expansion supplies the filter
  coordinates. The missing results require the rate under a source condition,
  the endpoint converse, and saturation.

  *Lean target.* Carriers at the pins: `ContinuousLinearMap.adjoint`, `Real.rpow`,
  `Asymptotics.IsBigO` and `Asymptotics.IsLittleO` along `nhdsWithin 0 (Set.Ioi 0)`. The fractional
  power $(K^*K)^\nu$ has no carrier for real Hilbert spaces: `CFC.rpow` needs a continuous
  functional calculus instance that Mathlib supplies through the complex C$^*$-algebra structure.
  State the source condition in singular coordinates: $(x^\dagger,e_n)=\sigma_n^{2\nu}(w,e_n)$ for
  all $n$, with $w\in X$. Conjuncts: (i) $\|x_\alpha-x^\dagger\|\le\alpha^\nu\|w\|$ for $0<\nu\le1$
  and $\alpha>0$; (ii) the noisy bound $\delta/(2\sqrt\alpha)+\alpha^\nu\|w\|$; (iii) the bound
  $\frac32\|w\|^{1/(2\nu+1)}\delta^{2\nu/(2\nu+1)}$ at $\alpha=(\delta/\|w\|)^{2/(2\nu+1)}$ for
  $w\ne0$; (iv) $\|x_\alpha-x^\dagger\|=O(\alpha)$ if and only if $x^\dagger$ is in the range of
  $K^*K$; (v) $o(\alpha)$ forces $x^\dagger=0$. Pitfall: `Real.rpow` with a zero base and exponent
  $2\nu>0$ is $0$, as wanted, but (iii) divides by $\|w\|$, so $w\ne0$ must stay a hypothesis.
  Depends on 22.6 and the singular system of 22.3. Statable at the pins. NASC:
  `NASC.tikhonov_error_le_of_adjoint_source` (`NASC/Regularization.lean`), proved, gives (ii) at
  $\nu=1$ with $x^\dagger=K^*Kw$; (i) for $\nu<1$, (iii), (iv) and (v) are open.

* **22.8. Discrepancy principle for Tikhonov regularization.** Let
  $K:X\to Y$ be bounded and linear with dense range, and $\delta>0$. For
  $y\in Y$, an element $x_0$ is a **minimum norm solution with discrepancy**
  $\delta$ if $\|Kx_0-y\|\le\delta$ and
  $\|x_0\|=\inf\{\|x\|:\|Kx-y\|\le\delta\}$.
  - For every $y\in Y$ there is a unique such $x_0$. If $\|y\|\le\delta$, then
    $x_0=0$. If $\|y\|>\delta$, then $x_0$ is the Tikhonov solution
    $(\alpha I+K^*K)^{-1}K^*y$ for a parameter $\alpha>0$ with
    $\|Kx_0-y\|=\delta$ (**Morozov's discrepancy principle**), and
    $\alpha(\|y\|-\delta)\le\|K\|^2\delta$.
  - (Regularity.) Let $K$ also be injective, $y\in R(K)$, and
    $\|y^\delta-y\|\le\delta<\|y^\delta\|$, and let $x^\delta$ be the minimum
    norm solution for the data $y^\delta$ with discrepancy $\delta$. Then
    $x^\delta\to K^{-1}y$ as $\delta\to0$.
  - (Rate.) If moreover $K^{-1}y=K^*z$ with $z\in Y$, then
    $\|x^\delta-K^{-1}y\|\le2\sqrt{\|z\|\,\delta}$.

  *Assessment.* Convexity and Hilbert projection supply ingredients. The
  discrepancy-constrained minimization and its relation to a Tikhonov
  parameter and error rate remain open.

  *Lean target.* Carriers at the pins: `DenseRange`, `ContinuousLinearMap.adjoint`, `IsLeast` for
  the constrained minimum, and `Real.sqrt`. No new definition is needed. Conjuncts: (i) for every
  $y$ and $\delta>0$ the set $\{x:\|Kx-y\|\le\delta\}$ has a unique element of least norm $x_0$;
  (ii) $\|y\|\le\delta$ gives $x_0=0$; (iii) $\|y\|>\delta$ gives $\alpha>0$ with
  $\alpha x_0+K^*Kx_0=K^*y$, $\|Kx_0-y\|=\delta$ and $\alpha(\|y\|-\delta)\le\|K\|^2\delta$; (iv)
  for injective $K$, $y=Kx$, and data with $\|y^\delta-y\|\le\delta<\|y^\delta\|$, the minimum-norm
  solutions converge to $x$, uniformly over the data; (v) if $x=K^*z$, the error is at most
  $2\sqrt{\|z\|\delta}$. Pitfall: nonemptiness of the constraint set uses the dense range when
  $\|y\|>\delta$. Statable at the pins. NASC: `NASC.exists_morozov_parameter`
  (`NASC/Regularization.lean`), sorry; it states (iii) together with minimality and uniqueness when
  $\|y\|>\delta$, and omits (ii), (iv) and (v).

* **22.9. Landweber iteration.** Let $K:X\to Y$ be compact and injective,
  and $0<a<1/\|K\|^2$. The **Landweber iteration**
  $x_0=aK^*y$, $x_k=(I-aK^*K)x_{k-1}+aK^*y$ for $k\ge1$, gives
  $$x_m=R_my,\qquad R_m=a\sum_{k=0}^m(I-aK^*K)^kK^*,$$
  and $(R_m)$ is a regularization scheme as $m\to\infty$ with
  $\|R_m\|\le\sqrt{a(m+1)}$. Hence $R_{m(\delta)}y^\delta\to K^{-1}y$ when
  $m(\delta)\to\infty$ and $\delta^2m(\delta)\to0$. If in addition $K$ has
  dense range, $y\in R(K)$ and $\gamma>1$, then for each $\delta>0$ there is a
  smallest $m(\delta)$ with $\|KR_{m(\delta)}y^\delta-y^\delta\|\le\gamma\delta$,
  and $R_{m(\delta)}y^\delta\to K^{-1}y$ as $\delta\to0$.

  *Assessment.* The adjoint gives the gradient step. The numerical gap is the
  filter representation and its norm bound, with convergence for both an a
  priori stopping rule and discrepancy stopping.

  *Lean target.* Carriers at the pins: `ContinuousLinearMap.adjoint`, powers in the ring of
  operators, `Finset.sum`, `Real.sqrt` and `Filter.Tendsto`. New definition: the Landweber operator
  $R_m=a\sum_{k=0}^m(I-aK^*K)^kK^*$. Conjuncts: (i) the iterates satisfy $x_m=R_my$; (ii)
  $\|R_m\|\le\sqrt{a(m+1)}$, which holds for every bounded $K$; (iii) $R_mKx\to x$ for injective
  $K$; (iv) convergence for an a priori stopping index with $m(\delta)\to\infty$ and
  $\delta^2m(\delta)\to0$; (v) existence of the first discrepancy index and convergence for it.
  Pitfall: the index $m$ counts $m+1$ gradient steps, and an off-by-one changes (ii). Depends on
  22.5 for the scheme. Statable at the pins. NASC: `NASC.landweberFilter`,
  `NASC.landweberFilter_norm_le_and_tendsto` and `NASC.exists_landweber_discrepancy_tendsto`
  (`NASC/Regularization.lean`), sorry; they state (ii), (iii) and (v); (i) and (iv) are missing.

* **22.10. Bregman distances and error estimates.** Let $U$ be a Banach
  space, $J:U\to\mathbb R\cup\{+\infty\}$ proper, convex and lower
  semicontinuous, and $p_0\in\partial J(u_0)$. The **Bregman distance** is
  $D_J^{p_0}(u,u_0)=J(u)-J(u_0)-\langle p_0,u-u_0\rangle\ge0$, and for
  $p\in\partial J(u)$ the **symmetric Bregman distance** is
  $D_J^{\mathrm{symm}}(u,u_0)=\langle p-p_0,u-u_0\rangle\ge0$. Let $V$ be a
  Hilbert space, $K:U\to V$ bounded and linear, $Ku^\dagger=f$,
  $\|f^\delta-f\|\le\delta$, and let $u_\alpha$ minimize
  $$\tfrac12\|Ku-f^\delta\|^2+\alpha J(u)$$
  over $U$. Assume the **source condition**: $K^*v\in\partial J(u^\dagger)$ for
  some $v\in V$. Then $u^\dagger$ minimizes $J$ on $\{u:Ku=f\}$, and with
  $p^\dagger=K^*v$ and the subgradient
  $p_\alpha=K^*(f^\delta-Ku_\alpha)/\alpha\in\partial J(u_\alpha)$,
  $$D_J^{\mathrm{symm}}(u^\dagger,u_\alpha)+\frac1{2\alpha}
  \|Ku_\alpha-f^\delta\|^2\le\frac{\delta^2}{2\alpha}
  +\frac\alpha2\|v\|^2 .$$
  For $v\ne0$ and $\alpha=\delta/\|v\|$ this gives
  $D_J^{\mathrm{symm}}(u^\dagger,u_\alpha)\le\|v\|\,\delta$. For
  $J=\frac12\|\cdot\|^2$ on a Hilbert space, $D_J^{\mathrm{symm}}(u,u_0)=
  \|u-u_0\|^2$ and the source condition reads $u^\dagger=K^*v$.

  *Assessment.* Not covered. TauCeti defines the subdifferential of an extended-real function with
  respect to a bilinear pairing, the setting of the Bregman distance. The missing result is the
  variational error estimate in the symmetric Bregman distance under the range source condition,
  which gives the rate without Hilbert-space structure on $U$.

  *Lean target.* Carriers at the pins: TauCeti's `TauCeti.subdifferential` with the pairing between
  $U$ and its dual, `LowerSemicontinuous`, `ConvexOn`, and `StrongDual`. The adjoint of $K:U\to V$
  with $V$ Hilbert is the functional $u\mapsto(v,Ku)$; `ContinuousLinearMap.adjoint` is for Hilbert
  spaces only. New definitions: the Bregman distance $D_J^p(u,u_0)=J(u)-J(u_0)-p(u-u_0)$ and the
  symmetric distance $(p-p_0)(u-u_0)$. Conjuncts: (i) $D_J^{p_0}(u,u_0)\ge0$ and the symmetric
  distance is nonnegative; (ii) under the source condition $u^\dagger$ minimizes $J$ on $\{Ku=f\}$;
  (iii) at a minimizer $u_\alpha$, $K^*(f^\delta-Ku_\alpha)/\alpha$ is a subgradient; (iv) the
  displayed estimate; (v) the bound $\|v\|\delta$ at $\alpha=\delta/\|v\|$; (vi) the quadratic case.
  Pitfall: with $J$ valued in `EReal`, $J(u)-J(u_0)$ is not meaningful at $+\infty-(+\infty)$; take
  $J(u_0)$ finite, as the subdifferential does, and state (iv) only at points where $J$ is finite,
  which the source condition and minimality give. Existence of $u_\alpha$ is a hypothesis. Statable
  at the pins. NASC: no declaration.

### Bayesian inverse problems

* **22.11. Cameron–Martin space of a Gaussian prior.** Let $H$ be a
  separable real Hilbert space, let $\mu_0=N(0,C)$, and let
  $E=\mathrm{Im}(C^{1/2})$ be its Cameron–Martin space with the inner product
  of 24.13. Then $E$ is the intersection of all measurable linear subspaces
  of full $\mu_0$-measure, it is compactly embedded in every separable Banach
  space $X$ continuously embedded in $H$ with $\mu_0(X)=1$, and
  $\mu_0(E)=0$ if $E$ is infinite-dimensional. The equivalence and
  shift-density results for Gaussian measures are in 24.13.

  *Assessment.* Gaussian measures and Fernique integrability are available.
  The selected theorem identifies the Cameron–Martin space by full-measure
  subspaces and proves the stated compact-embedding and null-set assertions.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussian`,
  `ProbabilityTheory.covarianceOperator` applied to the centred image, `HilbertBasis`, and
  `IsCompactOperator`. The operator square root $C^{1/2}$ has no carrier for real Hilbert spaces, so
  $E$ is stated in eigen-coordinates as in 24.13: $h\in E$ when
  $(h,\varphi_k)=\sqrt{\lambda_k}(v,\varphi_k)$ for some $v\in H$, with $\|h\|_C$ the least such
  $\|v\|$. New definition: the Cameron–Martin space as a submodule with this norm. Conjuncts: (i)
  $E$ equals the intersection of all measurable subspaces of full measure; (ii) for a separable
  Banach space $X$ with a continuous injective linear map into $H$ whose range has full measure, $E$
  lies in the range and the inclusion of $E$ into $X$ is compact; (iii) $\mu_0(E)=0$ when $E$ is
  infinite-dimensional. Pitfall: the range of $X$ in $H$ is Borel by the Lusin–Souslin theorem
  (`MeasurableSet.image_of_continuousOn_injOn`), which (ii) needs before $\mu_0(X)=1$ means
  anything. Depends on 24.13. Statable at the pins; the StochasticCalculus roadmap, §8.1, owns the
  Cameron–Martin space of a Gaussian measure on a Banach space. NASC:
  `NASC.measure_cameronMartin_coordinates_eq_zero` (`NASC/BayesianInverseProblems.lean`), sorry; it
  is (iii) in coordinates, for i.i.d. standard normal coordinates; (i) and (ii) are missing.

* **22.12. Bayes' theorem in function space.** Let $X$ be a separable Banach
  space, $\mu_0$ a probability measure (the **prior**) on $X$,
  $G:X\to\mathbb R^q$ continuous, and $y=G(u)+\eta$, where $u\sim\mu_0$ and
  the noise $\eta$ is independent of $u$ with a Lebesgue density $\rho$ that
  is positive on all of $\mathbb R^q$. Let $\Phi(u;y)$ differ from
  $-\log\rho(y-G(u))$ by a function of $y$ alone, and put
  $Z(y)=\int_X\exp\bigl(-\Phi(u;y)\bigr)\,d\mu_0(u)$. Then $Z(y)>0$ for every
  $y$, and $Z(y)<\infty$ for Lebesgue-almost every $y$ (for every $y$ if $\rho$
  is bounded). The conditional law $\mu^y$ of $u$ given $y$ (the
  **posterior**) has a version that, for every $y$ with $Z(y)<\infty$, is
  absolutely continuous with respect to $\mu_0$ with
  $$\frac{d\mu^y}{d\mu_0}(u)=\frac1{Z(y)}\exp\bigl(-\Phi(u;y)\bigr).$$
  For Gaussian noise $\eta\sim N(0,\Gamma)$ with $\Gamma$ positive definite one
  may take $\Phi(u;y)=\frac12|\Gamma^{-1/2}(y-G(u))|^2$.

  *Assessment.* Partly covered. Mathlib supplies the abstract Radon–Nikodym theorem for posterior
  kernels and almost-everywhere uniqueness. The selected target is an explicit posterior version for
  independent additive noise with an everywhere positive density.

  *Scope.* The target is the explicit density of a posterior version, with its normalizer, for
  additive noise with an everywhere positive Lebesgue density; Gaussian noise is the principal
  instance.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.condDistrib`,
  `ProbabilityTheory.posterior` with `ProbabilityTheory.absolutelyContinuous_posterior` and
  `ProbabilityTheory.posterior_eq_withDensity`, `MeasureTheory.Measure.withDensity`, `∫⁻`, and for
  the Gaussian case `ProbabilityTheory.multivariateGaussian` and `Matrix.PosDef`. New definitions:
  the likelihood $u\mapsto\exp(-\Phi(u;y))$ in `ℝ≥0∞` and the normalized posterior. Conjuncts: (i)
  $Z(y)>0$ for every $y$; (ii) $Z(y)<\infty$ for almost every $y$, and for every $y$ when $\rho$ is
  bounded; (iii) the kernel $y\mapsto Z(y)^{-1}e^{-\Phi(\cdot;y)}\mu_0$ disintegrates the joint law,
  that is, the joint measure of $A\times B$ is the integral over $A$ of the kernel at $B$ against
  the law of $y$; (iv) for Gaussian noise $Z(y)\le1$. Pitfall: `(⊤ : ℝ≥0∞)⁻¹ = 0`, so a normalized
  posterior at a $y$ with $Z(y)=\infty$ is the zero measure, and (iii) must not claim a probability
  measure there; `Matrix.inv` is $0$ for a singular $\Gamma$, and `multivariateGaussian` falls back
  when $\Gamma$ is not positive semidefinite, so $\Gamma$ positive definite is a hypothesis.
  Statable at the pins. NASC: `NASC.gibbsLikelihood`, `NASC.posteriorMeasure`,
  `NASC.gaussianObservationPotential` and `NASC.gaussian_posterior_disintegrates`
  (`NASC/BayesianInverseProblems.lean`), sorry; Gaussian noise only, with (i), (iii) and (iv).

* **22.13. Well-posedness of the posterior.** Let $H$ be a separable Hilbert
  space, $\mu_0$ a Gaussian measure on $H$, $X\subset H$ a separable Banach
  space with $\mu_0(X)=1$, and $Y$ a Banach space. Let $\Phi:X\times
  Y\to\mathbb R$ satisfy:
  - (i) for all $\varepsilon,r>0$ there is $M(\varepsilon,r)\in\mathbb R$ with
    $\Phi(u;y)\ge M-\varepsilon\|u\|_X^2$ for all $u\in X$ and $\|y\|_Y<r$;
  - (ii) for every $r>0$ there is $K(r)>0$ with $\Phi(u;y)\le K$ whenever
    $\max\{\|u\|_X,\|y\|_Y\}<r$;
  - (iii) for every $r>0$ there is $L(r)>0$ with
    $|\Phi(u_1;y)-\Phi(u_2;y)|\le L\|u_1-u_2\|_X$ whenever
    $\max\{\|u_1\|_X,\|u_2\|_X,\|y\|_Y\}<r$;
  - (iv) for all $\varepsilon,r>0$ there is $C(\varepsilon,r)\in\mathbb R$
    with $|\Phi(u;y_1)-\Phi(u;y_2)|\le\exp\bigl(\varepsilon\|u\|_X^2+C\bigr)
    \|y_1-y_2\|_Y$ for all $u\in X$ and $\max\{\|y_1\|_Y,\|y_2\|_Y\}<r$.

  Under (i)–(iii), $0<Z(y)<\infty$ and $d\mu^y/d\mu_0=Z(y)^{-1}
  \exp(-\Phi(\cdot;y))$ defines a probability measure $\mu^y$ for each
  $y\in Y$. Under (i), (ii) and (iv), for every $r>0$ there is $C(r)>0$ with
  $$d_{\mathrm{Hell}}(\mu^y,\mu^{y'})\le C(r)\|y-y'\|_Y\qquad\text{whenever }
  \max\{\|y\|_Y,\|y'\|_Y\}<r,$$
  where $d_{\mathrm{Hell}}(\mu,\mu')^2=\frac12\int\bigl(\sqrt{d\mu/d\nu}-
  \sqrt{d\mu'/d\nu}\bigr)^2d\nu$ for any $\nu$ dominating both. If
  $f:X\to W$, with $W$ a Banach space, has second moments under $\mu$ and
  $\mu'$, then $\|\mathbb E^\mu f-\mathbb E^{\mu'}f\|\le2\bigl(\mathbb E^\mu
  \|f\|^2+\mathbb E^{\mu'}\|f\|^2\bigr)^{1/2}d_{\mathrm{Hell}}(\mu,\mu')$. If
  $\Phi$ has the form in 22.12 with Gaussian noise, (i)–(iv) hold, with
  $Y=\mathbb R^q$ and norm $|\Gamma^{-1/2}\cdot|$, when $|\Gamma^{-1/2}G(u)|\le
  \exp(\varepsilon\|u\|_X^2+M(\varepsilon))$ for every $\varepsilon>0$ and $G$
  is Lipschitz on bounded subsets of $X$.

  *Assessment.* Mathlib's Fernique theorem supplies the main integrability
  ingredient. The missing results give positivity and finiteness of the
  normalization and the Hellinger stability with the given local data and
  prior assumptions.

  *Lean target.* Carriers at the pins: Mathlib's Fernique theorem
  `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`, `MeasureTheory.Measure.rnDeriv`, and
  `∫⁻`. The Hellinger distance has no carrier at the pins. New definition: the squared Hellinger
  distance $\frac12\int(\sqrt{d\mu/d\nu}-\sqrt{d\mu'/d\nu}\,)^2d\nu$ with $\nu=\mu+\mu'$. Conjuncts:
  (i) under (i)–(iii), $0<Z(y)<\infty$ and $\mu^y$ is a probability measure; (ii) under (i), (ii)
  and (iv), the local Lipschitz bound in Hellinger distance; (iii) the bound on the difference of
  expectations of $f$ with second moments; (iv) the Gaussian-noise case. Pitfall: the TauCeti
  Hellinger distance on main is normalized as $2(1-\text{affinity})$, twice the square here; state
  second moments with `∫⁻` of $\|f\|^2$, since a Bochner integral of a non-integrable function is
  $0$. Depends on 22.12. Statable at the pins. NASC: `NASC.hellingerSq_le_of_exponential_moment`
  (`NASC/BayesianInverseProblems.lean`), sorry; it gives (ii) for the squared distance, with an
  exponential-moment hypothesis in place of the Gaussian prior and the bound in the form
  $C\exp(\varepsilon\|u\|^2)$; (i) beyond positivity, (iii) and (iv) are missing.

* **22.14. MAP estimators and Tikhonov regularization.** In the setting of
  22.13 with $\mu_0=N(0,C)$ and Cameron–Martin space $E$, fix $y$ and let
  $$I(u)=\tfrac12\|u\|_C^2+\Phi(u;y),\qquad u\in E.$$
  If $\Phi$ satisfies (i) and (iii) of 22.13, then $I$ attains its infimum on
  $E$, and every minimizing sequence has a subsequence that converges in $E$
  to a minimizer. If $H=\mathbb R^n$ and $C$ is positive definite, then
  $\mu^y$ has a Lebesgue density proportional to $\exp(-I(u))$, so the modes
  of $\mu^y$ (the **maximum a posteriori** estimators) are the minimizers of
  $I$. For $G(u)=Au$ linear and noise $N(0,\Gamma)$, $I$ is the generalized
  Tikhonov functional
  $\frac12|\Gamma^{-1/2}(y-Au)|^2+\frac12\|C^{-1/2}u\|^2$.

  *Assessment.* The finite-dimensional objective has the usual quadratic
  terms. In the infinite-dimensional setting the gaps concern compactness of
  minimizing sequences in the Cameron–Martin norm and attainment of the action
  minimum.

  *Lean target.* Carriers at the pins: `IsCompactOperator`, `Filter.Tendsto`, `StrictMono`, and in
  finite dimension `ProbabilityTheory.multivariateGaussian` with Lebesgue densities. The
  Cameron–Martin space is modelled as a Hilbert space $E$ with a compact embedding into $X$. New
  definition: a mode of a measure with a continuous Lebesgue density, as a maximizer of that
  density. Conjuncts: (i) $I$ attains its infimum on $E$; (ii) every minimizing sequence has a
  subsequence converging in $E$ to a minimizer; (iii) for $H=\mathbb R^n$ and $C$ positive definite,
  the posterior density is proportional to $\exp(-I)$ and the modes are the minimizers; (iv) the
  linear Gaussian case is the generalized Tikhonov functional. Pitfall: (iii) needs the density of
  $N(0,C)$, whose `Matrix.inv` is junk unless $C$ is positive definite. Depends on 22.12 and 22.13.
  Statable at the pins. NASC: `NASC.exists_mapEstimator_compactEmbedding`
  (`NASC/BayesianInverseProblems.lean`), sorry; it states (i) and (ii) with continuity of $\Phi$ in
  place of (iii) of 22.13, a weaker hypothesis under which the result still holds; (iii) and (iv)
  are missing.

### Filtering

* **22.15. The Kalman filter.** Let $M\in\mathbb R^{n\times n}$,
  $H\in\mathbb R^{p\times n}$, and let $\Sigma$, $\Gamma$ and $C_0$ be positive
  definite. Consider $v_{j+1}=Mv_j+\xi_j$ and $y_{j+1}=Hv_{j+1}+\eta_{j+1}$ for
  $j\in\mathbb N_0$, with $v_0\sim N(m_0,C_0)$, $\xi_j\sim N(0,\Sigma)$ i.i.d.,
  $\eta_{j}\sim N(0,\Gamma)$ i.i.d., and $v_0$, $(\xi_j)$, $(\eta_j)$
  independent. Let $Y_j=(y_1,\dots,y_j)$. Then the **filtering distribution**
  of $v_j$ given $Y_j$ is Gaussian, $N(m_j,C_j)$ with $C_j$ positive definite,
  and the means and covariances satisfy
  $$C_{j+1}^{-1}=(MC_jM^\top+\Sigma)^{-1}+H^\top\Gamma^{-1}H,\qquad
  C_{j+1}^{-1}m_{j+1}=(MC_jM^\top+\Sigma)^{-1}Mm_j+H^\top\Gamma^{-1}y_{j+1}.$$
  Equivalently, with $\hat m_{j+1}=Mm_j$, $\hat C_{j+1}=MC_jM^\top+\Sigma$,
  $S_{j+1}=H\hat C_{j+1}H^\top+\Gamma$ and the **Kalman gain**
  $L_{j+1}=\hat C_{j+1}H^\top S_{j+1}^{-1}$,
  $$m_{j+1}=\hat m_{j+1}+L_{j+1}(y_{j+1}-H\hat m_{j+1}),\qquad
  C_{j+1}=(I-L_{j+1}H)\hat C_{j+1}.$$
  The mean $m_{j+1}$ is the minimizer of
  $\frac12|\Gamma^{-1/2}(y_{j+1}-Hv)|^2+\frac12|\hat C_{j+1}^{-1/2}(v-\hat
  m_{j+1})|^2$.

  *Assessment.* Partly covered. TauCeti gives mean and covariance updates by
  Gaussian conditioning for one observation. The selected result assembles
  prediction and update into the recursion and identifies its precision and
  gain forms.

  *Scope.* The target is the prediction and update recursion as a whole,
  including its interpretation as the conditional law of the unobserved state.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.multivariateGaussian`,
  `ProbabilityTheory.condDistrib`, `Matrix.PosDef`, and TauCeti's
  `EuclideanSpace.gaussianCondMean_of_posDef`, `Matrix.gaussianCondCov_of_posDef` and
  `TauCeti.Probability.condDistrib_multivariateGaussian`. New definition: the recursion $(m_j,C_j)$
  as a function of the data. Conjuncts: (i) the conditional law of $v_j$ given $Y_j$ is $N(m_j,C_j)$
  for almost every $Y_j$; (ii) $C_j$ is positive definite; (iii) the information form; (iv) the gain
  form equals it; (v) $m_{j+1}$ minimizes the quadratic functional. Pitfall: `Matrix.inv` is $0$ for
  a singular matrix, so positive definiteness of $\hat C_{j+1}$ and $S_{j+1}$ must be proved before
  the formulas mean anything; the first observation here is $y_1$, while the KalmanFiltering
  roadmap's §3.1 puts it at time $0$. TauCeti main adds `Matrix.kalmanGain`,
  `Matrix.measurementUpdate` and `Matrix.riccatiMap`, not at the pin. Statable at the pins. NASC:
  `NASC.kalman_posterior_eq_gaussian` (`NASC/BayesianInverseProblems.lean`), sorry; one prediction
  and update step in information form, with positive semidefinite $C$, stated as a reweighting of
  the predicted law; the recursion, (i) over many steps and (iv) are missing.

## 23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations

[Synopsis](SYNOPSIS.md#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations) · [Coverage inventory](STRUCTURE.md#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations)

Probability limits, Gaussian laws, kernel constructions, and an Itô integral
provide foundations for the estimator and stochastic evolution gaps.

Throughout, $(\Omega,\mathcal F,P)$ is a probability
space with expectation $\mathbb E$ and variance $\mathrm{Var}$. A Wiener
process $W=(W^1,\dots,W^m)$ is an $m$-dimensional standard Brownian motion
adapted to a filtration $(\mathcal F_t)$ satisfying the usual conditions,
with $W_t-W_s$ independent of $\mathcal F_s$ for $s\le t$. Integrals against
$dW$ are Itô integrals. The unit cube is $[0,1]^s$, and $\{x\}=x-\lfloor x\rfloor$
is the fractional part, applied componentwise to vectors.

### Monte Carlo methods

* **23.1. Plain Monte Carlo.** Let $Z$ be a real random variable with
  $\mathbb E Z^2<\infty$, mean $z=\mathbb E Z$ and variance $\sigma^2=\mathrm{Var}\,Z$,
  and let $Z_1,Z_2,\dots$ be independent copies of $Z$. The **crude Monte
  Carlo estimator** is $\hat z_R=(Z_1+\dots+Z_R)/R$ and the **sample
  variance** is $s_R^2=(R-1)^{-1}\sum_{r=1}^R(Z_r-\hat z_R)^2$ for $R\ge2$.
  Then:
  - $\mathbb E\hat z_R=z$ and $\mathbb E(\hat z_R-z)^2=\sigma^2/R$ for every
    $R\ge1$;
  - $\hat z_R\to z$ almost surely as $R\to\infty$, and $s_R^2\to\sigma^2$
    almost surely;
  - $\sqrt R(\hat z_R-z)\to N(0,\sigma^2)$ in distribution;
  - if $\sigma>0$, $0<\alpha<1$ and $q$ is the $(1-\alpha/2)$-quantile of the
    standard normal distribution, then
    $$\lim_{R\to\infty}P\bigl(|\hat z_R-z|\le q\,s_R/\sqrt R\bigr)=1-\alpha,$$
    so $\hat z_R\pm q\,s_R/\sqrt R$ is an **asymptotic $(1-\alpha)$ confidence
    interval** for $z$. For $1-\alpha=0.95$, $q\approx1.96$.

  In particular, for $f\in L^2([0,1]^s)$ and independent uniform points
  $t_0,\dots,t_{n-1}$ in $[0,1]^s$, the root-mean-square error of
  $n^{-1}\sum_{i<n}f(t_i)$ as an approximation of $\int_{[0,1]^s}f$ is
  exactly $\sigma(f)/\sqrt n$, where $\sigma(f)^2=\int f^2-(\int f)^2$.

  *Assessment.* Partly covered. Mathlib has the strong law, the iid central limit theorem, the
  variance identities and Slutsky's theorem, and TauCeti the mean-square error of a sample mean. The
  selected results concern consistency of the sample variance and the studentized interval.

  *Scope.* The selected claims are almost-sure consistency of the sample variance and the asymptotic
  coverage of the studentized interval.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.strong_law_ae`,
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`,
  `ProbabilityTheory.IndepFun.variance_sum`,
  `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, TauCeti's
  `TauCeti.integral_finiteMean_sub_sq`, `ProbabilityTheory.iIndepFun`, and
  `ProbabilityTheory.gaussianReal`. New definitions: the sample mean and the sample variance with
  divisor $R-1$. Conjuncts: (i) unbiasedness and $\mathbb E(\hat z_R-z)^2=\sigma^2/R$; (ii)
  almost-sure convergence of $\hat z_R$ and $s_R^2$; (iii) $\sqrt R(\hat z_R-z)$ converges in
  distribution to `gaussianReal 0 σ²`; (iv) for $\sigma>0$ and every $q>0$ the probability
  $P(|\hat z_R-z|\le qs_R/\sqrt R)$ tends to the standard normal mass of $[-q,q]$; (v) the
  uniform-points corollary. Pitfall: the sample variance at $R=1$ divides by $0$ and Lean returns
  $0$, so index from $R=2$; the pins have no normal quantile function, so (iv) is stated for every
  $q$ rather than for the quantile; Mathlib's central limit theorem is normalized to variance one,
  and $\sigma=0$ gives the Dirac law, which `gaussianReal 0 0` is. Statable at the pins. NASC:
  `NASC.sampleMean`, `NASC.sampleVariance` and `NASC.sampleVariance_tendsto_and_coverage`
  (`NASC/MonteCarlo.lean`), sorry; they state (ii) for $s_R^2$ and (iv).

* **23.3. Importance sampling and the zero-variance measure.** Let $Z$ be an
  integrable random variable on $(\Omega,\mathcal F,P)$, let $\tilde P$ be a
  probability measure on $(\Omega,\mathcal F)$ with expectation $\tilde{\mathbb E}$,
  and let $L\ge0$ be measurable with
  $\mathbb 1_{\{Z\ne0\}}\,dP=\mathbb 1_{\{Z\ne0\}}L\,d\tilde P$ as measures.
  Then $\tilde{\mathbb E}[ZL]=\mathbb E Z$, so the average of independent
  $\tilde P$-copies of $ZL$ is an unbiased estimator of $\mathbb E Z$ (the
  **importance sampling estimator**). Suppose $\mathbb E|Z|>0$ and define $P^*$ by
  $dP^*/dP=|Z|/\mathbb E|Z|$, with likelihood ratio $L^*=\mathbb E|Z|/|Z|$ on
  $\{Z\ne0\}$. Then the second moment of $ZL^*$ under $P^*$ equals
  $(\mathbb E|Z|)^2$, which is at most $\tilde{\mathbb E}[(ZL)^2]$ for every
  admissible pair $(\tilde P,L)$; hence $P^*$ minimizes the variance. If
  $Z\ge0$ almost surely, then $ZL^*=\mathbb E Z$ almost surely under $P^*$, and
  the variance is zero. For instance, if $Z=g(X_1,\dots,X_n)$ with $X_i$
  independent with density $f$ under $P$, and independent with density
  $\tilde f$ under $\tilde P$, where $f$ and $\tilde f$ have the same support, then
  $L=\prod_{i=1}^nf(X_i)/\tilde f(X_i)$ is admissible.

  *Assessment.* Partly covered. The integral-with-density formula supports the
  unbiasedness assertion. The selected result minimizes variance over
  admissible laws and specifies the case of zero variance.

  *Scope.* The target is the variance-minimizing proposal and the
  zero-variance conclusion for a nonnegative integrand.

  *Lean target.* Carriers at the pins: `MeasureTheory.Measure.withDensity`,
  `integral_withDensity_eq_integral_smul₀`, `MeasureTheory.Measure.restrict`, and `∫⁻`. No new
  definition is needed. Conjuncts: (i) for every admissible pair,
  $\tilde{\mathbb E}[ZL]=\mathbb EZ$; (ii) $P^*$ is a probability measure and $(P^*,L^*)$ is
  admissible; (iii) the second moment of $ZL^*$ under $P^*$ is $(\mathbb E|Z|)^2$; (iv) it is at
  most the second moment of every admissible pair; (v) $Z\ge0$ almost surely gives $ZL^*=\mathbb EZ$
  almost surely under $P^*$; (vi) the product-density likelihood ratio is admissible. Pitfall: the
  second moments may be infinite and must be `∫⁻` in `ℝ≥0∞`; $L^*=\mathbb E|Z|/|Z|$ is $0$ on
  $\{Z=0\}$ in Lean, which is harmless because admissibility only constrains $\{Z\ne0\}$. Statable
  at the pins. NASC: `NASC.importanceSampling_optimal_secondMoment` (`NASC/MonteCarlo.lean`), sorry;
  it states (ii), (iii) and (iv) with `∫⁻`; (i), (v) and (vi) are missing.

* **23.4. Metropolis–Hastings.** Let $E$ be a finite or countable set, let
  $\pi:E\to(0,\infty)$ with $C=\sum_{x\in E}\pi(x)<\infty$, and let
  $\pi^*=\pi/C$. Let $q$ be a transition matrix on $E$ (the **proposal**). For
  $q(x,y)>0$ put
  $$\alpha(x,y)=\min\Bigl\{1,\frac{\pi(y)q(y,x)}{\pi(x)q(x,y)}\Bigr\}.$$
  The **Metropolis–Hastings chain** has transition matrix
  $p(x,y)=q(x,y)\alpha(x,y)$ for $y\ne x$ (with $p(x,y)=0$ when $q(x,y)=0$),
  and $p(x,x)=1-\sum_{y\ne x}p(x,y)$. Then:
  - (**detailed balance**) $\pi(x)p(x,y)=\pi(y)p(y,x)$ for all $x,y\in E$;
    consequently $\pi^*$ is a stationary distribution, $\pi^*p=\pi^*$, and the
    normalizing constant $C$ is never needed;
  - (**ergodic theorem**) if the chain is irreducible, then for every initial
    state and every $f:E\to\mathbb R$ with $\sum_x|f(x)|\pi^*(x)<\infty$,
    $$\frac1{n+1}\sum_{k=0}^nf(\xi_k)\to\sum_{x\in E}f(x)\pi^*(x)\quad
    \text{almost surely as }n\to\infty.$$
  A transition from $x$ to $y\ne x$ in one step is possible exactly when
  $q(x,y)>0$ and $q(y,x)>0$, so irreducibility must be checked for each
  proposal; it holds if $q(x,y)>0$ for all $x,y$.

  *Assessment.* Partly covered. Mathlib proves that a kernel reversible with respect to a measure
  leaves it invariant, and TauCeti proves almost-sure convergence of occupation frequencies with
  Kac's identification of the limit for an irreducible chain with an invariant probability. The
  missing result constructs the accept–reject transition, checks detailed balance, and extends the
  ergodic theorem from indicators to $\pi^*$-integrable functions.

  *Scope.* The target is the Metropolis–Hastings matrix on a countable space with its detailed
  balance, and the ergodic theorem for every $\pi^*$-integrable function from every initial state.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.Kernel.IsReversible` and
  `ProbabilityTheory.Kernel.IsReversible.invariant`, `ProbabilityTheory.Kernel.IsIrreducible`,
  TauCeti's `Matrix.rowStochastic.isReversible_toKernel_iff_isSymm_diagonal_mul`,
  `MeasureTheory.Measure.ae_tendsto_visitCount_div_markovChainLaw`,
  `ProbabilityTheory.Kernel.Invariant.apply_singleton_eq_inv_meanReturnTime`, and
  `TauCeti.Probability.markovChainLaw`. New definition: the Metropolis–Hastings matrix on a
  countable set. Conjuncts: (i) it is nonnegative with rows summing to $1$; (ii) detailed balance;
  (iii) invariance of $\pi$, hence of $\pi^*$; (iv) under irreducibility, for every initial state
  and every $f$ with $\sum|f|\pi^*<\infty$, the ergodic averages converge almost surely under the
  chain law; (v) a move from $x$ to $y\ne x$ has positive probability exactly when $q(x,y)>0$ and
  $q(y,x)>0$. Pitfall: `tsum` of a non-summable row is $0$, so summability of each proposal row is a
  hypothesis; $p(x,x)$ is defined by complement and must be shown nonnegative; the ratio divides by
  $\pi(x)$ and $q(x,y)$, where $\min(q(x,y),\pi(y)q(y,x)/\pi(x))$ avoids the second division.
  TauCeti main adds a finite-state `metropolisHastingsKernel`. Statable at the pins. NASC:
  `NASC.metropolisHastings` and `NASC.metropolisHastings_detailedBalance` (`NASC/MonteCarlo.lean`),
  sorry; they state (i)–(iii), with no summability hypothesis on the target; (iv) and (v) are
  missing.

### Quasi-Monte Carlo methods

* **23.5. Star discrepancy and the Koksma–Hlawka inequality.** Let
  $P=\{t_0,\dots,t_{n-1}\}$ be a finite list of points in $[0,1]^s$, and let
  $Q_n(f)=n^{-1}\sum_{i=0}^{n-1}f(t_i)$ and $I(f)=\int_{[0,1]^s}f$. The
  **local discrepancy** is
  $$\Delta_P(x)=\frac1n\#\{i:t_i\in[0,x]\}-x_1x_2\cdots x_s,\qquad x\in[0,1]^s,$$
  where $[0,x]=\prod_j[0,x_j]$, and the **star discrepancy** is
  $D_n^*(P)=\sup_{x\in[0,1]^s}|\Delta_P(x)|$. For $u\subseteq\{1,\dots,s\}$
  write $(x_u;1)$ for the point whose $j$-th coordinate is $x_j$ for $j\in u$
  and $1$ otherwise. If all mixed partial derivatives
  $\partial^{|u|}f/\partial x_u$ ($u\subseteq\{1,\dots,s\}$) exist and are
  continuous on $[0,1]^s$, then (**Hlawka–Zaremba identity**)
  $$Q_n(f)-I(f)=\sum_{\emptyset\ne u\subseteq\{1,\dots,s\}}(-1)^{|u|}
  \int_{[0,1]^{|u|}}\frac{\partial^{|u|}f}{\partial x_u}(x_u;1)\,
  \Delta_P(x_u;1)\,dx_u,$$
  and hence (**Koksma–Hlawka inequality**)
  $$|Q_n(f)-I(f)|\le D_n^*(P)\sum_{\emptyset\ne u\subseteq\{1,\dots,s\}}
  \int_{[0,1]^{|u|}}\Bigl|\frac{\partial^{|u|}f}{\partial x_u}(x_u;1)\Bigr|
  \,dx_u .$$
  The sum on the right is the variation $V(f)$ of $f$ in the sense of Hardy
  and Krause; more generally $|Q_n(f)-I(f)|\le D_n^*(P)V(f)$ for every $f$ of
  bounded Hardy–Krause variation.

  *Assessment.* The missing inequality compares integration error with
  discrepancy and multivariate variation. Both notions must use their stated
  face and boundary conventions.

  *Lean target.* Carriers at the pins: `iteratedFDeriv`, `ContDiff`, the volume on `Fin s → ℝ`
  restricted to `Set.Icc 0 1`, and `Finset.powerset`. New definitions: the local and star
  discrepancies, the face derivative, and the Hardy–Krause variation for functions of bounded
  variation. Conjuncts: (i) the Hlawka–Zaremba identity for $f$ with continuous mixed first
  derivatives; (ii) the Koksma–Hlawka inequality in that case; (iii) the inequality for every $f$ of
  bounded Hardy–Krause variation. Pitfall: a real `sSup` is $0$ on an empty or unbounded set; the
  discrepancy set is nonempty and bounded by $1$, which should be a lemma next to the definition;
  Hardy–Krause variation is a supremum over partitions and needs `ℝ≥0∞` or an explicit boundedness
  hypothesis. Statable at the pins for (i) and (ii); (iii) needs the variation, which no library
  defines. NASC: `NASC.starDiscrepancy`, `NASC.faceDerivative` and
  `NASC.quadrature_error_le_starDiscrepancy` (`NASC/MonteCarlo.lean`), sorry; (ii) under global
  `ContDiff ℝ s`, stronger than the hypothesis of the entry.

* **23.6. Low-discrepancy sequences.** For an integer $b\ge2$ the **radical
  inverse** of $i=\sum_{k\ge0}a_kb^k$ ($a_k\in\{0,\dots,b-1\}$) is
  $\phi_b(i)=\sum_{k\ge0}a_kb^{-k-1}$. With $p_1<\dots<p_s$ the first $s$
  primes, the **Halton sequence** is
  $t_i=(\phi_{p_1}(i),\dots,\phi_{p_s}(i))$, $i\ge0$, and the **Hammersley
  point set** with $n$ points is $t_i=(i/n,\phi_{p_1}(i),\dots,\phi_{p_{s-1}}(i))$,
  $0\le i<n$. There are constants $C_s$ depending only on $s$ such that, for
  all $n\ge2$ and all $f$ of bounded Hardy–Krause variation, the rule $Q_n$
  on the first $n$ Halton points satisfies
  $|Q_n(f)-I(f)|\le C_s(\log n)^sV(f)/n$, and the rule on the Hammersley set
  satisfies $|Q_n(f)-I(f)|\le C_s(\log n)^{s-1}V(f)/n$. Let $t\le m$ be
  nonnegative integers. A **$(t,m,s)$-net in base $b$** is a set of $b^m$
  points of $[0,1)^s$ such that every box $\prod_{j=1}^s[a_jb^{-d_j},(a_j+1)b^{-d_j})$
  with integers $d_j\ge0$, $0\le a_j<b^{d_j}$ and $d_1+\dots+d_s=m-t$ contains
  exactly $b^t$ of the points. A **$(t,s)$-sequence in base $b$** is a
  sequence $(t_i)_{i\ge0}$ in $[0,1)^s$ such that for all integers $m>t$ and
  $\ell\ge0$ the block $t_{\ell b^m},\dots,t_{(\ell+1)b^m-1}$ is a
  $(t,m,s)$-net in base $b$. The first $n$ points of a $(t,s)$-sequence have
  star discrepancy at most $C(\log n)^s/n$ for $n\ge2$, with $C$ depending
  only on $t$, $s$ and $b$; with 23.5 this gives the integration error bound
  $C(\log n)^sV(f)/n$.

  *Assessment.* Not covered. Neither library has the radical inverse, digital nets or
  low-discrepancy sequences. The gap gives the explicit Halton, Hammersley and $(t,s)$-sequence
  discrepancy bounds, which with 23.5 are the quasi-Monte Carlo error rates.

  *Lean target.* Carriers at the pins: `Nat.digits`, `Nat.nth Nat.Prime` for the $j$-th prime,
  `Real.log`, and the star discrepancy of 23.5. New definitions: the radical inverse in base $b$,
  the Halton sequence, the Hammersley set, $(t,m,s)$-nets and $(t,s)$-sequences in base $b$.
  Conjuncts: (i) there is $C_s$ with $D_n^*\le C_s(\log n)^s/n$ for the first $n$ Halton points, for
  all $n\ge2$; (ii) $C_s(\log n)^{s-1}/n$ for the Hammersley set; (iii) $C(t,s,b)(\log n)^s/n$ for
  the first $n$ points of a $(t,s)$-sequence; (iv) the integration bounds through 23.5. Pitfall:
  `Nat.digits` lists digits from the least significant, matching $a_k$ with weight $b^{-k-1}$; the
  Hammersley set with $s=1$ is $\{i/n\}$. Depends on 23.5. Statable at the pins for (i)–(iii) and
  for smooth $f$ in (iv). NASC: no declaration.

* **23.7. Randomly shifted lattice rules and the component-by-component
  construction.** Let $n\ge2$, let $U_n=\{z\in\{1,\dots,n-1\}:\gcd(z,n)=1\}$
  with $\varphi(n)=\#U_n$, and let weights $\gamma_u>0$ be given for
  $\emptyset\ne u\subseteq\{1,\dots,s\}$, with $\gamma_\emptyset=1$. The
  **weighted unanchored Sobolev space** $H_{s,\gamma}$ consists of the
  functions on $[0,1]^s$ whose mixed first derivatives are square integrable,
  with norm
  $$\|f\|_{s,\gamma}^2=\sum_{u\subseteq\{1,\dots,s\}}\gamma_u^{-1}
  \int_{[0,1]^{|u|}}\Bigl(\int_{[0,1]^{s-|u|}}\frac{\partial^{|u|}f}{\partial x_u}(x)
  \,dx_{-u}\Bigr)^2dx_u ,$$
  where $x_{-u}$ denotes the coordinates not in $u$. For a point set $P$, the
  **worst-case error** is $e(P)=\sup\{|Q_n(f)-I(f)|:\|f\|_{s,\gamma}\le1\}$. For
  a generating vector $z\in U_n^s$ and a shift $\Delta\in[0,1]^s$, the
  **randomly shifted rank-one lattice rule** is
  $Q_n(\Delta;f)=n^{-1}\sum_{k=0}^{n-1}f(\{kz/n+\Delta\})$, and its
  **shift-averaged worst-case error** $e^{\mathrm{sh}}(z)$ is given by
  $e^{\mathrm{sh}}(z)^2=\int_{[0,1]^s}e(P_z+\Delta)^2\,d\Delta$, where
  $P_z+\Delta$ is the shifted point set. Then:
  - for every $f\in H_{s,\gamma}$, with $\Delta$ uniform on $[0,1]^s$,
    $\mathbb E_\Delta|I(f)-Q_n(\Delta;f)|^2\le e^{\mathrm{sh}}(z)^2\|f\|_{s,\gamma}^2$;
  - with $B_2(x)=x^2-x+\tfrac16$,
    $$e^{\mathrm{sh}}(z)^2=\sum_{\emptyset\ne u\subseteq\{1,\dots,s\}}\gamma_u\,
    \frac1n\sum_{k=0}^{n-1}\prod_{j\in u}B_2\Bigl(\Bigl\{\frac{kz_j}{n}\Bigr\}\Bigr);$$
  - (**CBC bound**) let $z_1=1$ and, for $r=2,\dots,s$, let $z_r\in U_n$
    minimize $e^{\mathrm{sh}}(z_1,\dots,z_r)^2$ with $z_1,\dots,z_{r-1}$ fixed
    (the **component-by-component construction**). Then for every
    $\lambda\in(\tfrac12,1]$, with $\zeta$ the Riemann zeta function,
    $$e^{\mathrm{sh}}(z_1,\dots,z_s)^2\le\Bigl(\frac1{\varphi(n)}
    \sum_{\emptyset\ne u\subseteq\{1,\dots,s\}}\gamma_u^\lambda
    \Bigl(\frac{2\zeta(2\lambda)}{(2\pi^2)^\lambda}\Bigr)^{|u|}\Bigr)^{1/\lambda}.$$

  For **product weights** $\gamma_u=\prod_{j\in u}\gamma_j$ and prime $n$ this
  gives, with $c_\lambda=2\zeta(2\lambda)/(2\pi^2)^\lambda$,
  $$e^{\mathrm{sh}}(z)\le(n-1)^{-1/(2\lambda)}
  \exp\Bigl(\frac{c_\lambda}{2\lambda}\sum_{j=1}^s\gamma_j^\lambda\Bigr).$$
  Hence, for $0<\delta\le\tfrac12$ and $\lambda=1/(2-2\delta)$, if
  $\sum_{j=1}^\infty\gamma_j^\lambda<\infty$, the root-mean-square error is
  $O(n^{-1+\delta})$ with a constant independent of $s$.

  *Assessment.* The weighted Sobolev and finite Fourier machinery are
  ingredients. The gap gives shift-averaged lattice error and its bound under
  the specified component selection.

  *Lean target.* Carriers at the pins: `Int.fract`, `Nat.totient`, `Nat.Coprime`,
  `Polynomial.bernoulli` for $B_2$, `Real.pi`, and the real series $\sum_{k\ge1}k^{-2\lambda}$ for
  $\zeta(2\lambda)$; Mathlib's reproducing kernel Hilbert space class `RKHS` can carry
  $H_{s,\gamma}$. New definitions: the weighted unanchored Sobolev space, the worst-case error, the
  shift-averaged error, and the component-by-component choice. Conjuncts: (i) the mean-square bound
  for every $f$; (ii) the formula for $e^{\mathrm{sh}}(z)^2$; (iii) the CBC bound for
  $\lambda\in(\frac12,1]$; (iv) the product-weight bound for prime $n$; (v) the $s$-independent
  $O(n^{-1+\delta})$ rate. Pitfall: `riemannZeta` is complex-valued, so use the real series; the
  worst-case error is a supremum over the unit ball and must be bounded before a real `sSup` is
  used; the CBC choice is a minimizer over a finite set of residues, so a tie needs either a rule or
  a hypothesis that covers every minimizer. Statable at the pins. NASC: `NASC.shiftedLatticeErrorSq`
  and `NASC.shiftedLatticeErrorSq_le_of_cbc` (`NASC/MonteCarlo.lean`), sorry; they take the formula
  of (ii) as the definition and state (iii); (i), (ii) as an identity with the worst-case error,
  (iv) and (v) are missing.

* **23.8. Multilevel Monte Carlo complexity.** Let $P$ be a random variable
  and let $P_0,P_1,\dots$ be approximations of it (level $\ell$). Suppose there
  are independent estimators $Y_\ell$, each the average of $N_\ell$
  independent samples, each sample having expected cost $C_\ell$ and variance
  $V_\ell$, and positive constants $\alpha,\beta,\gamma,c_1,c_2,c_3$ with
  $\alpha\ge\frac12\min(\beta,\gamma)$, such that for all $\ell\ge0$
  - $|\mathbb E[P_\ell-P]|\le c_12^{-\alpha\ell}$;
  - $\mathbb E Y_0=\mathbb E P_0$ and $\mathbb E Y_\ell=\mathbb E[P_\ell-P_{\ell-1}]$
    for $\ell>0$;
  - $V_\ell\le c_22^{-\beta\ell}$;
  - $C_\ell\le c_32^{\gamma\ell}$.

  Then there is a constant $c_4>0$ such that for every $\varepsilon<e^{-1}$
  there are $L$ and $N_0,\dots,N_L$ for which the **multilevel estimator**
  $Y=\sum_{\ell=0}^LY_\ell$ has mean square error
  $\mathbb E[(Y-\mathbb E P)^2]<\varepsilon^2$ and expected total cost
  $\mathbb E[C]=\sum_\ell N_\ell C_\ell$ bounded by
  $$\mathbb E[C]\le\begin{cases}c_4\varepsilon^{-2},&\beta>\gamma,\\
  c_4\varepsilon^{-2}(\log\varepsilon)^2,&\beta=\gamma,\\
  c_4\varepsilon^{-2-(\gamma-\beta)/\alpha},&\beta<\gamma.\end{cases}$$
  The usual choice is $Y_\ell=N_\ell^{-1}\sum_{n=1}^{N_\ell}(P_\ell^{(n)}-P_{\ell-1}^{(n)})$
  with $P_{-1}=0$, where the fine and coarse values in each sample are coupled
  and the samples are independent. For example, let $P=\phi(X_T)$ with $\phi$
  Lipschitz, and let $P_\ell=\phi(Y^{(\ell)}_N)$ where $Y^{(\ell)}$ is the
  Euler–Maruyama approximation (23.11) with step $h_\ell=2^{-\ell}h_0$, the fine
  and coarse paths driven by the same Brownian path. If
  $\mathbb E|X_T-Y^{(\ell)}_N|^2=O(h_\ell)$ and the cost per path is
  proportional to $h_\ell^{-1}$, then $V_\ell=O(2^{-\ell})$,
  $|\mathbb E[P_\ell-P]|=O(2^{-\ell/2})$ and $C_\ell=O(2^\ell)$, so the theorem
  applies with $\alpha=\tfrac12$ and $\beta=\gamma=1$ and gives cost
  $O(\varepsilon^{-2}(\log\varepsilon)^2)$.

  *Assessment.* Probability variance and summability results are available.
  The selected theorem combines telescoping estimator differences, level-wise
  variance and work to prove the complexity regimes.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IndepFun.variance_sum`,
  `ProbabilityTheory.variance`, `Real.log`, `Real.exp`, `Real.rpow` and `Nat.ceil`. No new
  definition is needed beyond the multilevel estimator. Conjuncts: (i) for independent level
  estimators the mean square error is the squared bias plus $\sum_\ell V_\ell/N_\ell$; (ii) the
  deterministic allocation: there is $c_4$ such that for $\varepsilon<e^{-1}$ some $L$ and integers
  $N_\ell\ge1$ give mean square error below $\varepsilon^2$ and cost within the three regimes; (iii)
  the Euler–Maruyama example. Pitfall: $(\log\varepsilon)^2$ for $\varepsilon<e^{-1}$ is at least
  $1$, which the $\beta=\gamma$ case uses; the $N_\ell$ are ceilings and the cost bound must absorb
  the rounding. Depends on 23.11 for (iii). Statable at the pins. NASC:
  `NASC.exists_multilevel_sample_budget` (`NASC/MonteCarlo.lean`), sorry; it states (ii) in the
  deterministic form; (i) and (iii) are missing.

### Stochastic differential equations

For the next four statements, $a:[t_0,T]\times\mathbb R^d\to\mathbb R^d$ and
$b:[t_0,T]\times\mathbb R^d\to\mathbb R^{d\times m}$, and $X$ solves the Itô
equation
$$X_t=X_{t_0}+\int_{t_0}^ta(s,X_s)\,ds+\sum_{j=1}^m\int_{t_0}^tb^{j}(s,X_s)\,dW^j_s,
\qquad t_0\le t\le T,$$
where $b^j$ is the $j$-th column of $b$. Norms on $\mathbb R^d$ and
$\mathbb R^{d\times m}$ are Euclidean and Frobenius. A **time discretization**
is $t_0=\tau_0<\tau_1<\dots<\tau_N=T$ with maximal step
$\delta=\max_n(\tau_{n+1}-\tau_n)$; write $\Delta_n=\tau_{n+1}-\tau_n$ and
$\Delta W_n=W_{\tau_{n+1}}-W_{\tau_n}$.

* **23.9. Existence and uniqueness of strong solutions.** Suppose that
  $a$ and $b$ are jointly measurable; that there is $K>0$ with
  $$|a(t,x)-a(t,y)|+\|b(t,x)-b(t,y)\|\le K|x-y|,\qquad
  |a(t,x)|^2+\|b(t,x)\|^2\le K^2(1+|x|^2)$$
  for all $t\in[t_0,T]$ and $x,y\in\mathbb R^d$; and that $X_{t_0}$ is
  $\mathcal F_{t_0}$-measurable with $\mathbb E|X_{t_0}|^2<\infty$. Then the
  equation has a **strong solution**: an $(\mathcal F_t)$-adapted process $X$
  with almost surely continuous paths satisfying the integral equation for
  all $t\in[t_0,T]$ almost surely. It satisfies
  $\sup_{t_0\le t\le T}\mathbb E|X_t|^2<\infty$, and it is **pathwise unique**:
  any two such solutions $X,\tilde X$ satisfy
  $P(\sup_{t_0\le t\le T}|X_t-\tilde X_t|>0)=0$.

  *Assessment.* Brownian and stochastic integral infrastructure is available.
  The missing existence and uniqueness result requires the contraction or
  iteration theory in the strong-solution setting.

  *Lean target.* Carriers at the pins: TauCeti's `TauCeti.Probability.IsFilteredPreBrownianReal`,
  `TauCeti.Probability.IsItoIntegral` and `TauCeti.Probability.timeMeasure`, with
  `MeasureTheory.Filtration` and `MeasureTheory.Adapted`. Infrastructure no library has: existence
  of the Itô integral for general adapted square-integrable integrands (the TauCeti predicate states
  uniqueness only), and $m$-dimensional Brownian motion with vector Itô integrals. New definition: a
  strong solution. Conjuncts: (i) existence of an adapted continuous solution; (ii)
  $\sup_t\mathbb E|X_t|^2<\infty$; (iii) pathwise uniqueness. Pitfall: the drift integral is a
  Bochner integral and is $0$ when the integrand is not integrable, so the definition of a solution
  must require pathwise integrability of $s\mapsto a(s,X_s)$ or the identity can hold for a spurious
  process; completeness of the filtration is a hypothesis. Statable at the pins for $d=m=1$; the
  proof needs the missing existence of the Itô integral. The StochasticCalculus roadmap, §9.1, owns
  the theorem. NASC: `NASC.IsScalarStrongSDESolution` and `NASC.exists_scalarStrongSDESolution`
  (`NASC/StochasticEquations.lean`), sorry; scalar case, with the integrability clause of the
  pitfall (almost surely, $s\mapsto a(s,X_s)$ integrable on every $[0,t]$), which the existence
  statement also concludes.

* **23.10. Itô–Taylor expansion.** A **multi-index** is a tuple
  $\alpha=(j_1,\dots,j_l)$ with $j_i\in\{0,1,\dots,m\}$; $l(\alpha)=l$ is its
  length, $v$ is the multi-index of length $0$, and for $l\ge1$, $-\alpha$ and
  $\alpha-$ are obtained by deleting the first and the last component. For
  stopping times $t_0\le\rho\le\tau\le T$ and a process $g$, the **multiple Itô
  integral** is defined recursively by $I_v[g]_{\rho,\tau}=g(\tau)$ and
  $$I_\alpha[g]_{\rho,\tau}=\int_\rho^\tau I_{\alpha-}[g]_{\rho,s}\,dW^{j_l}_s,
  \qquad dW^0_s=ds.$$
  With the operators
  $$L^0=\frac{\partial}{\partial t}+\sum_{k=1}^da^k\frac{\partial}{\partial x^k}
  +\frac12\sum_{k,i=1}^d\sum_{j=1}^mb^{k,j}b^{i,j}\frac{\partial^2}{\partial x^k\partial x^i},
  \qquad L^j=\sum_{k=1}^db^{k,j}\frac{\partial}{\partial x^k}\ (1\le j\le m),$$
  the **Itô coefficient functions** of $f:[t_0,T]\times\mathbb R^d\to\mathbb R$
  are $f_v=f$ and $f_\alpha=L^{j_1}f_{-\alpha}$ for $l(\alpha)\ge1$. A set
  $\mathcal A$ of multi-indices is **hierarchical** if it is nonempty, its
  lengths are bounded, and $-\alpha\in\mathcal A$ for every
  $\alpha\in\mathcal A\setminus\{v\}$; its **remainder set** is
  $\mathcal B(\mathcal A)=\{\alpha\notin\mathcal A:-\alpha\in\mathcal A\}$. Then
  $$f(\tau,X_\tau)=\sum_{\alpha\in\mathcal A}I_\alpha\bigl[f_\alpha(\rho,X_\rho)\bigr]_{\rho,\tau}
  +\sum_{\alpha\in\mathcal B(\mathcal A)}I_\alpha\bigl[f_\alpha(\cdot,X_\cdot)\bigr]_{\rho,\tau},$$
  provided all derivatives of $f,a,b$ and all multiple Itô integrals that
  occur exist. For $f(t,x)=x$ and $\mathcal A=\{v,(0),(1),\dots,(m)\}$ the
  leading terms give the Euler–Maruyama step; adding the indices $(j_1,j_2)$
  with $j_1,j_2\ge1$ gives the Milstein step. For $1\le j\le m$ one has
  $I_{(j,j)}[1]_{\tau_n,\tau_{n+1}}=\frac12\bigl((\Delta W^j_n)^2-\Delta_n\bigr)$.

  *Assessment.* The Itô integral supplies ingredients. The selected expansion
  requires recursive multiple integrals and control of the terms omitted by
  truncation.

  *Lean target.* Carriers at the pins: as in 23.9, with `iteratedDeriv` and `List` for
  multi-indices. Infrastructure no library has: existence of Itô integrals of general integrands,
  Itô's formula for Itô processes, and iterated Itô integrals. New definitions: multiple Itô
  integrals by recursion, the operators $L^0,L^j$, the coefficient functions, hierarchical sets and
  remainder sets. Conjuncts: (i) the expansion identity under existence hypotheses; (ii) the
  Euler–Maruyama and Milstein truncations; (iii) $I_{(j,j)}=\frac12((\Delta W^j_n)^2-\Delta_n)$.
  Pitfall: the identity needs every multiple integral to exist, which must be a hypothesis or a
  consequence of the regularity assumptions. Depends on 23.9. NASC:
  `NASC.exists_itoTaylor_local_remainder_bound` (`NASC/StochasticEquations.lean`), sorry; scalar,
  $f(x)=x$, the Milstein truncation, with the local mean-square remainder $O(h^3)$.

* **23.11. Euler–Maruyama: strong order 1/2 and weak order 1.** The
  **Euler–Maruyama scheme** is
  $Y_{n+1}=Y_n+a(\tau_n,Y_n)\Delta_n+b(\tau_n,Y_n)\Delta W_n$.
  - (Strong order $\tfrac12$.) Take $t_0=0$. Suppose $\mathbb E|X_0|^2<\infty$,
    $(\mathbb E|X_0-Y_0|^2)^{1/2}\le K_1\delta^{1/2}$, and for all
    $s,t\in[0,T]$, $x,y\in\mathbb R^d$:
    $|a(t,x)-a(t,y)|+|b(t,x)-b(t,y)|\le K_2|x-y|$,
    $|a(t,x)|+|b(t,x)|\le K_3(1+|x|)$ and
    $|a(s,x)-a(t,x)|+|b(s,x)-b(t,x)|\le K_4(1+|x|)|s-t|^{1/2}$, with
    $K_1,\dots,K_4$ independent of $\delta$. Then
    $\mathbb E|X_T-Y_N|\le K_5\delta^{1/2}$ with $K_5$ independent of $\delta$.
  - (Weak order $1$.) Suppose $a=a(x)$ and $b=b(x)$ are autonomous and
    globally Lipschitz, all components of $a$ and $b$ are four times
    continuously differentiable with all derivatives up to order four of
    polynomial growth, and $Y_0=X_0$ is a deterministic point. Then for every
    $g:\mathbb R^d\to\mathbb R$ that is four times continuously differentiable
    with all derivatives up to order four of polynomial growth there is $C_g$,
    independent of $\delta$, with $|\mathbb E g(X_T)-\mathbb E g(Y_N)|\le C_g\delta$.

  *Assessment.* An explicit Euler recursion and the exact SDE must be compared
  in the two stated senses. The missing convergence results also need the
  specified differentiability and moment hypotheses.

  *Lean target.* Carriers at the pins: as in 23.9, with `ContDiff` and polynomial growth bounds. New
  definition: the Euler–Maruyama recursion on a time grid. Conjuncts: (i) the strong bound
  $\mathbb E|X_T-Y_N|\le K_5\delta^{1/2}$; (ii) the weak bound for $C^4$ test functions of
  polynomial growth. Pitfall: the hypotheses include an initial error of order $\delta^{1/2}$ in
  mean square, which a uniform grid model must keep. Depends on 23.9; (ii) needs the Kolmogorov
  backward equation, which no library has. The StochasticCalculus roadmap, §9.6, owns the theorem.
  NASC: `NASC.exists_eulerMaruyama_strong_error_bound` (`NASC/StochasticEquations.lean`), sorry;
  scalar, uniform steps, with mean-square error $O(h)$, which implies (i); (ii) is missing.

* **23.12. Milstein scheme: strong order 1.** Let $m=1$, let
  $a=f(x)$ and $b=g(x)$ be autonomous, let the steps be uniform,
  $\tau_n=n\Delta t$, and let $X_0=u_0$ be deterministic. The **Milstein
  scheme** is
  $$u_{n+1}=u_n+f(u_n)\Delta t+g(u_n)\Delta W_n
  +\tfrac12\,Dg(u_n)g(u_n)\bigl((\Delta W_n)^2-\Delta t\bigr),$$
  where $Dg$ is the Jacobian of $g$. Suppose $f$ and $g$ are globally
  Lipschitz with linear growth, twice continuously differentiable with
  bounded second derivatives, and that $x\mapsto Dg(x)g(x)$ is globally
  Lipschitz. Then for every $T>0$ there is $K$, independent of $\Delta t$, with
  $$\max_{0\le n\Delta t\le T}\bigl(\mathbb E|X_{n\Delta t}-u_n|^2\bigr)^{1/2}\le K\Delta t.$$
  For general $m$ the Milstein scheme adds
  $\sum_{j_1,j_2=1}^mL^{j_1}b^{j_2}(\tau_n,Y_n)\,I_{(j_1,j_2)}$ to the
  Euler–Maruyama step, and it has strong order $1$ under Lipschitz, linear
  growth and Hölder-in-time conditions on the coefficients and on some of
  their images under the operators $L^j$ of 23.10. The integrals $I_{(j_1,j_2)}$
  with $j_1\ne j_2$ are not functions of the increments $\Delta W^j_n$; if they
  are replaced by $\frac12\Delta W^{j_1}_n\Delta W^{j_2}_n$, the strong order
  drops to $\tfrac12$ in general, for example for $dX^1=dW^1$,
  $dX^2=X^1dW^2$. If $g$ is constant (additive noise), the Milstein and
  Euler–Maruyama schemes coincide.

  *Assessment.* The missing higher-order stochastic step uses the Itô–Taylor
  correction and, in multiple dimensions, the information contained in
  iterated integrals.

  *Lean target.* Carriers at the pins: as in 23.9, with `deriv`, `LipschitzWith` and `ContDiff`. New
  definition: the Milstein recursion. Conjuncts: (i) the scalar strong order one; (ii) the
  multidimensional scheme with iterated integrals; (iii) loss of order with the product
  approximation for $dX^1=dW^1$, $dX^2=X^1dW^2$; (iv) coincidence with Euler–Maruyama for additive
  noise. Pitfall: `deriv` is $0$ at points of non-differentiability, so $C^2$ regularity must be a
  hypothesis. Depends on 23.9 and 23.10. NASC: `NASC.exists_milstein_strong_error_bound`
  (`NASC/StochasticEquations.lean`), sorry; (i) for steps $h\le1$; (ii)–(iv) are missing.

* **23.13. Mean-square stability of the stochastic θ-method.** Let
  $r,\sigma\in\mathbb R$ and consider geometric Brownian motion
  $du=ru\,dt+\sigma u\,dW$ with deterministic $u(0)=u_0\ne0$. Then
  $\mathbb E u(t)^2=e^{(2r+\sigma^2)t}u_0^2$, so $\mathbb E u(t)^2\to0$ if and
  only if $r+\sigma^2/2<0$. For $\theta\in[0,1]$ and $\Delta t>0$ with
  $1-\theta r\Delta t\ne0$, the **θ-Euler–Maruyama method**
  $$u_{n+1}=u_n+\bigl((1-\theta)ru_n+\theta ru_{n+1}\bigr)\Delta t+\sigma u_n\Delta W_n$$
  satisfies $\mathbb E u_n^2=R^nu_0^2$ with
  $$R=\frac{(1+(1-\theta)r\Delta t)^2+\sigma^2\Delta t}{(1-\theta r\Delta t)^2},$$
  and $\mathbb E u_n^2\to0$ as $n\to\infty$ if and only if
  $$r+\frac{\sigma^2}2+\frac{(1-2\theta)r^2\Delta t}2<0 .$$
  Hence for $\theta=0$ (Euler–Maruyama) and $r+\sigma^2/2<0$ the method is
  mean-square stable if and only if $0<\Delta t<-2(r+\sigma^2/2)/r^2$, while
  for $\theta\ge\tfrac12$ it is mean-square stable for every $\Delta t>0$
  whenever $r+\sigma^2/2<0$. For $\theta=\tfrac12$ its stability region
  coincides with that of the exact solution.

  *Assessment.* Partly covered. TauCeti gives the exact geometric Brownian
  power moments. The selected result gives the separate moment recursion and
  boundary of stability for the discrete θ-method.

  *Scope.* The selected claim is the mean-square stability criterion for the
  stochastic numerical recursion.

  *Lean target.* Carriers at the pins: TauCeti's
  `ProbabilityTheory.IsPreBrownianReal.integral_rpow_geometricBrownianMotion` and
  `TauCeti.Probability.IsFilteredPreBrownianReal`. No new definition is needed. Conjuncts: (i)
  $\mathbb Eu(t)^2=e^{(2r+\sigma^2)t}u_0^2$; (ii) $\mathbb Eu_n^2=R^nu_0^2$; (iii) the stability
  criterion; (iv) the $\theta=0$ step-size bound and unconditional stability for $\theta\ge\frac12$.
  Pitfall: the recursion divides by $1-\theta r\Delta t$, so its nonvanishing is a hypothesis, and
  (ii) uses independence of the increment from $u_n$, which adaptedness to the Brownian filtration
  gives. Statable and provable at the pins. NASC: `NASC.theta_mean_square_stability`
  (`NASC/StochasticEquations.lean`), sorry; it states (ii) and (iii); (i) and (iv) are missing.

* **23.16. Strong convergence for a parabolic SPDE.** Let $H$ be a separable
  Hilbert space and $A:D(A)\subset H\to H$ a linear operator with a complete
  orthonormal set of eigenfunctions $\phi_j$ and eigenvalues
  $0<\lambda_1\le\lambda_2\le\cdots$. Let $f:H\to H$ satisfy
  $\|f(u)\|\le L(1+\|u\|)$ and $\|f(u_1)-f(u_2)\|\le L\|u_1-u_2\|$. Let $W$ be
  either a $Q$-Wiener process on $H$, with $Q$ symmetric, nonnegative definite
  and of finite trace, or the cylindrical Wiener process ($Q=I$), and assume
  $Q\phi_j=q_j\phi_j$ for all $j$. Let $\sigma>0$ and suppose
  $\|A^{(\zeta-1)/2}Q^{1/2}\|_{\mathrm{HS}}<\infty$ for some $\zeta\in(0,2]$. Then
  the equation $du=(-Au+f(u))\,dt+\sigma\,dW$, $u(0)=u_0\in D(A)$
  deterministic, has a unique mild solution
  $$u(t)=e^{-tA}u_0+\int_0^te^{-(t-s)A}f(u(s))\,ds+\sigma\int_0^te^{-(t-s)A}\,dW(s)$$
  on $[0,T]$. Let $P_J$ be the orthogonal projection onto
  $\mathrm{span}\{\phi_1,\dots,\phi_J\}$, $A_J=P_JA$, $t_n=n\Delta t$, and
  define the spectral Galerkin, semi-implicit Euler–Maruyama approximation by
  $u_{J,0}=P_Ju_0$ and
  $$u_{J,n+1}=(I+\Delta tA_J)^{-1}\bigl(u_{J,n}+\Delta t\,P_Jf(u_{J,n})
  +\sigma P_J(W(t_{n+1})-W(t_n))\bigr).$$
  Then for every $\epsilon>0$ there is $K$ such that, as $\Delta t\to0$ and
  $J\to\infty$ with $\Delta t\lambda_J$ fixed,
  $$\max_{0\le t_n\le T}\bigl(\mathbb E\|u(t_n)-u_{J,n}\|^2\bigr)^{1/2}\le
  K\Delta t^{\zeta/2-\epsilon}.$$
  For the stochastic heat equation $du=u_{xx}\,dt+\sigma\,dW$ on $(0,a)$ with
  homogeneous Dirichlet conditions, $\lambda_j=(j\pi/a)^2$, and space-time
  white noise ($Q=I$) the condition holds exactly for $\zeta<\tfrac12$, so
  the rate is $\Delta t^{1/4-\epsilon}$ for every $\epsilon>0$.

  *Assessment.* TauCeti has semigroup machinery and an Itô integration
  development. The selected result controls time and spectral discretization
  of the mild SPDE with its stated noise and smoothing exponents.

  *Lean target.* Carriers at the pins: TauCeti's
  `ProbabilityTheory.IsPreBrownianReal.wienerIntegral` for each mode,
  `ProbabilityTheory.IsPreBrownianReal`, and `TauCeti.Probability.timeMeasure`. Infrastructure no
  library has: $Q$-Wiener and cylindrical Wiener processes, Hilbert-space-valued stochastic
  integrals, and mild solutions of semilinear SPDEs. New definitions: the mild solution and the
  semi-implicit spectral Galerkin scheme. Conjuncts: (i) existence and uniqueness of the mild
  solution; (ii) the strong error bound with $\Delta t\lambda_J$ fixed; (iii) the white-noise heat
  equation with $\zeta<\frac12$. Pitfall: a cylindrical process is not $H$-valued, so a diagonal
  model by independent scalar Brownian motions with weights $q_j$ is the practical carrier. NASC:
  `NASC.stochastic_convolution_spectral_error_le` (`NASC/StochasticEquations.lean`), sorry; the
  linear case $f=0$, $u_0=0$, diagonal noise, under $\Delta t\lambda_N\ge1$ in place of a fixed
  ratio, with the mean-square error summed over modes in `ℝ≥0∞` (`∫⁻`); (i) and the semilinear case
  are missing.

## 24. High-dimensional approximation, uncertainty quantification, and model reduction

[Synopsis](SYNOPSIS.md#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction) · [Coverage inventory](STRUCTURE.md#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction)

Approximation numbers, Gaussian laws, Hilbert bases and polynomial and
neural-network expressiveness provide ingredients. The selected results
quantify dimension, error and reduced-model stability.

Here $d$ denotes the number of variables of the functions being
approximated. For a multi-index $l\in\mathbb N^d$ write
$|l|_1=l_1+\cdots+l_d$ and $|l|_\infty=\max_j l_j$; inequalities between
multi-indices hold componentwise, and $\mathbf 1=(1,\dots,1)$. Weak greedy
selection uses a constant $\gamma\in(0,1]$. Quasi-Monte Carlo lattice rules
and their error bounds are in section 23, and low-rank and tensor
approximation in section 6.

### Sparse grids

* **24.2. Sparse grid interpolation.** For $n\in\mathbb N$ the **sparse grid
  space** is $V^{(1)}_n=\bigoplus_{|l|_1\le n+d-1}W_l$, and the sparse grid
  interpolant of $u\in X^{q,2}_0$ is $u^{(1)}_n=\sum_{|l|_1\le n+d-1}u_l$. Put
  $h_n=2^{-n}$. The number of grid points is
  $$\dim V^{(1)}_n=\sum_{i=0}^{n-1}2^i\binom{d-1+i}{d-1}
  =2^n\Bigl(\frac{n^{d-1}}{(d-1)!}+O(n^{d-2})\Bigr)
  =O\bigl(h_n^{-1}|\log_2h_n|^{d-1}\bigr),$$
  against $(2^n-1)^d=O(h_n^{-d})$ for the full grid
  $V^{(\infty)}_n=\bigoplus_{|l|_\infty\le n}W_l$. With
  $A(d,n)=\sum_{k=0}^{d-1}\binom{n+d-1}{k}=n^{d-1}/(d-1)!+O(n^{d-2})$, every
  $u\in X^{q,2}_0$ satisfies
  $$\|u-u^{(1)}_n\|_{L^\infty}\le\frac{2\,|u|_{2,\infty}}{8^d}\,2^{-2n}A(d,n),
  \qquad
  \|u-u^{(1)}_n\|_{L^2}\le\frac{2\,|u|_{2,2}}{12^d}\,2^{-2n}A(d,n),$$
  so both errors are $O(h_n^2|\log_2h_n|^{d-1})$, and in the energy norm
  $\|v\|_E=\|\nabla v\|_{L^2}$,
  $$\|u-u^{(1)}_n\|_E\le\frac{d\,|u|_{2,\infty}}{2\cdot3^{(d-1)/2}\cdot4^{d-1}}\,2^{-n}
  =O(h_n).$$
  The implied constants in the $O$-terms depend on $d$ and on the seminorm
  of $u$.

  *Assessment.* Tensor products and univariate interpolation provide
  ingredients. The gap needs the mixed hierarchical decomposition and the
  joint mesh-size, cost and error bound.

  *Lean target.* Carriers at the pins: `Nat.choose`, `iteratedFDeriv`, `MeasureTheory.Lp`, and
  `Finset.sum` over level vectors. New definitions: the hierarchical hat functions, the increment
  spaces $W_l$, the sparse grid space and interpolant, and the mixed seminorms $|u|_{2,\infty}$ and
  $|u|_{2,2}$. Conjuncts: (i) the exact point count; (ii) its asymptotic form; (iii) the $L^\infty$
  and $L^2$ bounds with $A(d,n)$; (iv) the energy bound. Pitfall: `(d - 1).choose` with natural
  subtraction needs $d\ge1$; levels are $1$-based here and $0$-based in a Lean index type, which
  shifts $|l|_1\le n+d-1$ to a sum below $n$. Statable at the pins for $u$ with continuous mixed
  second derivatives. NASC: `NASC.SparseGridIndex` and `NASC.card_sparseGridIndex`
  (`NASC/ModelReduction.lean`), sorry; only (i).

### Information-based complexity and tractability

* **24.3. Worst-case setting and tractability.** Let $S:F\to G$ be a map
  from a subset $F$ of a normed space into a normed space $G$, and let
  $\Lambda$ be a class of admissible linear functionals on $F$: either
  $\Lambda^{\mathrm{all}}$, all continuous linear functionals, or
  $\Lambda^{\mathrm{std}}$, point evaluations. An **algorithm using $n$
  information operations** is a map $A_n=\varphi\circ N$ with
  $N(f)=(L_1(f),\dots,L_n(f))$, $L_i\in\Lambda$, and an arbitrary
  $\varphi:N(F)\to G$. Its **worst-case error** is
  $e(A_n)=\sup_{f\in F}\|S(f)-A_n(f)\|$. For a sequence of problems
  $S_d:F_d\to G_d$, $d\in\mathbb N$, the **information complexity**
  $n(\varepsilon,d)$ is the least $n\ge0$ for which some $A_n$ has
  $e(A_n)\le\varepsilon$ (**absolute error criterion**), or
  $e(A_n)\le\varepsilon\,e_0$, where $e_0=\sup_{f\in F_d}\|S_d f\|$ is the
  initial error (**normalized error criterion**); the minimum over the empty
  set is $\infty$. The problem is **polynomially tractable** if there are
  $C,p,q\ge0$ with
  $$n(\varepsilon,d)\le C\,d^{\,q}\varepsilon^{-p}\qquad
  \text{for all }d\in\mathbb N,\ \varepsilon\in(0,1),$$
  **strongly polynomially tractable** if this holds with $q=0$, and **weakly
  tractable** if $\log n(\varepsilon,d)/(\varepsilon^{-1}+d)\to0$ as
  $\varepsilon^{-1}+d\to\infty$. If $S:H\to G$ is a compact linear operator
  between Hilbert spaces, $F$ is the unit ball of $H$, $\dim H\ge n$, and
  $\lambda_1\ge\lambda_2\ge\cdots\ge0$ are the eigenvalues of $S^*S$ with
  orthonormal eigenvectors $e_i$, then for $\Lambda^{\mathrm{all}}$ the
  minimal worst-case error of algorithms using $n$ functionals is
  $\sqrt{\lambda_{n+1}}$, attained by the linear algorithm
  $A_n(f)=\sum_{i=1}^n\langle f,e_i\rangle S(e_i)$. Consequently the
  absolute-error information complexity is
  $n(\varepsilon)=\min\{n:\lambda_{n+1}\le\varepsilon^2\}$.

  *Assessment.* Not covered. TauCeti has approximation numbers of compact operators and their
  identification with singular values. The gap defines worst-case algorithms and information
  complexity and proves that the truncated singular expansion is optimal among all algorithms using
  $n$ continuous linear functionals.

  *Lean target.* Carriers at the pins: TauCeti's `ContinuousLinearMap.singularValue` (approximation
  numbers, indexed from $0$), `IsCompactOperator`, and `StrongDual`. New definitions: an algorithm
  as a composition of $n$ admissible functionals with an arbitrary map, its worst-case error, the
  minimal error, information complexity, and polynomial, strong polynomial and weak tractability.
  Conjuncts: (i) for compact $S$ between Hilbert spaces the minimal error with $n$ functionals is
  $\sqrt{\lambda_{n+1}}$; (ii) the linear algorithm attains it; (iii)
  $n(\varepsilon)=\min\{n:\lambda_{n+1}\le\varepsilon^2\}$. Pitfall: the worst-case error is a
  supremum that may be infinite, so use `ℝ≥0∞`; information complexity is a minimum over a possibly
  empty set, so use `ℕ∞`, since `sInf ∅ = 0` in `ℕ`. Statable at the pins. NASC: no declaration.

* **24.4. Tractability of linear problems on Hilbert spaces.** Let
  $S_d:H_d\to G_d$ be nonzero compact linear operators between Hilbert
  spaces, let $\lambda_{d,1}\ge\lambda_{d,2}\ge\cdots\ge0$ be the eigenvalues
  of $S_d^*S_d$, and consider the absolute error criterion with
  $\Lambda^{\mathrm{all}}$, so that
  $n(\varepsilon,d)=\min\{n:\lambda_{d,n+1}\le\varepsilon^2\}$.
  - The problem is polynomially tractable if and only if there are $C_1>0$,
    $q_1,q_2\ge0$ and $\tau>0$ with
    $$C_2:=\sup_{d\in\mathbb N}\Bigl(\sum_{j=\lceil C_1d^{q_1}\rceil}^\infty
    \lambda_{d,j}^{\tau}\Bigr)^{1/\tau}d^{-q_2}<\infty ,$$
    and then $n(\varepsilon,d)\le(C_1+C_2^{\tau})\,d^{\max(q_1,q_2\tau)}
    \varepsilon^{-2\tau}$ for all $\varepsilon\in(0,1]$ and $d\in\mathbb N$.
    It is strongly polynomially tractable if and only if this holds with
    $q_1=q_2=0$.
  - (**Curse of dimensionality for tensor products.**) Let
    $S_d=S_1\otimes\cdots\otimes S_1$ ($d$ factors) for a compact linear
    $S_1:H_1\to G_1$ between Hilbert spaces, and let
    $\lambda_1\ge\lambda_2\ge\cdots$ be the eigenvalues of $S_1^*S_1$. If
    $\lambda_1=\lambda_2=1$, then $n(\varepsilon,d)\ge2^d$ for all
    $\varepsilon\in(0,1)$ and $d\in\mathbb N$, so the problem is not even
    weakly tractable. If $\lambda_2>0$ and $\lambda_1<1$, then polynomial
    tractability, strong polynomial tractability, and
    $\lambda_n=O(n^{-r})$ for some $r>0$ are equivalent.

  *Assessment.* TauCeti supplies compact Hilbert-space singular expansions and
  approximation numbers. The selected result interprets these as optimal
  linear information complexity and gives all stated tractability tests.

  *Lean target.* Carriers at the pins: TauCeti's `ContinuousLinearMap.singularValue` and `Nat.ceil`,
  `Real.rpow`, `Summable`. The Hilbert tensor product has no carrier at the pins; state the
  tensor-product case through its eigenvalues, the products $\lambda_{i_1}\cdots\lambda_{i_d}$ in
  nonincreasing order. Conjuncts: (i) the polynomial tractability criterion with the explicit bound;
  (ii) strong polynomial tractability with $q_1=q_2=0$; (iii) $\lambda_1=\lambda_2=1$ gives
  $n(\varepsilon,d)\ge2^d$ and no weak tractability; (iv) for $\lambda_2>0$ and $\lambda_1<1$, the
  three equivalent conditions. Pitfall: $\lambda_{d,n+1}$ is $1$-based here and `singularValue` is
  $0$-based; tail sums must be `tsum` under summability. Depends on 24.3. Statable at the pins.
  NASC: `NASC.polynomial_tractability_iff_summable_tail` (`NASC/ModelReduction.lean`), sorry; (i)
  without the explicit bound, for an abstract antitone null sequence; (ii)–(iv) are missing.

* **24.5. Tractability of integration in weighted Sobolev spaces.** Let
  $\gamma_1,\gamma_2,\ldots>0$ be weights and $c\in[0,1]$ an anchor. Let
  $H_{s,\gamma}$ be the reproducing kernel Hilbert space on $[0,1]^s$ with
  kernel
  $$K_{s,\gamma}(x,y)=\prod_{j=1}^s\bigl(1+\gamma_j\,\eta(x_j,y_j)\bigr),
  \qquad
  \eta(x,y)=\begin{cases}\min(x,y)-c,&x,y>c,\\ c-\max(x,y),&x,y<c,\\
  0,&\text{otherwise,}\end{cases}$$
  the **weighted anchored Sobolev space** with product weights; for $s=1$
  its norm is
  $\|f\|^2=f(c)^2+\gamma_1^{-1}\int_0^1f'(x)^2\,dx$. Consider
  approximating $I_s(f)=\int_{[0,1]^s}f$ over the unit ball of $H_{s,\gamma}$
  by arbitrary algorithms using $n$ function values, with the absolute
  error criterion. This problem is strongly polynomially tractable if and
  only if $\sum_{j=1}^\infty\gamma_j<\infty$, and it is polynomially
  tractable if and only if
  $$\limsup_{s\to\infty}\frac{\sum_{j=1}^s\gamma_j}{\log(s+1)}<\infty .$$
  The same characterizations hold for the unanchored weighted Sobolev space.
  In particular, with equal weights $\gamma_j=1$ the problem is not
  polynomially tractable.

  *Assessment.* Not covered. Mathlib has reproducing kernel Hilbert spaces. The gap is the
  characterization of strong polynomial and polynomial tractability of integration with function
  values in weighted anchored and unanchored Sobolev spaces, which needs lower bounds for arbitrary
  algorithms and upper bounds through quasi-Monte Carlo rules.

  *Lean target.* Carriers at the pins: Mathlib's `RKHS`, `Real.log`, `Summable`, and the complexity
  notions of 24.3 with point evaluations. New definitions: the anchored kernel, the space
  $H_{s,\gamma}$, and the information complexity of integration with $n$ function values. Conjuncts:
  (i) strong polynomial tractability if and only if $\sum_j\gamma_j<\infty$; (ii) polynomial
  tractability if and only if $\sum_{j\le s}\gamma_j\le C\log(s+1)$ for some $C$ and all $s\ge1$;
  (iii) the same for the unanchored space; (iv) equal weights give no polynomial tractability.
  Pitfall: a real `Filter.limsup` of an unbounded sequence is junk, so (ii) is stated with an
  explicit constant, which is equivalent because $\log(s+1)>0$ for $s\ge1$. Depends on 24.3, and on
  23.7 for the upper bound. Statable at the pins. NASC: no declaration.

### Widths, greedy bases, and parametric holomorphy

* **24.6. Kolmogorov widths and the weak greedy algorithm.** Let $K$ be a
  compact subset of a Banach space $V$. Its **Kolmogorov $n$-width** is
  $$d_n(K)_V=\inf_{\dim V_n\le n}\ \sup_{v\in K}\ \inf_{w\in V_n}\|v-w\|_V ,$$
  the infimum over linear subspaces, so that $d_0(K)_V=\max_{v\in K}\|v\|_V$.
  The **weak greedy algorithm** with constant $\gamma$ chooses
  $g_0,g_1,\ldots\in K$ such that, with $V_n=\mathrm{span}\{g_0,\dots,g_{n-1}\}$
  ($V_0=\{0\}$),
  $$\mathrm{dist}(g_n,V_n)_V\ge\gamma\max_{g\in K}\mathrm{dist}(g,V_n)_V ;$$
  its error is $\sigma_n(K)_V=\max_{g\in K}\mathrm{dist}(g,V_n)_V$. If $V$ is
  a Hilbert space, then for every such sequence:
  - $\sigma_n(K)_V\le\sqrt2\,\gamma^{-1}\min_{1\le m<n}
    d_0(K)_V^{\,m/n}\,d_m(K)_V^{\,(n-m)/n}$ for $n\ge2$; in particular
    $\sigma_{2n}(K)_V\le\gamma^{-1}\sqrt{2\,d_0(K)_V\,d_n(K)_V}$ for
    $n\ge1$;
  - if $s>0$, $C_0>0$ and $d_n(K)_V\le C_0\max\{1,n\}^{-s}$ for all
    $n\ge0$, then $\sigma_n(K)_V\le\gamma^{-2}2^{4s+1}C_0\max\{1,n\}^{-s}$
    for all $n\ge0$;
  - if $s,c_0,C_0>0$ and $d_n(K)_V\le C_0e^{-c_0n^s}$ for all $n\ge0$, then
    $\sigma_n(K)_V\le C_0\max\{\sqrt2\gamma^{-1},e^{c_1}\}e^{-c_1n^s}$ for
    all $n\ge0$, where $c_1=(c_0/2)\,3^{-s}$.

  *Assessment.* Orthogonal projections and metric approximation are available.
  The missing result compares the errors of a weak greedy sequence with the
  Kolmogorov widths and transfers decay rates.

  *Lean target.* Carriers at the pins: `Metric.infDist`, `Submodule.span`, `Module.finrank`,
  `IsCompact`, and `Real.rpow`. New definitions: the Kolmogorov width, a weak greedy sequence and
  its error. Conjuncts: (i) the bound with the minimum over $m<n$ and the $\sigma_{2n}$ special
  case; (ii) the polynomial transfer; (iii) the exponential transfer. Pitfall: the width is an
  infimum of suprema; for nonempty compact $K$ the suprema are finite and the infimum is over a
  nonempty set bounded below by $0$, which should be lemmas beside a real `sInf`/`sSup` definition.
  Statable at the pins. NASC: `NASC.kolmogorovWidth` and `NASC.weak_greedy_error_two_mul_le`
  (`NASC/ModelReduction.lean`), sorry; only the $\sigma_{2n}$ case of (i).

* **24.7. Holomorphy and sparse polynomial approximation of parametric
  solutions.** Let $D\subset\mathbb R^m$ be a bounded Lipschitz domain,
  $V=H^1_0(D)$ with norm $\|\nabla v\|_{L^2}$, $f\in H^{-1}(D)$, and for
  $a\in L^\infty(D)$ let $u(a)\in V$ solve $-\mathrm{div}(a\nabla u)=f$
  weakly. Let $\bar a,\psi_1,\psi_2,\ldots\in L^\infty(D)$ be real,
  $(\|\psi_j\|_{L^\infty})_j\in\ell^1$, put $U=[-1,1]^{\mathbb N}$ and
  $a(y)=\bar a+\sum_{j\ge1}y_j\psi_j$, and assume **uniform ellipticity**
  with a constant $r>0$:
  $$\sum_{j\ge1}|\psi_j(x)|\le\bar a(x)-r\qquad\text{for a.e. }x\in D.$$
  - For complex $a\in L^\infty(D)$ with $\mathrm{Re}\,a\ge r$ a.e., the
    weak problem has a unique solution, $\|u(a)\|_V\le\|f\|_{H^{-1}}/r$, and
    $a\mapsto u(a)$ is holomorphic on the open set
    $\{a:\mathrm{ess\,inf}\,\mathrm{Re}\,a>0\}$. Hence $y\mapsto u(a(y))$
    extends to the polydisc $\{z\in\mathbb C^{\mathbb N}:|z_j|\le1\}$,
    holomorphic in each $z_j$, with $\sup_z\|u(a(z))\|_V\le\|f\|_{H^{-1}}/r$.
  - Let $\mathcal F$ be the set of finitely supported
    $\nu\in\mathbb N_0^{\mathbb N}$, $y^\nu=\prod_jy_j^{\nu_j}$, and let
    $t_\nu=\partial^\nu u(0)/\nu!$ be the Taylor coefficients. If moreover
    $(\|\psi_j\|_{L^\infty})_{j\ge1}\in\ell^p$ for some $0<p<1$, then
    $(\|t_\nu\|_V)_{\nu\in\mathcal F}\in\ell^p(\mathcal F)$, the Taylor series
    $\sum_\nu t_\nu y^\nu$ converges to $u(a(y))$ unconditionally in
    $L^\infty(U,V)$, and for any set $\Lambda_n$ of $n$ indices carrying the
    $n$ largest $\|t_\nu\|_V$,
    $$\sup_{y\in U}\Bigl\|u(a(y))-\sum_{\nu\in\Lambda_n}t_\nu y^\nu\Bigr\|_V
    \le\bigl\|(\|t_\nu\|_V)_\nu\bigr\|_{\ell^p}\,(n+1)^{-(1/p-1)} .$$
  The best $n$-term rate $n^{-(1/p-1)}$ does not depend on the number of
  parameters.

  *Assessment.* Coercive variational solvability and holomorphic maps are
  ingredients. The selected theorem needs a uniform parameter-dependent
  complex domain and summability of the resulting polynomial coefficients.

  *Lean target.* Carriers at the pins: `AnalyticOnNhd`, `DifferentiableOn ℂ`, `Finsupp` (`ℕ →₀ ℕ`)
  for multi-indices, `Summable` of $p$-th powers, and the Lax–Milgram equivalence
  `IsCoercive.continuousLinearEquivOfBilin`. $H^1_0(D)$ on a Lipschitz domain has no convenient
  carrier; state the result on an abstract complex Hilbert space $V$ with a bounded family of
  coercive forms $a(z)=\bar a+\sum_jz_j\psi_j$. Conjuncts: (i) solvability and the bound for
  $\mathrm{Re}\,a\ge r$; (ii) holomorphy in each $z_j$ on the polydisc; (iii) $\ell^p$ summability
  of the Taylor coefficients; (iv) unconditional convergence and the best $n$-term bound. Pitfall:
  $\ell^p$ with $p<1$ is not normed, so use summability of $\|t_\nu\|^p$ rather than `lp`. Statable
  at the pins in the abstract form. NASC: `NASC.exists_analyticOnNhd_parametric_inverse`
  (`NASC/ModelReduction.lean`), sorry; a Neumann-series holomorphy lemma for one affine operator
  family, an ingredient of (i)–(ii); (iii) and (iv) are missing.

### Projection-based model reduction

* **24.8. Proper orthogonal decomposition.** Let
  $S=[u_1|\cdots|u_{n_s}]\in\mathbb R^{N_h\times n_s}$ be a snapshot matrix
  of rank $r$, let $X_h\in\mathbb R^{N_h\times N_h}$ be symmetric positive
  definite with $\|v\|_{X_h}^2=v^\top X_hv$, and let
  $X_h^{1/2}S=\tilde U\Sigma Z^\top$ be a singular value decomposition with
  singular values $\sigma_1\ge\cdots\ge\sigma_r>0$ and left singular vectors
  $\tilde\zeta_1,\tilde\zeta_2,\ldots$. For $N\le r$ the **POD basis** is
  $V=X_h^{-1/2}[\tilde\zeta_1|\cdots|\tilde\zeta_N]$, which satisfies
  $V^\top X_hV=I_N$. Among all $W\in\mathbb R^{N_h\times N}$ with
  $W^\top X_hW=I_N$, that is, among all $N$-dimensional subspaces with the
  $X_h$-orthogonal projection $WW^\top X_h$, the POD basis minimizes the
  snapshot projection error, and
  $$\sum_{i=1}^{n_s}\|u_i-VV^\top X_hu_i\|_{X_h}^2
  =\min_{W^\top X_hW=I_N}\sum_{i=1}^{n_s}\|u_i-WW^\top X_hu_i\|_{X_h}^2
  =\sum_{i=N+1}^r\sigma_i^2 .$$

  *Assessment.* The underlying spectral and low-rank machinery is available in part: Mathlib has
  singular values of linear maps, and TauCeti identifies approximation numbers with them and proves
  the Ky Fan and Hilbert–Schmidt identities. The selected weighted snapshot projection identity
  expresses the minimum over subspaces in the metric of the state space.

  *Lean target.* Carriers at the pins: `LinearMap.singularValues`, `Matrix.toEuclideanLin`,
  TauCeti's `ContinuousLinearMap.singularValue_eq_linearMap_singularValues` and
  `ContinuousLinearMap.tsum_singularValue_sq_eq_hilbertSchmidtEnergy`, and `IsLeast`. No new
  definition is needed. Conjuncts: (i) the POD basis is $X_h$-orthonormal; (ii) it attains the
  minimum; (iii) the minimum is $\sum_{i>N}\sigma_i^2$. Pitfall: `singularValues` is indexed from
  $0$ and vanishes beyond the rank, so the tail is a sum over $N\le i<\min(N_h,n_s)$; the weighted
  case reduces to the Euclidean one through any factorization $X_h=R^\top R$, which avoids a matrix
  square root. Statable at the pins. NASC: `NASC.isLeast_pod_snapshot_error_sq`
  (`NASC/ModelReduction.lean`), sorry; the Euclidean case $X_h=I$ of (ii) and (iii).

* **24.9. Residual-based a posteriori error bound.** Let $V_h$ be a
  finite-dimensional Hilbert space and, for a parameter $\mu$, let
  $a(\cdot,\cdot;\mu)$ be a bilinear form on $V_h$ with continuity constant
  $\gamma_h(\mu)=\sup_{v,w\ne0}a(v,w;\mu)/(\|v\|\|w\|)$ and inf-sup constant
  $\beta_h(\mu)=\inf_{v\ne0}\sup_{w\ne0}a(v,w;\mu)/(\|v\|\|w\|)>0$; let
  $u_h(\mu)\in V_h$ solve $a(u_h,v;\mu)=f(v;\mu)$ for all $v\in V_h$. For any
  approximation $u_N(\mu)\in V_h$, for instance a reduced basis Galerkin
  solution, define the residual $r(v;\mu)=f(v;\mu)-a(u_N(\mu),v;\mu)$ and its
  dual norm $\|r(\cdot;\mu)\|_{V_h'}$. Then
  $$\frac{\|r(\cdot;\mu)\|_{V_h'}}{\gamma_h(\mu)}\le\|u_h(\mu)-u_N(\mu)\|
  \le\frac{\|r(\cdot;\mu)\|_{V_h'}}{\beta_h(\mu)} .$$
  Consequently, if $0<\beta^{\mathrm{LB}}(\mu)\le\beta_h(\mu)$ (in the
  coercive case a lower bound of the coercivity constant), the
  **error estimator** $\Delta_N(\mu)=\|r(\cdot;\mu)\|_{V_h'}/
  \beta^{\mathrm{LB}}(\mu)$ satisfies
  $$\|u_h(\mu)-u_N(\mu)\|\le\Delta_N(\mu)
  \le\frac{\gamma_h(\mu)}{\beta^{\mathrm{LB}}(\mu)}\,\|u_h(\mu)-u_N(\mu)\| ,$$
  with effectivity bounded independently of the reduced dimension.

  *Assessment.* Continuity, inf-sup stability and dual norms are ingredients.
  The selected result translates the residual into both a certified
  reduced-basis error bound and an effectivity estimate.

  *Argument.* For the error vector the residual functional is the bilinear
  form with that vector in the first slot. Continuity and the inf-sup bound
  squeeze its dual norm between the corresponding two multiples of the error
  norm. Inserting the certified lower bound for the inf-sup constant gives the
  estimator.

  *Lean target.* Carriers at the pins: `StrongDual`, the operator norm with
  `ContinuousLinearMap.le_opNorm`. No new definition is needed. Conjuncts: (i) the two-sided bound
  by the residual dual norm; (ii) the estimator bound and its effectivity. Pitfall: the continuity
  and inf-sup constants are a supremum and an infimum of ratios; state them as hypotheses
  $\|A\|\le\gamma$ and $\beta\|v\|\le\|Av\|$ to avoid a real `sSup` over an unbounded set. Statable
  and provable at the pins. NASC: `NASC.residual_dualNorm_error_bounds`
  (`NASC/ModelReduction.lean`), proved; it gives (i) with the residual as $Au_h-Au_N$; (ii) is a
  one-line consequence not stated.

* **24.10. Empirical interpolation.** Let $X_M\subset C(\bar\Omega)$ have a
  basis $\rho_1,\dots,\rho_M$ and let $t_1,\dots,t_M\in\bar\Omega$ be such
  that $\rho_i(t_i)=1$, $\rho_j(t_i)=0$ for $i<j$, and
  $\|\rho_j\|_{L^\infty}\le1$; the **empirical interpolation method**,
  which picks each $t_j$ where the current interpolation residual of a
  greedily chosen snapshot attains its maximum modulus and takes $\rho_j$ to
  be that residual normalized at $t_j$, produces such data. Then the matrix
  $B_M=(\rho_j(t_i))_{i,j}$ is unit lower triangular with entries of modulus
  at most $1$, interpolation $I_Mg=\sum_{i=1}^Mg(t_i)\ell_i$ at the points
  $t_i$ in $X_M$ is well defined, the **Lebesgue constant**
  $\Lambda_M=\sup_{x}\sum_{i=1}^M|\ell_i(x)|$ satisfies
  $$\Lambda_M\le2^M-1,$$
  and every $g\in C(\bar\Omega)$ satisfies
  $\|g-I_Mg\|_{L^\infty}\le(1+\Lambda_M)\inf_{g_M\in X_M}\|g-g_M\|_{L^\infty}$.

  *Assessment.* Finite interpolation is available. The empirical greedy
  construction needs to prove existence of each interpolation point and
  control the resulting interpolation operator.

  *Lean target.* Carriers at the pins: `ContinuousMap` with the sup norm on a compact space,
  `Submodule.span`, and the operator norm. New definitions: the interpolation operator and the
  greedy selection. Conjuncts: (i) the greedy procedure yields data with the triangular properties;
  (ii) $B_M$ is unit lower triangular with entries of modulus at most $1$; (iii) the interpolation
  is well defined and $\Lambda_M\le2^M-1$; (iv) the Lebesgue inequality. Pitfall: the Lebesgue
  constant is the operator norm of interpolation on $C(\bar\Omega)$, which avoids a real `sSup`; the
  greedy step needs a nonzero residual, so the procedure stops at the dimension of the snapshot
  span. Statable at the pins. NASC: `NASC.exists_empiricalInterpolator`
  (`NASC/ModelReduction.lean`), sorry; (iii) as an operator-norm bound with reproduction; (i) and
  (iv) are missing.

* **24.11. Balanced truncation.** Let $A\in\mathbb R^{n\times n}$ have all
  eigenvalues in the open left half plane, $B\in\mathbb R^{n\times m}$,
  $C\in\mathbb R^{q\times n}$, with $(A,B)$ controllable and $(A,C)$
  observable, and let $H(s)=C(sI-A)^{-1}B$. The **Gramians** $P$ and $Q$ are
  the symmetric positive definite solutions of
  $$AP+PA^\top+BB^\top=0,\qquad A^\top Q+QA+C^\top C=0 ,$$
  and the **Hankel singular values** $\eta_1\ge\cdots\ge\eta_n>0$ are the
  square roots of the eigenvalues of $PQ$. Write $P=UU^\top$, $Q=LL^\top$,
  $U^\top L=ZSY^\top$ (a singular value decomposition, $S=\mathrm{diag}(\eta_i)$),
  and for $r<n$ with $\eta_r>\eta_{r+1}$ put
  $V=UZ_rS_r^{-1/2}$, $W=LY_rS_r^{-1/2}$, where $Z_r,Y_r$ are the first $r$
  columns and $S_r=\mathrm{diag}(\eta_1,\dots,\eta_r)$. Then $W^\top V=I_r$,
  the reduced system $A_r=W^\top AV$, $B_r=W^\top B$, $C_r=CV$ is
  asymptotically stable, and $H_r(s)=C_r(sI-A_r)^{-1}B_r$ satisfies
  $$\|H-H_r\|_{\mathcal H_\infty}=\sup_{\omega\in\mathbb R}
  \|H(i\omega)-H_r(i\omega)\|_2\le2\,(\eta_{r+1}+\cdots+\eta_n).$$

  *Assessment.* The underlying stable Lyapunov equations and Gramian
  identities are prerequisites. The selected result gives stability and the
  transfer-function error bound of balanced truncation.

  *Lean target.* Carriers at the pins: `spectrum`, `Matrix.PosDef`, `Matrix.diagonal`, and the
  operator $2$-norm from the scoped instances `Matrix.Norms.L2Operator`. Gramians, Lyapunov
  equations and controllability have no carrier at the pin; TauCeti main adds
  `Matrix.IsControllable` and `Matrix.ctrbMatrix`, and the LinearSystemsAndControl roadmap, §4.1 and
  §§5.2–5.3, owns Gramians and Lyapunov equations. New definitions: the transfer function, the
  Gramians and the square-root balancing matrices. Conjuncts: (i) $W^\top V=I_r$; (ii) $A_r$ is
  stable; (iii) the $\mathcal H_\infty$ bound. Pitfall: `Matrix.inv` is $0$ for a singular matrix,
  so $(sI-A)^{-1}$ is meaningful on the imaginary axis only through stability; state (iii) pointwise
  in $\omega$ to avoid a real `iSup`; the default matrix norm is not the operator norm. Statable at
  the pins. NASC: `NASC.stateSpaceTransfer` and `NASC.balancedTruncation_stable_transfer_error`
  (`NASC/ModelReduction.lean`), sorry; (ii) and (iii) for a realization that is already balanced;
  the balancing construction and (i) are missing.

* **24.12. Rational interpolation by projection.** Let
  $H(s,p)=C(p)\bigl(sE(p)-A(p)\bigr)^{-1}B(p)$ with matrix-valued $E,A$
  ($n\times n$), $B$ ($n\times m$), $C$ ($q\times n$), let
  $V,W\in\mathbb C^{n\times r}$, and let
  $H_r(s,p)=C_r(p)(sE_r(p)-A_r(p))^{-1}B_r(p)$ with $E_r=W^\top EV$,
  $A_r=W^\top AV$, $B_r=W^\top B$, $C_r=CV$. Let $\hat s\in\mathbb C$ and
  $\hat p$ be such that $\hat sE(\hat p)-A(\hat p)$ and
  $\hat sE_r(\hat p)-A_r(\hat p)$ are invertible, and let $\hat r\in\mathbb
  C^m$, $\hat\ell\in\mathbb C^q$ be nonzero.
  - If $(\hat sE(\hat p)-A(\hat p))^{-1}B(\hat p)\hat r\in\mathrm{Ran}(V)$,
    then $H(\hat s,\hat p)\hat r=H_r(\hat s,\hat p)\hat r$.
  - If $\bigl(\hat\ell^\top C(\hat p)(\hat sE(\hat p)-A(\hat p))^{-1}\bigr)^\top
    \in\mathrm{Ran}(W)$, then
    $\hat\ell^\top H(\hat s,\hat p)=\hat\ell^\top H_r(\hat s,\hat p)$.
  - If both conditions hold and $E,A,B,C$ are continuously differentiable
    near $\hat p$, then also
    $\hat\ell^\top\partial_sH(\hat s,\hat p)\hat r
    =\hat\ell^\top\partial_sH_r(\hat s,\hat p)\hat r$ and
    $\nabla_p\bigl(\hat\ell^\top H(\hat s,\hat p)\hat r\bigr)
    =\nabla_p\bigl(\hat\ell^\top H_r(\hat s,\hat p)\hat r\bigr)$.

  *Assessment.* The matrix resolvent and rational functions provide
  ingredients. The gap relates inclusion of tangential directions in the trial
  and test spaces to interpolation of the reduced transfer function.

  *Lean target.* Carriers at the pins: `Matrix.det`, `Matrix.inv`, `Matrix.mulVec`, `deriv` and
  `HasFDerivAt`. No new definition is needed. Conjuncts: (i) right tangential interpolation; (ii)
  left tangential interpolation; (iii) Hermite interpolation in $s$ and matching of parameter
  gradients. Pitfall: the projection uses $W^\top$, not the conjugate transpose, and both pencils
  must be invertible as hypotheses because `Matrix.inv` is $0$ otherwise. Statable and provable at
  the pins. NASC: `NASC.projection_transfer_right_interpolation` (`NASC/ModelReduction.lean`, over
  any field), proved; (i) at one point with the pencil fixed; (ii) and (iii) are missing.

### Gaussian measures and random fields

* **24.13. Gaussian measures on Hilbert spaces and the Cameron–Martin
  theorem.** Let $H$ be a separable real Hilbert space. A Borel probability
  measure $\mu$ on $H$ is **Gaussian** if the image of $\mu$ under every
  continuous linear functional is a Gaussian measure on $\mathbb R$,
  possibly a Dirac measure. Such $\mu$ has a mean $m\in H$ and a covariance
  operator $C$ that is self-adjoint, positive semidefinite and of trace class,
  with $\mathrm{tr}\,C=\int\|x-m\|^2\,d\mu(x)$; conversely, for every $m\in H$
  and every such $C$ there is exactly one Gaussian measure $N(m,C)$. By
  **Fernique's theorem** there is $\alpha>0$ with
  $\int\exp(\alpha\|x\|^2)\,d\mu(x)<\infty$. The **Cameron–Martin space** of
  $N(m,C)$ is $E=C^{1/2}H$ with inner product
  $\langle h,k\rangle_C=\langle C^{-1/2}h,C^{-1/2}k\rangle$, where
  $C^{-1/2}h$ is the preimage of $h$ under $C^{1/2}$ in $(\ker C)^\perp$.
  Two Gaussian
  measures on $H$ are either equivalent or mutually singular
  (**Feldman–Hájek**). For $h\in H$, the shifted measure $N(m+h,C)$ is
  equivalent to $N(m,C)$ if and only if $h\in E$ (**Cameron–Martin**), and
  then
  $$\frac{dN(m+h,C)}{dN(m,C)}(x)=\exp\Bigl(\langle h,x-m\rangle_C
  -\tfrac12\|h\|_C^2\Bigr),$$
  where, with $C\varphi_k=\lambda_k\varphi_k$ an orthonormal eigenbasis,
  $\langle h,x-m\rangle_C$ is the $L^2(N(m,C))$-limit of
  $\sum_{k\le n,\ \lambda_k>0}\lambda_k^{-1}\langle h,\varphi_k\rangle
  \langle x-m,\varphi_k\rangle$.

  *Assessment.* Partly covered. Mathlib has Gaussian linear images, Fernique
  integrability and finite-dimensional covariance constructions. The
  trace-class characterization and infinite-dimensional Gaussian equivalence
  and shift assertions are the selected gaps.

  *Scope.* The selected claims concern the trace-class covariance of a
  Hilbert-space Gaussian law and which shifts preserve equivalence of
  measures.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussian`,
  `ProbabilityTheory.covarianceOperator`, `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`,
  `HilbertBasis`, `MeasureTheory.Measure.AbsolutelyContinuous`,
  `MeasureTheory.Measure.MutuallySingular` and `MeasureTheory.Measure.rnDeriv`. Trace-class
  operators and the operator square root have no carrier at the pins; state the trace as a `tsum`
  over a Hilbert basis and the Cameron–Martin space in eigen-coordinates. Conjuncts: (i) the
  covariance of the centred law is positive with finite trace equal to the second moment; (ii)
  existence and uniqueness of $N(m,C)$; (iii) Fernique; (iv) Feldman–Hájek; (v) the shift criterion;
  (vi) the density formula with its $L^2$ limit. Pitfall: `covarianceOperator` is uncentred, so it
  must be applied to the image under $x\mapsto x-m$; the density formula needs the $L^2$ limit as an
  element of `MeasureTheory.Lp`. Statable at the pins. The StochasticCalculus roadmap, §8.1, owns
  the Cameron–Martin space of a Gaussian measure on a Banach space. NASC:
  `NASC.IsGaussian.covariance_trace_eq`, `NASC.IsGaussian.shift_equivalent_iff_squareRoot_range`
  and `NASC.existsUnique_gaussian_of_summable_spectrum` (`NASC/GaussianApproximation.lean`), sorry;
  (i), (v) with the singular alternative, and (ii) for a diagonal covariance; (iv) and (vi) are
  missing.

* **24.14. Karhunen–Loève expansion.** Let $D\subset\mathbb R^d$ be
  measurable and let $u$ be a random field with $u\in L^2(\Omega,L^2(D))$,
  mean $\mu\in L^2(D)$ and covariance
  $c(x,y)=\mathbb E[(u(x)-\mu(x))(u(y)-\mu(y))]$. Then $c\in L^2(D\times D)$,
  and the covariance operator $(\mathcal Cv)(x)=\int_Dc(x,y)v(y)\,dy$ has an
  orthonormal basis of eigenfunctions $\phi_j$ of $L^2(D)$ with eigenvalues
  $\nu_1\ge\nu_2\ge\cdots\ge0$. With
  $\xi_j=\nu_j^{-1/2}\langle u-\mu,\phi_j\rangle_{L^2(D)}$ for $\nu_j>0$,
  $$u(x,\omega)=\mu(x)+\sum_{j:\,\nu_j>0}\sqrt{\nu_j}\,\phi_j(x)\,\xi_j(\omega),$$
  with convergence in $L^2(\Omega,L^2(D))$; the $\xi_j$ have mean $0$ and
  variance $1$ and are pairwise uncorrelated, and if $u$ is Gaussian they are
  independent $N(0,1)$. The truncation $u_J$ after the first $J$ terms has
  $\mathbb E\|u-u_J\|_{L^2(D)}^2=\sum_{j>J}\nu_j$. If $D$ is closed and
  bounded, every nonempty relatively open subset of $D$ has positive measure,
  and $c$ is continuous on $D\times D$, then the $\phi_j$ with
  $\nu_j>0$ are continuous,
  $$\sup_{x,y\in D}\Bigl|c(x,y)-\sum_{j\le J}\nu_j\phi_j(x)\phi_j(y)\Bigr|
  \le\sup_{x\in D}\sum_{j>J}\nu_j\phi_j(x)^2\to0 ,$$
  and $\sup_{x\in D}\mathbb E\bigl[(u(x)-u_J(x))^2\bigr]\to0$ as
  $J\to\infty$.

  *Assessment.* Compact spectral theory and Hilbert-space second moments
  supply ingredients. The missing expansion identifies the orthogonal random
  coefficients and exact truncation error.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.covarianceOperator`, `MeasureTheory.Lp`,
  `MeasureTheory.MemLp`, and `HilbertBasis`. The spectral theorem for compact self-adjoint operators
  in infinite dimension enters as a hypothesis, an eigenbasis of the covariance. Conjuncts: (i)
  $c\in L^2(D\times D)$ and the integral operator is the covariance operator; (ii) the expansion
  converges in $L^2(\Omega,L^2(D))$; (iii) the coefficients are centred, of variance $1$ and
  uncorrelated, and independent standard normal in the Gaussian case; (iv) the truncation error is
  $\sum_{j>J}\nu_j$; (v) Mercer's uniform bound and the pointwise variance convergence for
  continuous $c$ on compact $D$ on which Lebesgue measure has full support (without it,
  $D=[0,1]\cup\{2\}$ and $c=\mathbf 1_{x=y=2}$ give the zero operator and $c(2,2)=1$). Pitfall:
  $\xi_j$ divides by $\sqrt{\nu_j}$, so it is defined only for $\nu_j>0$. Statable at the pins.
  NASC: `NASC.karhunenLoeve_projection_error_sq` (`NASC/GaussianApproximation.lean`), sorry; (iv)
  for a Hilbert-space-valued field and any finite set of modes; (i)–(iii) and (v) are missing.

* **24.16. Stochastic Galerkin method.** Let $(\Theta,\mathcal F,P)$ be a
  probability space, $\mathcal U$ a real Hilbert space, and $A(\theta)$ a
  measurable family of bilinear forms on $\mathcal U$ with constants
  $0<c_*\le C^*<\infty$ independent of $\theta$:
  $|A(\theta)(v,w)|\le C^*\|v\|\|w\|$ and $A(\theta)(v,v)\ge c_*\|v\|^2$.
  On $\mathcal H=L^2(\Theta,P;\mathcal U)$ put
  $\alpha(X,Y)=\mathbb E[A(X,Y)]$ and $\beta(Y)=\mathbb E[\langle F,Y\rangle]$
  for given $F\in L^2(\Theta,P;\mathcal U')$. Then $\alpha$ is bounded with
  constant $C^*$ and coercive with constant $c_*$ on $\mathcal H$, so there
  is a unique $X\in\mathcal H$ with $\alpha(X,Y)=\beta(Y)$ for all
  $Y\in\mathcal H$. For every closed subspace $\mathcal H_N\subset\mathcal H$,
  for instance a finite element space tensored with polynomials in finitely
  many random variables, the **stochastic Galerkin** solution
  $X_N\in\mathcal H_N$ with $\alpha(X_N,Y)=\beta(Y)$ for all
  $Y\in\mathcal H_N$ exists, is unique, and satisfies
  $$\|X-X_N\|_{\mathcal H}\le\frac{C^*}{c_*}\inf_{Y\in\mathcal H_N}
  \|X-Y\|_{\mathcal H} ;$$
  if every $A(\theta)$ is symmetric, $X_N$ is the best approximation from
  $\mathcal H_N$ in the energy norm $\alpha(Y,Y)^{1/2}$.

  *Assessment.* Coercive Lax–Milgram theory already supplies the full
  problem's variational framework. The selected result covers the
  approximation in the tensor-product trial space and its energy-error
  statement.

  *Lean target.* Carriers at the pins: `IsCoercive.continuousLinearEquivOfBilin`, `MeasureTheory.Lp`
  for $L^2(\Theta,P;\mathcal U)$ and its dual, and `MeasureTheory.AEStronglyMeasurable`. No new
  definition is needed. Conjuncts: (i) $\alpha$ is bounded and coercive; (ii) existence and
  uniqueness on $\mathcal H$ and on every closed subspace; (iii) the Céa bound $C^*/c_*$; (iv) best
  approximation in the energy norm for symmetric forms. Pitfall: the Bochner integral of a
  non-integrable function is $0$, so integrability of $\theta\mapsto A(\theta)(X,Y)$ must be proved
  from the bounds before $\alpha$ is used. Statable and provable at the pins. NASC:
  `NASC.existsUnique_stochasticGalerkin` (`NASC/GaussianApproximation.lean`), sorry; (ii) only.

### Neural network approximation

* **24.17. Approximation rates of deep ReLU networks.** Let
  $\sigma(t)=\max(t,0)$. For $W,L\in\mathbb N$ let
  $\Upsilon^{W,L}(d)$ be the set of functions $\mathbb R^d\to\mathbb R$ of the
  form $x\mapsto W^{(L+1)}X^{(L)}+b^{(L+1)}$ with $X^{(0)}=x$ and
  $X^{(\ell)}=\sigma(W^{(\ell)}X^{(\ell-1)}+b^{(\ell)})$ for
  $\ell=1,\dots,L$, where $\sigma$ acts componentwise and all hidden layers
  have width $W$ (networks of **width** $W$ and **depth** $L$). For a set
  $K$ and approximants $\Sigma$ in a normed space $X$ write
  $E(K,\Sigma)_X=\sup_{f\in K}\inf_{S\in\Sigma}\|f-S\|_X$.
  - Let $K$ be the unit ball of $\mathrm{Lip}\,1$ on $[0,1]$, normed by
    $\|f\|_{C[0,1]}+\sup_{x\ne y}|f(x)-f(y)|/|x-y|$. For every even
    $n\in\mathbb N$,
    $$E\bigl(K,\Upsilon^{11,16n+2}(1)\bigr)_{C[0,1]}\le6\,n^{-2},$$
    twice the exponent of piecewise linear approximation with $O(n)$
    parameters. For fixed $W_0$ and $C$ there is $c_0>0$ with
    $E(K,\Upsilon^{W_0,Cn}(1))_{C[0,1]}\ge c_0n^{-2}$ for all $n$.
  - Let $\Omega=[0,1]^d$, $1\le p\le\infty$, $0<q,\tau\le\infty$, $s>0$, and
    let $K$ be the unit ball of the Besov space $B^s_q(L^\tau(\Omega))$ with
    $\delta:=s-d/\tau+d/p>0$. There is $C=C(s,d,\delta)$ such that, with
    $\beta=\max\{1,2d/(s-\delta)\}$ and $m_n=\lceil n(\log_2n)^\beta\rceil$,
    $$E\bigl(K,\Upsilon^{6d,\,Cm_n}(d)\bigr)_{L^p(\Omega)}\le
    C\,n^{-s/d}\qquad(n\ge2).$$

  *Assessment.* TauCeti has ReLU activation and network maps. The missing
  quantitative theorem gives the explicit depth, width and approximation-error
  dependence on the smoothness class.

  *Lean target.* Carriers at the pins: TauCeti's `TauCeti.Neuromanifold.MLPSpec` with
  `TauCeti.Neuromanifold.MLPSpec.evalPrefix`, which applies the identity on the output layer, and
  `TauCeti.Neuromanifold.reluActivation`. Besov spaces have no carrier at the pins. New definitions:
  the network class $\Upsilon^{W,L}(d)$ and the worst-case approximation error. Conjuncts: (i) the
  upper bound $6n^{-2}$ for even $n$; (ii) the lower bound $c_0n^{-2}$ for fixed width and linear
  depth; (iii) the Besov rate. Pitfall: the error over a unit ball is a supremum, which must be
  bounded or taken in `ℝ≥0∞`; the Lipschitz ball uses the sum of sup norm and Lipschitz constant;
  (ii) needs a bound on the number of linear pieces, which no library has. Statable at the pins for
  (i) and (ii); (iii) waits for Besov spaces. NASC: `NASC.reluScalarSpec`, `NASC.reluScalarEval` and
  `NASC.exists_reluScalarEval_error_le` (`NASC/NeuralApproximation.lean`), sorry; only (i), in the
  sup–inf form (error at most $6/n^2+\varepsilon$ for every $\varepsilon>0$, attainment not
  asserted).
