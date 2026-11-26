# Principal gaps in numerical analysis and scientific computing

The [mathematical synopsis](SYNOPSIS.md) gives 396 numbered entries in 24
sections and a [guide to their sources](SYNOPSIS.md#reference-guide). The
[coverage inventory](STRUCTURE.md) records the relevant Mathlib and TauCeti
declarations and the hypotheses at which they apply. The
[bibliography](NASC-bib.md) gives the full source details.

This catalogue selects **277 principal statements and theorem families**
across the 24 sections. Of these, **235** have no matching proved
result identified in the two libraries and **42** have partial coverage at
the level of the synopsis entry. The selection emphasizes the main numerical
methods, the estimates that explain their behavior, and results on which
other numerical guarantees depend. Counts refer to numbered entries. A
single entry may contain several related conclusions.

Identifiers and cross-references retain their synopsis meaning. For
example, **5.18** is statement 18 of section 5. Statements carry enough
context to identify the numerical problem and its hypotheses. Follow the
section links for background results cited by number. Each *Assessment*
describes the missing mathematical content and its relation to known
results. The **50** *Scope* notes identify the selected part of a
broader synopsis entry. The **13** *Argument* notes sketch comparatively
short derivations from the cited facts or other selected results.

The short derivations are **2.1**, **2.13**, **4.6**, **5.1**, **5.18**,
**7.11**, **13.1**, **13.2**, **13.3**, **16.4**, **19.18**, **21.16**,
**24.9**.

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
- [2. Conditioning and matrix perturbation theory](#2-conditioning-and-matrix-perturbation-theory) — 12 selected.
- [3. Direct methods for linear systems and least squares](#3-direct-methods-for-linear-systems-and-least-squares) — 10 selected.
- [4. Eigenvalue and singular value computations](#4-eigenvalue-and-singular-value-computations) — 13 selected.
- [5. Iterative methods for linear systems](#5-iterative-methods-for-linear-systems) — 12 selected.
- [6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation](#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation) — 12 selected.
- [7. Interval arithmetic and verified computation](#7-interval-arithmetic-and-verified-computation) — 10 selected.
- [8. Nonlinear equations, continuation, and algorithmic differentiation](#8-nonlinear-equations-continuation-and-algorithmic-differentiation) — 10 selected.
- [9. Numerical optimization](#9-numerical-optimization) — 10 selected.
- [10. Polynomial and rational approximation](#10-polynomial-and-rational-approximation) — 12 selected.
- [11. Splines, kernels and wavelets](#11-splines-kernels-and-wavelets) — 12 selected.
- [12. Orthogonal polynomials and numerical quadrature](#12-orthogonal-polynomials-and-numerical-quadrature) — 10 selected.
- [13. Discrete Fourier analysis and sparse recovery](#13-discrete-fourier-analysis-and-sparse-recovery) — 12 selected.
- [14. Initial value problems: one-step and multistep methods](#14-initial-value-problems-one-step-and-multistep-methods) — 11 selected.
- [15. Stiff problems, differential-algebraic equations, and geometric integration](#15-stiff-problems-differential-algebraic-equations-and-geometric-integration) — 10 selected.
- [16. Finite difference methods for differential equations](#16-finite-difference-methods-for-differential-equations) — 10 selected.
- [17. Hyperbolic conservation laws and finite volume methods](#17-hyperbolic-conservation-laws-and-finite-volume-methods) — 10 selected.
- [18. Galerkin and finite element methods for elliptic problems](#18-galerkin-and-finite-element-methods-for-elliptic-problems) — 17 selected.
- [19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation](#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation) — 13 selected.
- [20. Multilevel and domain decomposition methods](#20-multilevel-and-domain-decomposition-methods) — 10 selected.
- [21. Integral equations and boundary element methods](#21-integral-equations-and-boundary-element-methods) — 13 selected.
- [22. Inverse problems and regularization](#22-inverse-problems-and-regularization) — 12 selected.
- [23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations](#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations) — 12 selected.
- [24. High-dimensional approximation, uncertainty quantification, and model reduction](#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction) — 13 selected.

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

* **1.6. Sterbenz lemma.** If $x,y\in\mathbb F$ satisfy $y/2\le x\le2y$, then
  $x-y\in\mathbb F$; hence $\circ(x-y)=x-y$ for every rounding function.

  *Assessment.* Exact subtraction of nearby numbers is specific to the format
  with its subnormal range. Integer divisibility and the exponent bounds give
  a route to the representability result.

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

* **1.12. Compensated summation.** Let $x_1,\dots,x_n\in\mathbb F$ and
  $S_n=\sum_ix_i$.
  - **Kahan's compensated summation** ($s=e=0$; for $i=1,\dots,n$:
    $t=s$, $y=x_i+e$, $s=t+y$, $e=(t-s)+y$, each operation rounded) satisfies,
    under the standard model,
    $$\widehat S_n=\sum_{i=1}^n(1+\mu_i)x_i,\qquad
    |\mu_i|\le2u+O(nu^2),$$
    with an implied constant independent of $n$, $u$ and the data. So
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

* **2.5. Normwise backward error (Rigal–Gaches).** Let $A\in\mathbb
  R^{n\times n}$, $b,y\in\mathbb R^n$, $E\in\mathbb R^{n\times n}$ and
  $f\in\mathbb R^n$ with $\|E\|\,\|y\|+\|f\|>0$, and put $r=b-Ay$. Then
  $$\eta_{E,f}(y):=\min\{\varepsilon:(A+\Delta A)y=b+\Delta b,\
  \|\Delta A\|\le\varepsilon\|E\|,\ \|\Delta b\|\le\varepsilon\|f\|\}
  =\frac{\|r\|}{\|E\|\,\|y\|+\|f\|}.$$

  *Assessment.* The result identifies a computable residual quotient with a
  minimum over perturbations. A rank-one norming construction realizes the
  bound.

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
  $0<\eta<1$, $A=\begin{pmatrix}1&0\\0&\eta\\0&0\end{pmatrix}$,
  $b=(1,0,1)^\top$, $\Delta b=0$ and $\Delta A=\eta\,e_3e_2^\top$, one has
  $\kappa_2(A)=1/\eta$, $\|\Delta A\|_2=\eta\|A\|_2$, $x=(1,0)^\top$,
  $y=(1,1/(2\eta))^\top$, so $\|x-y\|_2/\|x\|_2=1/(2\eta)
  =\tfrac12\kappa_2(A)^2\|\Delta A\|_2/\|A\|_2$.

  *Assessment.* Finite-dimensional orthogonal projection and singular values
  support the linearization. The coefficient and residual perturbations and
  their dependence on the least-squares geometry remain to be formalized.

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

* **3.3. Backward error of LU factorization.** Let $A\in\mathbb R^{m\times n}$
  with $m\ge n$ and $nu<1$. If Gaussian elimination runs to completion on $A$,
  the computed factors $\widehat L\in\mathbb R^{m\times n}$ and
  $\widehat U\in\mathbb R^{n\times n}$ satisfy
  $$\widehat L\widehat U=A+\Delta A,\qquad
  |\Delta A|\le\gamma_n|\widehat L||\widehat U| .$$
  If $m=n$ and the systems $\widehat Ly=b$ and $\widehat Ux=y$ are then solved
  by substitution, the computed solution $\widehat x$ of $Ax=b$ satisfies
  $$(A+\Delta A)\widehat x=b,\qquad |\Delta A|\le2\gamma_n|\widehat L||\widehat U| .$$
  If in addition $\widehat L\ge0$ and $\widehat U\ge0$ entrywise and
  $nu<\tfrac12$, then $|\widehat L||\widehat U|\le(1-\gamma_n)^{-1}|A|$, so that
  $|\Delta A|\le2\gamma_n(1-\gamma_n)^{-1}|A|$. With pivoting, these bounds
  hold with $A$ replaced by the permuted matrix $PA$ (or $PAQ$) that is
  eliminated without interchanges.

  *Assessment.* The factorization and substitution identities must be joined
  with the scalar rounding model. This gives separate certificates for the
  computed factors and for the computed solution.

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

### Cholesky and QR factorization

* **3.8. Backward stability of Cholesky factorization.** Let
  $A\in\mathbb R^{n\times n}$ be symmetric positive definite and
  $(n+1)u<1$.
  - If the Cholesky factorization runs to completion (every square root has
    a positive argument), the computed factor satisfies
    $$\widehat R^\top\widehat R=A+\Delta A,\qquad
    |\Delta A|\le\gamma_{n+1}|\widehat R^\top||\widehat R| ,$$
    and the computed solution of $Ax=b$ by the two triangular solves
    satisfies $(A+\Delta A)\widehat x=b$ with $|\Delta A|\le2\gamma_{n+1}
    |\widehat R^\top||\widehat R|$. If also $n\gamma_{n+1}<1$, this
    $\Delta A$ satisfies
    $$\|\Delta A\|_2\le2n\gamma_{n+1}(1-n\gamma_{n+1})^{-1}\|A\|_2 .$$
  - Write $A=DHD$ with $D=\mathop{\mathrm{diag}}(A)^{1/2}$, so that $H$ has
    unit diagonal. If $\lambda_{\min}(H)>n\gamma_{n+1}/(1-\gamma_{n+1})$,
    the Cholesky factorization runs to completion and gives a nonsingular
    $\widehat R$. If $\lambda_{\min}(H)\le-n\gamma_{n+1}/(1-\gamma_{n+1})$,
    it fails.

  *Assessment.* TauCeti constructs the exact Cholesky factor. The rounded
  recursion must account for breakdown and establish the componentwise
  backward error upon completion.

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

## 4. Eigenvalue and singular value computations

[Synopsis](SYNOPSIS.md#4-eigenvalue-and-singular-value-computations) · [Coverage inventory](STRUCTURE.md#4-eigenvalue-and-singular-value-computations)

Hermitian spectral decomposition, singular-value theory and compression
interlacing provide the analytic framework. The selected statements concern
normal forms beyond that framework, actual iterations, and the nonlinear
eigenvalue problem.

A matrix $H=(h_{ij})$ is **upper Hessenberg** if $h_{ij}=0$ for $i>j+1$, and
an upper Hessenberg matrix is **unreduced** if $h_{i+1,i}\ne0$ for all $i$.
A **phase matrix** is a diagonal unitary matrix. For a matrix that need not
be Hermitian, an ordering of its eigenvalues is stated where it is used.
Statements on rounding errors use the standard model 1.5; there
$O(u)$ means a quantity bounded by $c_n u$ for all sufficiently small $u$,
with $c_n$ depending only on the dimension.

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

  *Assessment.* The existing Hermitian diagonalization treats a special normal
  class. General Schur forms require unitary triangularization with chosen
  eigenvalue order and real invariant blocks of dimension one or two.

* **4.3. Singular value decomposition.** For every
  $A\in\mathbb C^{m\times n}$, with $p=\min\{m,n\}$, there are unitary
  $U\in\mathbb C^{m\times m}$ and $V\in\mathbb C^{n\times n}$ such that
  $$U^*AV=\Sigma=\mathrm{diag}(\sigma_1,\dots,\sigma_p)\in\mathbb R^{m\times n},
  \qquad \sigma_1\ge\cdots\ge\sigma_p\ge0 .$$
  If $A$ is real, $U$ and $V$ can be taken real orthogonal.

  *Assessment.* Partly covered. Mathlib supplies ordered singular values and
  the rank identity, and TauCeti supplies square unitary SVD and rectangular
  rank-one expansions. The selected assertion is the rectangular full
  factorization in orthonormal coordinates.

  *Scope.* The target is the explicit rectangular factorization with ordered
  diagonal, including real orthogonal factors for real input.

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
    eigenvectors $q_j$, and suppose there are indices $J\ne K$ with
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

  *Assessment.* The QR factorization API gives one factorization at a time.
  The gap is the identity between the sequence of QR similarities, the
  factorizations of matrix powers and simultaneous iteration.

  *Argument.* Iterating the similarity formula gives $A_{i+1}=P_i^*AP_i$. Also
  $AP_{i-1}=P_{i-1}A_i=P_iR_i$. Apply this identity inductively to $A^i$ and
  use uniqueness of the positive-diagonal QR factorization to identify the
  simultaneous iterates.

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

* **4.8. Hessenberg form and the shifted QR step.** For every
  $A\in\mathbb C^{n\times n}$ there is a unitary $Q$, a product of $n-2$
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
  $a^{(i)}_{n,n-1}\to0$, at least quadratically, so that $a^{(i)}_{nn}$
  converges to an eigenvalue of $A$.

  *Assessment.* Mathlib has algebraic Hessenberg similarity certificates. The
  selected result requires unitary reduction and preservation of Hessenberg
  form in the shifted QR step.

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
    $Aq_j=\beta_{j-1}q_{j-1}+\alpha_jq_j+\beta_jq_{j+1}$ with $\alpha_j$,
    $\beta_j$ real.

  *Assessment.* Inner products and orthogonal bases are available. The Arnoldi
  relation requires the generated Krylov basis, the residual coefficient, and
  the tridiagonal specialization for Hermitian inputs.

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

  *Assessment.* Compression interlacing is available. The stronger Ritz-value
  rate needs a Krylov polynomial extremal estimate that also accounts for the
  starting vector's angle.

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

  *Assessment.* SVD and the adjoint are ingredients. The coupled
  bidiagonalization recurrence must preserve orthogonality and give both
  matrix relations with the terminal residual.

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
  analytic ingredients. The missing result identifies the pole terms and their
  coefficients with the normalized left and right Jordan chains of the matrix
  function.

* **4.19. Companion linearization.** Let
  $P(z)=\sum_{j=0}^{\ell}z^jD_j$ with $D_j\in\mathbb C^{n\times n}$ and
  $\ell\ge1$, and let $L(z)\in\mathbb C^{\ell n\times\ell n}$ be the pencil
  with first block row $(D_0,D_1,\dots,D_{\ell-2},D_{\ell-1}+zD_\ell)$ (for
  $\ell=1$ the sole block is $D_0+zD_1$) and,
  for $2\le j\le\ell$, block row $j$ equal to $-zI_n$ in block column $j-1$,
  $I_n$ in block column $j$, and $0$ elsewhere. With
  $b(z)=(1,z,\dots,z^{\ell-1})^\top$,
  $$L(z)\bigl(b(z)\otimes v\bigr)=e_1\otimes P(z)v,\qquad
  \det L(z)=\det P(z)$$
  for all $z\in\mathbb C$ and $v\in\mathbb C^n$. Hence
  $\ker L(\lambda)=\{b(\lambda)\otimes v:v\in\ker P(\lambda)\}$ for every
  $\lambda$. The pencil $L$ is regular exactly when $P$ is.

  *Assessment.* Partly covered. TauCeti treats scalar polynomial companion
  pencils. The selected block-coefficient version identifies the determinant,
  right kernel, algebraic multiplicities and the left-vector correspondence.

  *Scope.* The target is the block-polynomial pencil identity, its determinant
  and the correspondence of eigenvectors for finite eigenvalues.

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

### Stationary iterations

* **5.1. Convergent matrices and splitting iterations.** Let $A=M-N$ be a splitting of the
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

* **5.9. Ostrowski–Reich theorem.** Let $A=D-E-E^*$ be Hermitian, with $D$
  Hermitian positive definite. For $0<\omega<2$ with $D-\omega E$
  nonsingular, the matrix
  $\mathcal L_\omega=(D-\omega E)^{-1}\bigl(\omega E^*+(1-\omega)D\bigr)$
  satisfies $\rho(\mathcal L_\omega)<1$ if and only if $A$ is positive
  definite. For Hermitian positive definite $A$ with $D$
  its diagonal and $-E$ its strictly lower part, point SOR converges for every
  starting vector if and only if $0<\omega<2$, and the same holds for block SOR
  with $D$ the block diagonal. For the Jacobi iteration with $A$ Hermitian and
  $D$ its diagonal: if $A$ and $2D-A$ are both positive definite, then
  $\rho(B_J)=\|B_J\|_A<1$, where $\|x\|_A=(x^*Ax)^{1/2}$.

  *Assessment.* The energy inner product is available for a positive definite
  matrix. SOR convergence and the necessity of the relaxation interval require
  the splitting identities and both directions of the stability analysis.

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

  *Assessment.* Mathlib has extremal Chebyshev polynomial results. The
  constrained value at a point outside the spectral interval, the exact
  iteration polynomial and the convergence factor are the target.

### Krylov subspace methods

* **5.12. Conjugate gradients: optimality and finite termination.** Let $A$ be
  Hermitian positive definite, $x^*=A^{-1}b$, $\|v\|_A=(v^*Av)^{1/2}$, and
  $r_0=b-Ax_0$. The **conjugate gradient (CG) method** sets $p_0=r_0$ and, for
  $k\ge0$ while $r_k\ne0$,
  $$\alpha_k=\frac{r_k^*r_k}{p_k^*Ap_k},\quad x_{k+1}=x_k+\alpha_kp_k,\quad
  r_{k+1}=r_k-\alpha_kAp_k,\quad
  p_{k+1}=r_{k+1}+\frac{r_{k+1}^*r_{k+1}}{r_k^*r_k}\,p_k.$$
  As long as $r_{k-1}\ne0$, no division by zero occurs, $r_k=b-Ax_k$,
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

* **5.13. Conjugate gradients: condition-number bound.** With $A$ Hermitian
  positive definite and $\kappa=\kappa_2(A)=\lambda_{\max}(A)/\lambda_{\min}(A)$,
  the CG iterates satisfy, for every $k\ge0$,
  $$\|x_k-x^*\|_A\le
  \frac{2c^k}{1+c^{2k}}\,\|x_0-x^*\|_A\le2c^k\|x_0-x^*\|_A,\qquad
  c=\frac{\sqrt\kappa-1}{\sqrt\kappa+1}.$$
  At $k=0$ take $c^0=1$. After exact termination the iterate is $x^*$.

  *Assessment.* The spectral theorem and Chebyshev inequalities are available.
  The selected conclusion is the exact arithmetic error factor of the CG
  iterates in the energy norm.

* **5.14. GMRES.** For $A$ nonsingular, the $k$-th **GMRES** iterate $x_k$ is the
  minimizer of $\|b-Ax\|_2$ over $x\in x_0+\mathcal K_k(A,r_0)$; its residual
  $r_k=b-Ax_k$ satisfies $\|r_{k+1}\|_2\le\|r_k\|_2$ and
  $$\|r_k\|_2=\min_{p\in\mathcal P_k^0}\|p(A)r_0\|_2.$$
  If $A=V\Lambda V^{-1}$ is diagonalizable, then
  $$\|r_k\|_2\le\kappa_2(V)\left(\min_{p\in\mathcal P_k^0}
  \max_{\lambda\in\Lambda(A)}|p(\lambda)|\right)\|r_0\|_2.$$

  *Assessment.* Hilbert projection supports residual minimization. The theorem
  identifies the reachable residual polynomials and gives the
  diagonalizable-matrix bound for the actual minimizers.

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
  Hermitian case, and TauCeti has Hermite interpolation. The primary matrix
  function needs the equality of the Jordan and polynomial constructions,
  including repeated eigenvalues.

  *Scope.* The target is the primary matrix function for general Jordan
  structure and its equivalence with the Hermite interpolant.

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

  *Assessment.* Partly covered. The normed-algebra exponential is a convergent
  power series. General Jordan-block boundary convergence and the holomorphic
  contour representation are the targets.

  *Scope.* The selected claims concern the Jordan-size criterion on the circle
  of convergence and the Cauchy representation for general matrices.

* **6.4. Fréchet derivative and condition number.** Let $f$ map an open
  subset of $\mathbb C^{n\times n}$ into $\mathbb C^{n\times n}$. Its
  **Fréchet derivative** at $A$ is the linear map $L_f(A):E\mapsto
  L_f(A,E)$ with $f(A+E)-f(A)-L_f(A,E)=o(\|E\|)$.
  - For a scalar $f$ holomorphic on an open set containing $\Lambda(A)$,
    the corresponding primary matrix function is Fréchet differentiable and
    $$f\begin{pmatrix}A&E\\0&A\end{pmatrix}=
    \begin{pmatrix}f(A)&L_f(A,E)\\0&f(A)\end{pmatrix}.$$
  - With $\|L_f(A)\|=\max_{\|Z\|=1}\|L_f(A,Z)\|$ for a given matrix norm,
    and $f(A)\ne0$, the relative **condition number**
    $$\mathrm{cond}(f,A)=\lim_{\varepsilon\to0}\ \sup_{\|E\|\le\varepsilon\|A\|}
    \frac{\|f(A+E)-f(A)\|}{\varepsilon\|f(A)\|}$$
    equals $\|L_f(A)\|\,\|A\|/\|f(A)\|$.
  - If $f(x)=\sum_{k\ge0}a_kx^k$ has radius of convergence $r$ and
    $\|A\|<r$ for a submultiplicative norm, then
    $$L_f(A,E)=\sum_{k\ge1}a_k\sum_{j=1}^kA^{j-1}EA^{k-j}.$$

  *Assessment.* Partly covered. TauCeti proves the exponential insertion
  formula and block identities. The selected Fréchet derivative and
  conditioning statements concern a general primary matrix function.

  *Scope.* The selected block identity uses a scalar function holomorphic near
  the spectrum. The derivative, condition number and differentiated series
  concern the resulting primary matrix function.

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

  *Assessment.* Partly covered. TauCeti gives disjoint-spectrum uniqueness and
  self-adjoint solvability results. The gap comprises the spectrum of the
  general Sylvester map and the contour and half-line representations.

  *Scope.* The selected claims are the spectrum of the general Sylvester map
  and the contour and half-line representations under their stated spectral
  hypotheses.

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

### Low-rank and randomized approximation

* **6.8. Schmidt–Eckart–Young–Mirsky theorem.** Let $A\in\mathbb K^{m\times
  n}$ have the singular value decomposition $A=\sum_{j=1}^p\sigma_ju_jv_j^*$,
  $p=\min\{m,n\}$, and put $\sigma_{p+1}=0$. For $0\le k\le p$ let
  $A_k=\sum_{j=1}^k\sigma_ju_jv_j^*$. Then
  $$\min_{\mathrm{rank}\,B\le k}\|A-B\|_F=\|A-A_k\|_F
  =\Bigl(\sum_{j=k+1}^p\sigma_j^2\Bigr)^{1/2}.$$

  *Assessment.* Partly covered. TauCeti identifies approximation numbers with
  singular values and supplies operator-norm attainment. The minimum and
  attaining truncation in Frobenius norm are the selected gap.

  *Scope.* The selected claim is the Frobenius-norm optimum and its attaining
  truncated singular value decomposition.

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

  *Assessment.* Projection, SVD and finite-dimensional Gaussian measures are
  available. The gap combines deterministic block estimates with the
  independence and pseudoinverse estimates used for Gaussian tests.

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
  for the random projection. Uniform control over a set or subspace requires
  the Gaussian width comparison and both singular-direction bounds.

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

* **6.14. Tensor trains.** For $\rho=(\rho_1,\dots,\rho_{d-1})\in\mathbb
  N^{d-1}$ and $\rho_0=\rho_d=1$, the **tensor train** set $\mathcal
  T_\rho$ consists of the $v\in\mathbb K^{n_1\times\cdots\times n_d}$ with
  $$v[i_1,\dots,i_d]=G_1[i_1]\,G_2[i_2]\cdots G_d[i_d],\qquad
  G_j[i_j]\in\mathbb K^{\rho_{j-1}\times\rho_j}.$$
  - $v\in\mathcal T_\rho$ implies $\rho_j\ge\rho_j^*:=\mathrm{rank}\,
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

  *Assessment.* Schmidt ranks of unfoldings and finite tensors supply
  ingredients. The missing results identify simultaneous representable ranks
  and control the approximation produced by successive truncations.

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

  *Assessment.* The approximation machinery provides polynomial interpolation
  and finite-rank maps. The gap connects the derivative bounds and
  admissibility geometry to quantitative separated kernel approximations.

## 7. Interval arithmetic and verified computation

[Synopsis](SYNOPSIS.md#7-interval-arithmetic-and-verified-computation) · [Coverage inventory](STRUCTURE.md#7-interval-arithmetic-and-verified-computation)

Mathlib's dyadic inclusion machinery provides a model for local enclosure
certificates. These gaps link real interval semantics and outward rounding to
validated numerical conclusions.

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

  *Assessment.* Partly covered. Order intervals and elementary interval
  arithmetic are available in Mathlib. The selected formulation characterizes
  the exact range of the real operation by the endpoint rule, including
  products across zero and admissible quotients.

  *Scope.* The target is the exact range of each real interval operation, with
  division defined under the stated exclusion of zero from the divisor
  interval.

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

  *Assessment.* The tactic inclusion API has operation-specific certificates.
  The selected theorem concerns arbitrary expressions and their natural
  extension, including repeated occurrences of variables.

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
  - $X\circledcirc Y$ is the smallest element of $\mathbb{IF}$ containing
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

  *Assessment.* Dyadic enclosures provide implementation ingredients. The gap
  is the statement that evaluating interval operations with outward-directed
  rounding preserves their real range inclusions.

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

  *Assessment.* The exact interval API and differentiability theory are
  ingredients. The quantitative result distinguishes the width of the computed
  interval from the width of the true range, both for the natural extension
  and for the mean-value construction.

### Nonlinear systems

* **7.8. Univariate interval Newton operator.** Let $X=[a,b]\in\mathbb{IR}$,
  let $f:X\to\mathbb R$ be continuously differentiable, let
  $\tilde x\in X$, and let $D\in\mathbb{IR}$ satisfy $f'(x)\in D$ for all
  $x\in X$ and $0\notin D$. Put
  $N(\tilde x,X)=\tilde x-f(\tilde x)/D$, computed by interval operations.
  - Every zero of $f$ in $X$ lies in $N(\tilde x,X)$.
  - If $N(\tilde x,X)\subseteq X$, then $f$ has exactly one zero in $X$.
  - If $N(\tilde x,X)\cap X=\emptyset$, then $f$ has no zero in $X$.

  *Assessment.* Mathlib has a scalar mean value theorem. The interval Newton
  assertion uses derivative enclosure to retain every root and, under the
  stated interior condition, to certify existence and uniqueness.

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

  *Assessment.* The vector mean-value integral can be built from the available
  calculus API. Its enclosure in an interval matrix and the resulting
  localization of zeros are the numerical targets.

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

  *Assessment.* A contraction theorem and Brouwer-type fixed-point machinery
  supply analytic ingredients. The Krawczyk result needs a validated Jacobian
  interval, its fixed-point enclosure, and the separate uniqueness condition.

### Linear systems

* **7.11. Norm-based verification for linear systems.** Let
  $A,R\in\mathbb R^{n\times n}$ and $b,\tilde x\in\mathbb R^n$.
  If $\|I-RA\|<1$ for a matrix norm induced by a vector norm $\|\cdot\|$,
  then $A$ and $R$ are nonsingular and
  $$\|A^{-1}b-\tilde x\|\le\frac{\|R(b-A\tilde x)\|}{1-\|I-RA\|}.$$

  *Assessment.* Partly covered. The spectral-radius condition gives
  invertibility at the Banach-algebra level. The residual-to-solution estimate
  is the selected conclusion.

  *Scope.* The selected certificate uses the computable residual and the
  induced-norm defect of the approximate inverse.

  *Argument.* Write $G=I-RA$. The Neumann series gives $\|(I-G)^{-1}\|\le
  (1-\|G\|)^{-1}$. Apply $(I-G)^{-1}$ to the preconditioned residual equation
  $(I-G)(A^{-1}b-\tilde x)=R(b-A\tilde x)$.

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

  *Assessment.* The gap couples interval interior inclusion with a strict
  spectral bound and a simultaneous enclosure of all the permitted linear
  systems.

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
  G(\|v\|_{\mathcal X})$ for all $v$, with a nondecreasing $G$ satisfying
  $G(t)=o(t)$ as $t\to0$.

  *Assessment.* TauCeti supplies coercive weak elliptic solvability and
  compactness ingredients. The verified theorem must relate the residual and
  inverse bounds at an approximate solution to a ball containing an exact
  solution.

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
  interval. The midpoint recursion and its invariant identify a nested
  enclosure with a geometric length bound.

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
  identity. The changing pair of points and its asymptotic ratio require a
  secant-specific argument.

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
    $\|x^k-x^*\|<\rho$ for $k\ge1$, converge to $x^*$, and
    $$\|x^{k+1}-x^*\|\le\frac\omega2\|x^k-x^*\|^2,\qquad k\ge0.$$
    Moreover $x^*$ is the only zero of $F$ in $D\cap B(x^*,2/\omega)$.

  *Assessment.* An inverse perturbation bound and Taylor estimates are
  available. The local theorem must keep every Newton iterate in the
  neighborhood, control the inverse derivative there and prove quadratic
  convergence.

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

  *Assessment.* The Banach fixed-point theorem is already available. The main
  gap is the majorant iteration giving a computable radius, convergence and a
  uniqueness enclosure.

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

  *Assessment.* The calculus inequalities and linear solves are available as
  ingredients. The proof must relate the step acceptance rule to descent and
  to convergence under the stated bounds on the level set.

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

  *Assessment.* The exact Newton local estimates support the analysis. The
  selected theorem adds residual forcing terms and distinguishes linear,
  superlinear and quadratic convergence by their decay.

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
  $B(x^*,\rho)\subset D$. Then the iterates satisfy $\|x^k-x^*\|<\rho$ for
  $k\ge1$, converge to $x^*$, and
  $$\|x^{k+1}-x^*\|\le\frac\omega2\|x^k-x^*\|^2+\kappa_*\|x^k-x^*\|.$$
  In particular the convergence is quadratic if $F(x^*)=0$ (a compatible
  problem), where one may take $\kappa_*=0$. The point $x^*$ is the only
  $x\in D\cap B(x^*,\sigma)$ with $F'(x)^+F(x)=0$.

  *Assessment.* The finite-dimensional adjoint and normal equations underlie
  the updates. The rate and its dependence on the limiting residual require
  the least-squares-specific linearization.

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

  *Assessment.* Mathlib's implicit function theorem provides a local solution
  graph. The numerical content is the predictor error, the corrector's
  convergence and the continuation along successive local charts.

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
  - for $\dot X\in\mathbb R^{n\times p}$ propagated simultaneously,
    $\mathrm{TIME}\{F(x),F'(x)\dot X\}\le\omega_{\mathrm{tang}_p}
    \mathrm{TIME}\{F(x)\}$ with $\omega_{\mathrm{tang}_p}\in[1+p,1+1.5p]$;
  - (cheap gradient principle)
    $\mathrm{TIME}\{F(x),\bar y^\top F'(x)\}\le\omega_{\mathrm{grad}}
    \mathrm{TIME}\{F(x)\}$ with $\omega_{\mathrm{grad}}\in[3,4]$; in
    particular, evaluating a scalar function together with its gradient
    costs at most $4$ times the evaluation of the function alone,
    independently of $n$;
  - for $q$ adjoint vectors propagated simultaneously the ratio lies in
    $[1+2q,1.5+2.5q]$.

  The constants are explicit functions of $(\mu,\pi,\nu)$, and the stated
  intervals are their ranges under the constraints on $w$.

  *Assessment.* The derivative identities are ingredients for the cost result.
  A separate operation model is needed to count the elemental evaluations and
  derivative operations.

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

* **9.5. Dennis–Moré condition and the BFGS method.** Let $f$ be twice
  continuously differentiable.
  - Let $x_{k+1}=x_k+\alpha_kp_k$ with descent directions $p_k$ and steps
    satisfying the Wolfe conditions with $c_1\le\frac12$. Suppose $x_k\to x^*$,
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

### Further topics

* **9.16. Discrete Kantorovich duality.** Let
  $a\in\mathbb R^n$, $b\in\mathbb R^m$ be probability vectors and
  $C\in\mathbb R^{n\times m}$. Let
  $U(a,b)=\{P\in\mathbb R_{\ge0}^{n\times m}:P\mathbf 1_m=a,\ P^\top\mathbf 1_n=b\}$.
  - (Kantorovich duality.)
    $$\min_{P\in U(a,b)}\langle C,P\rangle
    =\max\{\langle f,a\rangle+\langle g,b\rangle:\ f_i+g_j\le C_{ij}
    \text{ for all }i,j\}.$$

  *Assessment.* Partly covered. TauCeti formalizes positive matrix scaling,
  projective contraction and error estimates for Sinkhorn updates. The
  selected assertion is unregularized finite transport duality.

  *Scope.* The selected assertion is finite Kantorovich duality for all
  probability vectors, including marginals with zero coordinates.

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

* **10.2. Haar spaces.** Let $K$ be a set containing at least $N$ points and
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
  - (Haar's theorem) Let $K$ be a compact metric space with at least $N$
    points and $V\subseteq C(K)$ a subspace of finite dimension $N\ge1$.
    Every $f\in C(K)$ has a unique best
    approximation from $V$ in the supremum norm if and only if $V$ is a Haar
    space on $K$.

  *Assessment.* Finite-dimensional spaces and unisolvent polynomial
  interpolation are available. The theorem connects all-node interpolation,
  zero counts and the Haar condition for general finite-dimensional subspaces.

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

  *Assessment.* The Chebyshev extremal polynomial is available in one
  polynomial setting. The selected theorem characterizes the best
  approximation to an arbitrary continuous function by the alternating extreme
  points.

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

  *Scope.* The selected quantitative claim is the derivative remainder for
  interpolation at arbitrary distinct real nodes.

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

  *Assessment.* Uniform interpolation and classical polynomial norms supply
  the algebraic side. Quantitative growth of the interpolation operator and
  construction of a divergent continuous-function example remain missing.

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

  *Assessment.* Mathlib proves endpoint derivative estimates for extremal
  polynomials. The Bernstein bound and the inverse regularity implications
  need separate estimates across polynomial degrees.

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

  *Assessment.* Analytic coefficient and contour tools are available. The
  selected bounds use the Bernstein ellipse parameter to control Chebyshev
  tails and interpolation errors.

* **10.12. Barycentric formula.** Let $x_0,\dots,x_n$ be distinct and
  $\lambda_j=1/\prod_{k\ne j}(x_j-x_k)$. The interpolant of the data $f_j$ at
  $x_j$ is
  $$p(x)=\sum_{j=0}^n\frac{\lambda_jf_j}{x-x_j}\Bigg/\sum_{j=0}^n
  \frac{\lambda_j}{x-x_j}\qquad(x\notin\{x_0,\dots,x_n\}),$$
  and $p(x_j)=f_j$. For the Chebyshev points $x_j=\cos(j\pi/n)$, $n\ge1$,
  $$p(x)=\sum_{j=0}^n{}'\frac{(-1)^jf_j}{x-x_j}\Bigg/\sum_{j=0}^n{}'
  \frac{(-1)^j}{x-x_j},$$
  where the primes mean that the terms $j=0$ and $j=n$ are multiplied by
  $1/2$.

  *Assessment.* Partly covered. Mathlib proves the general barycentric
  formula. The selected assertion evaluates the weights for the Chebyshev
  extrema, including the two endpoint factors.

  *Scope.* The target is the explicit weights for Chebyshev points and their
  use in the barycentric identity.

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

  *Assessment.* The gap requires controlling defective rational types and
  characterizing best uniform rational approximants by alternation.

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

  *Assessment.* Linear algebra and formal power series supply ingredients. The
  result needs the rational equivalence relation, normalization at the center
  and the table's degree-defect structure.

* **10.15. Theorem of de Montessus de Ballore.** Let $R>0$ and let $f$ be
  meromorphic in the closed disk $|z|\le R$, with poles exactly at the
  distinct points $z_1,\dots,z_m$, where $0<|z_1|\le\cdots\le|z_m|<R$, of
  multiplicities $\mu_1,\dots,\mu_m$ with $\sum_k\mu_k=M$. Then for all
  sufficiently large $L$ the Padé approximant $[L/M]$ (in the sense of Baker)
  of the Maclaurin series of $f$ exists, and
  $$[L/M]\to f\qquad(L\to\infty)$$
  uniformly on every compact subset of $\{z:|z|\le R\}\setminus\{z_1,\dots,z_m\}$.

  *Assessment.* The analytic prerequisites are available in part. The missing
  convergence theorem controls a fixed-denominator-degree Padé row in the
  presence of poles of prescribed multiplicity.

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

  *Assessment.* Moment theory and complex integration provide ingredients. The
  selected result connects the Padé entries to negative real poles, residues,
  and convergence under the specified moment condition.

## 11. Splines, kernels and wavelets

[Synopsis](SYNOPSIS.md#11-splines-kernels-and-wavelets) · [Coverage inventory](STRUCTURE.md#11-splines-kernels-and-wavelets)

This section selects local spline bases and interpolation, strict kernel
positivity and error, and theorems about multiresolution and nonlinear
approximation.

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
    $\mu\le m$ in $y_i,\dots,y_{i+m}$ it has continuous derivatives up to
    order $m-1-\mu$.
  - **Partition of unity.** If $y_\ell<y_{\ell+1}$, then
    $\sum_{i=\ell+1-m}^{\ell}N_i^m(x)=1$ for $y_\ell\le x<y_{\ell+1}$.

  *Assessment.* Piecewise polynomials are expressible with existing types. The
  Cox–de Boor recurrence with repeated knots, support, positivity and
  partition-of-unity assertions need a spline API.

* **11.3. Curry–Schoenberg theorem.** In the setting of 11.1, choose an
  **extended partition** $y_1\le\cdots\le y_m\le a$,
  $b\le y_{m+K+1}\le\cdots\le y_{2m+K}$, with $b<y_{2m+K}$, and with
  $y_{m+1}\le\cdots\le y_{m+K}$ equal to the knots $x_1,\dots,x_k$, each
  $x_i$ repeated $m_i$ times. Then the restrictions to $[a,b]$ of the
  B-splines $N_1^m,\dots,N_{m+K}^m$ form a basis of
  $\mathcal S(\mathbb P_{m-1};\mathcal M;\Delta)$. They are nonnegative and
  sum to $1$ on $[a,b]$. If instead $b=y_{m+K+1}=\cdots=y_{2m+K}$, the same
  holds after the value of $N_{m+K}^m$ at $b$ is replaced by its left limit.

  *Assessment.* Finite-dimensional polynomial constructions are available. The
  proof must identify the spline space basis for the knot sequence and
  multiplicities.

* **11.4. Schoenberg–Whitney theorem.** Let $y_1\le\cdots\le y_{n+m}$ with
  $y_i<y_{i+m}$ for all $i$, and let $t_1<\cdots<t_n$. The collocation matrix
  $\bigl(N_j^m(t_i)\bigr)_{i,j=1}^n$ is nonsingular if and only if
  $N_i^m(t_i)\ne0$ for $i=1,\dots,n$. Hence, under this condition, for all
  data $v_1,\dots,v_n$ there is exactly one spline
  $s=\sum_{j=1}^nc_jN_j^m$ with $s(t_i)=v_i$ for all $i$.

  *Assessment.* Matrix determinants are available. The missing theorem
  connects positivity of the collocation determinant to the interlacing of
  interpolation sites and knot supports.

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

  *Assessment.* Hilbert projection gives the variational pattern. Identifying
  the interpolating natural cubic spline as the curvature minimizer requires
  the piecewise polynomial and boundary identities.

* **11.7. Error of complete cubic spline interpolation.** Let
  $f\in C^4[a,b]$ with $|f^{(4)}|\le L$ on $[a,b]$, let $\Delta$ be as in 11.6
  with mesh size $\|\Delta\|=\max_j(x_{j+1}-x_j)$, and let $K\ge1$ satisfy
  $\|\Delta\|\le K(x_{j+1}-x_j)$ for all $j$. Let $S$ be the complete cubic
  spline interpolant of 11.6. Then there are absolute constants $c_k\le2$
  such that, for all $x\in[a,b]$,
  $$|f^{(k)}(x)-S^{(k)}(x)|\le c_kL\|\Delta\|^{4-k}\quad(k=0,1,2),\qquad
  |f'''(x)-S'''(x)|\le c_3LK\|\Delta\|,$$
  with one-sided values of $S'''$ at the knots. Hence $S$, $S'$ and $S''$
  converge uniformly to $f$, $f'$ and $f''$ as $\|\Delta\|\to0$, and $S'''$
  converges uniformly to $f'''$ along mesh sequences with bounded $K$. The
  bounds hold with $c_0=5/384$, $c_1=1/24$, $c_2=3/8$ and
  $c_3=(K+K^{-1})/2$, and $c_0$ and $c_1$ are then best possible.

  *Assessment.* The numerical error needs a cubic spline interpolation
  operator with the specified endpoint conditions and the mesh-dependent
  derivative estimates.

### Kernels and scattered data

* **11.9. Strict positive definiteness from spectral support.** Let $\mu$
  be a finite nonnegative Borel measure on $\mathbb R^d$ whose support
  contains a nonempty open set, and define
  $$\Phi(x)=(2\pi)^{-d/2}\int_{\mathbb R^d}e^{-ix^\top\omega}\,d\mu(\omega).$$
  Then for every $N\ge1$, pairwise distinct $x_1,\dots,x_N\in\mathbb R^d$ and
  nonzero $\alpha\in\mathbb C^N$,
  $$\sum_{j,k=1}^N\alpha_j\overline{\alpha_k}\Phi(x_j-x_k)>0.$$

  *Assessment.* Partly covered. TauCeti proves Bochner representation and
  Fourier nonnegativity. The selected implication passes from the open support
  of the representing measure to strict positivity at distinct sites.

  *Scope.* The target is strict positive definiteness on every set of distinct
  sites from the support hypothesis on the spectral measure.

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

  *Assessment.* TauCeti's positive-definite kernel constructions supply
  related examples. The degree, smoothness and dimension-dependent strict
  positivity of the compact radial polynomials remain gaps.

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

  *Assessment.* The Gram and saddle-point matrix API is useful. The missing
  theorem gives nonsingularity on the polynomially constrained subspace and
  the resulting interpolation system.

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
  - Let $\Omega$ be bounded and satisfy an **interior cone condition** (there
    are $\theta\in(0,\pi/2)$ and $r>0$ such that every $x\in\Omega$ is the
    vertex of a cone of radius $r$ and angle $\theta$ contained in
    $\Omega$). The **fill distance** is
    $h_{X,\Omega}=\sup_{x\in\Omega}\min_j\|x-x_j\|_2$. For $\Phi_{d,k}$ of
    11.10 there are constants $C,h_0>0$, independent of $f$, $x$ and $X$,
    such that for all $f\in\mathcal N_{\Phi_{d,k}}(\Omega)$, all
    $\alpha\in\mathbb N_0^d$ with $|\alpha|\le k$, all $x\in\Omega$, and all
    $X$ with $h_{X,\Omega}\le h_0$,
    $$|D^\alpha f(x)-D^\alpha s_{f,X}(x)|\le C\,h_{X,\Omega}^{k+1/2-|\alpha|}
    \|f\|_{\mathcal N_{\Phi_{d,k}}(\Omega)}.$$

  *Assessment.* Mathlib supplies reproducing kernels and Hilbert projection.
  The gap identifies the norm of the interpolation error functional with the
  power function and gives the stated fill-distance estimates.

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

  *Assessment.* Hilbert bases, dilation and translation are available. The
  selected theorem links nested approximation spaces and the orthogonal
  splitting to an orthonormal wavelet basis.

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

  *Assessment.* The wavelet-specific filter construction, compact support,
  vanishing moments and regularity of the orthogonal system remain to be
  developed.

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

  *Assessment.* TauCeti has Besov-space and Littlewood–Paley theory. The gap
  connects best nonlinear selection of wavelet coefficients with the
  approximation space and its rates.

## 12. Orthogonal polynomials and numerical quadrature

[Synopsis](SYNOPSIS.md#12-orthogonal-polynomials-and-numerical-quadrature) · [Coverage inventory](STRUCTURE.md#12-orthogonal-polynomials-and-numerical-quadrature)

The Gaussian rule depends on a common moment, polynomial and spectral
framework. The integration-error gaps include Peano kernels and estimates for
analytic and periodic functions.

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
**interpolatory** if it has degree of exactness $n-1$.

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

  *Assessment.* Classical families and weighted inner products give individual
  examples. The selected theorem characterizes the existence and uniqueness of
  monic orthogonal polynomials by the moment determinants.

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

  *Assessment.* Recurrences for individual polynomial families supply
  examples. The gap gives the general recurrence with positive coefficients
  and Favard's converse measure construction.

* **12.3. Zeros.** For $n\ge1$, all zeros of $\pi_n$ are real and simple and
  lie in the open interval $(a,b)$, where $[a,b]$ is the support interval. The
  zeros of $\pi_n$ and $\pi_{n+1}$ strictly interlace: if
  $\tau^{(m)}_1>\cdots>\tau^{(m)}_m$ are the zeros of $\pi_m$, then
  $$\tau^{(n+1)}_{n+1}<\tau^{(n)}_n<\tau^{(n+1)}_n<\cdots<\tau^{(n)}_1
  <\tau^{(n+1)}_1.$$
  Every open interval $(c,d)$ with $\mu((c,d))=0$ contains at most one zero of
  $\pi_n$.

  *Assessment.* The missing result locates all zeros in the interior of the
  convex hull of the support and controls simplicity and interlacing using
  orthogonality.

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

  *Assessment.* Symmetric spectral decomposition supports the finite Jacobi
  matrix. The selected result relates its characteristic polynomial and the
  reproducing sum to the orthogonal family.

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

  *Assessment.* The theorem must link the orthogonal zeros to the positive
  rule and its exactness through degree $2n-1$.

* **12.7. Golub–Welsch.** Let $J_n=V\,\mathrm{diag}(x_1,\dots,x_n)\,V^\top$
  with $V$ orthogonal and columns $v_1,\dots,v_n$. Then the nodes of the
  $n$-point Gauss rule are the eigenvalues $x_k$ of $J_n$, and its weights
  are
  $$w_k=\beta_0\,v_{k,1}^2=\mu(\mathbb R)\,v_{k,1}^2,\qquad k=1,\dots,n,$$
  where $v_{k,1}$ is the first component of the unit eigenvector $v_k$.

  *Assessment.* Hermitian eigendecomposition is available. The missing
  assertion retrieves the quadrature weights from the squared first components
  of the Jacobi eigenvectors.

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

  *Assessment.* The endpoint-modified rules need the corresponding weighted
  orthogonality and a common interpolation-remainder argument with exact
  constants.

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

  *Assessment.* Calc and integration APIs give the ingredients for the
  integral Taylor remainder. The gap represents arbitrary functionals that
  annihilate the stated polynomials by a Peano kernel.

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

  *Assessment.* Partly covered. TauCeti gives Euler–Maclaurin with an integral
  Bernoulli remainder on integer endpoints. The selected form uses an
  arbitrary mesh and the stated remainder and periodic bound.

  *Scope.* The target includes the composite mesh weights, the derivative
  error formula and the periodic smooth-function estimate.

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
  derivative bound. Exponential convergence requires explicit hypotheses on
  analytic continuation, and the estimates depend on strip width and decay.

## 13. Discrete Fourier analysis and sparse recovery

[Synopsis](SYNOPSIS.md#13-discrete-fourier-analysis-and-sparse-recovery) · [Coverage inventory](STRUCTURE.md#13-discrete-fourier-analysis-and-sparse-recovery)

The additive-circle and cyclic DFT APIs provide Fourier ingredients. The
selected gaps include matrix normalization, FFT factorization, reconstruction
from samples and uniform recovery of sparse data.

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

### Nonequispaced data and exponential sums

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

* **14.1. Local Picard–Lindelöf and convergence of Euler polygons.** Let
  $D=\{(t,y):t_0\le t\le t_0+a,\ \|y-y_0\|\le b\}$ with $a,b>0$. Let $f$ be
  continuous on $D$ and satisfy $\|f(t,y)\|\le A$ for some $A>0$ and
  $\|f(t,y)-f(t,z)\|\le L\|y-z\|$ for points $(t,y),(t,z)\in D$ at the same
  time. The initial value problem has a unique solution on
  $[t_0,t_0+\alpha]$ with $\alpha=\min(a,b/A)$ and its graph lies in $D$.
  On a partition of this interval, set $y_{j+1}=y_j+(t_{j+1}-t_j)f(t_j,y_j)$
  starting at $y_0$. The piecewise linear interpolants through the
  $(t_j,y_j)$ converge uniformly to the solution as the maximal step
  size tends to zero.

  *Assessment.* Partly covered. The libraries give local or global existence
  and uniqueness in their respective ODE frameworks. Uniform convergence of
  polygonal Euler approximants is the selected gap.

  *Scope.* The selected conclusion is convergence of the variable-step Euler
  polygons in the local Lipschitz rectangle.

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
  global error is $O(h^p)$. For Euler's method $\Phi=f$, with $\|f\|\le A$,
  $\|\partial f/\partial t\|\le M$ and Lipschitz constant $L$ on a suitable
  set, the bound reads
  $\|y(t)-y_h(t)\|\le\frac{M+AL}{L}\bigl(e^{L(t-t_0)}-1\bigr)h$.

  *Assessment.* Existing Grönwall estimates apply once the recurrence for the
  accumulated error has been derived. The selected theorem connects a bound on
  the local defect to a global error on a variable step grid.

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

* **14.9. Collocation methods.** Let $c_1,\dots,c_s\in\mathbb R$ be distinct.
  For sufficiently smooth $f$, use the local branch of the stage equations
  near $y_0$ for small nonzero $h$. The **collocation polynomial** is the
  polynomial $u$ of degree at most $s$
  with $u(t_0)=y_0$ and $u'(t_0+c_ih)=f(t_0+c_ih,u(t_0+c_ih))$ for
  $i=1,\dots,s$, and the **collocation method** sets $y_1=u(t_0+h)$.
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

  *Scope.* The selected coefficient and order assertions concern the local
  branch of the implicit stages.

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
  \bigr)$. The method is
  **consistent** if $p\ge1$, that is, $\rho(1)=0$ and $\rho'(1)=\sigma(1)$.

  *Assessment.* The selected equivalences need the local multistep error
  functional and its moment conditions, including the generating-polynomial
  characterization.

  *Scope.* The target is the multistep order test, including the first nonzero
  defect coefficient and the consistency conditions.

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

* **14.12. First Dahlquist barrier.** A zero-stable linear $k$-step method has
  order $p\le k+2$ if $k$ is even and $p\le k+1$ if $k$ is odd. If
  $\beta_k/\alpha_k\le0$, in particular if the method is explicit, then
  $p\le k$.

  *Assessment.* The gap is the sharp order restriction under the root
  condition, with the separate explicit-method bound.

* **14.13. Backward differentiation formulas.** The **$k$-step BDF method**
  has $\sigma(\zeta)=\zeta^k$ and
  $$\rho(\zeta)=\sum_{j=1}^k\frac1j\,\zeta^{k-j}(\zeta-1)^j.$$
  It has order $k$, and it is zero-stable if and only if $1\le k\le6$; so it
  is convergent of order $k$ exactly for $k\le6$.

  *Assessment.* The order computation and the exact root locations for BDF
  zero-stability are missing. The general equivalence theorem then supplies
  the convergence classification.

### Error expansions, extrapolation and B-series

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
  $y'=\lambda y$, a Runge–Kutta method gives $y_{n+1}=R(h\lambda)y_n$ whenever
  $I-h\lambda A$ is invertible, where
  the **stability function** is
  $$R(z)=1+zb^\top(I-zA)^{-1}\mathbb 1=
  \frac{\det(I-zA+z\mathbb 1b^\top)}{\det(I-zA)},$$
  a rational function with numerator and denominator of degree at most $s$.
  For an explicit method $R$ is a polynomial of degree at most $s$. If the
  method has order $p$, then $R(z)=e^z+O(z^{p+1})$ as $z\to0$. The
  **stability domain** is $S=\{z\in\mathbb C:|R(z)|\le1\}$.

  *Assessment.* The matrix inverse and determinant lemmas are available. The
  selected assertion derives the test-equation stability function from the
  stage system and connects its expansion to method order.

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
    $\Rightarrow$ A-stable;
  - for non-confluent methods the three properties algebraic stability,
    B-stability and AN-stability are equivalent;
  - the Gauss, Radau IA, Radau IIA and Lobatto IIIC methods are
    algebraically stable, and the Lobatto IIIA and IIIB methods are not
    AN-stable, hence not B-stable.

  *Assessment.* The inner-product API can express dissipativity and positive
  semidefiniteness. The numerical theorem links these to the one-step
  contraction and the stated algebraic-stability criteria.

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
  differentiations of $\delta$. The **index of nilpotency** is $\max_im_i$;
  it does not depend on the choice of $P,Q$.
  The **differentiation index** of $F(u',u)=0$ is the least $m$ such that
  $F=0$ and its first $m$ derivatives with respect to $t$ allow one to
  extract by algebraic manipulation an explicit system $u'=\varphi(u)$. For
  $Bu'+Au=d$ with a regular pencil it equals the index of nilpotency.

  *Assessment.* The library has matrix Jordan infrastructure in individual
  settings. The gap is the regular matrix pencil decomposition, its nilpotent
  blocks and the index of the resulting differential-algebraic system.

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
  $$\|u_n-u(t_n)\|_V\le Ch\sup_{0\le t\le t_n}\|A^{\beta-1}F'(t)\|_V,
  \qquad0\le nh\le T,$$
  with $C$ depending on $T$ but not on $n$ or $h$.

  *Assessment.* TauCeti has semigroup and variation-of-constants
  infrastructure. The exponential Euler convergence theorem needs the
  quadrature defect and the stiffness-uniform bounds in the specified spaces.

### Geometric integration

* **15.13. Quadratic invariants and symplectic Runge–Kutta methods.** A
  **quadratic invariant** of $y'=f(y)$ is $Q(y)=y^\top Cy$ with $C$
  symmetric and $y^\top Cf(y)=0$ for all $y$.
  - If $b_ia_{ij}+b_ja_{ji}=b_ib_j$ for all $i,j$ (that is, $M=0$ in 15.7),
    then the Runge–Kutta method conserves every quadratic invariant and is
    symplectic. The Gauss methods satisfy this condition.
  - Conversely, an irreducible symplectic Runge–Kutta method satisfies
    $M=0$.
  - For $n\ge3$ no Runge–Kutta method conserves every polynomial invariant
    of degree $n$. The obstruction is $\det Y$, a polynomial invariant of
    degree $n$ of $Y'=AY$, $Y\in\mathbb R^{n\times n}$, whenever
    $\mathrm{tr}\,A=0$.

  *Assessment.* TauCeti proves preservation of the symplectic form by exact
  Hamiltonian flows. The gap concerns the discrete Runge–Kutta coefficients,
  quadratic invariants and the induced step map.

* **15.15. Backward error analysis.** For a one-step method
  $y_{n+1}=\Phi_h(y_n)$ applied to $y'=f(y)$, the **modified equation** is
  the formal series $\tilde y'=f(\tilde y)+hf_2(\tilde y)+h^2f_3(\tilde y)
  +\cdots$ whose time-$h$ flow equals $\Phi_h$ as a formal series in $h$;
  for a method of order $p$, $f_2=\dots=f_p=0$. Let $f$ be analytic and
  bounded by $M$ on the complex ball $B_{2R}(y_0)$, and let the Taylor
  coefficients of $\Phi_h(y)=y+hf(y)+h^2d_2(y)+\cdots$ satisfy
  $\|d_j(y)\|\le\mu M(2\kappa M/R)^{j-1}$ on $B_R(y_0)$ (for a Runge–Kutta
  method this holds with $\mu=\sum_i|b_i|$ and
  $\kappa=\max_i\sum_j|a_{ij}|$). Put $\eta=2\max(\kappa,\mu/(2\log2-1))$,
  $h_0=R/(e\eta M)$ and $\gamma=e(2+1.65\eta+\mu)$. If $h\le h_0/4$ and
  $N$ is the largest integer with $hN\le h_0$, then the time-$h$ flow
  $\tilde\varphi_{N,h}$ of the modified equation truncated after the term
  $h^{N-1}f_N$ satisfies
  $$\|\Phi_h(y_0)-\tilde\varphi_{N,h}(y_0)\|\le h\gamma Me^{-h_0/h}.$$

  *Assessment.* Formal series and local flow theory supply ingredients. The
  missing result constructs the modified vector field and turns an optimally
  truncated expansion into a quantitative small-defect estimate.

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
  and $0\le\phi\le1/8$. Apply the discrete maximum principle of 16.2. The
  scaled Euclidean estimate follows by bounding the scaled number of grid
  points.

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
    $\mathrm{TV}(u(t))\le\mathrm{TV}(u_0)$ and the time continuity
    $\|u(t)-u(s)\|_{L^1}\le\|f\|_{\mathrm{Lip}}\,\mathrm{TV}(u_0)\,|t-s|$.

  For $d=1$, if $u$ and $v$ are the entropy solutions with Lipschitz,
  piecewise $C^2$ fluxes $f$ and $g$ and data $u_0,v_0\in L^1\cap BV$, then
  $$\|u(t)-v(t)\|_{L^1}\le\|u_0-v_0\|_{L^1}
  +t\,\min\{\mathrm{TV}(u_0),\mathrm{TV}(v_0)\}\,\|f-g\|_{\mathrm{Lip}}.$$

  *Assessment.* TauCeti develops bounded variation and distributional
  approximation. The existence, uniqueness, contraction and initial-data
  dependence of the scalar entropy solution remain gaps.

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

* **17.8. Order barriers for monotone and positive schemes.** Two
  results state that the accuracy of monotone schemes is limited.
  - (Harten–Hyman–Lax) If a conservative consistent scheme is monotone and
    its numerical flux $g$ is $C^3$, then it is at most first order
    accurate: on smooth solutions the local truncation error is
    $\frac12\Delta t^2\,\partial_x\bigl(\beta(u)\,\partial_xu\bigr)
    +O(\Delta t^3)$ with
    $\beta\ge0$, and $\beta>0$ unless the scheme is an exact translation,
    which requires $f$ linear.
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
  $$\|u(T)-v(T)\|_{L^1}\le\|u_0-v_0\|_{L^1}
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
  $\alpha_h\ge\gamma_h\alpha$. Conversely, if $\alpha_h>0$, such an operator
  exists.

  *Assessment.* Finite-dimensional duality and rank identities are available.
  The numerical gap is the equivalence with discrete inf-sup stability and the
  Fortin operator criterion.

* **18.3. Quasi-optimality: Céa, Babuška, Xu–Zikatanov.** In the setting of
  18.2, with $u$ the exact solution and $\alpha_h>0$, **Galerkin
  orthogonality** $a(u-u_h,w_h)=0$ holds for all $w_h\in W_h$, and
  $$\|u-u_h\|_V\le\Bigl(1+\frac{\|a\|}{\alpha_h}\Bigr)
  \inf_{v_h\in V_h}\|u-v_h\|_V \qquad\text{(Babuška).}$$
  If $V$ is a Hilbert space and $\{0\}\ne V_h\ne V$, the factor improves to
  $\|a\|/\alpha_h$ (Xu–Zikatanov). If $V=W$ is a Hilbert space, $V_h=W_h$
  and $a$ is coercive with constant $\alpha$, the factor is $\|a\|/\alpha$
  (Céa), and it is $(\|a\|/\alpha)^{1/2}$ if moreover $a$ is symmetric.

  *Assessment.* Partly covered. Orthogonal projection gives the inner-product
  instance. The selected bounds concern the general coercive or inf-sup-stable
  bilinear forms, including the sharp Hilbert-space variants.

  *Scope.* The target is quasi-optimality with a discrete inf-sup constant,
  including the sharpened Hilbert-space bound and the coercive case.

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

### Sobolev space tools

* **18.6. The onto trace from $H^1(\Omega)$.** For a bounded Lipschitz
  domain $\Omega$, the value trace is a bounded surjection
  $$\gamma:H^1(\Omega)\longrightarrow H^{1/2}(\partial\Omega)$$
  with kernel $H^1_0(\Omega)$. For functions in $H^1(\Omega)$ continuous on
  $\overline\Omega$, $\gamma$ agrees with restriction to $\partial\Omega$.

  *Assessment.* Partly covered. TauCeti gives bounded first-order traces in
  boundary charts and identifies the zero-trace kernel. The selected result
  gives surjectivity onto the fractional boundary trace space.

  *Scope.* The target is the onto trace theorem at first order with the
  boundary Sobolev space as codomain.

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

  *Assessment.* TauCeti has local and flat-boundary Hessian estimates. The
  selected gap is global regularity and a solution bound for the homogeneous
  Dirichlet problem on convex or polygonal domains.

  *Scope.* The selected regularity estimates use homogeneous Dirichlet data on
  convex domains and, for the Laplacian, on planar polygons.

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
    $d\in\{2,3\}$ and every cell has at most one face on $\partial\Omega$
    (in $d=2$: no triangle with two edges on $\partial\Omega$). For $d=2$
    and smooth solutions, $\|u-u_h\|_{1,\Omega}+\|p-p_h\|_{0,\Omega}\le Ch^s
    (\|u\|_{s+1,\Omega}+\|p\|_{s,\Omega})$ for $0\le s\le2$.

  By 18.19 both pairs are then quasi-optimal.

  *Assessment.* The Stokes form and pressure–velocity pairing can be developed
  from the Sobolev API. The named mesh-dependent pairs need uniform inf-sup
  constants and stability analyses.

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

For items 19.2–19.4, let $\Omega\subset\mathbb R^d$ be a bounded domain with
smooth boundary and consider $u_t-\Delta u=f$ in $\Omega\times(0,\infty)$,
$u=0$ on $\partial\Omega$, $u(0)=v$. Let $\{S_h\}_{0<h<1}$ be a family of
finite-dimensional subspaces of $H^1_0(\Omega)$ and $r\ge2$ an integer (the
**order of accuracy**) such that for $1\le s\le r$ and all
$w\in H^s(\Omega)\cap H^1_0(\Omega)$
$$\inf_{\chi\in S_h}\bigl(\|w-\chi\|+h\|\nabla(w-\chi)\|\bigr)\le Ch^s\|w\|_s .$$
Continuous piecewise polynomials of degree $r-1$ are the model case. In
each estimate below, $u$ is assumed regular enough for the right-hand side
to be finite, and $C$ is independent of $h$, $k$, $t$ and $u$.

* **19.2. Ritz projection and semidiscrete Galerkin method.** The **Ritz** (or
  elliptic) **projection** $R_h:H^1_0(\Omega)\to S_h$ is defined by
  $(\nabla R_hw,\nabla\chi)=(\nabla w,\nabla\chi)$ for all $\chi\in S_h$. It
  satisfies $\|\nabla R_hw\|\le\|\nabla w\|$ and
  $$\|R_hw-w\|+h\|\nabla(R_hw-w)\|\le Ch^s\|w\|_s,\qquad
  w\in H^s\cap H^1_0,\ 1\le s\le r .$$
  The **semidiscrete Galerkin approximation** is the function
  $u_h:[0,\infty)\to S_h$ with $u_h(0)=v_h\in S_h$ and
  $(u_{h,t},\chi)+(\nabla u_h,\nabla\chi)=(f,\chi)$ for all $\chi\in S_h$ and
  $t>0$. If $v\in H^r(\Omega)\cap H^1_0(\Omega)$ and $u_t$ is integrable
  in $H^r(\Omega)$ on the time interval considered, then
  $$\|u_h(t)-u(t)\|\le\|v_h-v\|+Ch^r\Bigl(\|v\|_r+\int_0^t\|u_t\|_r\,ds\Bigr).$$
  With $v_h=R_hv$ or $v_h$ the $L^2$ projection of $v$ onto $S_h$, the first
  term is at most $Ch^r\|v\|_r$, so the error is $O(h^r)$ uniformly on bounded
  time intervals.

  *Assessment.* Partly covered. TauCeti proves the finite-dimensional
  autonomous semidiscrete problem is uniquely solvable for continuous forcing.
  The Ritz projection estimates and the spatial convergence bound are the
  selected gap.

  *Scope.* The targets are the Ritz estimate and the time-dependent error in
  the spatial $L^2$ norm.

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

  *Assessment.* The static elliptic and semidiscrete estimates are
  prerequisites. The gap controls the interaction of spatial projection error
  and the temporal error of the two fully discrete schemes.

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

  *Assessment.* Mathlib has Parseval's identity for the Fourier basis. The
  selected rates need finite frequency cutoffs, aliasing, and inverse and
  interpolation bounds in the periodic norms.

* **19.10. Legendre–Galerkin method.** Let $\alpha\ge0$, $f$ continuous on
  $[-1,1]$, and let $u\in H^1_0(I)$ be the weak solution of $-u''+\alpha u=f$,
  $u(\pm1)=0$. The **Legendre–Galerkin approximation** is the
  $u_N\in\mathbb P^0_N$ with
  $\int_Iu_N'v'\,dx+\alpha\int_Iu_Nv\,dx=\int_I(I_Nf)v\,dx$ for all
  $v\in\mathbb P^0_N$, where $I_N$ is LGL interpolation. If
  $\partial_xu\in B^{m-1}_{0,0}(I)$ and $f\in B^k_{-1,-1}(I)$ with
  $1\le m,k\le N+1$, then
  $$\|u-u_N\|_1\le c\sqrt{\tfrac{(N-m+1)!}{N!}}(N+m)^{\frac{1-m}2}
  \|\partial_x^mu\|_{\omega^{m-1,m-1}}+c\sqrt{\tfrac{(N-k+1)!}{N!}}
  (N+k)^{-\frac{k+1}2}\|\partial_x^kf\|_{\omega^{k-1,k-1}},$$
  with $c$ independent of $m$, $k$, $N$, $f$ and $u$. For fixed $m$ and $k$
  the right-hand side is $O(N^{1-m}+N^{-k})$: the convergence rate is limited
  only by the regularity of $u$ and $f$.

  *Assessment.* Orthogonal polynomial and coercive form APIs supply
  ingredients. The missing result constructs the space with zero endpoint
  values and proves its spectral Galerkin error estimate.

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
  eigenproblem, reciprocals and a concrete Dirichlet min–max theorem. The
  selected claims are the general variational min–max and the conforming
  discrete upper bounds.

  *Scope.* The target is the variational characterization for the energy
  eigenproblem and its use with conforming finite-dimensional subspaces.

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

  *Assessment.* Compactness and spectral perturbation estimates are available.
  The missing approximation theorem controls the discrete eigenspaces and
  excludes spurious modes under the discrete hypotheses.

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

  *Assessment.* The variational eigenproblem and a spectral gap are
  ingredients. The numerical estimate distinguishes the first-order eigenspace
  error from the squared eigenvalue error.

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

  *Assessment.* Weak elliptic solvability is present. The missing estimator
  theory involves mesh residuals, jumps, patchwise efficiency and data
  oscillation.

* **19.18. Prager–Synge identity for Poisson's equation.** Let $u\in
  H^1_0(\Omega)$ solve $-\Delta u=f\in L^2(\Omega)$. For every $u_h\in
  H^1_0(\Omega)$ and every $\sigma^*\in H(\mathrm{div};\Omega)$ with
  $\nabla\cdot\sigma^*=f$,
  $$\|\nabla(u-u_h)\|^2+\|\nabla u+\sigma^*\|^2=\|\nabla u_h+\sigma^*\|^2 ,$$
  so $\|\nabla u_h+\sigma^*\|$ is a guaranteed upper bound of the error.

  *Assessment.* The selected hypercircle identity uses the weak equation and
  normal-flux integration by parts. It gives a guaranteed energy bound
  whenever a flux with the required divergence is available.

  *Scope.* The selected claim is the Poisson hypercircle identity and the
  guaranteed energy error bound from an equilibrated flux.

  *Argument.* The cross term between $\nabla(u_h-u)$ and $\nabla u+\sigma^*$
  is zero by the weak equation and integration by parts. Expanding the square
  of their sum gives the identity.

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

  *Assessment.* The selected result combines discrete reliability, marking,
  refinement, a contraction and complexity relative to an approximation class.

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

  *Assessment.* TauCeti has general Gamma-convergence definitions. The
  obstacle problem requires admissible sets on the meshes, discrete
  compactness and recovery, and convergence of the computed minimizers.

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
  $r:\mathbb K^{n_\ell}\to\mathbb K^{n_{\ell-1}}$, and smoothing iterations for
  $A_\ell$ with iteration matrices $S_\ell$. The **two-grid iteration** with
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

  *Assessment.* The two-grid estimate joins a smoother and a coarse-space
  projector. Its convergence factor requires the stated smoothing and
  approximation inequalities.

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

  *Assessment.* The missing result constructs the multilevel recursion and
  bounds its error operator uniformly in the number of levels under the
  W-cycle conditions.

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

  *Assessment.* The symmetric smoother and spectral estimates are ingredients.
  The selected result needs the energy-norm contraction and the recursive
  V-cycle comparison.

* **20.4. Finite element multigrid for a model problem.** Let
  $\Omega\subset\mathbb R^2$ be a convex polygon, $a(u,v)=\int_\Omega(\alpha
  \nabla u\cdot\nabla v+\beta uv)\,dx$ with smooth $\alpha,\beta$,
  $0<\alpha_0\le\alpha\le\alpha_1$ and $0\le\beta\le\beta_1$, and let $V_k\subset
  H^1_0(\Omega)$ be the continuous piecewise linear functions on triangulations
  $\mathcal T_k$, where $\mathcal T_{k+1}$ is obtained from $\mathcal T_k$ by
  joining edge midpoints. Let the $k$-th level iteration use $m$ Richardson
  smoothing steps $z\mapsto z+\Lambda_k^{-1}(g-A_kz)$, where $\Lambda_k\ge
  \rho(A_k)$ and $\Lambda_k\le Ch_k^{-2}$, with transfers given by inclusion and
  its adjoint, and write $\|v\|_E=a(v,v)^{1/2}$. Then:
  - (two-grid) $\|e_{\mathrm{TG}}\|_E\le Cm^{-1/2}\|e_0\|_E$ for the one-sided
    two-grid method with $m$ presmoothing steps;
  - (W-cycle) for every $\gamma\in(0,1)$ there is $m_0$ such that, for
    $m\ge m_0$, the one-sided W-cycle reduces the energy error by the factor
    $\gamma$ on every level $k$;
  - (V-cycle) with $m$ pre- and $m$ postsmoothing steps, the V-cycle satisfies
    $\|z-MG(k,z_0,g)\|_E\le\frac{C_*}{m+C_*}\|z-z_0\|_E$ for every $m\ge1$
    and every $k$, with $C_*$ independent of $k$ and $m$;
  - (full multigrid) if the $k$-th level iteration is a contraction in
    $\|\cdot\|_E$ with a contraction number $\gamma$ independent of $k$, and
    $r$ iterations are performed on each level with $2\gamma^r<1$, starting
    from the interpolated result of the previous level, then the full
    multigrid approximation $\hat u_k$ satisfies
    $\|u_k-\hat u_k\|_E\le Ch_k|u|_{H^2(\Omega)}$, where $u_k$ is the Galerkin
    solution and $u$ the exact solution.

  *Assessment.* The approximation properties of finite elements give
  ingredients. The missing theorem quantifies mesh-independent contraction and
  the work-to-accuracy relation on a hierarchy.

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

  *Assessment.* Orthogonal projections exist in the energy norm. The gap
  connects a stable decomposition with the spectrum of the sum of subspace
  solvers.

* **20.6. The Xu–Zikatanov identity.** Let $A$ be symmetric positive definite
  on $V$, let $V_1,\dots,V_J$ be subspaces with $V=V_1+\cdots+V_J$, and let
  $P_i$ be the $(\cdot,\cdot)_A$-orthogonal projection onto $V_i$. The
  **successive subspace correction** method with exact subspace solves has
  error propagation operator $E=(I-P_J)(I-P_{J-1})\cdots(I-P_1)$, and
  $$\|E\|_A^2=1-\frac1{1+c_0},\qquad
  c_0=\sup_{\|v\|_A=1}\ \inf_{\substack{v_i\in V_i\\ \sum_iv_i=v}}\
  \sum_{i=1}^J\Bigl\|P_i\sum_{j=i+1}^Jv_j\Bigr\|_A^2.$$
  In particular $\|E\|_A<1$.

  *Assessment.* The finite product of projection corrections is expressible.
  The selected identity gives its exact energy-norm contraction in terms of an
  extremal decomposition constant.

* **20.7. Two-level convergence identity and optimal coarse spaces.** Let $A$
  be symmetric positive definite on $V=\mathbb R^n$, and let $R$ be a smoother
  whose symmetrization $\bar R=R^\top+R-R^\top AR$ is symmetric positive
  definite (equivalently, $\|I-RA\|_A<1$). For a coarse space $V_c\subset V$,
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

  *Assessment.* Matrix eigendecomposition and variational inequalities are
  available. The missing result identifies the exact two-level norm and
  optimizes the coarse space.

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
  - (stable decomposition) there is $C_0$ such that every $u\in V$ has a
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

  *Assessment.* Schur complement and projection results are ingredients. The
  selected theorem connects stable decomposition and strengthened interactions
  to spectra of the additive Schwarz operator.

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
  $h$, $H$ or $\delta$. The multiplicative and hybrid variants then converge
  at rates bounded through 20.8.

  *Assessment.* The gap needs a mesh partition, overlap and coarse projection
  estimates before the abstract Schwarz bounds yield the stated condition
  number.

* **20.11. Polylogarithmic bounds for nonoverlapping methods.** Let $\Omega$
  be partitioned into nonoverlapping, shape-regular subdomains of diameter
  about $H$, with a quasi-uniform finite element mesh of size $h$ aligned with
  the subdomain boundaries, and let the problem be reduced to the Schur
  complement $S_h$ on the interface. For the model problem of 20.10 in two
  dimensions:
  - the Bramble–Pasciak–Schatz, Neumann–Neumann (with coarse space) and BDDC
    preconditioners $B$ satisfy $\kappa(BS_h)\le C(1+\log(H/h))^2$, with $C$
    independent of $h$, $H$ and the number of subdomains;
  - the bounds for the BPS and Neumann–Neumann preconditioners are sharp in
    their dependence on $H/h$.

  For $-\nabla\cdot(\rho\nabla u)$ in three dimensions, with $\rho$ a positive
  constant $\rho_i$ on each subdomain and no subdomain whose boundary meets
  the Dirichlet boundary in only one or a few points, the balancing
  Neumann–Neumann method and the FETI-DP method whose primal constraints are
  the subdomain vertex values and the averages over all edges and faces
  satisfy the condition number bound $C(1+\log(H/h))^2$, with $C$ independent
  of $h$, $H$ and the values $\rho_i$. In two dimensions, FETI-DP with primal
  vertex values satisfies a bound of the same form. Apart from the eigenvalue
  $1$, the preconditioned BDDC and FETI-DP operators with corresponding
  primal constraints have the same spectrum.

  *Assessment.* The interface operators can use Schur complements. The
  selected result is the polylogarithmic conditioning bound under the
  geometric and discrete constraints on primal and dual degrees of freedom.

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

* **21.1. Compactness of integral operators.** Integral operators $(A\varphi)(x)=\int_GK(x,y)
  \varphi(y)\,dy$ with continuous or weakly singular kernels are compact on
  $C(G)$. With continuous kernels they are also compact on $L^2(G)$.

  *Assessment.* Partly covered. Mathlib and TauCeti give the abstract
  compact-operator Fredholm and Riesz assertions in their settings. The
  selected gap proves compactness for the integral operators under their
  kernel hypotheses.

  *Scope.* The selected claim is compactness for the indicated integral
  kernels in the two function-space settings.

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

  *Assessment.* Partly covered. The compact index-zero and
  continuous-transpose results are available. The selected alternative uses a
  possibly different nondegenerate normed dual system and identifies
  solvability on both sides.

  *Scope.* The target is the normed-space dual Fredholm alternative and the
  compatibility condition for the inhomogeneous problem.

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

  *Assessment.* The continuous Fredholm result excludes nontrivial homogeneous
  solutions. The missing approximation result proves eventual discrete
  solvability and a quantitative projection error for second-kind equations.

* **21.7. Collectively compact approximation.** A set of linear operators
  $\mathcal A$ from $X$ to $Y$ is **collectively compact** if
  $\{A\varphi:\varphi\in U,\ A\in\mathcal A\}$ is relatively compact for every
  bounded $U\subset X$. Let $X$ be a Banach space, $A:X\to X$ compact with
  $I-A$ injective, and $(A_n)$ collectively compact with $A_n\varphi\to
  A\varphi$ for all $\varphi$. Then $\|(A_n-A)A_n\|\to0$, and for all $n$ with
  $\|(I-A)^{-1}(A_n-A)A_n\|<1$ the inverse $(I-A_n)^{-1}$ exists, with
  $$\|(I-A_n)^{-1}\|\le\frac{1+\|(I-A)^{-1}\|\,\|A_n\|}
  {1-\|(I-A)^{-1}(A_n-A)A_n\|},$$
  and the solutions of $\varphi-A\varphi=f$ and $\varphi_n-A_n\varphi_n=f_n$
  satisfy
  $$\|\varphi_n-\varphi\|\le\frac{1+\|(I-A)^{-1}\|\,\|A_n\|}
  {1-\|(I-A)^{-1}(A_n-A)A_n\|}\bigl(\|(A_n-A)\varphi\|+\|f_n-f\|\bigr).$$

  *Assessment.* The theory of individual compact operators is available. The
  gap uses collective compactness and pointwise approximation to control
  inverse operators uniformly.

* **21.8. Nyström method.** Let $K$ be continuous on $G\times G$ and let
  $Q_n(g)=\sum_{k=1}^n\alpha_k^{(n)}g(x_k^{(n)})$ be quadrature rules with
  $Q_n(g)\to\int_Gg\,dy$ for every $g\in C(G)$. The **Nyström operators**
  $(A_n\varphi)(x)=\sum_k\alpha_k^{(n)}K(x,x_k^{(n)})\varphi(x_k^{(n)})$ are
  collectively compact and converge pointwise to $A$ on $C(G)$, though not in
  norm. Solving $\varphi_n-A_n\varphi_n=f$ is equivalent to solving the linear
  system for the nodal values $\varphi_n(x_j)$ and then using the
  Nyström interpolation formula
  $\varphi_n(x)=f(x)+\sum_k\alpha_kK(x,x_k)\varphi_n(x_k)$. If
  $\varphi-A\varphi=f$ is uniquely solvable, then for $n\ge N$ the Nyström
  equations are uniquely solvable, $\|(I-A_n)^{-1}\|_\infty$ is bounded
  uniformly in $n$, and
  $$\|\varphi-\varphi_n\|_\infty\le c\,\|(A-A_n)\varphi\|_\infty,$$
  so the error is of the order of the quadrature error for the integrands
  $K(x,\cdot)\varphi$.

  *Assessment.* The missing result converts converging quadrature into
  pointwise and collectively compact operator approximation and a Nyström
  error estimate.

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

  *Assessment.* Existing resolvent and integration theory supplies
  ingredients. Volterra equations need iterated triangular-kernel estimates
  that imply convergence without a small operator norm condition.

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

  *Assessment.* Interpolation and causal Volterra stability are ingredients.
  The gap is the collocation recurrence and its uniform and nodal convergence
  orders.

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

  *Assessment.* The kernel singularity and limited solution smoothness require
  graded-mesh consistency estimates. The selected result specifies the
  resulting convergence rate as a function of grading.

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
  $\nu\cdot(\nabla v(x+h\nu(x))-\nabla v(x-h\nu(x)))\to0$ uniformly.

  *Assessment.* Fundamental solutions and weak derivatives are available in
  relevant settings. The missing jump identities relate interior and exterior
  boundary traces of the layer potentials.

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

  *Assessment.* The Sobolev API supplies ingredients for trace spaces. The
  selected layer operators must be defined and bounded on the Lipschitz
  boundary spaces with the stated dualities.

* **21.14. Ellipticity of the single-layer operator.** For the Laplace
  operator in $\mathbb R^3$ and a bounded Lipschitz domain, there are
  constants $c_V,c_W>0$ such that
  $$\langle V\varphi,\varphi\rangle\ge c_V\|\varphi\|^2_{H^{-1/2}(\Gamma)}
  \quad(\varphi\in H^{-1/2}(\Gamma)),\qquad
  \langle W\psi,\psi\rangle\ge c_W\|\psi\|^2_{H^{1/2}(\Gamma)/\mathbb K}
  \quad(\psi\in H^{1/2}(\Gamma)).$$
  Hence the first-kind equation $V\varphi=g$ has a unique solution
  $\varphi\in H^{-1/2}(\Gamma)$ for every $g\in H^{1/2}(\Gamma)$, and its
  Galerkin approximations in any closed subspace are quasi-optimal (Céa's
  lemma).

  *Assessment.* The gap comprises ellipticity in the boundary energy norm and
  the corresponding isomorphism of the single-layer operator under the
  indicated dimensional conditions.

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

  *Assessment.* Partly covered. TauCeti gives continuous compatibility and
  solvability for compact perturbations of coercive forms. The selected
  conclusions are eventual discrete well-posedness and uniform
  quasi-optimality.

  *Scope.* The selected claims are eventual discrete well-posedness and
  quasi-optimality uniformly over the approximation spaces.

* **21.16. Ill-posedness of first-kind equations with compact operators.** If
  $A:X\to Y$ is a compact linear operator between normed spaces and $X$ is
  infinite-dimensional, then $A$ has no bounded inverse on $A(X)$.

  *Assessment.* Mathlib has compactness of the identity exactly in finite
  dimension over the scalar fields in question. The selected ill-posedness
  criterion expresses the consequence for bounded inverses on the range.

  *Argument.* A bounded inverse on the range would make the unit ball of the
  domain totally bounded, because the compact image of that ball is totally
  bounded with the norm inherited from the ambient space. This contradicts
  Riesz's lemma in infinite dimension.

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

  *Assessment.* The spectral calculus is a prerequisite. The selected theorem
  relates approximation on the exact range and noise amplification to a
  convergent parameter choice, with spectral cutoff as a model.

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

* **22.12. Bayes' formula in function space with Gaussian noise.** Let $X$
  be a separable Banach space, $\mu_0$ a prior probability measure on $X$,
  and $G:X\to\mathbb R^q$ continuous. Observe $y=G(u)+\eta$ with $u$ of
  law $\mu_0$ and independent noise $\eta\sim N(0,\Gamma)$ with positive
  definite $\Gamma$. Define
  $$\Phi(u;y)=\tfrac12|\Gamma^{-1/2}(y-G(u))|^2,\qquad
  Z(y)=\int_X e^{-\Phi(u;y)}\,d\mu_0(u).$$
  Then $0<Z(y)\le1$ for every $y\in\mathbb R^q$. A version $\mu^y$ of the
  conditional law of $u$ given $y$ is absolutely continuous with respect
  to $\mu_0$ with density
  $$\frac{d\mu^y}{d\mu_0}(u)=Z(y)^{-1}e^{-\Phi(u;y)}.$$

  *Assessment.* Partly covered. Mathlib supplies the abstract Radon–Nikodym
  theorem for posterior kernels and almost-everywhere uniqueness. The selected
  target is an explicit posterior version for the independent, nondegenerate
  additive Gaussian observation.

  *Scope.* The selected formula uses independent nondegenerate Gaussian
  observation noise, with a finite positive normalizer for every observation.

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

  *Assessment.* Partly covered. Mathlib has the strong law, iid central limit
  theorem and variance identities. The selected results concern consistency of
  the sample variance and the studentized interval.

  *Scope.* The selected claims are almost-sure consistency of the sample
  variance and the asymptotic coverage of the studentized interval.

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
  the variance is zero.

  *Assessment.* Partly covered. The integral-with-density formula supports the
  unbiasedness assertion. The selected result minimizes variance over
  admissible laws and specifies the case of zero variance.

  *Scope.* The target is the variance-minimizing proposal and the
  zero-variance conclusion for a nonnegative integrand.

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

  *Assessment.* Mathlib has Markov kernels and irreducibility theory. The
  missing result constructs the accept–reject transition, checks detailed
  balance and applies the stated ergodic conclusion.

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

### Information-based complexity and tractability

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

  *Assessment.* The underlying spectral and low-rank machinery is available in
  part. The selected weighted snapshot projection identity expresses the
  minimum over subspaces in the metric of the state space.

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
  bounded and $c$ is continuous on $D\times D$, then the $\phi_j$ with
  $\nu_j>0$ are continuous,
  $$\sup_{x,y\in D}\Bigl|c(x,y)-\sum_{j\le J}\nu_j\phi_j(x)\phi_j(y)\Bigr|
  \le\sup_{x\in D}\sum_{j>J}\nu_j\phi_j(x)^2\to0 ,$$
  and $\sup_{x\in D}\mathbb E\bigl[(u(x)-u_J(x))^2\bigr]\to0$ as
  $J\to\infty$.

  *Assessment.* Compact spectral theory and Hilbert-space second moments
  supply ingredients. The missing expansion identifies the orthogonal random
  coefficients and exact truncation error.

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
