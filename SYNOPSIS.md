# Core knowledge in numerical analysis and scientific computing

This synopsis collects definitions and principal theorems of numerical
analysis and scientific computing. It covers floating-point arithmetic and
conditioning, numerical linear algebra, verified computation, nonlinear
equations and optimization, approximation theory and quadrature, discrete
Fourier analysis and sparse recovery, and the numerical solution of ordinary,
partial, integral and stochastic differential equations. It ends with inverse
problems, sampling methods, and high-dimensional approximation, uncertainty
quantification and model reduction. The [bibliography](NASC-bib.md) and
reference guide give the mathematical sources. Proofs are outside its scope.
The synopsis has 396 numbered entries in 24 sections. Statement $x.y$ is the $y$-th
statement of section $x$, and the reference guide follows the same sections.

## Contents

- [1. Floating-point arithmetic and rounding error analysis](#1-floating-point-arithmetic-and-rounding-error-analysis), items 1.1–1.13.
- [2. Conditioning and matrix perturbation theory](#2-conditioning-and-matrix-perturbation-theory), items 2.1–2.18.
- [3. Direct methods for linear systems and least squares](#3-direct-methods-for-linear-systems-and-least-squares), items 3.1–3.16.
- [4. Eigenvalue and singular value computations](#4-eigenvalue-and-singular-value-computations), items 4.1–4.19.
- [5. Iterative methods for linear systems](#5-iterative-methods-for-linear-systems), items 5.1–5.18.
- [6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation](#6-matrix-functions-matrix-equations-and-low-rank-randomized-and-tensor-approximation), items 6.1–6.16.
- [7. Interval arithmetic and verified computation](#7-interval-arithmetic-and-verified-computation), items 7.1–7.14.
- [8. Nonlinear equations, continuation, and algorithmic differentiation](#8-nonlinear-equations-continuation-and-algorithmic-differentiation), items 8.1–8.16.
- [9. Numerical optimization](#9-numerical-optimization), items 9.1–9.17.
- [10. Polynomial and rational approximation](#10-polynomial-and-rational-approximation), items 10.1–10.17.
- [11. Splines, kernels and wavelets](#11-splines-kernels-and-wavelets), items 11.1–11.18.
- [12. Orthogonal polynomials and numerical quadrature](#12-orthogonal-polynomials-and-numerical-quadrature), items 12.1–12.16.
- [13. Discrete Fourier analysis and sparse recovery](#13-discrete-fourier-analysis-and-sparse-recovery), items 13.1–13.17.
- [14. Initial value problems: one-step and multistep methods](#14-initial-value-problems-one-step-and-multistep-methods), items 14.1–14.16.
- [15. Stiff problems, differential-algebraic equations, and geometric integration](#15-stiff-problems-differential-algebraic-equations-and-geometric-integration), items 15.1–15.17.
- [16. Finite difference methods for differential equations](#16-finite-difference-methods-for-differential-equations), items 16.1–16.15.
- [17. Hyperbolic conservation laws and finite volume methods](#17-hyperbolic-conservation-laws-and-finite-volume-methods), items 17.1–17.15.
- [18. Galerkin and finite element methods for elliptic problems](#18-galerkin-and-finite-element-methods-for-elliptic-problems), items 18.1–18.22.
- [19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation](#19-time-dependent-spectral-and-adaptive-galerkin-methods-and-eigenvalue-approximation), items 19.1–19.20.
- [20. Multilevel and domain decomposition methods](#20-multilevel-and-domain-decomposition-methods), items 20.1–20.11.
- [21. Integral equations and boundary element methods](#21-integral-equations-and-boundary-element-methods), items 21.1–21.16.
- [22. Inverse problems and regularization](#22-inverse-problems-and-regularization), items 22.1–22.16.
- [23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations](#23-monte-carlo-quasi-monte-carlo-and-stochastic-differential-equations), items 23.1–23.16.
- [24. High-dimensional approximation, uncertainty quantification, and model reduction](#24-high-dimensional-approximation-uncertainty-quantification-and-model-reduction), items 24.1–24.17.
- [Reference guide](#reference-guide).

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

This section covers the floating-point number system, rounding and the unit
roundoff, the standard model of arithmetic, exact operations and error-free
transformations, and the classical a priori rounding error bounds for sums,
inner products, matrix products, polynomial evaluation and triangular
systems. Floating-point numbers are real. A **floating-point format** is given
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

* **1.2. Spacing.** For $e_{\min}\le e\le e_{\max}$, consecutive elements of
  $\mathbb F$ in $[\beta^e,\beta^{e+1}]$ differ by exactly $\beta^{e-p+1}$,
  and the subnormal numbers together with $0$ are equally spaced with spacing
  $\alpha$. Consequently, if $x$ and its neighbour $y$ in $\mathbb F$ are both
  normal, then
  $$\beta^{-p}|x|\le|y-x|\le\beta^{1-p}|x|.$$

* **1.3. Rounding and correct rounding.** For real $x$, $\mathrm{RD}(x)$ is the
  largest element of $\mathbb F\cup\{-\infty\}$ not exceeding $x$,
  $\mathrm{RU}(x)$ the smallest element of $\mathbb F\cup\{+\infty\}$ not
  less than $x$, $\mathrm{RZ}(x)$ equals $\mathrm{RD}(x)$ for $x\ge0$ and
  $\mathrm{RU}(x)$ for $x\le0$, and a **round-to-nearest** function
  $\mathrm{RN}$ satisfies $|\mathrm{RN}(x)-x|\le|t-x|$ for every
  $t\in\mathbb F$, with a tie-breaking rule (ties to even: the neighbour with
  even integral significand). Each of these functions is nondecreasing and
  fixes every element of $\mathbb F$. An operation is **correctly rounded**
  for $\circ$ if it returns $\circ$ of the exact result. The IEEE 754-2008
  standard requires addition, subtraction, multiplication, division, square
  root and the fused multiply-add $(a,b,c)\mapsto\circ(ab+c)$ to be correctly
  rounded. Its binary32 format has $\beta=2$, $p=24$, $e_{\min}=-126$,
  $e_{\max}=127$, and its binary64 format has $\beta=2$, $p=53$,
  $e_{\min}=-1022$, $e_{\max}=1023$; with rounding to nearest, $u=2^{-24}$ and
  $u=2^{-53}$ respectively.

* **1.4. Relative error of rounding.** Let $x$ lie in the normal range. Then
  $\circ(x)=x(1+\delta)$ with $|\delta|<u$, for $\circ$ rounding to nearest
  (any tie rule) as well as for $\circ\in\{\mathrm{RD},\mathrm{RU},
  \mathrm{RZ}\}$ with the respective $u$. For rounding to nearest the sharper
  bound
  $$|\delta|\le\frac{u}{1+u}$$
  holds, and it is attained at $x=1+u$. If $|x|<\beta^{e_{\min}}$, then
  $|x-\mathrm{RN}(x)|\le\tfrac12\alpha$ and $|x-\circ(x)|<\alpha$ for directed
  roundings, while the relative error can be arbitrarily close to $1$.

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

* **1.6. Sterbenz lemma.** If $x,y\in\mathbb F$ satisfy $y/2\le x\le2y$, then
  $x-y\in\mathbb F$; hence $\circ(x-y)=x-y$ for every rounding function.

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

* **1.11. Horner's rule.** Let $a_0,\dots,a_n,x\in\mathbb F$ and
  $p(x)=\sum_{i=0}^na_ix^i$, evaluated by $q_n=a_n$,
  $q_i=\mathrm{fl}(\mathrm{fl}(x\,q_{i+1})+a_i)$ for $i=n-1,\dots,0$. Under the
  standard model,
  $$\hat q_0=\sum_{i=0}^{n-1}(1+\theta_{2i+1})a_ix^i+(1+\theta_{2n})a_nx^n,
  \qquad|\theta_k|\le\gamma_k,$$
  so
  $$|p(x)-\hat q_0|\le\gamma_{2n}\sum_{i=0}^n|a_i||x|^i.$$
  If each step is one fused multiply-add, $\gamma_{2n}$ may be replaced by
  $\gamma_n$.

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

## 2. Conditioning and matrix perturbation theory

This section covers condition numbers of maps and of linear systems, normwise
and componentwise backward errors, the distance to singularity, the
variational and perturbation theory of eigenvalues and singular values, the
sensitivity of least squares problems, and pseudospectra. A norm on
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

* **2.2. Condition number of matrix inversion.** Let $A\in\mathbb K^{n\times
  n}$ be nonsingular. Then
  $$\lim_{\varepsilon\to0}\ \sup_{\|\Delta A\|\le\varepsilon\|A\|}
  \frac{\|(A+\Delta A)^{-1}-A^{-1}\|}{\varepsilon\|A^{-1}\|}=\kappa(A)
  =\|A\|\,\|A^{-1}\|,$$
  and $\kappa_2(A)=\sigma_1(A)/\sigma_n(A)$.

* **2.3. Distance to singularity.** Let $A\in\mathbb K^{n\times n}$ be
  nonsingular. If $\|A^{-1}\|\,\|\Delta A\|<1$, then $A+\Delta A$ is
  nonsingular. Moreover (Gastinel–Kahan)
  $$\min\Bigl\{\frac{\|\Delta A\|}{\|A\|}:A+\Delta A\text{ singular}\Bigr\}
  =\frac1{\kappa(A)},$$
  and the minimum is attained by a matrix $\Delta A$ of rank one. In the
  $2$-norm the minimum of $\|\Delta A\|_2$ is $\sigma_n(A)$.

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

* **2.5. Normwise backward error (Rigal–Gaches).** Let $A\in\mathbb
  R^{n\times n}$, $b,y\in\mathbb R^n$, $E\in\mathbb R^{n\times n}$ and
  $f\in\mathbb R^n$ with $\|E\|\,\|y\|+\|f\|>0$, and put $r=b-Ay$. Then
  $$\eta_{E,f}(y):=\min\{\varepsilon:(A+\Delta A)y=b+\Delta b,\
  \|\Delta A\|\le\varepsilon\|E\|,\ \|\Delta b\|\le\varepsilon\|f\|\}
  =\frac{\|r\|}{\|E\|\,\|y\|+\|f\|}.$$

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

* **2.7. Courant–Fischer minimax theorem.** Let $A\in\mathbb C^{n\times n}$
  be Hermitian with eigenvalues $\lambda_1\ge\cdots\ge\lambda_n$, and let
  $R(x)=x^*Ax/x^*x$ for $x\ne0$. For $k=1,\dots,n$,
  $$\lambda_k=\max_{\dim S=k}\ \min_{0\ne x\in S}R(x)
  =\min_{\dim S=n-k+1}\ \max_{0\ne x\in S}R(x),$$
  the outer optimizations running over subspaces $S\subseteq\mathbb C^n$. In
  particular $\lambda_1=\max_{x\ne0}R(x)$ and $\lambda_n=\min_{x\ne0}R(x)$.

* **2.8. Weyl inequalities.** Let $A,B\in\mathbb C^{n\times n}$ be
  Hermitian, with eigenvalues in decreasing order. For $i,j\ge1$ with
  $i+j\le n+1$,
  $$\lambda_{i+j-1}(A+B)\le\lambda_i(A)+\lambda_j(B).$$
  In particular, for every $k$,
  $\lambda_k(A)+\lambda_n(B)\le\lambda_k(A+B)\le\lambda_k(A)+\lambda_1(B)$,
  so $|\lambda_k(A+B)-\lambda_k(A)|\le\|B\|_2$. If $B$ is positive
  semidefinite, then $\lambda_k(A+B)\ge\lambda_k(A)$ for every $k$.

* **2.9. Cauchy interlacing.** Let $A\in\mathbb C^{n\times n}$ be Hermitian.
  - If $\hat A=\begin{pmatrix}A&y\\ y^*&a\end{pmatrix}$ with
    $y\in\mathbb C^n$ and $a\in\mathbb R$, then
    $\lambda_1(\hat A)\ge\lambda_1(A)\ge\lambda_2(\hat A)\ge\lambda_2(A)\ge
    \cdots\ge\lambda_n(A)\ge\lambda_{n+1}(\hat A)$.
  - If $A_r$ is an $r\times r$ principal submatrix of $A$, $1\le r\le n$,
    then for $j=1,\dots,r$
    $$\lambda_{j+n-r}(A)\le\lambda_j(A_r)\le\lambda_j(A).$$

* **2.10. Perturbation of singular values.** Let
  $A,B\in\mathbb C^{m\times n}$ and $q=\min(m,n)$.
  - (Weyl) $|\sigma_i(A)-\sigma_i(B)|\le\|A-B\|_2$ for $i=1,\dots,q$.
  - (Mirsky) For every unitarily invariant norm $\|\cdot\|$ on
    $\mathbb C^{m\times n}$ (one with $\|UXV\|=\|X\|$ for all unitary $U,V$),
    $\|A-B\|\ge\|\Sigma(A)-\Sigma(B)\|$, where $\Sigma(\cdot)$ is the
    $m\times n$ diagonal matrix of the singular values in decreasing order.
    In particular
    $$\Bigl(\sum_{i=1}^q(\sigma_i(A)-\sigma_i(B))^2\Bigr)^{1/2}
    \le\|A-B\|_F.$$
  - (Interlacing) If $\hat A$ is $A$ with one column deleted and $m\ge n$,
    then $\sigma_1(A)\ge\sigma_1(\hat A)\ge\sigma_2(A)\ge\cdots\ge
    \sigma_{n-1}(\hat A)\ge\sigma_n(A)$; if $m<n$, then
    $\sigma_1(A)\ge\sigma_1(\hat A)\ge\cdots\ge\sigma_m(A)\ge
    \sigma_m(\hat A)\ge0$.

* **2.11. Hoffman–Wielandt theorem.** Let $A,E\in\mathbb C^{n\times n}$ with
  $A$ and $A+E$ normal, with eigenvalues $\lambda_1,\dots,\lambda_n$ and
  $\hat\lambda_1,\dots,\hat\lambda_n$ in some order. Then there is a
  permutation $\pi$ of $\{1,\dots,n\}$ with
  $$\Bigl(\sum_{i=1}^n|\hat\lambda_{\pi(i)}-\lambda_i|^2\Bigr)^{1/2}\le
  \|E\|_F.$$
  If $A$ and $B$ are Hermitian, then
  $\sum_{i=1}^n(\lambda_i(A)-\lambda_i(B))^2\le\|A-B\|_F^2$ with both spectra
  in decreasing order. The normality of both matrices cannot be dropped.

* **2.12. Gershgorin theorem.** Let $A=(a_{ij})\in\mathbb C^{n\times n}$ and
  $R_i=\{z\in\mathbb C:|z-a_{ii}|\le\sum_{j\ne i}|a_{ij}|\}$. Every
  eigenvalue of $A$ lies in $\bigcup_{i=1}^nR_i$. If $I\subseteq\{1,\dots,n\}$
  has $k$ elements and $\bigcup_{i\in I}R_i$ is disjoint from
  $\bigcup_{i\notin I}R_i$, then $\bigcup_{i\in I}R_i$ contains exactly $k$
  eigenvalues of $A$, counted with algebraic multiplicity. The same holds
  with column sums in place of row sums.

* **2.13. Bauer–Fike theorem.** Let $A=S\Lambda S^{-1}\in\mathbb C^{n\times
  n}$ with $\Lambda=\mathrm{diag}(\lambda_1,\dots,\lambda_n)$, let
  $E\in\mathbb C^{n\times n}$, and let $\|\cdot\|$ be a matrix norm with
  $\|D\|=\max_i|d_i|$ for every diagonal $D=\mathrm{diag}(d_1,\dots,d_n)$
  (for instance an induced $p$-norm). Then every eigenvalue $\mu$ of $A+E$
  satisfies
  $$\min_i|\mu-\lambda_i|\le\|S\|\,\|S^{-1}\|\,\|E\|.$$
  If $A$ is normal, then $\min_i|\mu-\lambda_i|\le\|E\|_2$.

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

* **2.17. Davis–Kahan $\sin\Theta$ theorem.** Let $A,B\in\mathbb C^{n\times n}$
  be Hermitian. Let $X,Y\in\mathbb C^{n\times r}$ have orthonormal columns
  spanning invariant subspaces of $A,B$, respectively, with $1\le r<n$.
  Suppose the spectrum of $X^*AX$ lies in $[a,b]$, and the spectrum of the
  restriction of $B$ to $(\mathrm{ran}\,Y)^\perp$ lies outside
  $(a-\delta,b+\delta)$, where $\delta>0$. If $\Theta$ is the diagonal
  matrix of principal angles between the two subspaces, whose cosines are
  the singular values of $X^*Y$, then in the spectral and Frobenius norms
  $$\|\sin\Theta\|\le\frac{\|(B-A)X\|}{\delta}
  \le\frac{\|B-A\|}{\delta}.$$

* **2.18. Wedin's singular subspace bound.** Let $A,B\in\mathbb C^{m\times n}$
  and let $1\le r<\min(m,n)$. Write $U_A,V_A$ and $U_B,V_B$ for orthonormal
  bases of their leading $r$ left and right singular subspaces, respectively,
  chosen from singular value decompositions. Suppose that
  $\sigma_{r+1}(A)\le a$ and $\sigma_r(B)\ge a+\delta$ with $a,\delta>0$.
  For $\Theta_U$ and $\Theta_V$ the diagonal matrices of principal angles
  between the corresponding left and right subspaces,
  $$\max\{\|\sin\Theta_U\|_2,\|\sin\Theta_V\|_2\}
  \le\frac{\|B-A\|_2}{\delta}.$$

## 3. Direct methods for linear systems and least squares

This section covers triangular factorizations and their existence, the rounding
error analysis of Gaussian elimination, Cholesky and Householder QR
factorization, linear least squares and the pseudoinverse, iterative
refinement, and the graph theory of sparse elimination. Rounding error
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

* **3.4. Growth factor.** For Gaussian elimination on $A\in\mathbb
  K^{n\times n}$, $A\ne0$, with reduced matrices
  $A=A^{(1)},A^{(2)},\dots,A^{(n)}=U$, the **growth factor** is
  $$\rho_n=\frac{\max_{i,j,k}|a^{(k)}_{ij}|}{\max_{i,j}|a_{ij}|}\ge1 .$$
  Let $A\in\mathbb R^{n\times n}$, $nu<1$, and suppose GEPP runs to
  completion and the computed factors satisfy $|\hat l_{ij}|\le1$ and
  $|\hat u_{ij}|\le\rho\max_{i,j}|a_{ij}|$ for some $\rho\ge1$. Then the
  computed solution $\widehat x$ of $Ax=b$ satisfies
  $$(A+\Delta A)\widehat x=b,\qquad
  \|\Delta A\|_\infty\le2n^2\gamma_n\,\rho\,\|A\|_\infty .$$
  In this sense the normwise backward stability of GEPP is governed by the
  growth factor of the computed reduced matrices.

* **3.5. Growth under partial pivoting.** For GEPP on any nonzero
  $A\in\mathbb K^{n\times n}$, $\rho_n\le2^{n-1}$, and $|u_{ij}|\le2^{i-1}
  \max_{k\le i}|a_{kj}|$ for the matrix $PA=(a_{kj})$ that is eliminated.
  The bound $2^{n-1}$ is attained for every $n$: for the matrix with
  $a_{ii}=1$, $a_{ij}=-1$ for $i>j$, $a_{in}=1$ for all $i$, and all other
  entries $0$, partial pivoting with ties broken in favour of the smallest
  row index makes no interchanges, and $u_{in}=2^{i-1}$, so
  $\rho_n=|u_{nn}|=2^{n-1}$.

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

### Cholesky and QR factorization

* **3.7. Cholesky factorization.** Every Hermitian positive definite
  $A\in\mathbb K^{n\times n}$ has a unique factorization $A=R^*R$ with $R$
  upper triangular and with positive real diagonal entries, the **Cholesky
  factorization**. Equivalently $A=GG^*$ with $G=R^*$ lower triangular. The
  diagonal entries satisfy $r_{kk}^2=\det A_k/\det A_{k-1}$, with
  $\det A_0:=1$.

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

* **3.9. QR factorization.** Let $A\in\mathbb K^{m\times n}$ with $m\ge n$.
  There is a unitary $Q\in\mathbb K^{m\times m}$ and an upper trapezoidal
  $R\in\mathbb K^{m\times n}$ with $A=QR$ (a **full QR factorization**);
  keeping the first $n$ columns of $Q$ and the first $n$ rows of $R$ gives a
  **reduced QR factorization** $A=Q_1R_1$ with $Q_1^*Q_1=I_n$ and $R_1$
  upper triangular. If $A$ has full column rank, the reduced QR
  factorization with positive real diagonal entries of $R_1$ is unique, the
  columns of $Q_1$ span $\mathop{\mathrm{range}}(A)$, and $R_1^*R_1$ is the
  Cholesky factorization of $A^*A$.

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

* **3.12. Moore–Penrose pseudoinverse.** For every $A\in\mathbb
  K^{m\times n}$ there is exactly one $X\in\mathbb K^{n\times m}$ satisfying
  the four **Penrose conditions**
  $$AXA=A,\qquad XAX=X,\qquad (AX)^*=AX,\qquad (XA)^*=XA .$$
  It is the **pseudoinverse** $A^+$. The matrix $AA^+$ is the orthogonal
  projector onto $\mathop{\mathrm{range}}(A)$ and $A^+A$ the orthogonal
  projector onto $\ker(A)^\perp$. If $A=U\Sigma V^*$ is a singular value
  decomposition with rank $r$ and nonzero singular values
  $\sigma_1,\dots,\sigma_r$, then
  $$A^+=V\Sigma^+U^*,\qquad
  \Sigma^+=\mathop{\mathrm{diag}}(\sigma_1^{-1},\dots,\sigma_r^{-1},0,\dots,0)
  \in\mathbb K^{n\times m}.$$
  Moreover $(A^+)^+=A$ and $(A^*)^+=(A^+)^*$; if $A$ has full column rank,
  $A^+=(A^*A)^{-1}A^*$; and if $A$ is square and nonsingular, $A^+=A^{-1}$.
  For every $b\in\mathbb K^m$, $x^+=A^+b$ solves the least squares problem
  of 3.11, and every other solution $x\ne x^+$ has $\|x\|_2>\|x^+\|_2$.

* **3.13. Backward stability of least squares by Householder QR.** Let $c$
  and $\tilde\gamma_m$ be as in 3.10, let $A\in\mathbb R^{m\times n}$,
  $m\ge n$, have full column rank, and assume $mn\tilde\gamma_m<1/2$. If the
  problem $\min_x\|b-Ax\|_2$ is solved by Householder QR factorization,
  application of the transformations to $b$, and back substitution, the
  computed $\widehat x$ is an exact solution of
  $$\min_x\|(b+\Delta b)-(A+\Delta A)x\|_2,$$
  where $\|\Delta A\|_F\le n\tilde\gamma_m\|A\|_F$,
  $\|\Delta b\|_2\le n\tilde\gamma_m\|b\|_2$, $|\Delta A|\le mn\tilde\gamma_m
  G|A|$ and $|\Delta b|\le mn\tilde\gamma_m G|b|$, for some $G\ge0$ with
  $\|G\|_F=1$.

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

## 4. Eigenvalue and singular value computations

This section covers the unitary normal forms on which eigenvalue algorithms
rest, the convergence of vector iterations and of the QR algorithm, the
structure that makes the QR algorithm efficient, the Jacobi method, backward
stability, Rayleigh–Ritz and Krylov approximation, bidiagonalization for the
singular value decomposition, and nonlinear eigenvalue problems. The
variational characterizations, interlacing for principal submatrices, and the
perturbation theorems for eigenvalues and singular values are in section 2.
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

* **4.2. Spectral theorems.** A matrix $A\in\mathbb C^{n\times n}$ is
  **normal** if $A^*A=AA^*$. The following are equivalent: $A$ is normal;
  $A=U\Lambda U^*$ with $U$ unitary and $\Lambda$ diagonal; $\mathbb C^n$ has
  an orthonormal basis of eigenvectors of $A$; and
  $\sum_{i,j}|a_{ij}|^2=\sum_i|\lambda_i|^2$. A matrix is Hermitian if and
  only if $A=U\Lambda U^*$ with $U$ unitary and $\Lambda$ real diagonal. A
  real matrix is symmetric if and only if $A=P\Lambda P^\top$ with $P$ real
  orthogonal and $\Lambda$ real diagonal.

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

* **4.9. Implicit Q theorem.** Let $A\in\mathbb C^{n\times n}$, let
  $Q=[q_1,\dots,q_n]$ and $U=[u_1,\dots,u_n]$ be unitary, and suppose that
  $H=Q^*AQ$ and $K=U^*AU$ are both upper Hessenberg, that
  $h_{i,i-1}\ne0$ for $2\le i\le n-1$, and that $u_1=\sigma q_1$ with
  $|\sigma|=1$. Then there is a phase matrix $S$ such that $U=QS$ and
  $K=S^*HS$.

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

* **4.11. Cyclic Jacobi method.** Let $A\in\mathbb R^{n\times n}$ be
  symmetric, $n\ge2$, and $\Psi(M)=\bigl(\sum_{i\ne j}m_{ij}^2\bigr)^{1/2}$.
  A **Jacobi rotation** in the plane $(p,q)$, $p<q$, replaces $A$ by
  $A'=G^\top AG$, where $G$ is the rotation by an angle $\theta$ in the
  coordinates $p,q$ with $a'_{pq}=0$; if $a_{pq}\ne0$, $t=\tan\theta$ is the
  root of smaller modulus of $t^2+2\eta t-1=0$,
  $\eta=(a_{qq}-a_{pp})/(2a_{pq})$, and if $a_{pq}=0$ then $G=I$. Then
  $$\Psi(A')^2=\Psi(A)^2-2a_{pq}^2 .$$
  The **row-cyclic Jacobi method** applies rotations in the planes
  $(1,2),\dots,(1,n),(2,3),\dots,(n-1,n)$, repeated cyclically; one sweep
  has $N=n(n-1)/2$ rotations. The iterates $A^{(k)}$ converge to a diagonal
  matrix whose diagonal entries are the eigenvalues of $A$. If the
  eigenvalues are distinct, with $\delta=\min_{i\ne j}|\lambda_i-\lambda_j|>0$,
  the convergence is ultimately quadratic per sweep: for all sufficiently
  large $k$,
  $$\Psi(A^{(k+N)})\le\frac{\Psi(A^{(k)})^2}{\sqrt2\,\delta}.$$

### Rayleigh–Ritz and Krylov methods

* **4.12. Rayleigh–Ritz and interlacing.** Let $A\in\mathbb C^{n\times n}$,
  let $Q\in\mathbb C^{n\times k}$ have orthonormal columns spanning a
  subspace $\mathcal S$, and let $H=Q^*AQ$. The eigenvalues $\theta$ of $H$
  are the **Ritz values** of $A$ with respect to $\mathcal S$, and the
  vectors $Qy$, $Hy=\theta y$, are the **Ritz vectors**. If $A$ is Hermitian
  and $\theta_1\ge\cdots\ge\theta_k$ are the Ritz values, then
  $$\lambda_i\ge\theta_i\ge\lambda_{n-k+i},\qquad i=1,\dots,k .$$
  This is the Poincaré separation theorem; it follows from the
  Courant–Fischer theorem of section 2.

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

* **4.15. Residual inclusion for normal matrices.** Let
  $A\in\mathbb C^{n\times n}$ be normal and $x\ne0$. For every polynomial
  $f$ there is an eigenvalue $\lambda$ of $A$ with
  $|f(\lambda)|\le\|f(A)x\|_2/\|x\|_2$. In particular (**Weinstein's
  bound**), with the Rayleigh quotient $\mu=x^*Ax/x^*x$, the disc
  $$\{z\in\mathbb C:|z-\mu|\le\|Ax-\mu x\|_2/\|x\|_2\}$$
  contains an eigenvalue of $A$. For Hermitian $A$ this bounds the error of a
  Ritz value of 4.12 with $k=1$ by its residual norm.

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

### Nonlinear eigenvalue problems

* **4.17. Nonlinear eigenvalue problems.** Let $\Omega\subseteq\mathbb C$
  be a domain and $F:\Omega\to\mathbb C^{n\times n}$ holomorphic. A number
  $\lambda\in\Omega$ is an **eigenvalue** of $F$ if $F(\lambda)v=0$ for some
  $v\ne0$ (a right eigenvector), equivalently $w^*F(\lambda)=0$ for some
  $w\ne0$ (a left eigenvector), that is, $\det F(\lambda)=0$. The set
  $\Lambda(F)$ of eigenvalues is closed in $\Omega$. The function $F$ is
  **regular** if $\det F$ does not vanish identically; then every eigenvalue
  is isolated. The **algebraic multiplicity** of $\lambda$ is its order as a
  zero of $\det F$ (finite when $F$ is regular, and possibly larger than $n$),
  and the **geometric multiplicity** is $\dim\ker F(\lambda)$. For regular
  $F$, a tuple $(v_0,\dots,v_{m-1})$ with $v_0\ne0$ is a **Jordan chain** at
  $\lambda$ if $v(z)=\sum_{k<m}(z-\lambda)^kv_k$ satisfies
  $F(z)v(z)=O((z-\lambda)^m)$. A complete system of Jordan chains exists,
  with lengths $m_1\ge\cdots\ge m_d$, $d$ the geometric multiplicity, where
  $v_0^1,\dots,v_0^d$ form a basis of $\ker F(\lambda)$ and each $m_j$ is
  the largest length of a Jordan chain starting with a vector of
  $\ker F(\lambda)$ outside $\mathrm{span}\{v_0^1,\dots,v_0^{j-1}\}$. These
  **partial multiplicities** sum to the algebraic multiplicity.

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

* **4.19. Companion linearization.** Let
  $P(z)=\sum_{j=0}^{\ell}z^jD_j$ with $D_j\in\mathbb C^{n\times n}$ and
  $\ell\ge1$, and let $L(z)\in\mathbb C^{\ell n\times\ell n}$ be the pencil
  with first block row $(D_0,D_1,\dots,D_{\ell-2},D_{\ell-1}+zD_\ell)$ and,
  for $2\le j\le\ell$, block row $j$ equal to $-zI_n$ in block column $j-1$,
  $I_n$ in block column $j$, and $0$ elsewhere. With
  $b(z)=(1,z,\dots,z^{\ell-1})^\top$,
  $$L(z)\bigl(b(z)\otimes v\bigr)=e_1\otimes P(z)v,\qquad
  \det L(z)=\det P(z)$$
  for all $z\in\mathbb C$ and $v\in\mathbb C^n$. Hence
  $\ker L(\lambda)=\{b(\lambda)\otimes v:v\in\ker P(\lambda)\}$ for every
  $\lambda$; $L$ is regular if and only if $P$ is; and $L$ and $P$ have the
  same eigenvalues with the same algebraic and geometric multiplicities. If
  $w$ is a left eigenvector of $L$ for $\lambda$ and its first block
  $(e_1\otimes I_n)^*w$ is nonzero, that block is a left eigenvector of $P$.

## 5. Iterative methods for linear systems

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

* **5.1. Convergent matrices and splitting iterations.** For $G\in\mathbb
  C^{n\times n}$, $G^k\to O$ as $k\to\infty$ if and only if $\rho(G)<1$. For
  every matrix norm induced by a vector norm,
  $\rho(G)=\lim_{k\to\infty}\|G^k\|^{1/k}$. Let $A=M-N$ be a splitting of the
  nonsingular matrix $A$ and $x^*=A^{-1}b$. The errors of the iteration satisfy
  $x_k-x^*=G^k(x_0-x^*)$ with $G=M^{-1}N$, so $x_k\to x^*$ for every starting
  vector $x_0$ if and only if $\rho(M^{-1}N)<1$.

* **5.2. Perron–Frobenius theorem.** A matrix $A\in\mathbb C^{n\times n}$ with
  $n\ge2$ is **reducible** if there is a permutation matrix $P$ such that
  $$PAP^\top=\begin{pmatrix}A_{11}&A_{12}\\ O&A_{22}\end{pmatrix}$$
  with square blocks $A_{11}$, $A_{22}$ of orders $r$ and $n-r$, $1\le r<n$;
  otherwise it is **irreducible**. Equivalently, $A$ is irreducible if and only
  if the directed graph with an arc $i\to j$ whenever $a_{ij}\ne0$ is strongly
  connected. A $1\times1$ matrix is irreducible if and only if its entry is
  nonzero. Let $A\ge O$ be irreducible. Then:
  - $\rho(A)>0$, and $\rho(A)$ is an eigenvalue of $A$;
  - there is an eigenvector $x>0$ with $Ax=\rho(A)x$;
  - $\rho(A)$ is an algebraically simple eigenvalue;
  - if $A'\ge A$ and $A'\ne A$, then $\rho(A')>\rho(A)$.

* **5.3. Diagonal dominance.** A matrix $A$ is **diagonally dominant** if
  $|a_{ii}|\ge\sum_{j\ne i}|a_{ij}|$ for all $i$; **strictly diagonally
  dominant** if all these inequalities are strict; and **irreducibly diagonally
  dominant** if it is irreducible, diagonally dominant, and at least one of the
  inequalities is strict. A strictly or irreducibly diagonally dominant matrix
  is nonsingular, and if its diagonal entries are real and positive, all its
  eigenvalues have positive real part. For such a matrix the Jacobi and the
  Gauss–Seidel iterations converge for every starting vector:
  $\rho(B_J)<1$ and $\rho(\mathcal L_1)<1$.

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

* **5.6. Comparison of regular splittings.** Let $A=M_1-N_1=M_2-N_2$ be two
  regular splittings with $A^{-1}\ge O$.
  - If $N_2\ge N_1$, then $1>\rho(M_2^{-1}N_2)\ge\rho(M_1^{-1}N_1)\ge0$.
  - If moreover $A^{-1}>O$, $N_1\ne O$ and $N_2\ne N_1$, then
    $1>\rho(M_2^{-1}N_2)>\rho(M_1^{-1}N_1)>0$.

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

* **5.8. Kahan's bound.** Let $B=L+U\in\mathbb C^{n\times n}$ with $L$
  strictly lower and $U$ strictly upper triangular, and let $\mathcal
  L_\omega=(I-\omega L)^{-1}((1-\omega)I+\omega U)$. Then for every
  $\omega\in\mathbb C$,
  $$\rho(\mathcal L_\omega)\ge|\omega-1|,$$
  with equality only if all eigenvalues of $\mathcal L_\omega$ have modulus
  $|\omega-1|$. Hence SOR with real $\omega$ can converge for every starting
  vector only if $0<\omega<2$.

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

* **5.13. Conjugate gradients: condition-number bound.** With $A$ Hermitian
  positive definite and $\kappa=\kappa_2(A)=\lambda_{\max}(A)/\lambda_{\min}(A)$,
  the CG iterates satisfy, for every $k\ge0$,
  $$\frac{\|x_k-x^*\|_A}{\|x_0-x^*\|_A}\le
  \frac{2c^k}{1+c^{2k}}\le2\Bigl(\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\Bigr)^k,
  \qquad c=\frac{\sqrt\kappa-1}{\sqrt\kappa+1}.$$

* **5.14. GMRES.** For $A$ nonsingular, the $k$-th **GMRES** iterate $x_k$ is the
  minimizer of $\|b-Ax\|_2$ over $x\in x_0+\mathcal K_k(A,r_0)$; its residual
  $r_k=b-Ax_k$ satisfies $\|r_{k+1}\|_2\le\|r_k\|_2$ and
  $$\|r_k\|_2=\min_{p\in\mathcal P_k^0}\|p(A)r_0\|_2.$$
  If $A=V\Lambda V^{-1}$ is diagonalizable, then
  $$\frac{\|r_k\|_2}{\|r_0\|_2}\le\kappa_2(V)\min_{p\in\mathcal P_k^0}
  \max_{\lambda\in\Lambda(A)}|p(\lambda)|.$$

* **5.15. Any nonincreasing residual curve is possible for GMRES.** Let
  $f_0\ge f_1\ge\cdots\ge f_{n-1}>0$, and let $\lambda_1,\dots,\lambda_n$ be
  nonzero complex numbers. Then there are $A\in\mathbb C^{n\times n}$ with
  eigenvalues $\lambda_1,\dots,\lambda_n$ (counted with algebraic multiplicity)
  and $b\in\mathbb C^n$ such that GMRES with $x_0=0$ produces residuals with
  $\|r_k\|_2=f_k$ for $k=0,1,\dots,n-1$ (and $r_n=0$). Thus no statement about
  the convergence of GMRES can depend on the eigenvalues alone.

* **5.16. Minimal residuals for Hermitian matrices (MINRES).** Let $A$ be
  Hermitian and nonsingular, possibly indefinite, and let $x_k$ minimize
  $\|b-Ax\|_2$ over $x_0+\mathcal K_k(A,r_0)$. Put
  $\kappa=\max_{\lambda\in\Lambda(A)}|\lambda|/\min_{\lambda\in\Lambda(A)}|\lambda|$
  and $c=(\kappa-1)/(\kappa+1)$. Then for every $k\ge0$, with
  $\mu=\lfloor k/2\rfloor$,
  $$\|r_k\|_2\le\frac{2c^\mu}{1+c^{2\mu}}\,\|r_0\|_2.$$

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

* **5.18. GMRES field-of-values bound.** Let $A\in\mathbb C^{n\times n}$
  with $n\ge1$. Its **field of values** is
  $W(A)=\{v^*Av:\|v\|_2=1\}$. If $\nu=\min_{z\in W(A)}|z|>0$, then
  $A$ is nonsingular and the GMRES residuals of 5.14 satisfy
  $$\|r_k\|_2\le
  \left(1-\frac{\nu^2}{\|A\|_2^2}\right)^{k/2}\|r_0\|_2
  \qquad(k\ge1).$$
  Iterates after exact termination are taken to be the exact solution.

## 6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation

This section covers functions of a square matrix and their conditioning,
the Sylvester and Lyapunov equations, best low-rank approximation of
matrices, randomized range finding and random embeddings, low-rank formats
for tensors, and hierarchical matrices. Matrices are complex unless a
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

* **6.3. Principal roots, logarithm and sign.** Write
  $\mathbb R^-=(-\infty,0]$. Let $A$ have no eigenvalue in $\mathbb R^-$
  and let $p\in\mathbb N$. There is a unique $X$ with $X^p=A$ all of whose
  eigenvalues lie in the sector $\{z:-\pi/p<\arg z<\pi/p\}$; it is a primary
  matrix function of $A$, the **principal $p$-th root** $A^{1/p}$, and it is
  real if $A$ is real. There is a unique $X$ with $e^X=A$ all of whose
  eigenvalues lie in the strip $\{z:|\mathrm{Im}\,z|<\pi\}$; it is the
  **principal logarithm** $\log A$, and it is real if $A$ is real. For any
  $B$, $\log(e^B)=B$ holds if and only if $|\mathrm{Im}\,\lambda|<\pi$ for
  every eigenvalue $\lambda$ of $B$. If $A$ has no purely imaginary
  eigenvalue, and $A=Z\,\mathrm{diag}(J_1,J_2)Z^{-1}$ with the eigenvalues
  of $J_1\in\mathbb C^{p\times p}$ in the open left half-plane and those of
  $J_2\in\mathbb C^{q\times q}$ in the open right half-plane, then the
  **matrix sign function** is
  $$\mathrm{sign}(A)=Z\,\mathrm{diag}(-I_p,I_q)\,Z^{-1}=A\,(A^2)^{-1/2}.$$

* **6.4. Fréchet derivative and condition number.** Let $f$ map an open
  subset of $\mathbb C^{n\times n}$ into $\mathbb C^{n\times n}$. Its
  **Fréchet derivative** at $A$ is the linear map $L_f(A):E\mapsto
  L_f(A,E)$ with $f(A+E)-f(A)-L_f(A,E)=o(\|E\|)$.
  - If $f$ is holomorphic on an open set containing $\Lambda(A)$, or $A$ has
    real spectrum and $f$ is $2n-1$ times continuously differentiable on an
    open interval containing $\Lambda(A)$, then $L_f(A)$ exists and
    $$f\begin{pmatrix}A&E\\0&A\end{pmatrix}=
    \begin{pmatrix}f(A)&L_f(A,E)\\0&f(A)\end{pmatrix}.$$
  - With $\|L_f(A)\|=\max_{\|Z\|=1}\|L_f(A,Z)\|$ for a given matrix norm,
    and $f(A)\ne0$, the relative **condition number**
    $$\mathrm{cond}(f,A)=\lim_{\varepsilon\to0}\ \sup_{\|E\|\le\varepsilon\|A\|}
    \frac{\|f(A+E)-f(A)\|}{\varepsilon\|f(A)\|}$$
    equals $\|L_f(A)\|\,\|A\|/\|f(A)\|$.
  - If $f(x)=\sum_{k\ge0}a_kx^k$ has radius of convergence $r$ and
    $\|A\|<r$ for a submultiplicative norm, then
    $$L_f(A,E)=\sum_{k\ge1}a_k\sum_{j=1}^kA^{j-1}EA^{k-j},$$
    and $\|f(A)\|\le\tilde f(\|A\|)$ and $\|L_f(A)\|\le\tilde f'(\|A\|)$,
    where $\tilde f(x)=\sum_{k\ge0}|a_k|x^k$.

* **6.5. Padé approximation of the exponential and scaling and squaring.**
  For $k,m\in\mathbb N_0$ the $[k/m]$ Padé approximant of $e^x$ is
  $r_{km}=p_{km}/q_{km}$ with
  $$p_{km}(x)=\sum_{j=0}^k\frac{(k+m-j)!\,k!}{(k+m)!\,(k-j)!\,j!}x^j,\qquad
  q_{km}(x)=\sum_{j=0}^m\frac{(k+m-j)!\,m!}{(k+m)!\,(m-j)!\,j!}(-x)^j;$$
  it satisfies $e^x-r_{km}(x)=O(x^{k+m+1})$, and it is the unique rational
  function with numerator degree at most $k$, denominator degree at most
  $m$ and $q(0)=1$ with this property. Write $r_m=r_{mm}$, let $\nu_m$ be
  the smallest modulus of a zero of $q_{mm}$, and let
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

### Low-rank and randomized approximation

* **6.8. Schmidt–Eckart–Young–Mirsky theorem.** Let $A\in\mathbb K^{m\times
  n}$ have the singular value decomposition $A=\sum_{j=1}^p\sigma_ju_jv_j^*$,
  $p=\min\{m,n\}$, and put $\sigma_{p+1}=0$. For $0\le k\le p$ let
  $A_k=\sum_{j=1}^k\sigma_ju_jv_j^*$. Then
  $$\min_{\mathrm{rank}\,B\le k}\|A-B\|_2=\|A-A_k\|_2=\sigma_{k+1},\qquad
  \min_{\mathrm{rank}\,B\le k}\|A-B\|_F=\|A-A_k\|_F
  =\Bigl(\sum_{j=k+1}^p\sigma_j^2\Bigr)^{1/2}.$$

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

* **6.11. Nyström approximation.** Let $A\in\mathbb R^{n\times n}$ be
  symmetric positive semidefinite with eigenvalues
  $\lambda_1\ge\lambda_2\ge\cdots\ge\lambda_n$. For a test matrix
  $X\in\mathbb R^{n\times\ell}$ the **Nyström approximation**
  $$A\langle X\rangle=(AX)(X^*AX)^\dagger(AX)^*=A^{1/2}P_{A^{1/2}X}A^{1/2}$$
  is positive semidefinite, depends only on the range of $X$, and
  $A-A\langle X\rangle$ is positive semidefinite. Let $1\le k<\ell-1$,
  $\ell\le n$, let $\Omega\in\mathbb R^{n\times\ell}$ be standard normal, and
  let $\hat A_k$ be a best rank-$k$ approximation of $A\langle\Omega\rangle$
  in the Frobenius norm. Then
  $$\mathbb E\|A-\hat A_k\|\le\lambda_{k+1}+\frac{k}{\ell-k-1}
  \sum_{j>k}\lambda_j.$$

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

### Hierarchical matrices

Let $I$ and $J$ be finite index sets and let each index $i$ have a support
$X_i\subset\mathbb R^m$ (for example the support of a basis function). For
$\tau\subset I$ put $X_\tau=\bigcup_{i\in\tau}X_i$, and define $Y_\sigma$
for $\sigma\subset J$ alike. A **cluster tree** $T(I)$ is a tree of subsets
of $I$ with root $I$ in which the sons of each non-leaf cluster partition
it; a **block partition** $P$ is a set of disjoint blocks $\tau\times\sigma$
with $\tau\in T(I)$, $\sigma\in T(J)$, covering $I\times J$.

* **6.15. Admissibility, hierarchical matrices and their cost.** For
  $\eta>0$ a block $\tau\times\sigma$ is **$\eta$-admissible** if
  $$\min\{\mathrm{diam}\,X_\tau,\mathrm{diam}\,Y_\sigma\}\le\eta\,
  \mathrm{dist}(X_\tau,Y_\sigma).$$
  Let $P=P^+\cup P^-$ with $P^+$ consisting of admissible blocks and every
  block in $P^-$ satisfying $\min\{\#\tau,\#\sigma\}\le n_{\min}$. For
  $r\in\mathbb N_0$ the set $\mathcal H(r,P)$ of **hierarchical matrices**
  consists of the $M\in\mathbb R^{I\times J}$ with $\mathrm{rank}\,M|_b\le r$
  for $b\in P^+$, stored as $M|_b=A_bB_b^*$ with $r$ columns in $A_b$ and
  $B_b$, the blocks in $P^-$ being stored in full. The storage is
  $S=r\sum_{P^+}(\#\tau+\#\sigma)+\sum_{P^-}\#\tau\,\#\sigma$. With the
  **sparsity constant**
  $$C_{\mathrm{sp}}(P)=\max\Bigl\{\max_{\tau}\#\{\sigma:\tau\times\sigma\in
  P\},\ \max_\sigma\#\{\tau:\tau\times\sigma\in P\}\Bigr\},$$
  one has
  $$S\le C_{\mathrm{sp}}(P)\max\{n_{\min},r\}\bigl((\mathrm{depth}\,T(I)+1)
  \#I+(\mathrm{depth}\,T(J)+1)\#J\bigr),$$
  and the number $N_{MV}$ of arithmetic operations of a matrix-vector
  product satisfies $S\le N_{MV}\le2S$. If no cluster has exactly one son,
  then $\#P\le(2\min\{\#I,\#J\}-1)\,C_{\mathrm{sp}}(P)$. For balanced trees
  of depth $O(\log n)$ and bounded $C_{\mathrm{sp}}$ this gives storage and
  matrix-vector cost $O(\max\{r,n_{\min}\}\,n\log n)$, $n=\#I+\#J$.

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

## 7. Interval arithmetic and verified computation

This section covers real interval arithmetic and its enclosure property, the
order of overestimation of interval extensions, outward rounding, and the
existence and enclosure theorems behind verification methods. These are the
interval Newton and Krawczyk tests for nonlinear systems, the verification
theorems for linear systems, and the abstract Newton–Kantorovich-type
theorem used in computer-assisted proofs for elliptic boundary value
problems. In this section $\mathbb{IR}$ is the set of nonempty compact real
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

* **7.2. Algebraic properties and inclusion isotonicity.** For
  $X,Y,Z\in\mathbb{IR}$, addition and multiplication are commutative and
  associative, and
  - **subdistributivity:** $X\cdot(Y+Z)\subseteq X\cdot Y+X\cdot Z$, with
    equality when $X$ is a point interval or when $yz\ge0$ for all $y\in Y$,
    $z\in Z$;
  - if $w(X)>0$, there is no $Y\in\mathbb{IR}$ with $X+Y=[0,0]$, and,
    when $0\notin X$, no $Y$ with $X\cdot Y=[1,1]$; always
    $0\in X-X$, and $1\in X/X$ when $0\notin X$;
  - **inclusion isotonicity:** if $X\subseteq X'$ and $Y\subseteq Y'$, then
    $X\circ Y\subseteq X'\circ Y'$ for $\circ\in\{+,-,\cdot\}$, and also for
    division when $0\notin Y'$.

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

* **7.4. Interval vectors and matrices.** Interval matrix–vector products
  are defined by the usual formulas with interval operations. If
  $A\in\mathbb{IR}^{m\times n}$ contains the matrix $A_0$ and
  $X\in\mathbb{IR}^n$ contains $x$, then $A_0x\in AX$.
  - If $x\in\mathbb R^n$ is a point vector, then
    $Ax=\{A_0x:A_0\in A\}$ exactly.
  - If $A\in\mathbb R^{m\times n}$ is a point matrix, then $AX$ is the hull
    of $\{Ax:x\in X\}$, and in midpoint–radius form
    $$AX=\bigl[A\mathop{\mathrm{mid}}X-|A|\mathop{\mathrm{rad}}X,\
    A\mathop{\mathrm{mid}}X+|A|\mathop{\mathrm{rad}}X\bigr].$$
    In general $AX$ is strictly larger than $\{Ax:x\in X\}$. In particular
    $b\in AX$ does not imply $A^{-1}b\in X$. For
    $A=\begin{pmatrix}2&-1\\1&2\end{pmatrix}$ and $X=[2,3]\times[1,3]$ one
    has $AX=[1,5]\times[4,9]\ni(4,8)^\top$, but
    $A^{-1}(4,8)^\top=(3.2,2.4)^\top\notin X$.

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

* **7.6. Verified nonsingularity with directed rounding.** For
  $x,y\in\mathbb F^n$, let $d_1$ be the sum of the
  $\mathrm{RD}(x_iy_i)$ computed with every addition rounded downward, in
  any order, and $d_2$ the corresponding upward-rounded quantity. Then
  $d_1\le x^\top y\le d_2$. Let $A,R\in\mathbb F^{n\times n}$. Compute
  $C_1$, an evaluation of $RA-I$ with every operation rounded downward, and
  $C_2$, the same with every operation rounded upward. Let
  $C=\max(|C_1|,|C_2|)$ entrywise and let $c$ be $\|C\|_\infty$ computed
  with upward rounding. Then $C_1\le RA-I\le C_2$ entrywise and
  $\rho(I-RA)\le\|I-RA\|_\infty\le c$. If $c<1$, then $A$ and $R$ are
  nonsingular. If $I-RA$ is evaluated instead of $RA-I$, the
  multiplication and the subtraction must be rounded in opposite
  directions for the same conclusion.

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

### Nonlinear systems

* **7.8. Univariate interval Newton operator.** Let $X=[a,b]\in\mathbb{IR}$,
  let $f:X\to\mathbb R$ be continuously differentiable, let
  $\tilde x\in X$, and let $D\in\mathbb{IR}$ satisfy $f'(x)\in D$ for all
  $x\in X$ and $0\notin D$. Put
  $N(\tilde x,X)=\tilde x-f(\tilde x)/D$, computed by interval operations.
  - Every zero of $f$ in $X$ lies in $N(\tilde x,X)$.
  - If $N(\tilde x,X)\subseteq X$, then $f$ has exactly one zero in $X$.
  - If $N(\tilde x,X)\cap X=\emptyset$, then $f$ has no zero in $X$.

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

### Linear systems

* **7.11. Norm-based verification for linear systems.** Let
  $A,R\in\mathbb R^{n\times n}$ and $b,\tilde x\in\mathbb R^n$.
  - If $\rho(I-RA)<1$, then $A$ and $R$ are nonsingular.
  - If $\|I-RA\|<1$ for a matrix norm induced by a vector norm $\|\cdot\|$,
    then $A$ and $R$ are nonsingular and
    $$\|A^{-1}b-\tilde x\|\le\frac{\|R(b-A\tilde x)\|}{1-\|I-RA\|}.$$

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

## 8. Nonlinear equations, continuation, and algorithmic differentiation

This section covers fixed-point iteration, the scalar methods of bisection
and secants, the local and semilocal convergence theory of Newton's method
and its damped, inexact, quasi-Newton and Gauss–Newton variants, the
following of solution curves by continuation, and the forward and reverse
modes of algorithmic differentiation with their cost bounds. Unless stated
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

* **8.1. Banach fixed-point theorem.** Let $K$ be a nonempty closed subset
  of a Banach space $V$, and let $T:K\to K$ be a **contraction**, that is,
  $\|T(u)-T(v)\|\le\alpha\|u-v\|$ for all $u,v\in K$ with a constant
  $0\le\alpha<1$. Then $T$ has exactly one fixed point $u^*\in K$. For every
  $u_0\in K$ the iterates $u_{n+1}=T(u_n)$ converge to $u^*$, and for
  $n\ge1$
  $$\|u_n-u^*\|\le\frac{\alpha^n}{1-\alpha}\|u_1-u_0\|,\qquad
  \|u_n-u^*\|\le\frac{\alpha}{1-\alpha}\|u_n-u_{n-1}\|,\qquad
  \|u_n-u^*\|\le\alpha\|u_{n-1}-u^*\|.$$
  The first bound is the **a priori** bound and the second the **a
  posteriori** bound. The same conclusions hold for a contraction of a
  complete metric space into itself, with distances in place of norms.

* **8.2. Local convergence of fixed-point iteration.**
  - (Ostrowski) Let $G:D\subset\mathbb R^n\to\mathbb R^n$ have a fixed point
    $x^*$ in the interior of $D$, let $G$ be continuously differentiable in a
    neighbourhood of $x^*$, and let $\rho(G'(x^*))<1$. Then there is a
    neighbourhood $S\subset D$ of $x^*$ such that for every $x^0\in S$ the
    iterates $x^{k+1}=G(x^k)$ lie in $D$ and converge to $x^*$.
  - (Order of a scalar iteration) Let $\varphi$ have the fixed point
    $\alpha\in\mathbb R$, let $I_\varepsilon=[\alpha-\varepsilon,
    \alpha+\varepsilon]$ with $\varepsilon>0$, let $p\ge1$ be an integer and
    $\varphi\in C^p(I_\varepsilon)$ with
    $$\varphi'(\alpha)=\cdots=\varphi^{(p-1)}(\alpha)=0,\qquad
    \varphi^{(p)}(\alpha)\ne0,$$
    and assume $\max_{t\in I_\varepsilon}|\varphi'(t)|<1$. Then for every
    $x_0\in I_\varepsilon$ the iterates $x_{n+1}=\varphi(x_n)$ stay in
    $I_\varepsilon$ and converge to $\alpha$, and if $x_n\ne\alpha$ for all
    $n$, then
    $$\lim_{n\to\infty}\frac{x_{n+1}-\alpha}{(x_n-\alpha)^p}
    =\frac{\varphi^{(p)}(\alpha)}{p!}.$$

* **8.3. Bisection.** Let $f\in C[a,b]$ with $a<b$, $f(a)<0$ and $f(b)>0$.
  Put $a_1=a$, $b_1=b$, and for $n\ge1$ let $x_n=\frac12(a_n+b_n)$; if
  $f(x_n)<0$, put $a_{n+1}=x_n$, $b_{n+1}=b_n$, and otherwise
  $a_{n+1}=a_n$, $b_{n+1}=x_n$. Then $f(a_n)<0\le f(b_n)$ and
  $b_n-a_n=2^{-(n-1)}(b-a)$ for all $n$. The sequences $(a_n)$ and $(b_n)$
  converge to a common limit $\alpha\in[a,b]$ with $f(\alpha)=0$, and
  $$|x_n-\alpha|\le\frac{b-a}{2^n},\qquad n\ge1.$$

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

* **8.7. Affine-covariant Kantorovich and Newton–Mysovskikh theorems.**
  - Let $X,Y$ be Banach spaces, $D\subset X$ open and convex,
    $F:D\to Y$ continuously Fréchet differentiable, and $x^0\in D$ with
    $F'(x^0)$ invertible. Let $\alpha\ge0$ and $\omega_0>0$ satisfy
    $$\|F'(x^0)^{-1}F(x^0)\|\le\alpha,\qquad
    \|F'(x^0)^{-1}(F'(y)-F'(x))\|\le\omega_0\|y-x\|\quad(x,y\in D),$$
    $h_0:=\alpha\omega_0\le\frac12$, and
    $\bar B(x^0,\rho_-)\subset D$ with
    $\rho_-=(1-\sqrt{1-2h_0})/\omega_0$. Then the Newton iterates are well
    defined, remain in $\bar B(x^0,\rho_-)$, and converge to a zero $x^*$
    of $F$; if $h_0<\frac12$ the convergence is Q-quadratic. If moreover
    $h_0<\frac12$ and $\bar B(x^0,\rho_+)\subset D$ with
    $\rho_+=(1+\sqrt{1-2h_0})/\omega_0$, then $x^*$ is the only zero of
    $F$ in $B(x^0,\rho_+)$.
  - Let $D\subset\mathbb R^n$ be convex, $F\in C^1(D;\mathbb R^n)$ with
    $F'(x)$ invertible for all $x\in D$, and let
    $$\|F'(z)^{-1}(F'(y)-F'(x))(y-x)\|\le\omega\|y-x\|^2$$
    for all collinear $x,y,z\in D$. Let $x^0\in D$ satisfy
    $h_0:=\omega\|\Delta x^0\|<2$ and $\bar B(x^0,\rho)\subset D$ with
    $\rho=\|\Delta x^0\|/(1-\frac12h_0)$. Then the Newton iterates remain
    in $\bar B(x^0,\rho)$ and converge to a zero $x^*\in\bar B(x^0,\rho)$,
    and for $k\ge1$
    $$\|x^{k+1}-x^k\|\le\tfrac12\omega\|x^k-x^{k-1}\|^2,\qquad
    \|x^k-x^*\|\le\frac{\|x^{k+1}-x^k\|}{1-\frac12\omega\|x^{k+1}-x^k\|}.$$

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

### Continuation

* **8.12. Solution curves.** Let $D\subset\mathbb R^n$ be open,
  $F\in C^1(D\times(a,b);\mathbb R^n)$, and let $(x_0,\lambda_0)$ satisfy
  $F(x_0,\lambda_0)=0$.
  - If $F_x(x_0,\lambda_0)$ is invertible, there are $\varepsilon>0$, a
    neighbourhood $U$ of $(x_0,\lambda_0)$ and a $C^1$ map
    $x:(-\varepsilon,\varepsilon)\to D$ with $x(0)=x_0$ such that the zeros
    of $F$ in $U$ are exactly the points $(x(s),\lambda_0+s)$, and
    $$F_x(x(s),\lambda_0+s)\,x'(s)=-F_\lambda(x(s),\lambda_0+s).$$
    If $F\in C^m$, then $x\in C^m$.
  - If only the $n\times(n+1)$ Jacobian $F'(x_0,\lambda_0)$ has rank $n$,
    there are a neighbourhood $U$ and $C^1$ maps $x$ and $\lambda$ on
    $(-\varepsilon,\varepsilon)$ with $(x(0),\lambda(0))=(x_0,\lambda_0)$
    such that the zeros of $F$ in $U$ are exactly the points
    $(x(s),\lambda(s))$.

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

* **8.16. Jacobian compression.** Let $A=F'(x)\in\mathbb R^{m\times n}$ have
  a known sparsity pattern. Two columns are **structurally orthogonal** if
  no row has a structural nonzero in both. Let $c:\{1,\dots,n\}\to
  \{1,\dots,p\}$ give different values to any two columns that are not
  structurally orthogonal, that is, $c$ is a colouring of the **column
  incidence graph**, and let the **seed matrix** $S\in\mathbb R^{n\times p}$
  have $j$-th row $e_{c(j)}^\top$. Then every structural nonzero of $A$ is
  an entry of $B=AS$: $a_{ij}=b_{i,c(j)}$. The least possible $p$ is the
  chromatic number of the column incidence graph. By 8.15, $A$ is obtained
  at a cost of at most $\omega_{\mathrm{tang}_p}\le1+1.5p$ times that of
  evaluating $F$. Row compression with the reverse mode is analogous. If
  some row of $A$ has no structural zero, the column incidence graph is
  complete and $p=n$; the cost of a full Jacobian is not in general a
  bounded multiple of the cost of $F$.

## 9. Numerical optimization

This section collects optimality conditions, the convergence theory of
line-search, Newton, quasi-Newton and trust-region methods, complexity
bounds for first-order methods in convex optimization, monotone operator
splitting, interior-point theory for self-concordant barriers, gradient
descent on manifolds, discrete optimal transport, and the first-order
optimality system of a linear-quadratic optimal control problem. Unless
stated otherwise, the space is $\mathbb R^n$ with the Euclidean inner
product and norm, $f^*$ is the optimal value, $x^*$ is a minimizer, and
$\nabla f_k=\nabla f(x_k)$. A function is **$L$-smooth** on a set when it is
differentiable there and its gradient is Lipschitz continuous with constant
$L$. A differentiable function $f$ is **$\mu$-strongly convex**, $\mu>0$, if
$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac\mu2\|y-x\|^2$ for all
$x,y$. Newton's method for nonlinear equations, Broyden's method, and the
Gauss–Newton method are in section 8.

### Optimality conditions

* **9.1. Unconstrained optimality conditions.** Let $f:\mathbb R^n\to\mathbb R$.
  - If $x^*$ is a local minimizer and $f$ is continuously differentiable in an
    open neighbourhood of $x^*$, then $\nabla f(x^*)=0$.
  - If $x^*$ is a local minimizer and $\nabla^2f$ exists and is continuous in an
    open neighbourhood of $x^*$, then $\nabla^2f(x^*)$ is positive semidefinite.
  - If $\nabla^2f$ is continuous in an open neighbourhood of $x^*$,
    $\nabla f(x^*)=0$ and $\nabla^2f(x^*)$ is positive definite, then $x^*$ is a
    **strict local minimizer**: $f(x)>f(x^*)$ for all $x\ne x^*$ in some
    neighbourhood of $x^*$.
  - If $f$ is convex and continuously differentiable on $\mathbb R^n$ and
    $\nabla f(x^*)=0$, then $x^*$ is a global minimizer.

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

* **9.4. Local convergence of Newton's method for minimization.** Let $f$ be
  twice differentiable, let $x^*$ satisfy $\nabla f(x^*)=0$ with
  $\nabla^2f(x^*)$ positive definite, and let $\nabla^2f$ be Lipschitz
  continuous in a neighbourhood of $x^*$. Consider
  $x_{k+1}=x_k-\nabla^2f(x_k)^{-1}\nabla f(x_k)$. If $x_0$ is sufficiently
  close to $x^*$, the iterates are defined and converge to $x^*$
  quadratically, and $\|\nabla f_k\|\to0$ quadratically. Quantitatively,
  suppose $\|\nabla^2f(x)-\nabla^2f(y)\|_2\le M\|x-y\|$ for all
  $x,y\in\mathbb R^n$ and $\nabla^2f(x^*)\succeq\mu I$ with $\mu>0$. If
  $\|x_0-x^*\|\le\bar r=2\mu/(3M)$, then $\|x_k-x^*\|\le\bar r$ for all $k$ and
  $$\|x_{k+1}-x^*\|\le\frac{M\|x_k-x^*\|^2}{2(\mu-M\|x_k-x^*\|)} .$$

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

* **9.10. Subgradient method.** Let $f$ be convex on $\mathbb R^n$, let
  $Q\subseteq\mathbb R^n$ be nonempty, closed and convex with Euclidean
  projection $\pi_Q$, let $x^*$ minimize $f$ on $Q$, and let $x_0\in Q$. Let
  $R\ge\|x_0-x^*\|$ and let $f$ be Lipschitz with constant $M$ on the ball
  $B(x^*,R)$. With steps $h_k>0$ and subgradients $g(x_k)\in\partial f(x_k)$,
  $g(x_k)\ne0$, put $x_{k+1}=\pi_Q\bigl(x_k-h_kg(x_k)/\|g(x_k)\|\bigr)$ (if
  $g(x_k)=0$, then $x_k$ is optimal). Then
  $$\min_{0\le i\le k}f(x_i)-f^*\le M\,\frac{R^2+\sum_{i=0}^kh_i^2}{2\sum_{i=0}^kh_i}.$$
  With $h_i=R/\sqrt{N+1}$ for $0\le i\le N$ the bound at $k=N$ is
  $MR/\sqrt{N+1}$. This is optimal in order: for $0\le k\le n-1$ there is a
  convex $f$ on $\mathbb R^n$ with a minimizer $x^*$, $\|x_0-x^*\|\le R$, and
  $f$ $M$-Lipschitz on $B(x^*,R)$, such that every method with
  $x_j\in x_0+\mathop{\mathrm{span}}\{g(x_0),\dots,g(x_{j-1})\}$ has
  $f(x_k)-f^*\ge MR/\bigl(2(2+\sqrt{k+1})\bigr)$.

* **9.11. Frank–Wolfe method.** Let $C\subseteq E$ be nonempty, compact and
  convex with $\|x-y\|\le\Omega$ for $x,y\in C$, and let $f$ be convex and
  $L_f$-smooth on an open convex set containing $C$. The **conditional
  gradient** (Frank–Wolfe) method takes $x_0\in C$,
  $p_k\in\mathop{\mathrm{argmin}}_{p\in C}\langle\nabla f(x_k),p\rangle$, and
  $x_{k+1}=x_k+t_k(p_k-x_k)$ with $t_k=2/(k+2)$, or $t_k$ chosen by exact line
  search on $[0,1]$. Then
  $$f(x_k)-\min_Cf\le\frac{2L_f\Omega^2}{k}\qquad(k\ge1).$$

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

### Further topics

* **9.15. Riemannian gradient descent.** Let $\mathcal M$ be a Riemannian
  manifold with a retraction $R$, and $f:\mathcal M\to\mathbb R$ smooth with
  $f\ge f_{\mathrm{low}}$. Let $x_{k+1}=R_{x_k}(s_k)$,
  $s_k=-\alpha_k\mathop{\mathrm{grad}}f(x_k)$. Suppose there is $L>0$ with
  $f(R_x(s))\le f(x)+\langle\mathop{\mathrm{grad}}f(x),s\rangle_x+\frac L2\|s\|_x^2$
  for all pairs $(x,s)$ in a set $S\subseteq T\mathcal M$ containing every
  $(x_k,s_k)$, and that $\alpha_k\in[\alpha_{\min},\alpha_{\max}]\subset(0,2/L)$.
  Then $f(x_k)-f(x_{k+1})\ge c\|\mathop{\mathrm{grad}}f(x_k)\|^2$ with
  $c=\min(\alpha_{\min}-\frac L2\alpha_{\min}^2,\alpha_{\max}-\frac L2\alpha_{\max}^2)>0$,
  $\mathop{\mathrm{grad}}f(x_k)\to0$, every accumulation point is critical, and for
  every $K\ge1$ some $k\le K-1$ has
  $\|\mathop{\mathrm{grad}}f(x_k)\|\le\sqrt{(f(x_0)-f_{\mathrm{low}})/(cK)}$. For
  $\alpha_k=1/L$ this reads
  $\|\mathop{\mathrm{grad}}f(x_k)\|\le\sqrt{2L(f(x_0)-f_{\mathrm{low}})/K}$.

* **9.16. Discrete optimal transport and Sinkhorn's algorithm.** Let
  $a\in\mathbb R^n$, $b\in\mathbb R^m$ be probability vectors and
  $C\in\mathbb R^{n\times m}$. Let
  $U(a,b)=\{P\in\mathbb R_{\ge0}^{n\times m}:P\mathbf 1_m=a,\ P^\top\mathbf 1_n=b\}$.
  - (Kantorovich duality.)
    $$\min_{P\in U(a,b)}\langle C,P\rangle
    =\max\{\langle f,a\rangle+\langle g,b\rangle:\ f_i+g_j\le C_{ij}
    \text{ for all }i,j\}.$$
  - Let $\varepsilon>0$ and $H(P)=-\sum_{ij}P_{ij}(\log P_{ij}-1)$. The problem
    $\min_{P\in U(a,b)}\langle C,P\rangle-\varepsilon H(P)$ has a unique
    solution, of the form $P_{ij}=u_iK_{ij}v_j$ with
    $K_{ij}=e^{-C_{ij}/\varepsilon}$ and positive scaling vectors $u,v$.
  - (Birkhoff.) The **Hilbert projective metric** on vectors with positive
    entries is $d_H(u,u')=\log\max_{i,j}\frac{u_iu'_j}{u_ju'_i}$. For a matrix
    $K$ with positive entries,
    $d_H(Kv,Kv')\le\lambda(K)d_H(v,v')$, where
    $\lambda(K)=\frac{\sqrt{\eta(K)}-1}{\sqrt{\eta(K)}+1}<1$ and
    $\eta(K)=\max_{i,j,k,l}\frac{K_{ik}K_{jl}}{K_{jk}K_{il}}$.
  - (Sinkhorn.) Let $a,b$ have positive entries, $v^{(0)}=\mathbf 1_m$,
    $u^{(\ell+1)}=a/(Kv^{(\ell)})$ and $v^{(\ell+1)}=b/(K^\top u^{(\ell+1)})$,
    entrywise. Then $(u^{(\ell)},v^{(\ell)})$ converges to scaling vectors
    $(u^\star,v^\star)$ of the solution in the Hilbert metric, with
    $d_H(u^{(\ell)},u^\star)=O(\lambda(K)^{2\ell})$ and
    $d_H(v^{(\ell)},v^\star)=O(\lambda(K)^{2\ell})$. Moreover, with
    $P^{(\ell)}=\mathop{\mathrm{diag}}(u^{(\ell)})K\mathop{\mathrm{diag}}(v^{(\ell)})$,
    $d_H(u^{(\ell)},u^\star)\le d_H(P^{(\ell)}\mathbf 1_m,a)/(1-\lambda(K)^2)$
    and likewise for $v$.

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

## 10. Polynomial and rational approximation

This section covers best uniform approximation by polynomials and by
rational functions, polynomial interpolation and its Lebesgue constants, the
rates of approximation of differentiable and of analytic functions, and Padé
approximation. Unless stated otherwise, $C[a,b]$ is the space of real
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

* **10.1. Weierstrass theorem and existence of best approximations.** For
  every $f\in C[a,b]$ and every $\varepsilon>0$ there is a polynomial $p$ with
  $\|f-p\|\le\varepsilon$. The trigonometric polynomials are dense, in the
  supremum norm, in the space of continuous $2\pi$-periodic functions on
  $\mathbb R$. If $V$ is a finite-dimensional subspace of a real or complex
  normed space $X$, then for every $u\in X$ there is $v^*\in V$ with
  $\|u-v^*\|=\inf_{v\in V}\|u-v\|$. In particular $E_n(f)$ is attained, and
  $E_n(f)\to0$ as $n\to\infty$ for every $f\in C[a,b]$.

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

* **10.4. Chebyshev polynomials.** For $n\ge1$ the leading coefficient of
  $T_n$ is $2^{n-1}$, the zeros of $T_n$ are $\cos\bigl((2k-1)\pi/(2n)\bigr)$,
  $k=1,\dots,n$, all simple and in $(-1,1)$, and $T_n(\cos(k\pi/n))=(-1)^k$
  for $k=0,\dots,n$. With $\mathring T_n=2^{1-n}T_n$, every monic real
  polynomial $p$ of degree $n\ge1$ satisfies
  $$\max_{-1\le x\le1}|p(x)|\ge\max_{-1\le x\le1}|\mathring T_n(x)|=2^{1-n},$$
  with equality only for $p=\mathring T_n$. More generally, a real polynomial
  of degree $n\ge1$ with leading coefficient $a_n\ne0$ attains on $[-1,1]$ a
  value of absolute value at least $|a_n|/2^{n-1}$. Consequently, among all
  choices of nodes $x_0,\dots,x_n\in[-1,1]$, the quantity
  $\max_{[-1,1]}\bigl|\prod_{i=0}^n(x-x_i)\bigr|$ is minimal, with value
  $2^{-n}$, exactly for the zeros of $T_{n+1}$.

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

* **10.6. Lebesgue constants and near-best approximation.** For distinct
  nodes $x_0,\dots,x_n\in[a,b]$, the **Lebesgue function** is
  $\lambda_n(x)=\sum_{i=0}^n|\ell_i(x)|$ and the **Lebesgue constant** is
  $\Lambda_n=\max_{a\le x\le b}\lambda_n(x)$. The interpolation operator
  $P_n\colon f\mapsto p_n(f;\cdot)$ on $C[a,b]$ is a linear projection onto
  $\mathbb P_n$ with operator norm $\|P_n\|=\Lambda_n$, so $\Lambda_n$ is the
  absolute condition number of interpolation in the supremum norm; it is
  invariant under affine changes of variable. More generally, let $L$ be any
  bounded linear projection of $C[a,b]$ onto $\mathbb P_n$ with operator norm
  $\Lambda$. Then for every $f\in C[a,b]$
  $$\|f-Lf\|\le(1+\Lambda)\,E_n(f).$$
  In particular $\|f-p_n(f;\cdot)\|\le(1+\Lambda_n)E_n(f)$.

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

* **10.15. Theorem of de Montessus de Ballore.** Let $R>0$ and let $f$ be
  meromorphic in the closed disk $|z|\le R$, with poles exactly at the
  distinct points $z_1,\dots,z_m$, where $0<|z_1|\le\cdots\le|z_m|<R$, of
  multiplicities $\mu_1,\dots,\mu_m$ with $\sum_k\mu_k=M$. Then for all
  sufficiently large $L$ the Padé approximant $[L/M]$ (in the sense of Baker)
  of the Maclaurin series of $f$ exists, and
  $$[L/M]\to f\qquad(L\to\infty)$$
  uniformly on every compact subset of $\{z:|z|\le R\}\setminus\{z_1,\dots,z_m\}$.

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

* **10.17. Approximation of $|x|$.** On $[-1,1]$ let
  $E_{mn}=\inf\{\|\,|x|-r\|:r\in R_{mn}^{\mathrm{real}}\}$. Then, as
  $n\to\infty$,
  $$E_{n0}\sim\frac\beta n,\quad\beta=0.2801\ldots,\qquad
  E_{nn}\sim8e^{-\pi\sqrt n}.$$
  Newman's bounds
  $$\tfrac12e^{-9\sqrt n}\le E_{nn}\le3e^{-\sqrt n}$$
  hold for all sufficiently large $n$. Thus rational approximation of $|x|$
  converges at the root-exponential rate $e^{-c\sqrt n}$, while polynomial
  approximation converges only at the rate $n^{-1}$.

## 11. Splines, kernels and wavelets

This section treats three families of approximants that are built from
local or translation-invariant generators: univariate polynomial splines,
interpolation by positive definite and conditionally positive definite
kernels on scattered points, and wavelet bases generated by a
multiresolution analysis. A spline of **order** $m$ is piecewise of degree at
most $m-1$, so its pieces lie in $\mathbb P_{m-1}$. Divided differences of
functions of $t$ at repeated arguments are taken in the Hermite sense, and
$(t-x)_+^{r}$ is $(t-x)^r$ for $t>x$ and $0$ otherwise. The Fourier transform
on $\mathbb R^d$ is $\hat f(\omega)=(2\pi)^{-d/2}\int f(x)e^{-ix^\top\omega}\,dx$.
For a function $\eta$ on $\mathbb R$ write
$\eta_{j,k}(x)=2^{j/2}\eta(2^jx-k)$ for $j,k\in\mathbb Z$.

### Splines

* **11.1. Spline spaces.** Let $a=x_0<x_1<\cdots<x_k<x_{k+1}=b$, let $m\ge1$,
  and let $1\le m_i\le m$ for $i=1,\dots,k$. The **spline space**
  $\mathcal S(\mathbb P_{m-1};\mathcal M;\Delta)$ consists of the functions
  $s$ on $[a,b]$ that agree on each $[x_i,x_{i+1})$ with a polynomial
  $s_i\in\mathbb P_{m-1}$ (the last piece on the closed interval), where
  $s_{i-1}^{(j)}(x_i)=s_i^{(j)}(x_i)$ for $j=0,\dots,m-1-m_i$. The integer
  $m_i$ is the **multiplicity** of the knot $x_i$. With $K=\sum_{i=1}^km_i$
  the space is a linear space of dimension $m+K$. In particular, the space
  $\mathcal S_m(\Delta)$ of splines of order $m$ with simple knots ($m_i=1$,
  so that the splines are in $C^{m-2}[a,b]$ when $m\ge2$) has dimension
  $m+k$.

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

* **11.3. Curry–Schoenberg theorem.** In the setting of 11.1, choose an
  **extended partition** $y_1\le\cdots\le y_m\le a$,
  $b\le y_{m+K+1}\le\cdots\le y_{2m+K}$, with $b<y_{2m+K}$, and with
  $y_{m+1}\le\cdots\le y_{m+K}$ equal to the knots $x_1,\dots,x_k$, each
  $x_i$ repeated $m_i$ times. Then the restrictions to $[a,b]$ of the
  B-splines $N_1^m,\dots,N_{m+K}^m$ form a basis of
  $\mathcal S(\mathbb P_{m-1};\mathcal M;\Delta)$. They are nonnegative and
  sum to $1$ on $[a,b]$. If instead $b=y_{m+K+1}=\cdots=y_{2m+K}$, the same
  holds after the value of $N_{m+K}^m$ at $b$ is replaced by its left limit.

* **11.4. Schoenberg–Whitney theorem.** Let $y_1\le\cdots\le y_{n+m}$ with
  $y_i<y_{i+m}$ for all $i$, and let $t_1<\cdots<t_n$. The collocation matrix
  $\bigl(N_j^m(t_i)\bigr)_{i,j=1}^n$ is nonsingular if and only if
  $N_i^m(t_i)\ne0$ for $i=1,\dots,n$. Hence, under this condition, for all
  data $v_1,\dots,v_n$ there is exactly one spline
  $s=\sum_{j=1}^nc_jN_j^m$ with $s(t_i)=v_i$ for all $i$.

* **11.5. Variation diminishing property.** For a finite real sequence $c$,
  let $S^-(c)$ be the number of sign changes in $c$ after zero entries are
  deleted. For a function $g$ on a set $I$, let $S^-_I(g)$ be the supremum of
  $S^-\bigl(g(\tau_1),\dots,g(\tau_p)\bigr)$ over all finite increasing
  sequences $\tau_1<\cdots<\tau_p$ in $I$. With knots as in 11.4 and any
  nonzero $c=(c_1,\dots,c_n)$,
  $$S^-_{\mathbb R}\Bigl(\sum_{i=1}^nc_iN_i^m\Bigr)\le S^-(c).$$
  In particular, nonnegative coefficients give a nonnegative spline, and
  nondecreasing coefficients give a nondecreasing spline.

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

* **11.8. Approximation order of splines by quasi-interpolants.** Let
  $\Delta=\{a=x_0<\cdots<x_{k+1}=b\}$, let
  $\bar\Delta=\max_i(x_{i+1}-x_i)$, and let $m\ge1$. There is a linear
  operator $Q$, defined on the bounded functions on $[a,b]$, with the
  following properties.
  - $Qf\in\mathcal S_m(\Delta)$, $Q$ reproduces $\mathbb P_{m-1}$, and
    $\|Qf\|_{C[a,b]}\le(2m)^m\|f\|_{C[a,b]}$ for $f\in C[a,b]$.
  - Let $1\le p\le q\le\infty$ and $1\le\sigma\le m$. If $f^{(\sigma-1)}$ is
    absolutely continuous and $f^{(\sigma)}\in L^p(a,b)$, then
    $$\|(f-Qf)^{(r)}\|_{L^q(a,b)}\le C\,
    \bar\Delta^{\,\sigma-r+1/q-1/p}\,\|f^{(\sigma)}\|_{L^p(a,b)},
    \qquad r=0,\dots,\sigma-1,$$
    where $C$ depends only on $m$ and $p$, and not on $\Delta$ or $f$.

  The operator $Q$ is local: it is a combination of B-splines whose
  coefficients are linear combinations of divided differences of $f$ at
  points of the support of the B-spline. For $\sigma<m$ the right side can be
  replaced by $C\bar\Delta^{\sigma-r+1/q-1/p}\omega_{m-\sigma}(f^{(\sigma)};
  \bar\Delta)_p$, where
  $\omega_\ell(g;t)_p=\sup_{0<h\le t}\|\Delta_h^\ell g\|_{L^p[a,b-\ell h]}$
  is the $\ell$-th **modulus of smoothness** and $\Delta_h^\ell$ is the
  $\ell$-th forward difference with step $h$.

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

* **11.12. Native spaces.** Let $\Omega\subseteq\mathbb R^d$ and let
  $\Phi:\Omega\times\Omega\to\mathbb R$ be a continuous symmetric **positive
  definite kernel**: for pairwise distinct $x_1,\dots,x_N\in\Omega$ the matrix
  $(\Phi(x_j,x_k))$ is positive definite. On
  $F_\Phi=\mathrm{span}\{\Phi(\cdot,y):y\in\Omega\}$ the form
  $\langle\Phi(\cdot,x),\Phi(\cdot,y)\rangle=\Phi(x,y)$ extends to an inner
  product, and the completion of $F_\Phi$ is realized as a Hilbert space
  $\mathcal N_\Phi(\Omega)$ of continuous functions on $\Omega$, the **native
  space**, with $f(x)=\langle f,\Phi(\cdot,x)\rangle_{\mathcal N_\Phi(\Omega)}$
  for all $f$ and $x$. It is a reproducing kernel Hilbert space with kernel
  $\Phi$, and it is the only Hilbert space of functions on $\Omega$ with
  reproducing kernel $\Phi$.
  - If $\Phi\in C(\mathbb R^d)\cap L^1(\mathbb R^d)$ is real-valued and
    positive definite, then $\mathcal N_\Phi(\mathbb R^d)$ is the space of
    $f\in L^2(\mathbb R^d)\cap C(\mathbb R^d)$ with
    $\hat f/\sqrt{\hat\Phi}\in L^2(\mathbb R^d)$, with inner product
    $(2\pi)^{-d/2}\int\hat f(\omega)\overline{\hat g(\omega)}/\hat\Phi(\omega)
    \,d\omega$.
  - If moreover $c_1(1+\|\omega\|_2^2)^{-s}\le\hat\Phi(\omega)\le
    c_2(1+\|\omega\|_2^2)^{-s}$ with $s>d/2$ and $0<c_1\le c_2$, then
    $\mathcal N_\Phi(\mathbb R^d)=H^s(\mathbb R^d)$ with equivalent norms.
  - For the functions of 11.10 with $k\ge1$ or $d\ge3$, there are
    $c_1,c_2>0$ depending only on $d$ and $k$ with
    $c_1(1+\|\omega\|_2)^{-d-2k-1}\le\hat\Phi_{d,k}(\omega)\le
    c_2(1+\|\omega\|_2)^{-d-2k-1}$, so
    $\mathcal N_{\Phi_{d,k}}(\mathbb R^d)=H^{d/2+k+1/2}(\mathbb R^d)$ with
    equivalent norms.

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

* **11.17. Jackson and Bernstein estimates; Besov spaces by wavelet
  coefficients.** Let $1\le p\le\infty$ and $s>0$. For an integer $n>s$ the
  **Besov space** $B^s_{p,q}(\mathbb R^d)$, $1\le q\le\infty$, consists of
  the $f\in L^p$ with
  $$\|f\|_{B^s_{p,q}}=\|f\|_{L^p}+\bigl\|\bigl(2^{sj}\omega_n(f,2^{-j})_p
  \bigr)_{j\ge0}\bigr\|_{\ell^q}<\infty,$$
  where $\omega_n(f,t)_p=\sup_{\|h\|_2\le t}\|\Delta_h^nf\|_{L^p}$; different
  $n>s$ give equivalent norms. Let $V_j$ be the spaces generated by a
  compactly supported tensor-product scaling function $\varphi$ with a
  compactly supported dual $\tilde\varphi$, with $\varphi\in L^p$ and
  $\tilde\varphi\in L^{p'}$, $1/p+1/p'=1$. Let $P_j$ be the associated
  projectors, $Q_j=P_{j+1}-P_j$, and let $V_j$ contain all polynomials of
  degree at most $n-1$.
  - The $P_j$ are bounded on $L^p$ uniformly in $j$, and (Jackson)
    $\|f-P_jf\|_{L^p}\le C2^{-nj}|f|_{W^{n,p}}$ and
    $\|f-P_jf\|_{L^p}\le C\omega_n(f,2^{-j})_p$.
  - If $\varphi\in W^{n,p}$, then (Bernstein) $\|f\|_{W^{n,p}}\le C2^{nj}
    \|f\|_{L^p}$ for $f\in V_j$.
  - If $\varphi\in B^{t}_{p,q_0}$ for some $q_0$, then for
    $0<s<\min\{n,t\}$ and $1\le q\le\infty$,
    $$\|f\|_{B^s_{p,q}}\asymp\|P_0f\|_{L^p}+\bigl\|\bigl(2^{sj}\|Q_jf\|_{L^p}
    \bigr)_{j\ge0}\bigr\|_{\ell^q}\asymp
    \Bigl\|\Bigl(2^{sj}2^{d(1/2-1/p)j}\|(c_\lambda)_{|\lambda|=j}\|_{\ell^p}
    \Bigr)_{j\ge-1}\Bigr\|_{\ell^q},$$
    where $c_\lambda=\langle f,\tilde\psi_\lambda\rangle$ are the wavelet
    coefficients of $f$, level $-1$ denoting the scaling coefficients at level
    $0$.

  All constants are independent of $j$ and $f$.

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

## 12. Orthogonal polynomials and numerical quadrature

This section covers orthogonal polynomials for a positive measure on the line,
Gaussian quadrature and its variants, the convergence of quadrature rules,
error representations for interpolatory rules, the Euler–Maclaurin formula and
extrapolation, the exponential convergence of the trapezoidal rule, and the
conditioning of the map from moments to Gauss rules. Throughout, $\mu$ is a
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

* **12.3. Zeros.** For $n\ge1$, all zeros of $\pi_n$ are real and simple and
  lie in the open interval $(a,b)$, where $[a,b]$ is the support interval. The
  zeros of $\pi_n$ and $\pi_{n+1}$ strictly interlace: if
  $\tau^{(m)}_1>\cdots>\tau^{(m)}_m$ are the zeros of $\pi_m$, then
  $$\tau^{(n+1)}_{n+1}<\tau^{(n)}_n<\tau^{(n+1)}_n<\cdots<\tau^{(n)}_1
  <\tau^{(n+1)}_1.$$
  Every open interval $(c,d)$ with $\mu((c,d))=0$ contains at most one zero of
  $\pi_n$.

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

### Gaussian quadrature

* **12.5. Degree of exactness.** Let $Q_n$ be an $n$-point rule with
  **node polynomial** $\omega_n(t)=\prod_{k=1}^n(t-x_k)$, and let
  $0\le m\le n$. Then $Q_n$ has degree of exactness $n-1+m$ if and only if
  $Q_n$ is interpolatory, that is $w_k=\int\ell_k\,d\mu$ with $\ell_k$ the
  Lagrange basis polynomials of the nodes, and
  $\int\omega_np\,d\mu=0$ for all $p\in\mathbb P_{m-1}$. No $n$-point rule
  has degree of exactness $2n$. There is exactly one $n$-point rule with
  degree of exactness $2n-1$, the **Gauss rule** $Q_n^G$; its nodes are the
  zeros of $\pi_n$.

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

* **12.7. Golub–Welsch.** Let $J_n=V\,\mathrm{diag}(x_1,\dots,x_n)\,V^\top$
  with $V$ orthogonal and columns $v_1,\dots,v_n$. Then the nodes of the
  $n$-point Gauss rule are the eigenvalues $x_k$ of $J_n$, and its weights
  are
  $$w_k=\beta_0\,v_{k,1}^2=\mu(\mathbb R)\,v_{k,1}^2,\qquad k=1,\dots,n,$$
  where $v_{k,1}$ is the first component of the unit eigenvector $v_k$.

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

* **12.11. Newton–Cotes error formulas.** Let $n\ge1$, $h=(b-a)/n$,
  $x_i=a+ih$ for $i=0,\dots,n$, let $I_n$ be the interpolatory rule for
  $\int_a^bf\,dx$ with these $n+1$ nodes (the closed **Newton–Cotes rule**),
  and put $\pi_{n+1}(t)=\prod_{i=0}^n(t-i)$.
  - If $n$ is even and $f\in C^{n+2}[a,b]$, then for some $\xi\in(a,b)$,
    $$\int_a^bf\,dx-I_n(f)=\frac{M_n}{(n+2)!}h^{n+3}f^{(n+2)}(\xi),\qquad
    M_n=\int_0^nt\,\pi_{n+1}(t)\,dt<0.$$
  - If $n$ is odd and $f\in C^{n+1}[a,b]$, then for some $\xi\in(a,b)$,
    $$\int_a^bf\,dx-I_n(f)=\frac{K_n}{(n+1)!}h^{n+2}f^{(n+1)}(\xi),\qquad
    K_n=\int_0^n\pi_{n+1}(t)\,dt<0.$$

  So the precise degree of exactness is $n+1$ for even $n$ and $n$ for odd
  $n$. For $n=1$ (trapezoidal rule) the error is $-h^3f''(\xi)/12$, and for
  $n=2$ (Simpson's rule) it is $-h^5f^{(4)}(\xi)/90$.

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

* **12.13. Richardson extrapolation and Romberg integration.**
  - Suppose $A(h)$ has an **asymptotic expansion**
    $A(h)\sim a_0+a_1h^{p_1}+a_2h^{p_2}+\cdots$ as $h\to0$, with
    $0<p_1<p_2<\cdots$, meaning that for every $k$,
    $A(h)-(a_0+a_1h^{p_1}+\cdots+a_kh^{p_k})=O(h^{p_{k+1}})$. Fix
    $q\in(0,1)$, set $A_1=A$ and
    $$A_{k+1}(h)=A_k(h)+\frac{A_k(h)-A_k(q^{-1}h)}{q^{-p_k}-1},
    \qquad k\in\mathbb N.$$
    Then for each $n\in\mathbb N$, $A_n$ has an asymptotic expansion
    $A_n(h)\sim a_0+a^{(n)}_nh^{p_n}+a^{(n)}_{n+1}h^{p_{n+1}}+\cdots$ with
    the same $a_0$, so $A_n(h)-a_0=O(h^{p_n})$.
  - (Romberg) Let $h_i=(b-a)/2^i$ and $T_{i0}=T(h_i)$, and let $T_{ik}$, for
    $0\le k\le i$, be the value at $0$ of the polynomial of degree at most $k$
    in $h^2$ that equals $T(h_j)$ at $h=h_j$ for $j=i-k,\dots,i$. If
    $f\in C^{2k+2}[a,b]$, then for some $\xi\in(a,b)$,
    $$T_{ik}-\int_a^bf\,dx=(b-a)\,h_{i-k}^2h_{i-k+1}^2\cdots h_i^2\,
    \frac{(-1)^kB_{2k+2}}{(2k+2)!}\,f^{(2k+2)}(\xi).$$

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
    |I-I_n|\le\frac{32}{15}\,\frac{V}{\pi\nu(n-2\nu-1)^{2\nu+1}}
    \quad\text{(Gauss, }n>2\nu+1).$$
  - The Gauss bound in the previous part also holds for Clenshaw–Curtis
    for all $n\ge n_0(\nu)$, where $n_0$ depends on $\nu$ but not on $f$.

* **12.16. Ill-conditioning of the moment map.** Let $G_n$ be the map from
  the moments $(\mu_0,\dots,\mu_{2n-1})$ to the Gauss rule
  $(w_1,\dots,w_n,x_1,\dots,x_n)$, defined near the moments of $\mu$, and let
  $\mathrm{cond}\,G_n=\|\partial G_n/\partial(\mu_0,\dots,\mu_{2n-1})\|_\infty$
  be its absolute condition number. If the support of $\mu$ lies in
  $[0,\infty)$, then
  $$\mathrm{cond}\,G_n\ge\min\Bigl(1,\frac1{\max_kw_k}\Bigr)
  \frac{\pi_n(-1)^2}{\min_k(1+x_k)\,\pi_n'(x_k)^2}.$$
  For $d\mu(t)=(t(1-t))^{-1/2}\,dt$ on $[0,1]$ this gives
  $$\mathrm{cond}\,G_n>\frac{(17+6\sqrt8)^n}{48n^2},\qquad n\ge4,$$
  so the condition number grows exponentially in $n$.

## 13. Discrete Fourier analysis and sparse recovery

This section covers the discrete Fourier transform and its fast algorithms,
the relation between discrete and continuous Fourier coefficients,
trigonometric interpolation, sampling, nonequispaced transforms, Prony's
method, and the recovery of sparse vectors from few linear measurements.
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

* **13.2. Cyclic convolution.** The **cyclic convolution** of
  $a,b\in\mathbb C^N$ is the vector $a*b$ with
  $(a*b)_n=\sum_{k=0}^{N-1}a_kb_{(n-k)\bmod N}$, and $a\circ b$ is the
  componentwise product. Then
  $$\widehat{a*b}=\hat a\circ\hat b,\qquad N\,\widehat{a\circ b}=\hat a*\hat b .$$
  If $V_N$ is the cyclic forward shift, $(V_Na)_j=a_{(j-1)\bmod N}$, and
  $M_N=\mathrm{diag}(1,w_N,\dots,w_N^{N-1})$, then $F_NV_N=M_NF_N$.

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

* **13.7. Poisson summation formula.** Let $f\in L^1(\mathbb R)\cap
  C_0(\mathbb R)$ satisfy
  $$\sum_{k\in\mathbb Z}\max_{x\in[-\pi,\pi]}|f(x+2k\pi)|<\infty
  \quad\text{and}\quad\sum_{k\in\mathbb Z}|\hat f(k)|<\infty .$$
  Then for every $x\in\mathbb R$
  $$2\pi\sum_{k\in\mathbb Z}f(x+2k\pi)=\sum_{k\in\mathbb Z}\hat f(k)e^{ikx},$$
  both series converging absolutely and uniformly on $\mathbb R$. In particular
  $2\pi\sum_kf(2k\pi)=\sum_k\hat f(k)$.

* **13.8. Shannon sampling theorem.** Let $f\in L^1(\mathbb R)\cap
  C_0(\mathbb R)$ be **bandlimited** on $[-L,L]$ for some $L>0$, that is,
  $\hat f(\omega)=0$ for $|\omega|>L$, and let $M\ge L$. Then
  $$f(x)=\sum_{k\in\mathbb Z}f\Bigl(\frac{k\pi}M\Bigr)\,\mathrm{sinc}(Mx-k\pi)
  \qquad(x\in\mathbb R),$$
  the series converging absolutely and uniformly on $\mathbb R$. In particular
  $f$ is determined by its samples $f(k\pi/M)$, $k\in\mathbb Z$.

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

### Sparse recovery

* **13.11. Sparsity and the minimal number of measurements.** A vector
  $x\in\mathbb K^N$ is **$s$-sparse** if $\|x\|_0=\mathrm{card}\{j:x_j\ne0\}\le s$.
  The **error of best $s$-term approximation** is
  $\sigma_s(x)_p=\inf\{\|x-z\|_p:z\text{ is }s\text{-sparse}\}$ for $p>0$, and
  $\sigma_s(x)_q\le s^{1/q-1/p}\|x\|_p$ for $q>p>0$. For
  $A\in\mathbb C^{m\times N}$ the following are equivalent: every $s$-sparse
  $x$ is the unique $s$-sparse solution of $Az=Ax$; $\ker A$ contains no
  nonzero $2s$-sparse vector; every $2s$ columns of $A$ are linearly
  independent. Hence such an $A$ has $m\ge2s$ when $N\ge2s$, and for every
  $N\ge2s$ there is an $A$ with $m=2s$ rows with these properties.

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

## 14. Initial value problems: one-step and multistep methods

This section covers existence and stability of solutions of initial value
problems, the convergence theory of one-step methods, the order theory of
Runge–Kutta methods by rooted trees, collocation methods, the classical theory
of linear multistep methods, asymptotic error expansions and extrapolation, and
B-series. The problem is $y'=f(t,y)$, $y(t_0)=y_0$, with
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
    $\alpha=\min(a,b/A)$, and its graph lies in $D$. The Euler polygons
    converge uniformly to it on this interval as the maximal step size tends
    to $0$.

* **14.2. Gronwall inequalities.**
  - (Continuous.) Let $p\ge0$ be integrable on $[t_0,T]$, let $g$ and
    $\varphi$ be continuous on $[t_0,T]$ with $g$ nondecreasing, and suppose
    $$\varphi(t)\le g(t)+\int_{t_0}^tp(\tau)\varphi(\tau)\,d\tau,\qquad
    t\in[t_0,T].$$
    Then $\varphi(t)\le g(t)\exp\bigl(\int_{t_0}^tp(\tau)\,d\tau\bigr)$ on
    $[t_0,T]$.
  - (Discrete.) Let $k_n\ge0$, $p_n\ge0$ and $g_0\ge0$, and let the real
    sequence $(\varphi_n)_{n\ge0}$ satisfy, for every $n\ge0$,
    $$\varphi_n\le g_0+\sum_{s=0}^{n-1}p_s+\sum_{s=0}^{n-1}k_s\varphi_s$$
    (empty sums are $0$). Then for every $n\ge0$
    $$\varphi_n\le\Bigl(g_0+\sum_{s=0}^{n-1}p_s\Bigr)
    \exp\Bigl(\sum_{s=0}^{n-1}k_s\Bigr).$$

* **14.3. Continuous dependence.** Let $y$ solve $y'=f(t,y)$ on
  $[t_0,T]$, and let $v:[t_0,T]\to\mathbb R^N$ be continuous and piecewise
  $C^1$, with right derivative $v'(t+0)$. Suppose that
  $\|v(t_0)-y(t_0)\|\le\rho$, that $\|v'(t+0)-f(t,v(t))\|\le\varepsilon$ for
  $t\in[t_0,T)$, and that $\|f(t,v)-f(t,w)\|\le L\|v-w\|$ for all $t$ and all
  $v,w$ in a set containing the values of $y$ and $v$, with $L>0$. Then for
  $t\in[t_0,T]$
  $$\|y(t)-v(t)\|\le\rho\,e^{L(t-t_0)}+\frac{\varepsilon}{L}
  \bigl(e^{L(t-t_0)}-1\bigr).$$
  For an inner product norm the Lipschitz constant may be replaced by a
  **one-sided Lipschitz constant** $\ell\in\mathbb R$, that is,
  $\langle f(t,y)-f(t,z),y-z\rangle\le\ell\|y-z\|^2$ for all $t,y,z$: two
  solutions $y,z$ then satisfy
  $\|y(t)-z(t)\|\le e^{\ell(t-t_0)}\|y(t_0)-z(t_0)\|$ for $t\ge t_0$.

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

* **14.5. Runge–Kutta methods.** An $s$-stage **Runge–Kutta method** with
  tableau $(A,b,c)$, $A=(a_{ij})\in\mathbb R^{s\times s}$,
  $b,c\in\mathbb R^s$ and $c_i=\sum_ja_{ij}$, is
  $$Y_i=y_n+h\sum_{j=1}^sa_{ij}f(t_n+c_jh,Y_j)\quad(i=1,\dots,s),\qquad
  y_{n+1}=y_n+h\sum_{i=1}^sb_if(t_n+c_ih,Y_i).$$
  It is **explicit** if $a_{ij}=0$ for $j\ge i$. If $f$ has Lipschitz
  constant $L$ in $y$ and $hL\max_i\sum_j|a_{ij}|<1$, then the stage
  equations have a unique solution.

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

* **14.7. Butcher barriers.** Let an explicit $s$-stage Runge–Kutta method
  have order $p$. Then $p\le s$. If $p\ge5$, then $s\ge p+1$. If $p\ge7$, then
  $s\ge p+2$. If $p\ge8$, then $s\ge p+3$. Explicit methods of order $7$ with
  $9$ stages and of order $8$ with $11$ stages exist.

* **14.8. Simplifying assumptions.** For a tableau $(A,b,c)$ consider
  $$B(p):\ \sum_ib_ic_i^{q-1}=\frac1q\ (q\le p),\qquad
  C(\eta):\ \sum_ja_{ij}c_j^{q-1}=\frac{c_i^q}q\ (\text{all }i,\ q\le\eta),$$
  $$D(\zeta):\ \sum_ib_ic_i^{q-1}a_{ij}=\frac{b_j(1-c_j^q)}q
  \ (\text{all }j,\ q\le\zeta).$$
  If $B(p)$, $C(\eta)$ and $D(\zeta)$ hold with $p\le\eta+\zeta+1$ and
  $p\le2\eta+2$, then the method has order $p$. The largest $\eta$ with
  $C(\eta)$ is the **stage order**.

* **14.9. Collocation methods.** Let $c_1,\dots,c_s\in\mathbb R$ be distinct.
  The **collocation polynomial** is the polynomial $u$ of degree at most $s$
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
    collocation method has order $s+r$.
  - Consequently the **Gauss methods** ($c_i$ the zeros of the shifted
    Legendre polynomial of degree $s$ on $[0,1]$) have order $2s$, the
    **Radau IIA methods** ($c_i$ the zeros of
    $\frac{d^{s-1}}{d\tau^{s-1}}\bigl(\tau^{s-1}(\tau-1)^s\bigr)$, so
    $c_s=1$) have order $2s-1$, and the **Lobatto IIIA methods** ($c_i$ the
    zeros of $\frac{d^{s-2}}{d\tau^{s-2}}\bigl(\tau^{s-1}(\tau-1)^{s-1}\bigr)$,
    $s\ge2$, so $c_1=0$, $c_s=1$) have order $2s-2$. A Runge–Kutta method
    with $s$ stages has order at most $2s$, and order $2s$ holds exactly for
    the Gauss method.

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

* **14.12. First Dahlquist barrier.** A zero-stable linear $k$-step method has
  order $p\le k+2$ if $k$ is even and $p\le k+1$ if $k$ is odd. If
  $\beta_k/\alpha_k\le0$, in particular if the method is explicit, then
  $p\le k$.

* **14.13. Backward differentiation formulas.** The **$k$-step BDF method**
  has $\sigma(\zeta)=\zeta^k$ and
  $$\rho(\zeta)=\sum_{j=1}^k\frac1j\,\zeta^{k-j}(\zeta-1)^j.$$
  It has order $k$, and it is zero-stable if and only if $1\le k\le6$; so it
  is convergent of order $k$ exactly for $k\le6$.

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

* **14.15. Gragg's method.** Let $f\in C^{2N+2}$, $h=(t-t_0)/n$ with $n\in\mathbb N$,
  and define $\eta_0=y_0$, $\eta_1=y_0+hf(t_0,y_0)$ and
  $\eta_{i+1}=\eta_{i-1}+2hf(t_i,\eta_i)$, and $\eta(t;h)=\eta_n$. Then
  $$\eta(t;h)=y(t)+\sum_{k=1}^Nh^{2k}\bigl(u_k(t)+(-1)^{(t-t_0)/h}v_k(t)
  \bigr)+h^{2N+2}E_{2N+2}(t;h),$$
  with $u_k,v_k$ independent of $h$ and $E_{2N+2}(t;h)$ bounded for fixed
  $t$ and all $h=(t-t_0)/n$. In particular, for even $n$ the error has an
  expansion in even powers of $h$, and so does
  the smoothed value $S_h=\frac14(\eta_{n-1}+2\eta_n+\eta_{n+1})$; these
  expansions are the basis of the Gragg–Bulirsch–Stoer extrapolation.

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

## 15. Stiff problems, differential-algebraic equations, and geometric integration

This section covers linear and nonlinear stability of Runge–Kutta and
multistep methods for stiff problems, convergence estimates independent of
stiffness, linear and semi-explicit differential-algebraic equations,
exponential integrators, and the structure-preserving integration of
Hamiltonian systems with its backward error analysis. Notation for
Runge–Kutta and linear multistep methods is that of Section 14;
$\mathbb 1=(1,\dots,1)^\top\in\mathbb R^s$, $\mathbb C^-=\{z:\mathrm{Re}\,z
\le0\}$, and $\langle\cdot,\cdot\rangle$ is an inner product on
$\mathbb C^N$ with norm $\|\cdot\|$. A Runge–Kutta method is
**non-confluent** if $c_1,\dots,c_s$ are distinct.

### Linear stability

* **15.1. Stability function.** Applied to the **Dahlquist test equation**
  $y'=\lambda y$, a Runge–Kutta method gives $y_{n+1}=R(h\lambda)y_n$, where
  the **stability function** is
  $$R(z)=1+zb^\top(I-zA)^{-1}\mathbb 1=
  \frac{\det(I-zA+z\mathbb 1b^\top)}{\det(I-zA)},$$
  a rational function with numerator and denominator of degree at most $s$.
  For an explicit method $R$ is a polynomial of degree at most $s$. If the
  method has order $p$, then $R(z)=e^z+O(z^{p+1})$ as $z\to0$. The
  **stability domain** is $S=\{z\in\mathbb C:|R(z)|\le1\}$.

* **15.2. A-stability and L-stability.** A Runge–Kutta method is
  **A-stable** if $\mathbb C^-\subset S$. This holds if and only if $R$ has
  no poles in $\{\mathrm{Re}\,z<0\}$ and $|R(iy)|\le1$ for all real $y$. It
  is **L-stable** if it is A-stable and $\lim_{z\to\infty}R(z)=0$. No
  explicit Runge–Kutta method is A-stable, since a nonconstant polynomial is
  unbounded on $\mathbb C^-$.

* **15.3. Padé approximations and the Ehle conjecture.** For
  $k,j\in\mathbb N_0$ the **$(k,j)$ Padé approximation** to $e^z$ is
  $R_{kj}=P_{kj}/Q_{kj}$ with
  $$P_{kj}(z)=\sum_{m=0}^k\frac{k!\,(j+k-m)!}{(j+k)!\,m!\,(k-m)!}z^m,
  \qquad Q_{kj}(z)=P_{jk}(-z).$$
  It is the unique rational function with numerator degree at most $k$ and
  denominator degree at most $j$ such that $R_{kj}(z)-e^z=O(z^{k+j+1})$.
  The function $R_{kj}$ is A-stable (bounded by $1$ in modulus on
  $\mathbb C^-$) if and only if $k\le j\le k+2$.

* **15.4. A-stable implicit Runge–Kutta methods.** For every $s\in\mathbb N$:
  - the $s$-stage Gauss method has order $2s$ and $R=R_{ss}$, and it is
    A-stable;
  - the $s$-stage Radau IA and Radau IIA methods have order $2s-1$ and
    $R=R_{s-1,s}$, and they are A-stable and L-stable;
  - for $s\ge2$, the $s$-stage Lobatto IIIA, IIIB and IIIC methods have
    order $2s-2$; $R=R_{s-1,s-1}$ for IIIA and IIIB and $R=R_{s-2,s}$ for
    IIIC; all are A-stable, and IIIC is L-stable.

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

* **15.6. A($\alpha$)-stability of BDF.** For $0<\alpha<\pi/2$, a convergent
  linear multistep method is **A($\alpha$)-stable** if its stability domain
  contains the sector $\{\mu\ne0:|\arg(-\mu)|<\alpha\}$. The $k$-step BDF
  methods are A($\alpha$)-stable for $k\le6$, with largest angles
  approximately $90^\circ,90^\circ,86.03^\circ,73.35^\circ,51.84^\circ,
  17.84^\circ$ for $k=1,\dots,6$.

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

* **15.8. B-convergence.** Suppose $f$ satisfies the one-sided Lipschitz
  condition $\mathrm{Re}\,\langle f(t,y)-f(t,z),y-z\rangle\le\nu\|y-z\|^2$.
  A Runge–Kutta method is **B-convergent of order $r$** if, for constant or
  variable steps with $h=\max_nh_n$ and $h\nu\le\alpha$, its global error
  satisfies
  $$\|y_n-y(t_n)\|\le h^r\gamma(t_n-t_0,\nu)\max_{j=1,\dots,l}
  \max_{t\in[t_0,t_n]}\|y^{(j)}(t)\|,$$
  where $l$, $\alpha$ and the function $\gamma$ depend only on the method,
  not on $f$ or on its Lipschitz constant. The $s$-stage Gauss and Radau IIA
  methods are B-convergent of order $s$, the Radau IA methods of order
  $s-1$, and the $2$-stage Lobatto IIIC method of order $1$.

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
  - (Multistep.) Let a linear multistep method of order $p$ have $0$ and
    $\infty$ in its stability domain, and apply it as
    $\sum_j\alpha_jy_{n+j}=h\sum_j\beta_jf(y_{n+j},z_{n+j})$,
    $0=\sum_j\beta_jg(y_{n+j},z_{n+j})$. If the starting errors are
    $O(h^p)$, then $y_n-y(t_n)=O(h^p)$ and $z_n-z(t_n)=O(h^p)$ for
    $t_n-t_0\le\mathrm{const}$. This applies to the BDF methods with
    $k\le6$.

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

### Geometric integration

* **15.12. Symplectic maps and Poincaré's theorem.** Let
  $J=\begin{pmatrix}0&I\\-I&0\end{pmatrix}\in\mathbb R^{2d\times2d}$. A
  differentiable map $g:U\to\mathbb R^{2d}$, $U\subset\mathbb R^{2d}$ open,
  is **symplectic** if $g'(y)^\top Jg'(y)=J$ for all $y\in U$. If
  $H:U\to\mathbb R$ is $C^2$, the flow $\varphi_t$ of the Hamiltonian system
  $y'=J^{-1}\nabla H(y)$, $y=(p,q)$, is a symplectic map wherever it is
  defined. A one-step method is **symplectic** if its one-step map
  $y_1=\Phi_h(y_0)$ is symplectic whenever it is applied to a smooth
  Hamiltonian system.

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

* **15.14. Symplectic Euler and Störmer–Verlet.** For $H(p,q)$ and
  $p'=-H_q$, $q'=H_p$, the **symplectic Euler method**
  $$p_{n+1}=p_n-hH_q(p_{n+1},q_n),\qquad q_{n+1}=q_n+hH_p(p_{n+1},q_n)$$
  is symplectic of order $1$, and the **Störmer–Verlet method**
  $$p_{n+1/2}=p_n-\tfrac h2H_q(p_{n+1/2},q_n),\quad
  q_{n+1}=q_n+\tfrac h2\bigl(H_p(p_{n+1/2},q_n)+H_p(p_{n+1/2},q_{n+1})
  \bigr),$$
  $$p_{n+1}=p_{n+1/2}-\tfrac h2H_q(p_{n+1/2},q_{n+1})$$
  is symplectic of order $2$.

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

* **15.16. Long-time energy conservation.** Let $H:D\to\mathbb R$ be analytic
  on an open $D\subset\mathbb R^{2d}$, and apply a symplectic method of order
  $p$ satisfying the analytic bounds of 15.15. If the numerical solution
  stays in a compact set $K\subset D$, then there are $h_0>0$ and a modified
  Hamiltonian $\tilde H=H+h^pH_{p+1}+\dots+h^{N-1}H_N$ with $N=N(h)$ as in
  15.15 such that
  $$\tilde H(y_n)=\tilde H(y_0)+O(e^{-h_0/(2h)}),\qquad
  H(y_n)=H(y_0)+O(h^p)\qquad\text{for }nh\le e^{h_0/(2h)}.$$

* **15.17. Splitting methods.** Let $y'=f^{[1]}(y)+f^{[2]}(y)$ with flows
  $\varphi^{[1]}_t,\varphi^{[2]}_t$ of the two parts. The **Lie–Trotter
  splitting** $\varphi^{[1]}_h\circ\varphi^{[2]}_h$ has order $1$, and the
  **Strang splitting** $\varphi^{[1]}_{h/2}\circ\varphi^{[2]}_h\circ
  \varphi^{[1]}_{h/2}$ is symmetric and has order $2$. For matrices,
  $$e^{tA/2}e^{tB}e^{tA/2}=\exp\Bigl(t(A+B)+t^3\bigl(-\tfrac1{24}
  [A,[A,B]]+\tfrac1{12}[B,[B,A]]\bigr)+O(t^5)\Bigr),$$
  with $[A,B]=AB-BA$. If both parts are Hamiltonian, the splittings are
  symplectic.

## 16. Finite difference methods for differential equations

This section covers finite difference methods for two-point boundary value
problems and the Poisson equation, the Lax–Richtmyer theory of stability and
convergence for evolution equations, Fourier (von Neumann) analysis, the
classical schemes for the advection and heat equations, and the stability
tools of the method of lines: the Kreiss matrix theorem, logarithmic norms,
positivity and strong stability preserving time stepping. For a grid
function $v=(v_j)_{j\in\mathbb Z}$ with spacing $\Delta x$ the discrete norms
are $\|v\|_{\Delta,p}=(\Delta x\sum_j|v_j|^p)^{1/p}$ for $p=1,2$ and
$\|v\|_{\Delta,\infty}=\sup_j|v_j|$. The **Courant number** for the
advection equation $u_t+au_x=0$ with constant $a\in\mathbb R$ is
$\nu=a\Delta t/\Delta x$. Inequalities between vectors and matrices are
entrywise.

### Boundary value problems

* **16.1. Two-point boundary value problem.** Let $q,g\in C[a,b]$ with
  $q\ge0$, and let $y\in C^4[a,b]$ solve $-y''+q(x)y=g(x)$, $y(a)=\alpha$,
  $y(b)=\beta$. Let $h=(b-a)/(n+1)$, $x_i=a+ih$, and let $u\in\mathbb R^n$
  solve
  $$\frac{-u_{i-1}+2u_i-u_{i+1}}{h^2}+q(x_i)u_i=g(x_i),\qquad
  i=1,\dots,n,\quad u_0=\alpha,\ u_{n+1}=\beta.$$
  The matrix $A_q$ of this system is symmetric positive definite, and
  $0\le A_q^{-1}\le A_0^{-1}$, where $A_0$ is the matrix for $q\equiv0$. The
  local truncation error is $\tau_i=-\frac{h^2}{12}y^{(4)}(\xi_i)$ with
  $\xi_i\in(x_{i-1},x_{i+1})$, and if $|y^{(4)}|\le M$ on $[a,b]$ then
  $$|y(x_i)-u_i|\le\frac{Mh^2}{24}(x_i-a)(b-x_i),\qquad
  \max_i|y(x_i)-u_i|\le\frac{Mh^2(b-a)^2}{96}.$$

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

* **16.4. Convergence of the five-point scheme.** Let $u\in C^4(\bar\Omega)$
  solve $-\Delta u=f$ in $\Omega=(0,1)^2$, $u=g$ on $\partial\Omega$, and let
  $U$ solve $-\Delta_hU=f$ on $\Omega_h$, $U=g$ on $\partial\Omega_h$. Then
  $$\max_{\Omega_h}|u-U|\le\frac{h^2}{96}(M_{xxxx}+M_{yyyy}).$$
  The proof compares the error with $\frac{h^2}{12}(M_{xxxx}+M_{yyyy})\phi$,
  where $\phi(x,y)=\frac14\bigl(x(1-x)+y(1-y)\bigr)$ satisfies
  $-\Delta_h\phi=1$ and $0\le\phi\le\frac18$. In the scaled Euclidean norm
  $\|e\|_h=h\bigl(\sum_{\Omega_h}|e_{ij}|^2\bigr)^{1/2}$ the error is also
  $O(h^2)$.

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

* **16.7. The CFL condition.** The **numerical domain of dependence** of a
  grid value is the set of initial grid points on which it depends. A
  difference method can be convergent only if, in the limit
  $\Delta t,\Delta x\to0$, its numerical domain of dependence contains the
  domain of dependence of the differential equation. For an explicit
  three-point scheme for $u_t+au_x=0$ with fixed $\Delta t/\Delta x$ this
  is the **CFL condition** $|\nu|\le1$. The condition is necessary but not
  sufficient for stability.

* **16.8. Classical schemes for the advection equation.** For $u_t+au_x=0$
  on $\mathbb R$ or with periodic boundary conditions:
  - the **upwind scheme** $u^{n+1}_j=u^n_j-\nu(u^n_j-u^n_{j-1})$ ($a>0$)
    satisfies $\|u^{n+1}\|_{\Delta,p}\le\|u^n\|_{\Delta,p}$ for $p=1,2,\infty$
    if $0\le\nu\le1$; its amplification factor $1-\nu+\nu e^{-i\theta}$ has
    modulus at most $1$ for all $\theta$ if and only if $0\le\nu\le1$;
  - the **Lax–Friedrichs scheme**
    $u^{n+1}_j=\frac12(u^n_{j+1}+u^n_{j-1})-\frac\nu2(u^n_{j+1}-u^n_{j-1})$
    satisfies $\|u^{n+1}\|_{\Delta,1}\le\|u^n\|_{\Delta,1}$ if $|\nu|\le1$;
  - the **Lax–Wendroff scheme**
    $u^{n+1}_j=u^n_j-\frac\nu2(u^n_{j+1}-u^n_{j-1})+\frac{\nu^2}2
    (u^n_{j+1}-2u^n_j+u^n_{j-1})$ has
    $|\tilde a(e^{i\theta})|^2=1-4\nu^2(1-\nu^2)\sin^4(\theta/2)$, so it is
    stable in $\|\cdot\|_{\Delta,2}$ if and only if $|\nu|\le1$; its
    truncation error is $O(\Delta t^2+\Delta x^2)$, while upwind and
    Lax–Friedrichs are first order;
  - the forward Euler centered scheme
    $u^{n+1}_j=u^n_j-\frac\nu2(u^n_{j+1}-u^n_{j-1})$ has
    $|\tilde a(e^{i\theta})|^2=1+\nu^2\sin^2\theta$ and is unstable for every
    fixed $\nu\ne0$.

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

### Stability tools for the method of lines

* **16.10. Kreiss matrix theorem.** Let $\|\cdot\|$ be a vector norm on
  $\mathbb C^N$ and the matrix norm it induces. For
  $A\in\mathbb C^{N\times N}$ let the **Kreiss constant** be
  $\mathcal K(A)=\sup_{|z|>1}(|z|-1)\|(zI-A)^{-1}\|$. Then
  $$\mathcal K(A)\le\sup_{k\ge0}\|A^k\|\le eN\mathcal K(A).$$
  So a family of $N\times N$ matrices with fixed $N$ is uniformly power
  bounded if and only if its Kreiss constants are uniformly bounded.

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

* **16.12. Von Neumann's theorem and contractivity.** Let $\|\cdot\|$ come
  from an inner product, let $A\in\mathbb C^{m\times m}$ satisfy
  $\mathrm{Re}\,\langle Av,v\rangle\le0$ for all $v$, and let $R$ be a
  rational function bounded on $\mathbb C^-$. Then
  $\|R(A)\|\le\sup_{\mathrm{Re}\,z\le0}|R(z)|$. In particular, if $R$ is the
  stability function of an A-stable method, then $\|R(\tau A)\|\le1$ for
  all $\tau>0$. For the θ-method of 16.9 and
  $\mathrm{Re}\,\langle Av,v\rangle\le\omega\|v\|^2$, one has
  $\|R(\tau A)\|\le\sup_{\mathrm{Re}\,z\le\tau\omega}|R(z)|$ whenever
  $1-\theta\tau\omega>0$; for $\theta\ge\frac12$ and $\omega\le0$ this
  gives $\|R(\tau A)\|\le1$. If $A$ is normal and $\tau\lambda\in S$ for every
  eigenvalue $\lambda$ of $A$, where $S$ is the stability domain of $R$,
  then $\|R(\tau A)^n\|_2\le1$ for all $n$.

* **16.13. Positivity.** Let $F:[0,T]\times\mathbb R^m\to\mathbb R^m$ be
  continuous and Lipschitz in $v$. The system $w'=F(t,w)$ is **positive**
  ($w(0)\ge0$ implies $w(t)\ge0$ for $t\ge0$) if and only if for all $t$
  and all $v\ge0$ with $v_i=0$ one has $F_i(t,v)\ge0$. A linear system
  $w'=Aw$ is positive if and only if $a_{ij}\ge0$ for all $i\ne j$.

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

## 17. Hyperbolic conservation laws and finite volume methods

This section covers the entropy theory of scalar conservation laws, the
convergence and accuracy of conservative finite volume schemes, entropy
stable fluxes, and the Riemann problem and small-data existence theory for
systems in one space dimension. A **scalar conservation law** is
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

* **17.2. Entropy pairs and admissibility.** An **entropy pair** is a convex
  $\eta\colon\mathbb R\to\mathbb R$ with an **entropy flux** $q$ satisfying
  $q'=\eta'f'$. A weak solution is an **entropy solution** if
  $$\partial_t\eta(u)+\nabla\cdot q(u)\le 0$$
  in the sense of distributions on $\mathbb R^d\times(0,\infty)$, with the
  initial condition attained, for every convex entropy pair. It suffices to
  take the **Kružkov pairs**
  $\eta(u)=|u-k|$, $q(u)=\mathop{\mathrm{sgn}}(u-k)\,(f(u)-f(k))$ for all
  $k\in\mathbb R$. If $f$ is smooth and the solutions $u^\varepsilon$ of
  $\partial_t u+\nabla\cdot f(u)=\varepsilon\Delta u$ are bounded uniformly
  in $\varepsilon$ and converge boundedly a.e. as $\varepsilon\to0$, then the
  limit is an entropy solution. Across a jump as in 17.1 the entropy
  inequality reads $q(u_R)-q(u_L)\le s\,(\eta(u_R)-\eta(u_L))$. For Burgers'
  equation with $\eta=u^2/2$ and $q=u^3/3$,
  $$q(u_R)-q(u_L)-s\,(\eta(u_R)-\eta(u_L))=\tfrac1{12}(u_R-u_L)^3,$$
  so a jump that satisfies Rankine–Hugoniot is admissible exactly when
  $u_L\ge u_R$; this rules out the jump in 17.1. For a strictly convex
  scalar flux, two equivalent forms of this criterion are the **Lax
  condition** $f'(u_L)>s>f'(u_R)$ at a shock and the **Oleinik condition**
  $u(x+a,t)-u(x,t)\le Ea/t$ for all $a>0$ and $t>0$, with $E$ independent of
  $x$, $a$ and $t$.

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

* **17.4. The scalar Riemann problem.** Let $d=1$ and let $u_0$ equal $u_L$
  on $x<0$ and $u_R$ on $x>0$. If $f\in C^2$ with $f''>0$, the entropy
  solution is self-similar, $u=w(x/t)$:
  - if $u_L>u_R$, it is the **shock** with speed
    $s=(f(u_L)-f(u_R))/(u_L-u_R)$;
  - if $u_L<u_R$, it is the **rarefaction wave**
    $w(\xi)=(f')^{-1}(\xi)$ for $f'(u_L)\le\xi\le f'(u_R)$, with $w=u_L$
    to the left and $w=u_R$ to the right of that fan.

  For a general flux, if $u_L<u_R$, then $w(\xi)=(\breve f')^{-1}(\xi)$,
  where $\breve f$ is the lower convex envelope of $f$ on $[u_L,u_R]$;
  if $u_L>u_R$, the upper concave envelope on $[u_R,u_L]$ is used. Jumps of $w$
  occur where the envelope is affine, and they satisfy Rankine–Hugoniot.

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

* **17.6. Monotone, contractive, TVD and monotonicity preserving
  schemes.** Write a scheme as $v^{n+1}_j=H(v^n_{j-p},\dots,v^n_{j+p})$. It
  is **monotone** if $H$ is nondecreasing in each argument; **$L^1$
  contractive** if $\|v^{n+1}-w^{n+1}\|_{\ell^1}\le\|v^n-w^n\|_{\ell^1}$ for
  integrable data; **total variation diminishing** (TVD) if
  $\mathrm{TV}(v^{n+1})\le\mathrm{TV}(v^n)$; and **monotonicity preserving**
  if monotone data $v^n$ give monotone $v^{n+1}$, in the same sense. For a
  conservative consistent scheme with continuous $H$:
  $$\text{monotone}\ \Longrightarrow\ L^1\text{ contractive}\ \Longrightarrow
  \ \text{TVD}\ \Longrightarrow\ \text{monotonicity preserving}.$$
  The **Lax–Friedrichs scheme**, with
  $g_{j+1/2}=\frac12(f(v_j)+f(v_{j+1}))-\frac1{2\lambda}(v_{j+1}-v_j)$, is
  monotone on data with values in $I$ when $\lambda\max_I|f'|\le1$.

* **17.7. Convergence of monotone schemes.** Let $f$ be Lipschitz,
  $u_0\in L^1\cap BV(\mathbb R)$, and let a conservative consistent
  monotone scheme with Lipschitz numerical flux be run with
  $\Delta t=\lambda\Delta x$, under the CFL-type condition that keeps it
  monotone. Let $u$ be the Kružkov entropy solution of 17.3. For each $T>0$
  and every compact interval $K\subset\mathbb R$, the whole family satisfies
  $$\sup_{0\le t\le T}\|v_{\Delta x}(\cdot,t)-u(\cdot,t)\|_{L^1(K)}
  \longrightarrow 0\qquad(\Delta x\to0).$$

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

### Systems in one space dimension

* **17.12. Hyperbolicity, characteristic fields and Riemann invariants.**
  The system is **hyperbolic** on a set of states if $Df(u)$ is
  diagonalizable with real eigenvalues there, and **strictly hyperbolic** if
  the eigenvalues $\lambda_1(u)<\dots<\lambda_m(u)$ are distinct, with right
  eigenvectors $r_k(u)$. The $k$-th field is **genuinely nonlinear** if
  $\nabla\lambda_k\cdot r_k\ne0$ and **linearly degenerate** if
  $\nabla\lambda_k\cdot r_k\equiv0$. A **$k$-Riemann invariant** is a smooth
  $w$ with $\nabla w\cdot r_k\equiv0$. Near each state there are $m-1$
  $k$-Riemann invariants with linearly independent gradients. In a linearly
  degenerate field, $\lambda_k$ is itself a $k$-Riemann invariant. In a
  $k$-rarefaction wave all $k$-Riemann invariants are constant. An entropy
  pair for a system is a convex $\eta$ and $q$ with
  $\nabla q^\top=\nabla\eta^\top Df$. If $\eta$ is strictly convex, then
  $D^2\eta\,Df$ is symmetric, so the system is hyperbolic, and in the
  entropy variables $w=\nabla\eta(u)$ it becomes symmetric (Godunov–Mock).

* **17.13. Lax shock conditions.** Let the system be strictly hyperbolic. A
  jump $(u_L,u_R,s)$ satisfying Rankine–Hugoniot is a **Lax $k$-shock** if
  $$\lambda_k(u_R)<s<\lambda_k(u_L),\qquad \lambda_{k-1}(u_L)<s<
  \lambda_{k+1}(u_R),$$
  with $\lambda_0=-\infty$ and $\lambda_{m+1}=+\infty$. Let the $k$-th field
  be genuinely nonlinear, normalized by $\nabla\lambda_k\cdot r_k>0$, and let
  $u_R$ lie on the Hugoniot curve of $u_L$ through
  $u_L+\varepsilon r_k(u_L)+O(\varepsilon^2)$, with $\varepsilon$ small.
  Then the Lax inequalities hold if and only if $\varepsilon<0$. If the system has
  a strictly convex entropy, the entropy inequality across the jump also
  holds if and only if $\varepsilon\le0$. In a linearly degenerate field, the
  jumps are **contact discontinuities** with $s=\lambda_k(u_L)=\lambda_k(u_R)$,
  and the entropy inequality holds with equality.

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

* **17.15. Existence and stability for small total variation.** Let the
  system be as in 17.14 near a state $\bar u$. There is $\delta>0$ such that
  for $u_0$ with $\|u_0-\bar u\|_{L^\infty}$ and $\mathrm{TV}(u_0)$ smaller than
  $\delta$ there is a global weak solution, obtained as the limit of front
  tracking approximations, with uniformly bounded total variation (Glimm's
  random choice method gives the same existence result). At isolated jumps
  it satisfies the Lax conditions. The solutions so obtained are unique and
  form an $L^1$-Lipschitz semigroup:
  $\|u(t)-v(t)\|_{L^1}\le C\,\|u_0-v_0\|_{L^1}$, with $C$ independent of
  $t$, $u_0$ and $v_0$. Front tracking approximations with parameter $\delta$
  are first order accurate in $L^1$: the error at time $t$ is $O(\delta)$.

## 18. Galerkin and finite element methods for elliptic problems

This section covers the abstract theory of Galerkin approximation, the
Sobolev space tools used in its analysis, conforming finite elements and
their error estimates, nonconforming and discontinuous Galerkin methods,
mixed methods, and finite element de Rham complexes. Spaces are real. For a
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

* **18.1. The Lax–Milgram lemma and the Banach–Nečas–Babuška theorem.**
  Let $V$ be a Banach space, $W$ a reflexive Banach space, $a$ a bounded
  bilinear form on $V\times W$ and $\ell\in W'$. The problem of finding
  $u\in V$ with $a(u,w)=\ell(w)$ for all $w\in W$ is **well posed** (has a
  unique solution for every $\ell$) if and only if
  - (inf-sup) $\displaystyle\alpha:=\inf_{v\ne0}\sup_{w\ne0}
    \frac{a(v,w)}{\|v\|_V\|w\|_W}>0$, and
  - (injectivity of the adjoint) if $w\in W$ and $a(v,w)=0$ for all $v\in V$,
    then $w=0$.

  Then $\|u\|_V\le\|\ell\|_{W'}/\alpha$. If $V=W$ is a Hilbert space and $a$
  is **coercive**, $a(v,v)\ge\alpha\|v\|_V^2$ for all $v$, both conditions
  hold, and the problem is well posed with the same bound (Lax–Milgram).

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

* **18.3. Quasi-optimality: Céa, Babuška, Xu–Zikatanov.** In the setting of
  18.2, with $u$ the exact solution and $\alpha_h>0$, **Galerkin
  orthogonality** $a(u-u_h,w_h)=0$ holds for all $w_h\in W_h$, and
  $$\|u-u_h\|_V\le\Bigl(1+\frac{\|a\|}{\alpha_h}\Bigr)
  \inf_{v_h\in V_h}\|u-v_h\|_V \qquad\text{(Babuška).}$$
  If $V$ is a Hilbert space and $\{0\}\ne V_h\ne V$, the factor improves to
  $\|a\|/\alpha_h$ (Xu–Zikatanov). If $V=W$ is a Hilbert space, $V_h=W_h$
  and $a$ is coercive with constant $\alpha$, the factor is $\|a\|/\alpha$
  (Céa), and it is $(\|a\|/\alpha)^{1/2}$ if moreover $a$ is symmetric. For
  the inner product, $a(v,w)=(v,w)_V$, the Galerkin solution is the
  orthogonal projection and all these factors equal $1$ except Babuška's,
  which equals $2$.

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

### Sobolev space tools

* **18.5. Poincaré inequalities.** Let $p\in[1,\infty]$. There are
  constants $C_{\mathrm{PF}}$ and $C_{\mathrm{PS}}$, depending only on $p$
  and $\Omega$, such that
  $$C_{\mathrm{PF}}\|v\|_{L^p(\Omega)}\le\ell_\Omega\|\nabla v\|_{L^p(\Omega)}
  \quad(v\in W^{1,p}_0(\Omega)),\qquad
  C_{\mathrm{PS}}\|v-\bar v\|_{L^p(\Omega)}\le\ell_\Omega|v|_{W^{1,p}(\Omega)}
  \quad(v\in W^{1,p}(\Omega)),$$
  where $\bar v$ is the mean of $v$ over $\Omega$. The first is the
  **Poincaré–Friedrichs** inequality and the second the
  **Poincaré–Steklov** (or Poincaré–Wirtinger) inequality. Both constants
  are invariant under dilation, translation and rotation of $\Omega$. For
  convex $\Omega$ and $p=2$ one may take $C_{\mathrm{PS}}=\pi$, and for $p=1$
  one may take $C_{\mathrm{PS}}=2$. On $\Omega=(0,1)$, $v(x)=\cos\pi x$ has
  mean zero and attains $\pi\|v\|_{L^2}=\|v'\|_{L^2}$, so $\pi$ is sharp.
  More generally, if $\Gamma\subset\partial\Omega$ has positive measure, then
  $\|v\|_{L^2(\Omega)}\le C(|\int_\Gamma v\,ds|+|v|_{1,\Omega})$ for all
  $v\in H^1(\Omega)$.

* **18.6. Traces and Sobolev embeddings.** Let $p\in[1,\infty)$ and let
  $s>1/p$ if $p>1$, or $s\ge1$ if $p=1$. There is a bounded linear **trace
  map** $\gamma\colon W^{s,p}(\Omega)\to L^p(\partial\Omega)$ with
  $\gamma v=v|_{\partial\Omega}$ for $v\in C(\overline\Omega)\cap
  W^{s,p}(\Omega)$, whose kernel is $W^{s,p}_0(\Omega)$. In particular,
  $H^1_0(\Omega)$ is the kernel of $\gamma$ on $H^1(\Omega)$, and $\gamma$
  maps $H^1(\Omega)$ onto $H^{1/2}(\partial\Omega)$. For $p\in[1,\infty]$ and
  $v\in W^{1,p}(\Omega)$ there is the multiplicative bound
  $\|v\|_{L^p(\partial\Omega)}\le C\|v\|_{L^p(\Omega)}^{1-1/p}
  \|v\|_{W^{1,p}(\Omega)}^{1/p}$. For $d\ge2$, $s>0$ and $p\in[1,\infty]$,
  $$W^{s,p}(\Omega)\hookrightarrow L^q(\Omega)\quad\text{for }
  q\in\Bigl[p,\frac{pd}{d-sp}\Bigr]\text{ if }sp<d,\qquad
  q\in[p,\infty)\text{ if }sp=d .$$
  If $k\in\mathbb N$ and $k>d/p$ with $p>1$, or $k\ge d$ with $p=1$, then
  every $v\in W^{k,p}(\Omega)$ has a continuous representative and
  $\|v\|_{L^\infty(\Omega)}\le C\|v\|_{W^{k,p}(\Omega)}$; in particular
  $H^2(\Omega)\subset C(\overline\Omega)$ for $d\le3$.

* **18.7. Elliptic regularity on convex and polygonal domains.** Let $A$
  be a Lipschitz, symmetric, uniformly positive definite matrix field and
  $f\in L^2(\Omega)$.
  - If $\Omega$ is convex, the weak solution of $-\nabla\cdot(A\nabla u)=f$
    with $u=0$ on $\partial\Omega$ is in $H^2(\Omega)$; so is the solution
    of the Neumann or Robin problem with zero boundary data, when it is
    well posed.
  - If $\Omega\subset\mathbb R^2$ is a polygon and $A=I$, there is
    $s_0\in(\frac12,1]$, with $s_0=1$ if $\Omega$ is convex, such that the
    solution of the Dirichlet problem with $u=0$ on $\partial\Omega$ is in
    $H^{1+s}(\Omega)$ for all $s\in[0,s_0]$. The same holds for compatible
    piecewise smooth boundary data and for the Neumann problem.

  By the closed graph theorem the solution map is then bounded:
  $\|u\|_{H^{1+s}(\Omega)}\le C\|f\|_{L^2(\Omega)}$. On the L-shaped domain
  the function $r^{2/3}\sin(2\theta/3)$, which is harmonic and vanishes on
  the two edges at the reentrant corner, is in $H^{1+s}$ near that corner
  only for $s<2/3$.

### Conforming finite elements

* **18.8. Finite elements in the sense of Ciarlet.** A **finite element** is
  a triple $(K,P,\Sigma)$ of a compact set $K\subset\mathbb R^d$ with
  nonempty interior, a finite-dimensional space $P$ of functions on $K$,
  and a set $\Sigma=\{\sigma_1,\dots,\sigma_n\}$ of linear forms on $P$
  (**degrees of freedom**) that is a basis of $P'$. The last condition,
  **unisolvence**, holds if and only if $n=\dim P$ and $\sigma_i(p)=0$ for
  all $i$ implies $p=0$. The **shape functions** $\theta_j\in P$ are the dual
  basis, $\sigma_i(\theta_j)=\delta_{ij}$, and the **local interpolant** is
  $I_Kv=\sum_i\sigma_i(v)\theta_i$, which is the identity on $P$. Two elements
  are **affine equivalent** if an invertible affine map $F$ carries one
  domain onto the other, $P$ onto $\{\hat p\circ F\}$, and the degrees of
  freedom correspondingly. For example, $\mathbb P_1$ with the vertex values,
  and $\mathbb P_2$ with the values at the vertices and edge midpoints, are
  unisolvent on every triangle, and all such elements are affine
  equivalent.

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

* **18.12. Inverse estimates.** Let $P_K$ be the local polynomial space.
  There is $C$ such that for integers $0\le m\le l$, all
  $p,q\in[1,\infty]$, all $K$ and all $v\in P_K$,
  $$|v|_{W^{l,p}(K)}\le C\,h_K^{m-l+d(1/p-1/q)}|v|_{W^{m,q}(K)},\qquad
  \|v\|_{L^p(F)}\le C\,h_K^{-1/p+d(1/p-1/q)}\|v\|_{L^q(K)}$$
  for each face $F$ of $K$. On a quasi-uniform family the global form is
  $(\sum_K\|v\|^p_{W^{l,p}(K)})^{1/p}\le Ch^{m-l+\min(0,d/p-d/q)}
  (\sum_K\|v\|^q_{W^{m,q}(K)})^{1/q}$ for piecewise polynomial $v$. For
  $v(x)=x$ on $K=[0,h]$, $|v|_{1,K}=\sqrt3\,h^{-1}\|v\|_{0,K}$.

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

* **18.15. Discrete maximum principle for linear elements.** Let $u_h\in
  V_{h,0}$ be the $\mathbb P_1$ Galerkin solution of a coercive problem as
  in 18.13 with stiffness matrix $\mathsf A$ on the interior vertices and load
  vector $B_i=\int_\Omega f\varphi_i\,dx$. The **discrete maximum
  principle** holds if $B\le0$ implies $u_h\le0$, so that $f\le0$
  implies $u_h\le0$. It holds if and only if $\mathsf A^{-1}\ge0$ entrywise,
  and it holds whenever $\mathsf A$ is a **Z-matrix** (nonpositive
  off-diagonal entries), which is then a nonsingular M-matrix. For the
  Laplacian, the mesh is **weakly acute** if
  $\int_\Omega\nabla\varphi_i\cdot\nabla\varphi_j\,dx\le0$ for all $i\ne j$.
  This holds if and only if, for each pair of adjacent vertices, the sum over
  the simplices containing their edge of
  $|F_{K,i}\cap F_{K,j}|\cot\alpha_{K,ij}$ is nonnegative. Here
  $\alpha_{K,ij}$ is the dihedral angle of $K$ between the faces
  $F_{K,i}$ and $F_{K,j}$ opposite the two vertices. In $d=2$ the condition is
  that the two angles opposite each interior edge sum to at most $\pi$; a
  mesh of nonobtuse triangles satisfies it. The condition is always met in
  $d=1$.

### Nonconforming and discontinuous Galerkin methods

* **18.16. The Crouzeix–Raviart element.** Let $V_h^{\mathrm{cr}}$ consist of
  the piecewise $\mathbb P_1$ functions $v$ with $\int_F[v]\,ds=0$ for every
  interior face $F$ and $\int_Fv\,ds=0$ for every boundary face. These are
  the piecewise linear functions continuous at the barycenters of interior
  faces and zero at those of boundary faces. For the Poisson problem, let
  $u_h\in V_h^{\mathrm{cr}}$ satisfy
  $\sum_K\int_K\nabla u_h\cdot\nabla w_h=\int_\Omega fw_h$ for all
  $w_h\in V_h^{\mathrm{cr}}$, and let $\nabla_h$ be the broken gradient. If
  $u\in H^{1+r}(\Omega)$ with $r>\frac12$ and $t=\min(1,r)$, then
  $$\|\nabla_h(u-u_h)\|_{0,\Omega}\le C\Bigl(\sum_Kh_K^{2t}|u|^2_{1+t,K}
  \Bigr)^{1/2},$$
  and the error is quasi-optimal in a norm that dominates
  $\|\nabla_h\cdot\|_{0,\Omega}$. If the smoothing property of 18.14 holds
  with $s\in(\frac12,1]$, then
  $\|u-u_h\|_{0,\Omega}\le Ch^s\ell_\Omega^{1-s}
  (\sum_Kh_K^{2t}|u|^2_{1+t,K})^{1/2}$.
  On a convex polygon this gives the errors $Ch|u|_{2,\Omega}$ and
  $Ch^2|u|_{2,\Omega}$, with $C$ depending only on the shape regularity.

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

## 19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation

This section extends the Galerkin framework of section 18 (Lax–Milgram, Céa,
Strang, interpolation estimates, Aubin–Nitsche duality, mixed and
discontinuous Galerkin methods) in four directions: parabolic problems
discretized in space by finite elements and in time by one-step or
discontinuous Galerkin schemes; spectral Galerkin and collocation methods
built on trigonometric and orthogonal polynomials; Galerkin approximation of
compact symmetric eigenvalue problems; and a posteriori error estimation and
adaptive mesh refinement, followed by two results on nonlinear problems.
Throughout, $(\cdot,\cdot)$ and $\|\cdot\|$ denote the inner product and norm of
$L^2$ on the domain in question, and $\|\cdot\|_s$ the norm of $H^s$. In
items 19.2–19.5 the letter $k$ denotes a time step and $r$ an order of
spatial accuracy.

### Parabolic problems

* **19.1. Weak parabolic problems (Lions' theorem).** Let $V$ and $L$ be
  separable real Hilbert spaces with $V$ continuously and densely embedded in
  $L$. Identify $L$ with its dual, so that $V\subset L\subset V'$ (a
  **Gelfand triple**), and write $\langle\cdot,\cdot\rangle$ for the pairing of
  $V'$ with $V$, which extends the inner product of $L$. Let $T>0$, $J=(0,T)$,
  and
  $$X=\{v\in L^2(J;V):\ \partial_tv\in L^2(J;V')\},$$
  with $\partial_t$ the weak time derivative.
  - $X$ is continuously embedded in $C^0([0,T];L)$, the map $v\mapsto v(0)$
    from $X$ to $L$ is surjective, and for all $v,w\in X$
    $$\int_J\bigl(\langle\partial_tv,w\rangle+\langle\partial_tw,v\rangle\bigr)\,dt
    =(v(T),w(T))_L-(v(0),w(0))_L.$$
  - Let $A:J\to\mathcal L(V;V')$ be such that $t\mapsto\langle A(t)v,w\rangle$
    is measurable for all $v,w\in V$, and suppose there are constants
    $M,\alpha>0$ with $\|A(t)v\|_{V'}\le M\|v\|_V$ and
    $\langle A(t)v,v\rangle\ge\alpha\|v\|_V^2$ for all $v\in V$ and almost
    every $t\in J$. Then for every $f\in L^2(J;V')$ and $u_0\in L$ there is
    exactly one $u\in X$ with $\partial_tu(t)+A(t)u(t)=f(t)$ in $V'$ for almost
    every $t\in J$ and $u(0)=u_0$. It satisfies
    $$\alpha\|u\|_{L^2(J;V)}^2+\|u(T)\|_L^2\le\alpha^{-1}\|f\|_{L^2(J;V')}^2
    +\|u_0\|_L^2 .$$

  The heat equation $\partial_tu-\nabla\cdot(\kappa\nabla u)=f$ with
  homogeneous Dirichlet data is the case $V=H^1_0(\Omega)$ normed by
  $\|\nabla v\|$, $L=L^2(\Omega)$, $A(t)v=-\nabla\cdot(\kappa(\cdot,t)\nabla v)$,
  where $\kappa$ is bounded, continuous in $t$, and bounded below by a positive
  constant.

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
  $t>0$. If $v=0$ on $\partial\Omega$, then for all $t\ge0$
  $$\|u_h(t)-u(t)\|\le\|v_h-v\|+Ch^r\Bigl(\|v\|_r+\int_0^t\|u_t\|_r\,ds\Bigr).$$
  With $v_h=R_hv$ or $v_h$ the $L^2$ projection of $v$ onto $S_h$, the first
  term is at most $Ch^r\|v\|_r$, so the error is $O(h^r)$ uniformly on bounded
  time intervals.

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

* **19.4. Nonsmooth initial data.** Let $f=0$, $v\in L^2(\Omega)$, and let
  $u_h$ be the semidiscrete approximation of 19.2 with $v_h=P_hv$, the
  $L^2$-orthogonal projection of $v$ onto $S_h$. Then
  $$\|u_h(t)-u(t)\|\le Ch^rt^{-r/2}\|v\|\qquad\text{for all }t>0,$$
  and $t$ may be replaced by $t+h^2$ on the right. For piecewise linear
  elements ($r=2$) this is $\|u_h(t)-u(t)\|\le Ch^2t^{-1}\|v\|$: the method
  converges with full order for every $t>0$ although $v$ has no smoothness.

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

* **19.7. Inverse inequalities for algebraic polynomials.**
  - For all $\varphi\in\mathbb P_N$, $\|\varphi'\|\le\tfrac12(N+1)(N+2)\|\varphi\|$
    in $L^2(I)$, and the order $N^2$ is sharp: $\|L_N'\|\ge cN^2\|L_N\|$ with
    $c>0$ independent of $N$, $L_N$ the Legendre polynomial. More generally,
    for $1\le p\le\infty$ and $r\ge1$, $\|\varphi^{(r)}\|_{L^p}\le CN^{2r}
    \|\varphi\|_{L^p}$, and in the Chebyshev-weighted $L^p_\omega$ norms the
    same bound holds for $2\le p\le\infty$.
  - With a shift of weight the order drops to $N$: for $\alpha,\beta>-1$ and
    $\varphi\in\mathbb P_N$,
    $$\|\varphi'\|_{\omega^{\alpha+1,\beta+1}}\le\sqrt{N(N+\alpha+\beta+1)}\,
    \|\varphi\|_{\omega^{\alpha,\beta}} .$$

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

* **19.9. Interpolation errors.** For $m\ge1$ and $N\ge m-1$:
  - (Legendre.) If $I_N$ is interpolation at the Legendre–Gauss,
    Gauss–Radau or Gauss–Lobatto nodes, then
    $\|u-I_Nu\|\le CN^{-m}\|u^{(m)}\|$ for $u\in H^m(I)$. For the LGL nodes
    the $H^1$ error is optimal, $\|u-I_Nu\|_{H^1}\le CN^{1-m}\|u^{(m)}\|$, and
    $\|I_Nu\|_{H^1}\le C\|u\|_{H^1}$ with $C$ independent of $N$; at the Gauss
    nodes the $H^1$ error can be larger by a factor of order $N^{1/2}$. In
    weighted form, for LGL interpolation and $1\le m\le N+1$,
    $$\|\partial_x(I_Nu-u)\|+N\|I_Nu-u\|_{\omega^{-1,-1}}\le
    c\sqrt{\tfrac{(N-m+1)!}{N!}}\,(N+m)^{(1-m)/2}\|\partial_x^mu\|_{\omega^{m-1,m-1}}$$
    with $c$ independent of $m$, $N$ and $u$.
  - (Chebyshev.) If $I_N$ is interpolation at any of the Chebyshev–Gauss,
    Gauss–Radau or Gauss–Lobatto node families and $\omega=(1-x^2)^{-1/2}$,
    then $\|u-I_Nu\|_\omega\le CN^{-m}\|u^{(m)}\|_\omega$ for
    $u\in H^m_\omega(I)$, and at the Chebyshev–Gauss nodes
    $\|\partial_x^l(I_Nu-u)\|_{\omega^{l-1/2,l-1/2}}\le CN^{l-m}
    \|\partial_x^mu\|_{\omega^{m-1/2,m-1/2}}$ for $0\le l\le m$.

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

* **19.11. Galerkin method with numerical integration (G-NI).** Let
  $a,b\in W^{1,\infty}(I)$ with $0<c_1\le a\le c_2$ and $0\le b\le c_3$ on
  $[-1,1]$, let $g$ be continuous, and let $u\in H^1_0(I)$ be the weak
  solution of $-(au')'+bu=g$, $u(\pm1)=0$. The **G-NI approximation** is the
  $u_N\in\mathbb P^0_N$ with
  $$\langle au_N',v'\rangle_N+\langle bu_N,v\rangle_N=\langle g,v\rangle_N
  \qquad\text{for all }v\in\mathbb P^0_N ,$$
  all integrals of the Galerkin method being replaced by LGL quadrature.
  - If $a$ is a constant, $u_N$ is the **LGL collocation** solution: it
    satisfies $-au_N''(x_j)+b(x_j)u_N(x_j)=g(x_j)$ at the interior nodes
    $x_1,\dots,x_{N-1}$.
  - If $u\in H^2(I)$, $\partial_x^2u$ and $\partial_x(au')$ belong to
    $B^{m-2}_{0,0}(I)$, $\partial_x(bu)\in B^{m-1}_{0,0}(I)$ and
    $g\in B^k_{-1,-1}(I)$, with $2\le m\le N+1$ and $1\le k\le N+1$, then
    $$\begin{aligned}\|u-u_N\|_1\le{}&c\sqrt{\tfrac{(N-m+1)!}{N!}}(N+m)^{\frac{1-m}2}
    \bigl(\|u\|_2+\|\partial_x^mu\|_{\omega^{m-2,m-2}}
    +\|\partial_x^{m-1}(au')\|_{\omega^{m-2,m-2}}
    +\|\partial_x^m(bu)\|_{\omega^{m-1,m-1}}\bigr)\\
    &+c\sqrt{\tfrac{(N-k+1)!}{N!}}(N+k)^{-\frac{k+1}2}
    \|\partial_x^kg\|_{\omega^{k-1,k-1}},\end{aligned}$$
    with $c$ depending only on the $L^\infty$ norms of $a$, $b$, $a'$, $b'$
    (and on $c_1$).

  The same structure holds in several dimensions on $(-1,1)^d$ with tensor LGL
  quadrature: the G-NI error is bounded by the best-approximation error plus
  the consistency errors of the quadrature in the bilinear and linear forms
  (first Strang lemma, section 18).

* **19.12. Exponential convergence for analytic functions.**
  - (Fourier.) Let $P_N$ here denote truncation of the Fourier series to
    $-N\le j\le N-1$. If $\eta>0$, $m\ge0$ and $u$ is $2\pi$-periodic with
    $\|u\|_{G_{\eta,m}}^2=\sum_je^{2\eta(1+|j|)}(1+|j|^{2m})|\hat u_j|^2<\infty$
    (which implies that $u$ is analytic in the strip $|\mathrm{Im}\,z|<\eta$),
    then $\|u-P_Nu\|_{H^l(0,2\pi)}\le CN^{l-m}e^{-\eta N}\|u\|_{G_{\eta,m}}$
    for $0\le l\le m$.
  - (Chebyshev.) If $u$ has an analytic extension to the closed region bounded
    by the ellipse $E_\eta$ with foci $\pm1$ and sum of semi-axes $e^\eta$,
    $\eta>0$, and $I_N$ is interpolation at Chebyshev–Gauss-type nodes, then
    for every $l\ge0$
    $$\|u^{(l)}-(I_Nu)^{(l)}\|_{\omega}\le\frac{C(l)}{\sinh\eta}\,N^{2l}
    e^{-\eta N}\max_{z\in E_\eta}|u(z)| ,\qquad \omega=(1-x^2)^{-1/2}.$$

  Exponential rates for best polynomial approximation of analytic functions
  are in section 10.

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

* **19.16. Spurious eigenvalues of a stable mixed method.** On
  $\Omega=(0,\pi)^2$ consider the Laplace eigenvalue problem in mixed form:
  find $\lambda$ and $(\sigma,u)\in H(\mathrm{div};\Omega)\times L^2(\Omega)$,
  $u\ne0$, with $(\sigma,\tau)+(\mathrm{div}\,\tau,u)=0$ and
  $(\mathrm{div}\,\sigma,v)=-\lambda(u,v)$ for all $\tau,v$; its eigenvalues
  are $j^2+l^2$, $j,l\in\mathbb N$. Discretize on the criss-cross triangular
  mesh sequence with $\Sigma_h$ the continuous piecewise linear vector fields
  and $U_h=\mathrm{div}\,\Sigma_h$. This pair satisfies ellipticity on the
  discrete kernel and the inf–sup condition in $H(\mathrm{div})\times L^2$, so
  the corresponding source problem has the quasi-optimal error bound of
  section 18; nevertheless the discrete eigenvalue problem does not converge
  in the sense of 19.14: there are discrete eigenvalues converging (at rate
  $h^2$) to $6$, $15$, $15$ and $24$, which are not eigenvalues. The failure
  is possible because the solution operator of the mixed source problem is
  not compact into $H(\mathrm{div};\Omega)\times L^2(\Omega)$, so stability of
  the source problem does not yield the uniform convergence of 19.14.

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

## 20. Multilevel and domain decomposition methods

This section treats multigrid iterations, subspace correction methods, and
Schwarz-type domain decomposition preconditioners for symmetric positive
definite systems arising from elliptic problems. For a symmetric positive
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

* **20.6. The Xu–Zikatanov identity.** Let $A$ be symmetric positive definite
  on $V$, let $V_1,\dots,V_J$ be subspaces with $V=V_1+\cdots+V_J$, and let
  $P_i$ be the $(\cdot,\cdot)_A$-orthogonal projection onto $V_i$. The
  **successive subspace correction** method with exact subspace solves has
  error propagation operator $E=(I-P_J)(I-P_{J-1})\cdots(I-P_1)$, and
  $$\|E\|_A^2=1-\frac1{1+c_0},\qquad
  c_0=\sup_{\|v\|_A=1}\ \inf_{\substack{v_i\in V_i\\ \sum_iv_i=v}}\
  \sum_{i=1}^J\Bigl\|P_i\sum_{j=i+1}^Jv_j\Bigr\|_A^2.$$
  In particular $\|E\|_A<1$.

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

* **20.10. Multilevel additive preconditioners.** Let $\Omega\subset\mathbb
  R^2$ be a polygon, $\mathcal T_1$ a triangulation and $\mathcal T_j$,
  $2\le j\le J$, obtained by successive regular refinement, so
  $h_j=2^{J-j}h_J$; let $V_j$ be the continuous piecewise linear functions on
  $\mathcal T_j$ vanishing on $\partial\Omega$ and $A_J$ the stiffness operator
  of $\int_\Omega\nabla u\cdot\nabla v\,dx$ on $V_J$. Let $B_{\mathrm{BPX}}$ be
  the additive preconditioner of 20.5 with the spaces $V_j$, the inclusions
  $I_j$, and $(B_jv,w)=\sum_pv(p)w(p)$, summed over the interior vertices of
  $\mathcal T_j$. If $\Omega$ is convex, then $\kappa(B_{\mathrm{BPX}}A_J)\le
  C$ with $C$ independent of $J$ and $h_J$. The hierarchical basis
  preconditioner $B_{\mathrm{HB}}$ satisfies only
  $\kappa(B_{\mathrm{HB}}A_J)\le C(1+|\log h_J|^2)$.

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

## 21. Integral equations and boundary element methods

This section treats linear integral equations of the second kind,
$\varphi-A\varphi=f$ with a compact operator $A$, their approximation by
projection and quadrature (Nyström) methods, Volterra equations and their
collocation, and boundary integral operators with their Galerkin
discretization. Spaces are complex normed spaces unless stated otherwise. Let
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

* **21.3. Neumann series and perturbation.** Let $X$ be a Banach space and
  $A:X\to X$ bounded with $\|A\|<1$. Then $I-A$ has the bounded inverse
  $(I-A)^{-1}=\sum_{k\ge0}A^k$ with $\|(I-A)^{-1}\|\le1/(1-\|A\|)$. Let $X$,
  $Y$ be Banach spaces, $A:X\to Y$ bounded with bounded inverse, and
  $A_n:X\to Y$ bounded with $\|A^{-1}(A_n-A)\|<1$. Then $A_n^{-1}$ exists, is
  bounded,
  $$\|A_n^{-1}\|\le\frac{\|A^{-1}\|}{1-\|A^{-1}(A_n-A)\|},$$
  and the solutions of $A\varphi=f$ and $A_n\varphi_n=f_n$ satisfy
  $$\|\varphi_n-\varphi\|\le\frac{\|A^{-1}\|}{1-\|A^{-1}(A_n-A)\|}
  \bigl(\|(A_n-A)\varphi\|+\|f_n-f\|\bigr).$$
  Conversely, if the $A_n^{-1}$ exist and are bounded by $\|A_n^{-1}\|$, then
  $\|A_n^{-1}(A_n-A)\|<1$ implies that $A^{-1}$ exists with
  $\|A^{-1}\|\le\|A_n^{-1}\|/(1-\|A_n^{-1}(A_n-A)\|)$.

### Projection and Nyström methods

* **21.4. Projection methods and Céa's lemma.** Let $A:X\to Y$ be an
  injective bounded operator between Banach spaces, $X_n\subset X$ and
  $Y_n\subset Y$ subspaces of dimension $n$, and $P_n:Y\to Y_n$ bounded
  projections. The **projection method** approximates $A\varphi=f$ by
  $P_nA\varphi_n=P_nf$ with $\varphi_n\in X_n$; it **converges** if there is
  $n_0$ such that for every $f\in A(X)$ and $n\ge n_0$ the projected equation
  has a unique solution and $\varphi_n\to\varphi$. Assume
  $\inf_{\psi\in X_n}\|\psi-\varphi\|\to0$ for every $\varphi\in X$. The
  method converges if and only if there are $n_0$ and $M$ such that, for
  $n\ge n_0$, $P_nA:X_n\to Y_n$ is invertible and $\|(P_nA)^{-1}P_nA\|\le M$;
  in that case
  $$\|\varphi_n-\varphi\|\le(1+M)\inf_{\psi\in X_n}\|\psi-\varphi\|.$$
  If the method converges for a bijective $A$, it also converges for $A+B$
  whenever $B$ is compact and $A+B$ is injective.

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

* **21.6. Iterated Galerkin method.** Let $X$ be a Hilbert space, $K$ compact,
  $\lambda\ne0$ with $\lambda-K$ injective, and $P_n$ orthogonal projections
  with $P_nx\to x$ for all $x$. With $x_n$ the Galerkin solution, the
  **iterated Galerkin solution** $\hat x_n=\lambda^{-1}(y+Kx_n)$ satisfies
  $P_n\hat x_n=x_n$, $(\lambda-KP_n)\hat x_n=y$, and for $n\ge N$
  $$\|x-\hat x_n\|\le c\,\|(I-P_n)K^*\|\,\|(I-P_n)x\|,\qquad
  \|(I-P_n)K^*\|\to0,$$
  with $c$ independent of $n$; hence $\|x-\hat x_n\|/\|x-x_n\|\to0$
  (superconvergence).

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

* **21.16. Ill-posedness of first-kind equations with compact operators.** If
  $A:X\to Y$ is a compact linear operator between normed spaces and $X$ is
  infinite-dimensional, then $A$ has no bounded inverse on $A(X)$, and the
  equation $A\varphi=f$ is improperly posed: its solution, when it exists,
  does not depend continuously on $f$. First-kind equations with smooth
  kernels are of this type; their regularization is the subject of section 22.
  The first-kind boundary integral equation of 21.14 is not of this type,
  because $V$ is an isomorphism from $H^{-1/2}(\Gamma)$ onto
  $H^{1/2}(\Gamma)$.

## 22. Inverse problems and regularization

This section covers linear ill-posed operator equations and their
regularization, convex variational regularization in Banach spaces, Bayesian
inverse problems with Gaussian priors, and the Kalman and 3DVAR filters.
Unless stated otherwise, $X$ and $Y$ are Hilbert spaces over $\mathbb K$ with
inner products $(\cdot,\cdot)$, $K:X\to Y$ is a bounded linear operator with
adjoint $K^*$, null space $N(K)$ and range $R(K)=K(X)$. Exact data are
$y\in Y$, and noisy data $y^\delta\in Y$ satisfy $\|y^\delta-y\|\le\delta$
with **noise level** $\delta>0$. The regularization parameter is $\alpha>0$,
or an integer $m$ for iterative methods. For a compact $K$ with infinitely
many nonzero singular values the system $(\sigma_n,e_n,g_n)$ of 22.2 is
indexed by $n\in\mathbb N$; for finite rank the sums below are finite.

### Ill-posedness and the singular value decomposition

* **22.1. Well-posedness.** Let $X,Y$ be normed spaces, $U\subset X$,
  $V\subset Y$, and $A:U\to V$ an operator. The equation $Ax=y$ is
  **well-posed** (in the sense of Hadamard) if $A:U\to V$ is bijective and
  $A^{-1}:V\to U$ is continuous; otherwise it is **ill-posed**. Thus
  ill-posedness means nonexistence, nonuniqueness, or instability of the
  solution. A bounded injective linear $K:X\to Y$ gives an ill-posed
  equation on its range when $K^{-1}:R(K)\to X$ is unbounded. If $K:X\to Y$
  is a compact linear operator between normed spaces and $X$ is infinite
  dimensional, then $Kx=y$ is ill-posed: there is no bounded linear
  $B:R(K)\to X$ with $BK=I$.

* **22.2. Singular system of a compact operator.** Let $K:X\to Y$ be compact
  and $K\neq0$. The **singular values** of $K$ are the nonnegative square roots
  of the eigenvalues of the compact, self-adjoint, nonnegative operator
  $K^*K$. Let $(\sigma_n)$ be the nonzero singular values in nonincreasing
  order, repeated according to the dimension of $N(\sigma_n^2I-K^*K)$. Then
  there are orthonormal sequences $(e_n)$ in $X$ and $(g_n)$ in $Y$ with
  $$Ke_n=\sigma_ng_n,\qquad K^*g_n=\sigma_ne_n,$$
  and for every $x\in X$
  $$x=\sum_n(x,e_n)e_n+Qx,\qquad Kx=\sum_n\sigma_n(x,e_n)g_n,$$
  where $Q$ is the orthogonal projection onto $N(K)$. Hence
  $\|Kx\|^2=\sum_n\sigma_n^2|(x,e_n)|^2$ and $\sigma_1=\|K\|$. A triple
  $(\sigma_n,e_n,g_n)$ with these properties is a **singular system**. If
  there are infinitely many singular values, then $\sigma_n\to0$. Moreover
  $\overline{R(K)}=N(K^*)^\perp$ and $N(K)=R(K^*)^\perp$.

* **22.3. Picard criterion.** Let $K:X\to Y$ be compact with singular system
  $(\sigma_n,e_n,g_n)$. The equation $Kx=y$ has a solution if and only if
  $y\in N(K^*)^\perp$ and
  $$\sum_n\frac{|(y,g_n)|^2}{\sigma_n^2}<\infty .$$
  In that case $x=\sum_n\sigma_n^{-1}(y,g_n)e_n$ is a solution, and it is the
  solution in $N(K)^\perp$.

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

### Variational regularization in Banach spaces

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

### Bayesian inverse problems

* **22.11. Cameron–Martin space of a Gaussian prior.** Let $H$ be a
  separable real Hilbert space, let $\mu_0=N(0,C)$, and let
  $E=\mathrm{Im}(C^{1/2})$ be its Cameron–Martin space with the inner product
  of 24.13. Then $E$ is the intersection of all measurable linear subspaces
  of full $\mu_0$-measure, it is compactly embedded in every separable Banach
  space $X$ continuously embedded in $H$ with $\mu_0(X)=1$, and
  $\mu_0(E)=0$ if $E$ is infinite-dimensional. The equivalence and
  shift-density results for Gaussian measures are in 24.13.

* **22.12. Bayes' theorem in function space.** Let $X$ be a separable Banach
  space, $\mu_0$ a probability measure (the **prior**) on $X$,
  $G:X\to\mathbb R^q$ continuous, and $y=G(u)+\eta$, where $u\sim\mu_0$ and
  the noise $\eta$ is independent of $u$ with a Lebesgue density $\rho$ that
  is positive on all of $\mathbb R^q$. Let $\Phi(u;y)$ differ from
  $-\log\rho(y-G(u))$ by a function of $y$ alone. Then the conditional law
  $\mu^y$ of $u$ given $y$ (the **posterior**) is absolutely continuous with
  respect to $\mu_0$, and
  $$\frac{d\mu^y}{d\mu_0}(u)=\frac1{Z(y)}\exp\bigl(-\Phi(u;y)\bigr),\qquad
  Z(y)=\int_X\exp\bigl(-\Phi(u;y)\bigr)\,d\mu_0(u)>0.$$
  For Gaussian noise $\eta\sim N(0,\Gamma)$ with $\Gamma$ positive definite one
  may take $\Phi(u;y)=\frac12|\Gamma^{-1/2}(y-G(u))|^2$.

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

* **22.16. Accuracy of 3DVAR.** Let $\Psi:\mathbb R^n\to\mathbb R^n$,
  $H\in\mathbb R^{p\times n}$, $\Gamma$ positive definite, and fix a positive
  definite model covariance $\hat C$. Put $S=H\hat CH^\top+\Gamma$ and
  $L=\hat CH^\top S^{-1}$. The **3DVAR filter** is
  $m_{j+1}=(I-LH)\Psi(m_j)+Ly_{j+1}$. Let the true signal satisfy
  $v_{j+1}^\dagger=\Psi(v_j^\dagger)$, and the data
  $y_{j+1}=Hv_{j+1}^\dagger+\epsilon_j$ with $\sup_j|\epsilon_j|=\epsilon$. If
  $(I-LH)\Psi$ is globally Lipschitz with constant $a<1$ in some norm
  $\|\cdot\|$ on $\mathbb R^n$, then, for every initial value $m_0$,
  $$\limsup_{j\to\infty}\|m_j-v_j^\dagger\|\le\frac{c}{1-a}\,\epsilon,$$
  where $c=\max_{|e|\le1}\|Le\|$ depends only on $L$ and the chosen norm.

## 23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations

This section covers the plain Monte Carlo estimator and two variance
reduction methods, the Metropolis–Hastings chain, quasi-Monte Carlo rules
with their discrepancy and lattice-rule error bounds, the multilevel Monte
Carlo complexity theorem, the strong and weak convergence and the stability
of time-stepping schemes for Itô stochastic differential equations, the bias
of the invariant measure of a discretized Langevin dynamics, a time-uniform
error bound for interacting particle approximations of Feynman–Kac flows,
and the strong convergence of a fully discrete scheme for a parabolic
stochastic partial differential equation. The Karhunen–Loève expansion is
stated in section 24. Throughout, $(\Omega,\mathcal F,P)$ is a probability
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

* **23.2. Control variates.** Let $(Z,W)$ be a pair of real random
  variables with finite second moments, with $w=\mathbb E W$ known and
  $\sigma_W^2=\mathrm{Var}\,W>0$. Write $\sigma_Z^2=\mathrm{Var}\,Z$ and
  $\sigma_{ZW}=\mathrm{Cov}(Z,W)$. For every $\alpha\in\mathbb R$ the variable
  $Z+\alpha(W-w)$ has mean $\mathbb E Z$ and variance
  $$\sigma_Z^2+\alpha^2\sigma_W^2+2\alpha\sigma_{ZW}.$$
  This is minimized exactly at $\alpha^*=-\sigma_{ZW}/\sigma_W^2$, where it
  equals $\sigma_Z^2-\sigma_{ZW}^2/\sigma_W^2$, which is $\sigma_Z^2(1-\rho^2)$
  with $\rho=\mathrm{Corr}(Z,W)$ when $\sigma_Z>0$. So the optimal control
  never increases the variance. If $(Z_r,W_r)$ are independent copies of
  $(Z,W)$ with sample means $\hat z,\hat w$, sample covariance $s_{ZW}$ and
  sample variance $s_W^2$, and $\hat\alpha=-s_{ZW}/s_W^2$, then the
  **control variate estimator** $\hat z_{\mathrm{CV}}=\hat z+\hat\alpha(\hat w-w)$
  satisfies
  $$\sqrt R\,(\hat z_{\mathrm{CV}}-\mathbb E Z)\to
  N\bigl(0,\sigma_Z^2-\sigma_{ZW}^2/\sigma_W^2\bigr)$$
  in distribution as $R\to\infty$.

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

* **23.14. Invariant measure of discretized Langevin dynamics.** Let
  $V\in C^\infty(\mathbb T_L^d)$ on the torus $\mathbb T_L^d=(L\mathbb T)^d$,
  let $\beta>0$, and consider overdamped Langevin dynamics
  $dq_t=-\nabla V(q_t)\,dt+\sqrt{2/\beta}\,dW_t$, with generator
  $\mathcal L=-\nabla V\cdot\nabla+\beta^{-1}\Delta$ and invariant probability
  measure $\nu(dq)=Z^{-1}e^{-\beta V(q)}dq$. The Euler–Maruyama scheme
  $q^{n+1}=q^n-\Delta t\nabla V(q^n)+\sqrt{2\Delta t/\beta}\,G^n$, with
  independent standard Gaussian vectors $G^n$, has an invariant probability
  measure $\pi_{\Delta t}$ for all sufficiently small $\Delta t>0$, and for every
  $\varphi\in C^\infty(\mathbb T_L^d)$ there are $C_\varphi,\Delta t^*>0$ such
  that for $0<\Delta t\le\Delta t^*$
  $$\int\varphi\,d\pi_{\Delta t}=\int\varphi\,d\nu+\Delta t\int\varphi f_2\,d\nu
  +\Delta t^2R_{\varphi,\Delta t},\qquad|R_{\varphi,\Delta t}|\le C_\varphi,$$
  with
  $$f_2=-\frac12\Bigl(\Delta V-\frac\beta2|\nabla V|^2-\frac{a_{\beta,V}}2\Bigr),
  \qquad a_{\beta,V}=\int\Delta V\,d\nu=\beta\int|\nabla V|^2\,d\nu .$$
  This is the case $p=1$, $A_1=\mathcal L$, of the following general result.
  Let the state space $\mathcal X$ be $\mathbb R^d$ or a torus, let
  $K_n:\mathcal X\to[1,\infty)$ with $K_n\le K_{n+1}$, write
  $\|\varphi\|_{L^\infty_{K}}=\sup|\varphi|/K$, and let $\mathcal S$ be the set of
  $\varphi\in C^\infty(\mathcal X)$ such that each derivative of $\varphi$ has
  finite $L^\infty_{K_m}$-norm for some $m$ (on a torus one may take $K_n=1$,
  so $\mathcal S=C^\infty$). Let $\pi$ be the invariant probability measure of
  the continuous dynamics, $\mathcal S_0=\{\varphi\in\mathcal S:\int\varphi\,d\pi=0\}$,
  and let a scheme have one-step operator
  $P_{\Delta t}\varphi(x)=\mathbb E(\varphi(x^{n+1})\mid x^n=x)$. Assume:
  - $\mathcal S$ is dense in $L^2(\pi)$, every $K_n$ is in $L^2(\pi)$, and for
    each $\varphi\in\mathcal S_0$ the equations $A_1\Phi=\varphi$ and
    $A_1^*\Phi=\varphi$ (adjoint in $L^2(\pi)$) have unique solutions, which
    lie in $\mathcal S_0$;
  - for some integer $p\ge1$ and every $\varphi\in\mathcal S$,
    $P_{\Delta t}\varphi=\varphi+\sum_{k=1}^{p+1}\Delta t^kA_k\varphi
    +\Delta t^{p+2}r_{\varphi,\Delta t}$ with operators $A_k$ mapping
    $\mathcal S$ into $\mathcal S$ and
    $\|r_{\varphi,\Delta t}\|_{L^\infty_{K_m}}\le K$ for $\Delta t\le\Delta t^*$,
    where $K,m,\Delta t^*$ may depend on $\varphi$;
  - $\int A_k\varphi\,d\pi=0$ for all $\varphi\in\mathcal S$ and
    $1\le k\le p$, and $g_{p+1}=A_{p+1}^*\mathbb 1\in\mathcal S_0$;
  - the scheme has an invariant probability measure $\pi_{\Delta t}$ with
    $\int K_n\,d\pi_{\Delta t}<\infty$ for all $n$.

  Then for every $\varphi\in\mathcal S$ there is $C_\varphi$ such that for
  $0<\Delta t\le\Delta t^*$
  $$\int\varphi\,d\pi_{\Delta t}=\int\varphi\,d\pi+\Delta t^p\int\varphi
  f_{p+1}\,d\pi+\Delta t^{p+1}R_{\varphi,\Delta t},\qquad
  |R_{\varphi,\Delta t}|\le C_\varphi,\qquad f_{p+1}=-(A_1^*)^{-1}g_{p+1}.$$
  The moment condition holds when $A_k=\mathcal L^k/k!$ for $k\le p$, that
  is, for a scheme of weak order $p$; it can also hold for schemes that are
  not of weak order $p$.

* **23.15. Time-uniform particle approximation of Feynman–Kac flows.** Let
  $(E_n)_{n\ge0}$ be measurable spaces, $\eta_0$ a probability measure on
  $E_0$, $M_n$ Markov kernels from $E_{n-1}$ to $E_n$, and $G_n:E_n\to(0,\infty)$
  measurable potentials. Let $(X_n)$ be the Markov chain with initial law
  $\eta_0$ and transitions $M_n$, and define the **Feynman–Kac flow**
  $\eta_n(f)=\gamma_n(f)/\gamma_n(1)$ with
  $\gamma_n(f)=\mathbb E[f(X_n)\prod_{p=0}^{n-1}G_p(X_p)]$. Then
  $\eta_n=\Phi_n(\eta_{n-1})$ where
  $\Phi_n(\mu)(f)=\mu(G_{n-1}M_nf)/\mu(G_{n-1})$. The **$N$-particle model**
  has $\xi_0^1,\dots,\xi_0^N$ independent with law $\eta_0$ and, given
  $\xi_{n-1}$, particles $\xi_n^1,\dots,\xi_n^N$ independent with law
  $\Phi_n(\eta_{n-1}^N)$, where $\eta_n^N=N^{-1}\sum_{i=1}^N\delta_{\xi_n^i}$.
  Suppose:
  - (G) $G_n(x)\ge\varepsilon_n(G)G_n(y)$ for all $x,y\in E_n$, with
    $\varepsilon_n(G)\in(0,1]$;
  - $(\mathrm M)_m$ for some integer $m\ge1$,
    $M_{p+1}M_{p+2}\cdots M_{p+m}(x,\cdot)\ge\varepsilon_p(M)\,
    M_{p+1}\cdots M_{p+m}(y,\cdot)$ as measures for all $p\ge0$ and
    $x,y\in E_p$, with $\varepsilon_p(M)\in(0,1)$;
  - $\varepsilon(G)=\inf_n\varepsilon_n(G)>0$ and $\varepsilon(M)=\inf_n\varepsilon_n(M)>0$.

  Then for every $N\ge1$
  $$\sup_{n\ge0}\ \sup_f\ \sqrt N\,\bigl(\mathbb E|\eta_n^N(f)-\eta_n(f)|^2\bigr)^{1/2}
  \le\frac{2m}{\varepsilon(M)^3\,\varepsilon(G)^{2m-1}},$$
  the inner supremum over measurable $f:E_n\to\mathbb R$ with
  $\sup_{x,y}|f(x)-f(y)|\le1$. Similar bounds hold for the $p$-th moments
  for every integer $p\ge1$, with $2$ replaced by a constant depending on $p$.

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

## 24. High-dimensional approximation, uncertainty quantification, and model reduction

This section covers sparse grids, the worst-case complexity and tractability
of multivariate problems, Kolmogorov widths and greedy reduced bases, the
holomorphy and polynomial approximation of parametric solution maps,
projection-based model reduction (proper orthogonal decomposition, reduced
basis error bounds, empirical interpolation, balanced truncation and rational
interpolation), Gaussian measures, Karhunen–Loève and polynomial chaos
expansions, stochastic Galerkin methods, and approximation rates of ReLU
networks. Here $d$ denotes the number of variables of the functions being
approximated. For a multi-index $l\in\mathbb N^d$ write
$|l|_1=l_1+\cdots+l_d$ and $|l|_\infty=\max_j l_j$; inequalities between
multi-indices hold componentwise, and $\mathbf 1=(1,\dots,1)$. Weak greedy
selection uses a constant $\gamma\in(0,1]$. Quasi-Monte Carlo lattice rules
and their error bounds are in section 23, and low-rank and tensor
approximation in section 6.

### Sparse grids

* **24.1. Hierarchical basis.** Let $\Omega=(0,1)^d$ and let
  $\phi(t)=\max(1-|t|,0)$. For a level $l\in\mathbb N^d$ put
  $h_l=(2^{-l_1},\dots,2^{-l_d})$, and for $i\in\mathbb N^d$ with
  $1\le i_j\le 2^{l_j}-1$ let
  $$\phi_{l,i}(x)=\prod_{j=1}^d\phi\bigl(2^{l_j}x_j-i_j\bigr),$$
  the piecewise $d$-linear **hat function** centred at the grid point
  $x_{l,i}=(i_1h_{l_1},\dots,i_dh_{l_d})$. Let
  $I_l=\{i:1\le i_j\le2^{l_j}-1,\ i_j\text{ odd for all }j\}$ and let the
  **hierarchical increment** be $W_l=\mathrm{span}\{\phi_{l,i}:i\in I_l\}$.
  The functions spanning $W_l$ have pairwise disjoint interiors of supports,
  $$\dim W_l=|I_l|=2^{|l|_1-d},$$
  and the full-grid space $V_l=\mathrm{span}\{\phi_{l,i}:1\le i_j\le 2^{l_j}-1\}$
  is the direct sum $V_l=\bigoplus_{k\le l}W_k$; its basis
  $\{\phi_{k,i}:i\in I_k,\ k\le l\}$ is the **hierarchical basis**. For
  $q\in\{2,\infty\}$ let $X^{q,2}_0$ be the space of functions
  $u:\bar\Omega\to\mathbb R$ that vanish on $\partial\Omega$ and have
  $D^\alpha u\in L^q(\Omega)$ for all $\alpha$ with $|\alpha|_\infty\le2$,
  and write $|u|_{2,q}=\|D^{(2,\dots,2)}u\|_{L^q(\Omega)}$. Each
  $u\in X^{q,2}_0$ has a unique expansion $u=\sum_{l\in\mathbb N^d}u_l$ with
  $u_l=\sum_{i\in I_l}v_{l,i}\phi_{l,i}\in W_l$, the series converging in
  $H^1(\Omega)$. The coefficients $v_{l,i}$, the **hierarchical surpluses**,
  and the components satisfy
  $$|v_{l,i}|\le 2^{-d}\,2^{-2|l|_1}|u|_{2,\infty},\qquad
  \|u_l\|_{L^\infty}\le 2^{-d}\,2^{-2|l|_1}|u|_{2,\infty},\qquad
  \|u_l\|_{L^2}\le 3^{-d}\,2^{-2|l|_1}|u|_{2,2}.$$

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

* **24.15. Wiener–Hermite polynomial chaos.** Let $\gamma_d=N(0,I)$ be the
  standard Gaussian measure on $\mathbb R^d$ and let $\mathrm{He}_n$ be the
  Hermite polynomials, orthogonal for $\gamma_1$ with
  $\int\mathrm{He}_m\mathrm{He}_n\,d\gamma_1=n!\,\delta_{mn}$. For
  $\alpha\in\mathbb N_0^d$ put
  $\mathrm{He}_\alpha(\xi)=\prod_{j=1}^d\mathrm{He}_{\alpha_j}(\xi_j)$.
  Then $\{\mathrm{He}_\alpha:\alpha\in\mathbb N_0^d\}$ is a complete
  orthogonal system in $L^2(\mathbb R^d,\gamma_d)$ with
  $\|\mathrm{He}_\alpha\|^2=\alpha!=\prod_j\alpha_j!$. Every
  $U\in L^2(\mathbb R^d,\gamma_d)$ has the **polynomial chaos expansion**
  $U=\sum_\alpha u_\alpha\mathrm{He}_\alpha$ with
  $u_\alpha=\langle U,\mathrm{He}_\alpha\rangle/\alpha!$, converging in
  $L^2(\gamma_d)$; its mean is $u_0$ and its variance is
  $\sum_{\alpha\ne0}\alpha!\,u_\alpha^2$, and each truncation is the
  orthogonal projection onto the span of the retained polynomials.

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

## Reference guide

The [bibliography](NASC-bib.md) lists the main texts, monographs and
surveys. Locators for the local sources use the printed pagination of the copies in `References/`,
read from the running heads, and theorem and equation numbers are those of
these copies. Several local copies are editions other than the one the
bibliography lists. Higham's *Accuracy and Stability of Numerical
Algorithms* is the first edition (1996). Golub–Van Loan is a partial copy of
the third edition (1996). Horn–Johnson's *Matrix Analysis* is the first
edition (1985). Butcher is the 2003 edition. Hackbusch's *Tensor Spaces* is
the first edition (2012). Saad's *Iterative Methods for Sparse Linear
Systems* is the author manuscript of the second edition, whose numbering
differs from the printed book. Trefethen's *Approximation Theory and
Approximation Practice* is the author manuscript. Hinze–Pinnau–Ulbrich–Ulbrich
is the 2009 Springer book. Acta Numerica surveys are cited by author, volume
and the printed pages of the article. Where a statement adds a hypothesis
that a source leaves implicit, corrects a misprint, or rests on a derivation
rather than on a printed statement, the guide says so.

### 1. Floating-point arithmetic and rounding error analysis

Higham is the first edition of *Accuracy and Stability of Numerical
Algorithms* (SIAM, 1996), the local copy. Muller et al. is the second edition
of the *Handbook of Floating-Point Arithmetic* (2018). Gautschi is the second
edition of *Numerical Analysis* (2012), Quarteroni–Sacco–Saleri the second
edition of *Numerical Mathematics* (2007), Stoer–Bulirsch the third edition of
*Introduction to Numerical Analysis* (2002), and Deuflhard–Hohmann the second
edition of *Numerical Analysis in Modern Scientific Computing* (2003). The
section follows the format conventions of Muller et al.: a number is
$M\beta^{e-p+1}$ with $|M|\le\beta^p-1$, so a normal number has
$1\le|x|/\beta^e<\beta$. Higham writes $y=\pm m\beta^{e-t}$ with
$\beta^{t-1}\le m\le\beta^t-1$, so his exponent is one larger and his exponent
range for IEEE single precision reads $-125\le e\le128$; the two descriptions
give the same sets. Quarteroni–Sacco–Saleri and Gautschi use a fraction
$0.d_1d_2\dots d_t$ and the same shift of exponent.

Item 1.1 is Muller et al., §2.1.1–2.1.2, pp. 15–19, with the values of
$\alpha$, $\beta^{e_{\min}}$ and $\Omega$ on pp. 18–19, and Higham, §2.1,
pp. 40–41, who also describes subnormal numbers. That every element of
$\mathbb F$ is a multiple of $\alpha$ is the observation in the proof of
Muller et al., Theorem 4.2, p. 102. Item 1.2 is the spacing statement in the
proof of Muller et al., Theorem 2.2, pp. 26–27, and Higham, Lemma 2.1, p. 41,
whose bounds are $\beta^{-1}\epsilon_M|x|$ and $\epsilon_M|x|$ with machine
epsilon $\epsilon_M=\beta^{1-t}$. Item 1.3 is Muller et al., §2.2.1,
pp. 22–23, the monotonicity remark on p. 25, the requirements of the
standard in §3.1.3.1, p. 70, and Table 3.1, p. 49; Higham, §2.1, p. 43,
gives the IEEE unit roundoffs.

Item 1.4 is Muller et al., Theorem 2.2, p. 26, Definition 2.3 and
Theorem 2.3, p. 27, and the subnormal bounds (2.4)–(2.5), p. 28. It is also
Higham, Theorem 2.2, p. 42, Quarteroni–Sacco–Saleri, Property 2.1, p. 51,
Gautschi, (1.13)–(1.14), p. 7, and Stoer–Bulirsch, (1.2.2), p. 5. The
statement in Quarteroni–Sacco–Saleri uses $x_{\min}=\beta^{L-1}$ as the lower
end of the range, which is the smallest normal number in their convention;
Stoer–Bulirsch prove (1.2.4) under the idealized assumption of an unbounded
exponent range. Item 1.5 is Muller et al., (2.6)–(2.7) and the refinement
for rounding to nearest, p. 28, together with Theorem 4.2 (Hauser), p. 102,
for underflow in sums. The model is Higham, (2.4)–(2.5), p. 44,
Quarteroni–Sacco–Saleri, (2.36), p. 52, Stoer–Bulirsch, (1.2.6), p. 7, and
Gautschi, (1.15), p. 7. Higham and Quarteroni–Sacco–Saleri point out that
without a guard digit the model can fail for subtraction; the IEEE standard
excludes this by requiring correct rounding.

Item 1.6 is Muller et al., Lemma 4.1, p. 101, which assumes that subnormal
numbers are available (as in the definition of $\mathbb F$ here), and Higham,
Theorem 2.5, p. 50, who assumes a guard digit and no underflow. Item 1.7 is
Muller et al., Theorem 4.3, p. 104 (Fast2Sum), the discussion of
Algorithm 4.4, p. 108 (2Sum, Knuth for normal inputs in any radix, Boldo et
al. for the radix-$2$ case with underflow), and condition (4.2) with
Algorithm 4.8, pp. 111–112 (2MultFMA); Higham, (4.7), p. 93, states the
Fast2Sum identity in base $2$ for $|a|\ge|b|$.

Item 1.8 is Higham, Lemma 3.1, p. 69, Lemma 3.3, p. 74, and Lemma 3.4,
pp. 74–75, and Muller et al., Definition 5.1, p. 166. Item 1.9 is Higham,
Algorithm 4.1 and (4.1)–(4.4), pp. 89–90, with the backward error statement
after (4.4), p. 90, and (4.6), p. 92, for pairwise summation; Higham's
(4.4) is the first-order form, and the rigorous $\gamma_{n-1}$ form is the
backward error result on p. 90. It is also Muller et al., (5.5), p. 168,
and Theorem 5.1 (Rump), p. 171, stated there for any radix. Item 1.10 is
Higham, (3.3)–(3.5), p. 69, (3.10)–(3.11), p. 76, and (3.12) with the
normwise bounds, p. 78, and Muller et al., (5.6), p. 168; the bound with
$nu$ is reported in Muller et al., p. 172, from Jeannerod and Rump, without
proof. Item 1.11 is Higham, (5.2)–(5.3), pp. 104–105, and Muller et al.,
(5.7) and the remark on the fused multiply-add, p. 168.

Item 1.12 is Higham, Algorithm 4.2 and (4.8)–(4.9), pp. 93–94, for Kahan's
method, with the same bound in Muller et al., (5.14), p. 179; neither source
makes the $O(nu^2)$ term explicit, and Higham attributes the proof to Knuth.
The cascaded summation bound is Muller et al., Algorithm 5.11 and
Theorem 5.7 (Rump, Ogita and Oishi), p. 182, and Priest's bound is Muller et
al., Algorithm 5.9 and Theorem 5.6, p. 181. Item 1.13 is Higham, Theorem 8.5,
p. 154, and the forward error bound at the start of §8.2, p. 155.
Deuflhard–Hohmann, Theorem 2.34, p. 46, state the backward error for forward
substitution as $|\widetilde L-L|\le n\,\mathrm{eps}\,|L|$, which is the
first-order form of Higham's $\gamma_n$ bound.

Mixed-precision iterative refinement is not stated in this section. Higham,
Theorems 11.1–11.2, p. 234, and Higham and Mary, Acta Numerica 31 (2022),
Theorem 6.1, p. 369, give its convergence only in approximate form ("reduces
the error by a factor approximately $\eta$"); the precise one-step recurrence
is Higham, (11.4), p. 233, and the topic belongs with section 3.

### 2. Conditioning and matrix perturbation theory

Higham is the 1996 first edition, Horn–Johnson the 1985 first edition of
*Matrix Analysis*, Golub–Van Loan the third edition (1996, a partial local
copy), Trefethen–Bau the 1997 SIAM edition, Trefethen–Embree the 2005
Princeton edition, and the other texts are the editions listed for section 1.
Horn–Johnson order the eigenvalues of a Hermitian matrix increasingly; their
statements have been translated to the decreasing order used here.
Horn–Johnson write $\|\cdot\|_2$ for the Frobenius norm and
$|\!|\!|\cdot|\!|\!|_2$ for the spectral norm.

Item 2.1 is Trefethen–Bau, (12.1)–(12.6), pp. 89–90, Gautschi, (1.25)–(1.28),
pp. 13–14, and Deuflhard–Hohmann, Definition 2.2, p. 26, and (2.1), p. 27.
Trefethen–Bau and Gautschi state the Jacobian formulas without listing the
hypotheses; the formulation with Fréchet differentiability, $x\ne0$ and
$f(x)\ne0$ is the one needed for the identity. Item 2.2 is Higham, the
definition on p. 122 and Theorem 6.4, p. 123; the expression of $\kappa_2$ by
singular values is Quarteroni–Sacco–Saleri, p. 61. Item 2.3 is Higham, Theorem
6.5 (Gastinel, Kahan), pp. 123–124, stated there for mixed subordinate norms,
with the rank-one minimizer from Lemma 6.3, p. 122; it is also
Quarteroni–Sacco–Saleri, Remark 3.1, p. 61, for $p$-norms, where the
nonsingularity criterion (3.7) is also stated. Trefethen–Embree, Theorem 4.1,
p. 28, give the nonsingularity criterion with the bound
$\|(A+E)^{-1}\|\le\|A^{-1}\|/(1-\|E\|\|A^{-1}\|)$ for operators.

Item 2.4 is Higham, Theorem 7.2 and the subsequent formula for
$\kappa_{E,f}(A,x)$, p. 133, and Quarteroni–Sacco–Saleri, Theorem 3.1, p. 62,
which is the case $E=A$, $f=b$ in the form $\|\delta
x\|/\|x\|\le\kappa(A)/(1-\kappa(A)\|\delta A\|/\|A\|)\, (\|\delta
b\|/\|b\|+\|\delta A\|/\|A\|)$. A related bound, under the hypotheses of Lemma
2.7.1, is Golub–Van Loan, Theorem 2.7.2, p. 83. Higham states the result for
real matrices; the proof is the same over $\mathbb C$. Item 2.5 is Higham,
Theorem 7.1 (Rigal and Gaches), p. 132, and Deuflhard–Hohmann, Theorem 2.38,
p. 50, for $E=A$, $f=b$. Higham writes the backward error as a minimum without
stating the nondegeneracy condition $\|E\|\|y\|+\|f\|>0$, which is needed for
the formula. Item 2.6 is Higham, Theorem 7.3 (Oettli and Prager), Theorem 7.4
and (7.10), p. 135, and Deuflhard–Hohmann, Theorem 2.39, p. 50, for $E=|A|$,
$f=|b|$. The page of Higham's §7.2 that precedes p. 135 carries the misprinted
running head "133".

Item 2.7 is Horn–Johnson, Theorem 4.2.11, p. 179, with the subspace form in
Problem 1, p. 180, and Stoer–Bulirsch, Theorem (6.9.14), p. 453, which uses
the decreasing order. Item 2.8 is Horn–Johnson, Theorem 4.3.1, p. 181, Theorem
4.3.7, pp. 184–185, and Corollary 4.3.3, p. 182, for the positive semidefinite
case; the bound by $\|B\|_2$ is the exercise after Corollary 6.3.4, p. 367.
Item 2.9 is Horn–Johnson, Theorem 4.3.8, pp. 185–186, and Theorem 4.3.15, p.
189. Item 2.10 is Horn–Johnson, Corollary 7.3.8 and Theorem 7.3.9, p. 419, and
Theorem 7.4.51, p. 448. Item 2.11 is Horn–Johnson, Theorem 6.3.5, p. 368,
Corollary 6.3.8 and the exercises following it, p. 370; the Hermitian form is
also the consequence of Mirsky's theorem in item 2.10 applied to eigenvalues.

Item 2.12 is Horn–Johnson, Theorem 6.1.1, p. 344, which requires the $k$ discs
to form a connected region disjoint from the others, and
Quarteroni–Sacco–Saleri, Theorem 5.2, p. 184, (5.6) and Property 5.2, p. 185,
which require only disjointness, as stated here; Stoer–Bulirsch, Theorem
(6.9.4), p. 444, give the inclusion. Item 2.13 is Horn–Johnson, Theorem 6.3.2,
p. 365, and Corollary 6.3.4, p. 367, Quarteroni–Sacco–Saleri, Theorem 5.3 and
(5.9), p. 187, for $p$-norms, and Stoer–Bulirsch, Theorems (6.9.6)–(6.9.7), p.
447, for absolute norms. Trefethen–Bau state it for the $2$-norm as Exercise
26.3, p. 201. Item 2.14 is Stoer–Bulirsch, Theorem (6.9.8), pp. 447–448, which
gives the analytic branch; Horn–Johnson, Lemma 6.3.10, p. 371, and Theorem
6.3.12, p. 372; and Quarteroni–Sacco–Saleri, Theorem 5.4 and (5.11), p. 188,
who also assume $A$ diagonalizable and normalize $\|x\|_2=\|y\|_2=1$. That the
supremum is attained by the rank-one $E$ is a direct computation from the
derivative formula, not stated in these sources.

Item 2.15 is Higham, Theorem 19.1 (Wedin), p. 392, with the example on p. 393.
Higham assumes that $A$ and $A+\Delta A$ both have full rank and leaves the
hypothesis $x\ne0$ implicit; the full rank of $A+\Delta A$ follows from
$\kappa_2(A)\varepsilon<1$ by item 2.10. The example has
$\kappa_2(A)\varepsilon=1$, at the boundary of the theorem's hypothesis, and
serves only to show that the $\kappa_2(A)^2$ dependence is attained. First
order versions are Golub–Van Loan, Theorem 5.3.1, p. 242, and Trefethen–Bau,
Theorem 18.1, p. 131. Item 2.16 is Trefethen–Embree, definitions (2.1), (2.3)
and (2.6), pp. 13, 14 and 16, Theorem 2.1, p. 16, (2.10), p. 17, Theorems 2.2,
p. 19, and 2.3 and 2.4(i), p. 20; the equivalence holds for an arbitrary norm
on $\mathbb C^N$ with its induced matrix norm. Theorem 4.3, p. 31, gives the
same equivalence for closed operators on Banach spaces.

Item 2.17 is the finite-dimensional $\sin\Theta$ theorem in Davis–Kahan,
[The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001),
SIAM Journal on Numerical Analysis 7 (1970), with the perturbation form
also given by Yu–Wang–Samworth, [A Useful Variant of the Davis–Kahan Theorem
for Statisticians](https://arxiv.org/pdf/1405.0680), Theorem 1 and the
discussion following it, p. 2 of the preprint, and the residual numerator
discussed on p. 4. Item 2.18 is the leading-subspace case of
[Wedin's perturbation theorem](https://doi.org/10.1007/BF01932678),
as stated in d'Aspremont–Cucuringu–Tyagi, [Ranking and Synchronization via
SVD](https://www.jmlr.org/papers/volume22/19-542/19-542.pdf), Theorem 22,
p. 51.

### 3. Direct methods for linear systems and least squares

Locators in this section refer to Higham, *Accuracy and Stability of
Numerical Algorithms*, 1st ed. (1996); Trefethen–Bau (1997); Golub–Van Loan,
3rd ed. (1996), cited from the partial scanned copy; Stoer–Bulirsch, 3rd ed.
(2002); and two Acta Numerica surveys, Davis–Rajamanickam–Sid-Lakhdar
(Vol. 25, 2016, pp. 383–566) and Higham–Mary (Vol. 31, 2022, pp. 347–414).
Higham and Golub–Van Loan work over $\mathbb R$, Trefethen–Bau over
$\mathbb C$. The rounding error statements follow Higham, whose bounds are
rigorous and explicit; Trefethen–Bau and Golub–Van Loan give the same
results in $O(\epsilon_{\mathrm{machine}})$ or first-order form.

Item 3.1 is Higham, Theorem 9.1, p. 171, with the determinant identity (9.1)
on p. 172, and Golub–Van Loan, Theorem 3.2.1, p. 97. Golub–Van Loan prove
existence when $A_k$ is nonsingular for $k\le n-1$ and uniqueness only for
nonsingular $A$; Higham states the equivalence without assuming $A$
nonsingular and proves the converse for nonsingular $A$, leaving the
singular case to Problem 9.1. The statement about the pivots follows from
$u_{kk}=\det A_k/\det A_{k-1}$ (Higham, p. 172). Item 3.2 is Trefethen–Bau,
(21.7) and the paragraph after it, p. 160, which asserts the factorization
for every square matrix, singular or not, and Algorithm 21.1, p. 160;
Golub–Van Loan, Theorem 3.4.1, p. 113; Higham, pp. 173 and 176; and
Stoer–Bulirsch, (4.1.9), p. 195.

Item 3.3 is Higham, Theorems 9.3 and 9.4, p. 175. The constant $2\gamma_n$ in
the solve bound, rather than $3\gamma_n+\gamma_n^2$, comes from the proof on
p. 176, and the bound for nonnegative factors is (9.8), p. 176. The remark
on pivoting is Higham, p. 174. Golub–Van Loan, Theorems 3.3.1 and 3.3.2,
pp. 105–106, give the first-order bounds
$|H|\le3(n-1)u(|A|+|\widehat L||\widehat U|)+O(u^2)$ and
$|E|\le nu(3|A|+5|\widehat L||\widehat U|)+O(u^2)$ for their outer-product
algorithm, and Trefethen–Bau, Theorem 22.1, p. 164, gives the normwise form
$\|\delta A\|/(\|L\|\|U\|)=O(\epsilon_{\mathrm{machine}})$.

Item 3.4 is Higham's definition of $\rho_n$ and Theorem 9.5, (9.9), p. 177.
Higham points out on the same page that the derivation applies the bounds
$|l_{ij}|\le1$ and $|u_{ij}|\le\rho_n\max|a_{ij}|$, which hold for the exact
factors, to the computed ones. The synopsis therefore states these bounds as
hypotheses on the computed factors; under them the result follows from
Theorem 9.4 and $\||\widehat L||\widehat U|\|_\infty\le n\cdot n\rho
\max|a_{ij}|$. Trefethen–Bau, (22.2), p. 164, define the growth factor as
$\max|u_{ij}|/\max|a_{ij}|$, using only the final $U$, and state the
corresponding result as Theorem 22.2, p. 165. Item 3.5 is Higham, p. 177,
where the bounds $|u_{ij}|\le2^{i-1}\max_{k\le i}|a_{kj}|$ and
$\rho_n\le2^{n-1}$ and the extremal matrix appear, with Theorem 9.6, p. 178,
characterizing all real matrices that attain $2^{n-1}$; and Trefethen–Bau,
(22.4)–(22.5), pp. 165–166, with Exercise 22.1 for the bound. The tie-breaking
rule is implicit in both sources: every pivot candidate in the extremal
matrix has modulus $1$.

Item 3.6 is Higham, Theorem 9.8 (Wilkinson), p. 181, proved through the
block version, Theorem 12.5, p. 252, which assumes $A$ nonsingular; hence the
nonsingularity hypothesis, which Theorem 9.8 leaves implicit. Golub–Van
Loan, Theorem 3.4.3, p. 120, give the column case for strictly diagonally
dominant matrices. The positive definite case is Higham, p. 206, where the
growth factor is stated to be exactly $1$ (Problem 10.4), together with the
positivity of the pivots on p. 204.

Item 3.7 is Trefethen–Bau, Theorem 23.1, p. 174, for Hermitian matrices;
Higham, Theorem 10.1, p. 204; and Golub–Van Loan, Theorem 4.2.5, p. 143,
in the form $A=GG^\top$. The formula for $r_{kk}^2$ follows from
$u_{kk}=\det A_k/\det A_{k-1}$, Higham, p. 204. Item 3.8 is Higham, Theorems
10.3 and 10.4, p. 206, with the normwise consequence (10.7), p. 206, and
Theorem 10.7 (Demmel), p. 208, for the success and failure criteria; and
Trefethen–Bau, Theorems 23.2 and 23.3, pp. 176–177, in
$O(\epsilon_{\mathrm{machine}})$ form. The perturbation $\Delta A$ for the
solve is not symmetric in general (Higham, p. 206).

Item 3.9 is Trefethen–Bau, Theorems 7.1 and 7.2, pp. 51–52, and Golub–Van
Loan, Theorems 5.2.1 and 5.2.2, pp. 229–230, the latter with the Cholesky
characterization of $R_1$. Item 3.10 is Higham, Theorem 18.4, p. 368. The
constant $\tilde\gamma_m$ is Higham's $\gamma_{cm}$ of p. 366, and the
hypothesis is Higham's assumption (18.4), p. 367, $mr\gamma_{cm}<1/2$ with
$r\le n$ Householder transformations. Trefethen–Bau, Theorem 16.1, p. 116,
give the normwise $O(\epsilon_{\mathrm{machine}})$ version over
$\mathbb C$.

Item 3.11 is Trefethen–Bau, Theorem 11.1 and the text following it,
pp. 80–81, and Stoer–Bulirsch, Theorem (4.8.1.3), p. 233. The formula
through QR is Higham, p. 395. Item 3.12 is Stoer–Bulirsch, §4.8.5,
pp. 243–246: Theorem (4.8.5.1) for the projector properties and the Penrose
conditions, Theorem (4.8.5.2) for uniqueness, Corollary (4.8.5.3), and
Theorem (4.8.5.4) for the minimum-norm solution, followed by the full-rank
formula on p. 246. The singular value formula and the minimum-norm property
are Golub–Van Loan, Theorem 5.5.1 and §5.5.4, p. 257, where $A^+$ is also
characterized as the minimal Frobenius norm solution of
$\min_X\|AX-I_m\|_F$. Stoer–Bulirsch work over $\mathbb C$, Golub–Van Loan
over $\mathbb R$. Item 3.13 is Higham, Theorem 19.3, p. 395, under the
standing assumption $mn\gamma_{cm}<1/2$ stated on the same page, and
Trefethen–Bau, Theorem 19.1, p. 140, in normwise form.

Item 3.14 is Higham, §11.1, pp. 232–234: the solver model (11.1) and the
iteration on p. 232, the residual bound (11.2), the identity (11.3) and the
recurrence (11.4) on p. 233. The $\limsup$ bound is an immediate consequence
of (11.4). Higham's Theorems 11.1 and 11.2, p. 234, summarize the
consequences for LU factorization informally. With residuals in doubled
precision ($\bar u=u^2$), and provided
$\eta=u\||A^{-1}||\widehat L||\widehat U|\|_\infty$ is sufficiently less than
$1$, the error contracts by a factor of about $\eta$ per step until the
relative error is about $u$. With $\bar u=u$ the limiting relative error is
about $2n\,\mathop{\mathrm{cond}}(A,x)u$, where
$\mathop{\mathrm{cond}}(A,x)=\||A^{-1}||A||x|\|_\infty/\|x\|_\infty$. These
are not stated in the synopsis as theorems, since the sources give them only
approximately. Higham–Mary, Theorem 6.1, p. 369 (from Carson and Higham),
gives the same kind of statement for three precisions $u_r\le u\le u_\ell$:
the limiting accuracy is approximately
$u+4p\mathop{\mathrm{cond}}(A,x)u_r$, with $p$ the maximal number of nonzeros
in a row of $[A\ b]$, whatever the solver precision $u_\ell$.

Item 3.15 is Davis–Rajamanickam–Sid-Lakhdar, pp. 395–397. Parter's
observation, p. 396, and the path lemma of Rose, Tarjan and Lueker, p. 397,
are both stated there in the convention that numerical
cancellation is neglected. The synopsis separates the purely graph-theoretic
statement from the inclusion of the nonzero pattern of $L$. The elimination
rule for graphs, including the pivot clique, is Stoer–Bulirsch, §4.12,
(4.12.2)–(4.12.3), pp. 276–277. Item 3.16 is Davis–Rajamanickam–Sid-Lakhdar,
§4.1, pp. 396–398, for the definition of the elimination tree, Liu's theorem
and the postordering, and §4.2.1, p. 399, for the row subtrees. The survey
gives these results in prose with references to the original papers (Liu
1990 for the elimination tree); the formulation in terms of $G^+$ is the
standard one and was not checked against a further local source.

### 4. Eigenvalue and singular value computations

Horn–Johnson is the first edition of *Matrix Analysis* (1985).
Trefethen–Bau is *Numerical Linear Algebra* (SIAM, 1997). Stoer–Bulirsch is
the third edition (2002), and Quarteroni–Sacco–Saleri is the second edition
(2007). Golub–Van Loan is the third edition (1996), of which the local copy
contains Chapters 1–6 only; its chapters on the unsymmetric and symmetric
eigenvalue problems and on Lanczos methods could not be consulted. Güttel and
Tisseur, "The nonlinear eigenvalue problem", is Acta Numerica 26 (2017),
pp. 1–94.

Item 4.1 is Horn–Johnson, Theorem 2.3.1, p. 79, for the complex and the real
triangular form, and Theorem 2.3.4, p. 82, for the real Schur form; also
Trefethen–Bau, Theorem 24.9, p. 187, Stoer–Bulirsch, Theorem (6.4.1), p. 379,
and Quarteroni–Sacco–Saleri, Property 1.5, p. 15. Item 4.2 is Horn–Johnson,
Theorem 2.5.4, p. 101, and Theorem 4.1.5, p. 171; Trefethen–Bau, Theorems
24.7 and 24.8, p. 187; and Stoer–Bulirsch, Theorems (6.4.2) and (6.4.5),
p. 381. Item 4.3 is Horn–Johnson, Theorem 7.3.5, p. 414; Trefethen–Bau,
Theorem 4.1, p. 29, and Theorems 5.1, 5.3, 5.4 and 5.5, pp. 33–34;
Golub–Van Loan, Theorem 2.5.2, p. 70, for the real case, with (2.5.3) and
(2.5.7)–(2.5.8), p. 71; and Quarteroni–Sacco–Saleri, Property 1.7, p. 17. The
block identity for the $2n\times2n$ Hermitian matrix is Trefethen–Bau,
(31.2)–(31.3), pp. 235–236. Horn–Johnson relate the singular values to the
eigenvalues of $AA^*$, Trefethen–Bau to those of $A^*A$ or $AA^*$.

Item 4.4 is Quarteroni–Sacco–Saleri, Theorem 5.6, p. 193, and Trefethen–Bau,
Theorem 27.1, p. 205, for the power method, and Trefethen–Bau, Theorem 27.2,
pp. 206–207, with Quarteroni–Sacco–Saleri, §5.3.2, pp. 195–196, for inverse
iteration. Trefethen–Bau assume throughout Lecture 27 that $A$ is real
symmetric; Quarteroni–Sacco–Saleri treat diagonalizable complex matrices but
state convergence of inverse iteration only as a limit. Their Theorem 5.6
bounds the unnormalized iterate $\tilde q^{(k)}$, a scalar multiple of
$q^{(k)}$, and gives the constant
$C=(\sum_{i\ge2}|\alpha_i/\alpha_1|^2)^{1/2}$; the proof uses orthogonality
of the eigenvectors, so for a general diagonalizable matrix only the
existence of a constant is claimed here, and the bound for the normalized
iterate follows with $C$ doubled. The bound on $|\lambda_1-\nu^{(k)}|$ for
symmetric matrices is Quarteroni–Sacco–Saleri, (5.23), p. 194, which has the
factor $|\lambda_1-\lambda_n|$ for eigenvalues ordered by modulus; this is
too small when $\lambda_1<0$ (for eigenvalues $-3,2,0$ and $q^{(0)}$
orthogonal to the third eigenvector it fails for large $k$), and the factor
$\max_i|\lambda_1-\lambda_i|$ used here is the one the expansion in
eigenvectors gives. Trefethen–Bau, Theorem 27.1, states the rate
$O(|\lambda_2/\lambda_1|^{2k})$ without a constant.

Item 4.5 is Trefethen–Bau, (27.2)–(27.3), pp. 203–204, and Theorem 27.3,
p. 208. The identity for $r(v)-\lambda$ is a direct computation from
$(A-\lambda I)q=0$ and the symmetry of $A$; Trefethen–Bau state it as
$r(x)-r(q_J)=O(\|x-q_J\|^2)$. Their Theorem 27.3 also asserts convergence
from almost every starting vector, without proof, and gives an eigenvalue
estimate $|\lambda^{(k+1)}-\lambda_J|=O(|\lambda^{(k)}-\lambda_J|^3)$; only
the eigenvector estimate, proved there for a simple eigenvalue, is stated
here, together with its consequence for the Rayleigh quotient.

Item 4.6 is Stoer–Bulirsch, Theorem (6.6.4.4), p. 418, and Trefethen–Bau,
Theorems 28.2 and 28.3, pp. 215–216. Trefethen–Bau state the equivalence of
simultaneous iteration and the QR algorithm without fixing a normalization of
the QR factors; the positive-diagonal normalization makes the factorizations
unique for nonsingular $A$ (section 3), which the identity of the two
sequences requires. Item 4.7 is Stoer–Bulirsch, Theorem (6.6.4.12),
pp. 421–423, and, for the real symmetric case with its rate, Trefethen–Bau,
Theorem 28.4, p. 218. Stoer–Bulirsch state the theorem without assuming
$\lambda_n\ne0$ but carry out the proof under that assumption, so it is
included here. Quarteroni–Sacco–Saleri, Property 5.9, pp. 201–202, state
convergence and the rate $|a^{(k)}_{i,i-1}|=O(|\lambda_i/\lambda_{i-1}|^k)$
for real matrices with real eigenvalues of distinct moduli but omit the
hypothesis on $X^{-1}$, which is needed for the eigenvalues to appear in the
order of decreasing modulus; that rate is not stated here.

Item 4.8 is Trefethen–Bau, Lecture 26, pp. 196–200, and Stoer–Bulirsch,
§6.5.4, p. 402, for the reduction; Stoer–Bulirsch, p. 425, for the
preservation of Hessenberg and Hermitian form, Theorem (6.6.5.5),
pp. 428–429, for the unreduced case and the deflation, (6.6.5.2)–(6.6.5.3),
p. 428, for the shifted iteration, and Theorem (6.6.5.8) with the shift
strategy (6.6.5.7b), p. 430, for Wilkinson's theorem. Stoer–Bulirsch give
Wilkinson's theorem without proof, citing Wilkinson (1968), and add that the
rate is cubic apart from rare exceptions. Item 4.9 is Stoer–Bulirsch, Theorem
(6.6.5.1), pp. 426–427; no second local source states it.

Item 4.10 is Trefethen–Bau, Theorem 26.1, p. 200, Theorem 29.1 and (29.10),
p. 223. Trefethen–Bau work in their model (13.5) and (13.7), which is the
standard model, and write $O(\epsilon_{\mathrm{machine}})$ with constants
depending on the dimension.

Item 4.11 is Stoer–Bulirsch, §6.5.2, pp. 395–397, and
Quarteroni–Sacco–Saleri, §5.10.1, pp. 226–228, with (5.64), p. 227, for the
decrease of $\Psi$; both sources give the formulas for $t$ in 4.11. Both state
the convergence of the cyclic method and its quadratic rate without proof,
citing Wilkinson (1962). Quarteroni–Sacco–Saleri, p. 228, give the bound
$\Psi(A^{(k+N)})\le\Psi(A^{(k)})^2/(\sqrt2\,\delta)$ for all $k$;
Stoer–Bulirsch, p. 397, give $S(A^{(i+N)})\le S(A^{(i)})^2/\delta$ with
$S=\Psi^2$, which is not homogeneous in $A$ and appears to be a misprint.
Wilkinson's result is asymptotic, so the bound is stated here for all
sufficiently large $k$.

Item 4.12 is Horn–Johnson, Corollary 4.3.16, p. 190, stated there with
eigenvalues in increasing order; the definition of Ritz values is
Trefethen–Bau, (33.10), p. 255, and Quarteroni–Sacco–Saleri, (5.67),
p. 234, for the extreme Ritz values. Item 4.13 is Trefethen–Bau, Theorem 33.1,
p. 255, Theorem 34.1, p. 259, and, for the Hermitian case, Theorem 36.1,
p. 278 (stated there for real symmetric $A$); Stoer–Bulirsch, §6.5.3,
(6.5.3.1)–(6.5.3.2), pp. 398–400, prove the Lanczos recurrence for Hermitian
$A$, the termination at the first $A$-invariant Krylov space, and that the
eigenvalues of the final tridiagonal matrix are eigenvalues of $A$.

Item 4.14 is Quarteroni–Sacco–Saleri, Property 5.12, p. 234, who refer to
Golub–Van Loan for the proof; Stoer–Bulirsch, p. 401, and Trefethen–Bau,
p. 340, cite Kaniel (1966), Paige (1971) and Saad (1980) without stating the
bound. Quarteroni–Sacco–Saleri define $\cos\varphi_n=|(q^{(n)})^\top u_n|$
in the second bound; the vector there is the Lanczos starting vector $q_1$,
as stated here. The hypotheses $\lambda_2>\lambda_n$ and
$\lambda_1>\lambda_{n-1}$ make $\rho_1$ and $\rho_n$ finite.

Item 4.15 is Stoer–Bulirsch, Theorems (6.9.12) and (6.9.13), p. 451; the
radius in Theorem (6.9.13) is written there with the moments
$\mu_{ik}=x^*(A^*)^iA^kx$ and equals $\|Ax-\mu x\|_2/\|x\|_2$. The
Bauer–Fike theorem and the eigenvalue perturbation bounds are in section 2.
No local source was found for Kahan's residual bound for a Rayleigh–Ritz
subspace of dimension $k>1$ or for Temple's inequality, and they are not
stated.

Item 4.16 is Stoer–Bulirsch, §6.7, pp. 436–440, and Trefethen–Bau,
Lecture 31, pp. 236–237. The last part is the Golub–Reinsch step as derived
in Stoer–Bulirsch, pp. 438–440, from Theorems (6.6.5.1) and (6.6.5.5).

Items 4.17 to 4.19 are from Güttel and Tisseur. Item 4.17 is their Definition
1.1, p. 2, Theorem 2.1 and the definitions of multiplicity, p. 7, and
Definition 2.3, p. 9; existence of a complete system of Jordan chains and the
equality of the sum of partial multiplicities with the algebraic multiplicity
are quoted there from Mennicken and Möller (2003), Propositions 1.6.4 and
1.8.5. Item 4.18 is their Theorem 2.8, p. 14, with the expansion (2.7)–(2.9),
pp. 12–13, and the normalization of the left Jordan chains in Theorem 2.5,
p. 10; the finiteness of the set of eigenvalues is assumed in the text
preceding (2.8), p. 13. They quote Keldysh's theorem from Mennicken and
Möller (2003), Theorem 1.6.5, and Kozlov and Maz'ja (1999), Theorem A.10.2.
Item 4.19 is the monomial case of their Theorem 6.7, p. 78, with the pencil
(6.18)–(6.20), pp. 76–77, the basis (6.9), p. 68, with $\sigma=0$ and all
$\beta_j=1$, and the Taylor row of Table 6.6, p. 77. The identity
$\det L(z)=\det P(z)$, and with it the equality of algebraic and geometric
multiplicities, is not stated there; it follows by multiplying $L(z)$ on the
right by the block unit lower triangular matrix whose first block column is
$b(z)\otimes I_n$, which gives a block upper triangular matrix with diagonal
blocks $P(z)$ and a unit lower triangular block.

### 5. Iterative methods for linear systems

Varga is the second edition (Springer Series in Computational Mathematics 27,
2000), cited from an OCR scan by its printed pages. Hackbusch is *Iterative
Solution of Large Sparse Systems of Equations*, 2nd ed. (2016). Saad is the
author manuscript of the second edition (January 2000), whose theorem numbering
differs from the printed book. Horn–Johnson is the 1985 first edition, and
Quarteroni–Sacco–Saleri is the 2nd ed. (2007).

Item 5.1 is Varga, Definition 1.9 and Theorem 1.10, p. 12, with the error
relation (3.22), p. 66; Horn–Johnson, Theorem 5.6.12, p. 298, and Corollary
5.6.14 (the spectral-radius formula), p. 299; and Hackbusch, Theorem 2.16,
p. 24. Item 5.2 combines Varga, Definition 1.15, p. 18, Theorem 1.17
(irreducibility and strong connectivity), p. 20, and the Perron–Frobenius
Theorem 2.7, p. 35, with Horn–Johnson, Definitions 6.2.21–6.2.22,
pp. 360–361, and Theorem 8.4.4, p. 508. Both sources call a $1\times1$ matrix
irreducible exactly when its entry is nonzero; the strict monotonicity in the
last part is Varga's part 3. Item 5.3 is Varga, Definition 1.20, p. 22, Theorem
1.21, p. 23, and Theorem 3.10, p. 79; Quarteroni–Sacco–Saleri, Theorem 4.2,
p. 130, prove the strictly diagonally dominant case only.

Item 5.4 follows Varga, Theorems 3.16 and 3.18, pp. 89–90, Corollaries 3.20,
3.21 and 3.24, Definitions 3.22–3.23 and Theorem 3.25, p. 91, and Hackbusch,
Appendix C.4: Definition C.41, p. 445, Theorem C.45 and Corollary C.46, p. 446,
Remark C.47 and Theorem C.48, p. 447, Theorem C.56, p. 450, and Theorem C.58,
p. 451. Hackbusch includes positivity of the diagonal in his definition and
shows in Lemma C.42 that it follows from the other conditions; Varga's
Definition 3.22 omits it. The form $A=sI-B$ is Varga, Theorem 3.16, applied
with $s\ge\max_ia_{ii}$ and $B=sI-A$. Varga proves the irreducibility statement
for Stieltjes matrices (Corollary 3.24) and Hackbusch for all M-matrices
(Corollary C.46 and Remark C.47).

Items 5.5 and 5.6 are Varga, Definition 3.28, p. 95, Theorem 3.29, p. 96,
Theorems 3.31 and 3.32, p. 97, and Theorem 3.37 (weak regular splittings),
p. 99; and Hackbusch, Definitions 7.9–7.10 and Theorem 7.11, p. 141, Theorem
7.12, p. 142, and Theorem 7.13, p. 143. Hackbusch phrases the comparison in
terms of $A\le M_1\le M_2$, which is $N_1\le N_2$. In Varga's strict version
"equality excluded" means that neither $N_1$ nor $N_2-N_1$ is the zero matrix
(footnote 17, p. 97).

Item 5.7 is Varga, Theorem 3.8, p. 76, and Corollary 3.9, p. 77, and Hackbusch,
Theorem 7.17, pp. 144–145. Varga states it for a nonnegative matrix with zero
diagonal written as $L+U$; Hackbusch states it for matrices with nonpositive
off-diagonal entries. Item 5.8 is Varga, Theorem 3.11, p. 82 (Kahan), with
Hackbusch, Lemma 3.40, p. 56, and Quarteroni–Sacco–Saleri, Theorem 4.7, p. 133.
Item 5.9 is Varga, Theorem 3.12, p. 83 (with the iteration (3.59)), which
gives the "if and only if" form under the stated nonsingularity hypothesis;
Hackbusch, Theorem 3.41, p. 57, proves the sufficiency and remarks on the
necessity, and Quarteroni–Sacco–Saleri, Property 4.3, p. 133, state it without
proof. The Jacobi statement is Hackbusch, Theorem 3.36, p. 55, and
Quarteroni–Sacco–Saleri, Theorem 4.3, p. 131.

Item 5.10 is Hackbusch, condition (4.24) and Criterion 4.24, p. 79, and
Theorem 4.27, p. 81, whose formula (4.28a) is reproduced here; and Varga,
Definition 4.3, p. 115, formula (4.30), p. 123, and Theorem 4.7, p. 125, whose
$p=2$ case gives the strict optimality of $\omega_{\mathrm{opt}}$. Varga's
hypothesis is that the eigenvalues of $B_J^2$ are real and nonnegative, which
is the same as real eigenvalues of $B_J$. Quarteroni–Sacco–Saleri, Property
4.4, p. 133, state the optimum under property A without proof. The value at
$\omega=1$ follows from (4.28a).

Item 5.11 is Varga, Theorem 5.1 and (5.21), p. 153, the recurrence (5.23),
p. 154, (5.25)–(5.26), p. 155, and (5.29), p. 156, together with Hackbusch,
Lemma 8.25, p. 188. Varga takes the minimization over polynomials of exact
degree $m$, Hackbusch over degree at most $m$; the minimizer is the same.

Item 5.12 is Trefethen–Bau, Theorems 38.1 and 38.2, pp. 295–296, and Theorems
38.3 and 38.4, pp. 298–299 (stated for real symmetric matrices and $x_0=0$),
with the general starting vector in Hackbusch, Lemma 10.18, p. 242, and
Quarteroni–Sacco–Saleri, Theorems 4.11–4.12, p. 155. Item 5.13 is Hackbusch,
Theorem 10.14, p. 239 (the sharper bound $2c^k/(1+c^{2k})$), Trefethen–Bau,
Theorem 38.5, p. 299, Saad, Theorem 6.6, p. 192, and (6.107), p. 193, and
Quarteroni–Sacco–Saleri, Theorem 4.12, p. 155.

Item 5.14 is Trefethen–Bau, Theorem 35.2, p. 270, and Saad, Lemma 6.6, p. 193,
and Proposition 6.15, p. 194. Item 5.15 is the theorem of Greenbaum, Pták and
Strakoš (SIAM J. Matrix Anal. Appl. 17, 1996), listed in the bibliography of
Trefethen–Embree but not stated in any local source; the statement rests on
that paper and no local source was checked. Item 5.16 is Hackbusch, Theorem
10.30, p. 254, stated there for the conjugate residual method with a
preconditioner $N$; with $N=I$ its iterates are the residual minimizers, and
the proof uses only that minimality. Item 5.17 is Saad, Section 9.2.1,
pp. 245–247, including Algorithm 9.1, p. 246, and the equivalence with the
split preconditioned Algorithm 9.2, p. 247; and Hackbusch, the algorithm
(10.23) and Theorem 10.17, p. 242, in which $W=M$ and $N=M^{-1}$.

Item 5.18 is the complex field-of-values form of Elman's bound recorded in
Liesen–Tichý, [The Field of Values Bound on Ideal
GMRES](https://www.karlin.mff.cuni.cz/~ptichy/download/public/LiTi2018.pdf),
(1.4) and the paragraph following it, p. 2.

### 6. Matrix functions, matrix equations, and low-rank, randomized and tensor approximation

Locators in this section use these local copies: Hackbusch, *Hierarchical
Matrices* (2015); Hackbusch, *Tensor Spaces and Numerical Tensor Calculus*,
first edition (2012, SSCM 42), not the second edition listed in the
bibliography; Higham, *Accuracy and Stability*, first edition (1996);
Trefethen–Bau (1997); the partial OCR copy of Golub–Van Loan, third
edition (1996); and the Acta Numerica surveys of Higham and Al-Mohy,
"Computing matrix functions" (Vol. 19, 2010, pp. 159–208), Martinsson and
Tropp (Vol. 29, 2020, pp. 403–572) and Lim (Vol. 30, 2021, pp. 555–764),
together with Benner–Gugercin–Willcox (*SIAM Review* 57, 2015,
pp. 483–531). Higham's *Functions of Matrices* (2008) is not local; the
survey of Higham and Al-Mohy summarizes it and refers to it for proofs.

Item 6.1 is Higham–Al-Mohy, Definitions 2.1 and 2.2, p. 161, the
equivalence argument on pp. 161–162 (the full proof is cited there from
Higham 2008, Theorem 1.12), and Theorem 2.3, p. 162, with the polynomial
property on p. 162. Hackbusch, *Hierarchical Matrices*, §14.1, pp.
355–359, gives the diagonalizable case (Remark 14.2, p. 356), the Jordan
block formula (Exercise 14.6, p. 357), the sum, product and composition
rules for diagonalizable matrices (Exercise 14.4, p. 356) and the spectral
mapping property (Exercise 14.9, p. 359).

Item 6.2: the power series criterion is Higham–Al-Mohy, Theorem 2.4, p.
163; Hackbusch, Lemma 14.5, p. 357, gives only the sufficient condition
$\rho(A-z_0I)<r$. The Cauchy integral is Hackbusch, Lemma 14.8, p. 358,
where it is shown to agree with the diagonalizable and the power series
definitions, with a check on a $2\times2$ Jordan block after the proof;
its agreement with Definition 2.1 for a general matrix is standard
(Higham 2008), but no local source proves it in full. The resolvent bound
is Hackbusch, Theorem 14.13, p. 361, and the diagonalizable bound is
Hackbusch, Theorem 14.10, p. 359, and Higham–Al-Mohy, p. 174. Hackbusch
works with $(\zeta I-M)^{-1}$ and does not state the rectifiability
assumption, which is added here.

Item 6.3 is Higham–Al-Mohy, Theorems 2.5 and 2.6, p. 164, the identity
$\log(e^B)=B$ on p. 165 (cited there from Higham 2008, Problem 1.39), and
the sign function (2.9)–(2.10), p. 165. Hackbusch, Example 14.3, p. 356,
defines a scalar sign with $\mathrm{sign}(0)=0$ for diagonalizable
matrices; that convention differs and is not used here. This item rests
on one local source.

Item 6.4 is Higham–Al-Mohy, §7: the definition (7.1) and the
differentiability condition, p. 190 (from Higham 2008, Theorem 3.8), the
condition number (7.2)–(7.3), p. 190 (from Higham 2008, Theorem 3.1),
Theorems 7.2 and 7.3, p. 191, and the block formula (7.10), p. 192. The
source says "open subset of $\mathbb R$ or $\mathbb C$"; the statement
here separates the real-spectrum case from the holomorphic case. Higham
1996 has no corresponding result. This item rests on one local source.

Item 6.5 is Higham–Al-Mohy, (5.2)–(5.3), pp. 175–176, and Lemma 5.1, p.
177. The printed Lemma 5.1 has a misprint: it assumes $A\in\Omega_m$ and
writes $\Delta A=h_{2m+1}(2^{-s}A)$. Since $r_m(X)=e^{X+h_{2m+1}(X)}$ with
commuting terms, the correct form, used here, assumes $2^{-s}A\in\Omega_m$
and has $\Delta A=2^sh_{2m+1}(2^{-s}A)$; the bound (5.4) is consistent only
with this form. The uniqueness of Padé approximants is stated on p. 175,
citing Baker–Graves-Morris. No second local source treats scaling and
squaring; Hackbusch, §14.2.2, pp. 361–362, has only the truncated Taylor
series with the halving rule and mentions Padé approximation in a
footnote.

Item 6.6 is Higham, §15 introduction, (15.1) and (15.3), pp. 310–311,
for $AX-XB=C$ with real $A\in\mathbb R^{m\times m}$ and $B\in\mathbb
R^{n\times n}$, and Hackbusch, *Hierarchical Matrices*, Lemma 15.1 and
Remark 15.2, p. 370, and Lemma 15.4, p. 372, for $AX+XB=C$ with square
matrices of equal size; the forms here are obtained by replacing $B$ with
$-B$. Hackbusch's integral (15.3), p. 370, assumes that the eigenvalues of
$A$ and of $B$ (in his sign convention) have positive real parts. The
complex and rectangular statement follows from the same Kronecker product
argument.

Item 6.7: the solvability condition and the symmetric solution are
Higham, §15.2.1, p. 316, for real $A$ and the equation $AX+XA^\top=C$,
where the condition reads $\lambda_i+\lambda_j\ne0$. The integral formula
is Hackbusch, Remark 15.2(c), p. 370, transcribed to $AX+XA^*+C=0$. The
Gramian and its Lyapunov equation are Benner–Gugercin–Willcox, (3.10) and
(3.15), pp. 500–501, with $E=I$; positive semidefiniteness for an
asymptotically stable system is stated there on p. 501. The positive
definiteness of $X$ for positive definite $C$ follows at once from the
integral but is not stated in the local sources. Hackbusch, Remark
15.2(b), states that the Lyapunov equation is solvable for symmetric
positive definite $A$; this is a special case of the condition above.

Item 6.8 is Trefethen–Bau, Theorems 5.8 and 5.9, pp. 35–36 (complex
case; Theorem 5.9 is stated without proof), and Hackbusch, *Hierarchical
Matrices*, Theorem 2.11, p. 30 (real case, both norms). Golub–Van Loan,
Theorem 2.5.3, p. 72, gives the spectral norm case for real matrices with
the minimum over matrices of rank exactly $k<\mathrm{rank}\,A$.

Item 6.9 is Martinsson–Tropp, Theorem 11.4, p. 472, and Theorem 11.5, p.
473, with the estimate of $\mathbb EZ$ on p. 474 (from Halko, Martinsson
and Tropp 2011). Theorem 11.5 states $B$ real but $\Omega\in\mathbb
F^{n\times\ell}$; it is stated here for real standard normal test
matrices, the case to which the constant $k/(\ell-k-1)$ applies. The proof
sketch on p. 474 writes $\|\Sigma_1\|_F$ where $\|\Sigma_2\|_F$ is meant.
The combined bound for $k\ge2$, $\ell-k\ge2$ is Halko, Martinsson and
Tropp's Theorem 10.5, which is not local. The relation between the range
finder and the randomized SVD is Martinsson–Tropp, §11.2, p. 469. Only one local
source treats this item.

Item 6.10 is Martinsson–Tropp: the restricted singular values (8.2), p.
447, the Gaussian embedding, §8.3, p. 448, the Gaussian width, §8.4, pp.
448–449, with (8.3), Theorem 8.4 (Gordon), p. 449, the
Johnson–Lindenstrauss discussion, §8.6, pp. 450–451, and subspace
embeddings, §8.7, pp. 452–453. The two consequences stated here are
derived directly from Theorem 8.4 with explicit probabilities, using
$w(E)\le\sqrt{2\log\#E}$ for a finite set of unit vectors (p. 451). The
source's displayed bound $\sqrt{2\log\#E}<\sqrt{2\log(N/2)}$ on p. 451 is a
misprint, since $\#E$ can be $N(N-1)/2$, and its sufficient dimension
$d\ge8\varepsilon^{-2}\log N$ is stated there without a failure
probability. Only one local source treats this item.

Item 6.11 is Martinsson–Tropp, (14.1) and the Schur complement identity,
p. 495, and Theorem 14.1, p. 496 (from Tropp, Yurtsever, Udell and Cevher
2017). The theorem is stated for the output of the source's Algorithm 16,
p. 497, which adds a small numerical shift; the statement here is for its
exact-arithmetic form. The source states it over $\mathbb F$ for $1\le
k<\ell\le n$; the bound is finite only for $k<\ell-1$, and the complex case
is not checked here, so the statement is restricted to real matrices.

Item 6.12 is Hackbusch, *Tensor Spaces*, Definitions 3.24 and 3.32, pp.
58 and 62, Lemma 3.42, p. 67, Proposition 9.10, p. 254, Lemma 9.11 and
Definition 9.12, p. 255, Remark 9.14, p. 256, and Definition 9.15 and
Proposition 9.16, pp. 256–257. For $r>2$, Lemma 9.11 refers to De Silva
and Lim (2008), Theorem 4.10, which is not local; Hackbusch notes that
closedness for $r>\min_j\dim V_j$ is not claimed. Lim, Acta Numerica 30,
(3.42)–(3.43), pp. 619–620, defines border rank for bilinear maps and gives
the same difference-quotient example; in (3.43) the first term on the
right, printed $\varphi_2(u)\psi_2(v)w_1$, should be
$\varphi_2(u)\psi_1(v)w_1$. Hackbusch also records (p. 255) that, by De
Silva and Lim, real tensors without a best rank-$r$ approximation form a
set of positive measure; that statement is not included.

Item 6.13 is Hackbusch, *Tensor Spaces*, Lemma 10.1, pp. 282–283,
Corollary 10.2 and Theorem 10.3, p. 283, and Corollary 10.4, p. 284. The
first inequality is attributed there to De Lathauwer, De Moor and
Vandewalle. Existence of a best approximation in $\mathcal T_r$ is
Hackbusch, Theorem 10.8, p. 290.

Item 6.14 is Hackbusch, *Tensor Spaces*, Definition 12.1 and Theorem
12.2, p. 373, and §12.2.7, p. 379, which transfers Theorem 11.58, (11.61),
p. 357, from the hierarchical format (factor $\sqrt{2d-3}$) to the tensor
train format (factor $\sqrt{d-1}$, since only $d-1$ projections occur).
The order of the projections, from the root to the leaves, is (11.60), p.
357, and the existence of a best approximation is Theorem 11.56, p. 354,
applied to the tensor train format as a hierarchical format with a linear
dimension tree (§12.2). The sequential TT-SVD of Oseledets, which projects from the first
factor onwards using the singular vectors of the partially truncated
tensor, satisfies the same bound, but no local source states that variant;
it is not included.

Item 6.15 is Hackbusch, *Hierarchical Matrices*: the supports and
diameters (5.3b) and (5.4a,b), p. 86, $\eta$-admissibility, Definition
5.5, p. 87, the leaf size condition (5.36), p. 109, Definition 6.1, pp.
119–120, the sparsity constant (6.5a,b), p. 122, Lemma 6.11, p. 124,
Lemma 6.13, p. 125, the discussion of depths on p. 126, and Lemma 7.17, p.
189. Lemma 6.11 assumes that no cluster has exactly one son, as stated in
its proof. Hackbusch works over $\mathbb R$ and with a general rank
distribution $r(b)$; the constant-rank case is stated. A second local
source for this item was not found.

Item 6.16 is Hackbusch, *Hierarchical Matrices*, Definition 4.9 and
(4.9a–d), pp. 59–60, Definition 4.14 and Example 4.16, pp. 64–65,
Theorem 4.17 and (4.18), p. 66, Remark 4.13, (4.16a,b), pp. 63–64, (5.8)
and Theorem 5.8, pp. 88–89. The source's derivation of (4.18) absorbs
polynomial factors and the factor $|x-y|^{-s}$ into its constant, and
Theorem 5.8 refers to "the constructions from above" without stating
them. The explicit bound in the first bullet is the Taylor estimate behind
Theorem 4.17, written with the Lagrange form of the remainder; for this it
assumes $X$ convex with $x_0\in X$ and $q+s\ge0$, which the source does not
state. The one-dimensional bound is Remark 4.13, where the source has
$0\le a<b<c<d\le1$. A second local source for this item was not found.

### 7. Interval arithmetic and verified computation

Rump is cited by the printed pages of the survey "Verification methods:
Rigorous results using floating-point arithmetic", Acta Numerica 19 (2010),
pp. 287–449. Muller et al. is the second edition of the *Handbook of
Floating-Point Arithmetic* (2018), Chapter 12. Nakao–Plum–Watanabe is the
2019 monograph, Springer Series in Computational Mathematics 53.

Item 7.1 is Rump, (5.1) and (5.4)–(5.6), pp. 310–311, with the width
identities (5.7)–(5.9), p. 311, and Muller et al., Definitions 12.1 and
12.2 and formulas (12.1), p. 454. Muller et al. also allow empty and
unbounded intervals and define general operations through the convex hull of
the range. The section restricts to nonempty compact intervals, as Rump does
from §5.4, p. 313. Item 7.2 is Nakao–Plum–Watanabe, §12.3.3, p. 431, which
calls inclusion isotonicity "monotonicity of enclosures" and states the
equality cases of subdistributivity. The same properties are in Muller et
al., §12.1.2, pp. 456–457. Rump, p. 320, states subdistributivity as
"$(X+Y)\cdot Z\subseteq X\cdot Y+X\cdot Z$", which is a misprint for
$X\cdot Z+Y\cdot Z$.

Item 7.3 is Muller et al., Definition 12.3 and Theorem 12.1 (the
"fundamental theorem of interval arithmetic"), p. 455, and Rump, the
inclusion property (5.16) and inclusion principle (5.17), p. 314. The
single-occurrence statement is Rump, Theorem 8.1, p. 321. Rump states it for
arithmetic expressions and attributes it to Moore. The hypothesis that the
standard functions are continuous and have exact interval versions is
needed when they occur, and is made explicit here. The example is Rump,
§8.1, pp. 320–321, where the square is evaluated as a standard function
(8.2). Isotonicity of the natural extension follows from 7.2 by induction on
the expression. It is used, but not stated as a numbered result, in the
local sources.

Item 7.4 is Rump, (9.1)–(9.8), pp. 325–327. The midpoint–radius formula is
Rump, (9.10), p. 329, stated there for an interval matrix times a point
matrix. The form in 7.4 is the transposed case, used in the proof of Lemma
10.5, p. 342. Item 7.5 is Rump, (4.1)–(4.2), p. 308, and (5.14)–(5.15),
p. 313, which notes that the rounded result is best possible. The floating
inclusion principle is Rump, p. 314, and Muller et al., §12.3.1, p. 465.
The width bounds are Muller et al., §12.4.1, p. 469, derived there from the
relative error bounds of directed rounding without underflow. Muller et al.,
p. 469, also remarks that for Lipschitz expressions the extra width from
rounding is linear in $u$, with a reference to Neumaier's *Interval Methods
for Systems of Equations*, Theorem 2.1.5. That book is not among the local
references, and that remark is not included in 7.5.

Item 7.6 is Rump, (4.3), p. 308, Algorithm 4.1 and Theorem 4.2, p. 309,
with the caution about evaluating $I-RA$ on p. 310. Rump states the
conclusion for $A$ and $R$, and allows overflow in the directed-rounding
bounds.

Item 7.7 rests on the standard theory (Moore; Neumaier, *Interval Methods
for Systems of Equations*, Ch. 2; Moore–Kearfott–Cloud). None of these is a
local reference, and no local source states the item as a theorem. The local
sources support it only in part. Rump, (11.10), p. 370, states the centred
(mean-value) form in one variable and reports, without a theorem number,
Hansen's result that its overestimation tends to zero quadratically as the
radius tends to zero. Tables 11.1–11.2, pp. 370–371, show the linear
overestimation of naive evaluation and the quadratic behaviour of the
centred form for small radii. The explicit constant $C=2nL'$ in the
second part is not taken from a source. It follows from a direct estimate.
With $r=w(X)/2$, the width of $F_{\mathrm{MV}}(X)$ is
$\sum_iw(X_i)\,|F'_i(X)|$, where $|F'_i(X)|$ is the magnitude, and
$|F'_i(X)|\le|\partial_if(m)|+L'\|w(X)\|_\infty$. The width of the range
is at least $f(m+s\circ r)-f(m-s\circ r)$ for
$s=\mathop{\mathrm{sign}}\nabla f(m)$, and by the mean value theorem this is
at least $\sum_iw(X_i)|\partial_if(m)|-nL'\|w(X)\|_\infty^2$. In one
variable the example $f(x)=x^2$, $X=[-r,r]$, $F'(X)=2X$ gives excess width
$3r^2=\tfrac34\,w(X)^2$ with $L'=2$, within the bound.
Sources often state the quadratic bound with the Hausdorff distance in
place of the excess width. For nested intervals the two differ by at most a
factor $2$.

Item 7.8 is Rump, Theorem 6.2, p. 316, with the computable version (6.5),
p. 317. Rump takes $D=f'(X)$, the range of the derivative. A box $D$
containing that range gives a larger $N$, so the hypothesis
$N\subseteq X$ for $D$ implies it for $f'(X)$. The other two parts carry
over by the same mean value argument. Continuous differentiability is
assumed here so that $f'(X)$ is a compact interval.

Item 7.9 is Rump, Theorem 13.1, p. 374, and Theorem 13.2, pp. 374–375. That
theorem is proved by Brouwer's fixed-point theorem, following Alefeld.
Rump's Theorem 13.2 assumes only differentiability, but the proof uses the
continuity of $x\mapsto\int_0^1f'(\tilde x+t(x-\tilde x))\,dt$. So
continuous differentiability, as in Theorem 13.1, is assumed here. Rump
takes $J$ to be the hull of the Jacobians, and any larger box works in the
same proof. In Rump's statement the conclusion "$\hat x\in N(\tilde x,X)$"
is listed separately. Here it appears as "every zero of $f$ in $X$ lies in
$N(\tilde x,X)$", which is what the proof shows.

Item 7.10 is Rump, Theorem 13.3, p. 375, and Nakao–Plum–Watanabe,
Theorem 12.6, p. 434, with the operator (12.14), p. 433. Both use the
interval enclosure of $\{f'(y):y\in\tilde x+X\}$, and any box containing it
gives a larger $K(X)$. Rump's conclusion reads "a unique root in
$\tilde x+S(X,\tilde x)$", and Nakao–Plum–Watanabe's reads "a local unique
solution within $\tilde x+K(X)$". Rump's proof shows that $f$ is injective
on $\tilde x+X$, which gives uniqueness in $\tilde x+X$ as stated here.

Item 7.11 is Rump, Theorem 1.1, pp. 299–300, and Theorem 10.2 with (10.8),
p. 339. Rump writes "for some matrix norm". The bound needs a norm
consistent with the vector norm, and 7.11 states it for an induced norm.
The nonsingularity of $R$ in the first part is immediate, because $RA$ is
nonsingular. Item 7.12 is Rump, Lemma 10.5, p. 342, Theorem 10.6 and
(10.14), p. 343, and Theorem 10.8, p. 344, together with
Nakao–Plum–Watanabe, Theorem 12.7, p. 435. The latter states the interval
data version with the residual form exactly as in 7.12.

Item 7.13 is Nakao–Plum–Watanabe, conditions (6.7)–(6.10), p. 181, the two
cases on pp. 182–183, Theorem 6.2, p. 184, and Theorem 6.4, p. 188. It is
also Rump, conditions (16.6)–(16.9), p. 415, the two cases on p. 416, and
Theorem 16.1, p. 417. The two sources differ. Rump's Theorem 16.1 gives
only existence, and its case 2 is the "dual and symmetric case"
$\mathcal Y=\mathcal X'$ with $L$ symmetric.
Nakao–Plum–Watanabe's case 2 asks only for dense range (6.13), and adds the
non-degeneracy and local uniqueness statements. Nakao–Plum–Watanabe,
Remark 6.3(d), p. 185, notes that local uniqueness does not need the
surjectivity of $L$. Remark 6.5(c), p. 188, notes that $\mathcal F$ need
only be defined on a neighbourhood containing the closed balls involved.
Both sources call the theorem "similar to the Newton–Kantorovich theorem".

Item 7.14 is Nakao–Plum–Watanabe, §1.1, p. 3, for the embeddings and the
solvability of $Av=g$, (1.11)–(1.15), pp. 5–6, and Lemma 1.1, p. 7, for the
abstract part. The one-dimensional bound is Theorem 1.5, p. 15. That
theorem is stated "for all $u\in H^1_0$", but the right-hand side requires
$u''\in L^2$, so the hypothesis $u\in H^2$ is added here. The piecewise
quadratic constant $h/(2\pi)$ is reported on pp. 6 and 17 from the
literature, without proof. The square-mesh bilinear constant is §1.4.2.2,
pp. 17–18, which cites Grisvard for
$|u|_{H^2}=\|\Delta u\|_{L^2}$ on convex polygons. The triangle constant is
§1.4.2.3, p. 18, and p. 6, reported from computer-assisted proofs in the
literature. Nakao–Plum–Watanabe write the right-hand side of the reference
estimate with the full $H^2(\Gamma)$ norm. The constant $0.4929$ refers to
the $H^2$ seminorm (the interpolation error vanishes on linear functions),
which is the form used here. That reading, and the description of the mesh
as one of right isosceles triangles with legs $h$, rest on the cited
literature and were not checked in a local source.

### 8. Nonlinear equations, continuation, and algorithmic differentiation

The local copies used here are Deuflhard, *Newton Methods for Nonlinear
Problems* (Springer SSCM 35, 2011 printing), Deuflhard–Hohmann, 2nd ed.
(2003), Stoer–Bulirsch, 3rd ed. (2002), Quarteroni–Sacco–Saleri, 2nd ed.
(2007), Gautschi, *Numerical Analysis*, 2nd ed. (2012), Ciarlet, *Linear and
Nonlinear Functional Analysis with Applications* (SIAM 2013), Han–Atkinson,
3rd ed. (2009), Nocedal–Wright, 2nd ed. (2006), and Griewank–Walther, 2nd
ed. (2008). The definitions of Q-convergence rates in the section preamble
follow Nocedal–Wright, §11.1, and Gautschi, Definitions 4.2.1 and 4.2.2,
p. 259; nondegenerate zeros are Nocedal–Wright, p. 274.

Item 8.1 is Han–Atkinson, Theorem 5.1.3, p. 209, which has all three
bounds, (5.1.4)–(5.1.6). The metric-space form with the a priori bound is
Ciarlet, Theorem 3.7-1, p. 153. Gautschi, Theorem 4.9.1, p. 284, gives the
a priori bound and the third bound in $\mathbb R^d$. Stoer–Bulirsch,
Theorem (5.2.3), p. 297, is a local form on a ball $\bar S_r(x_0)$ with
$\|x_1-x_0\|\le(1-K)r$. Deuflhard–Hohmann, Theorem 4.4, p. 83, is the
scalar case.

In item 8.2, the Ostrowski theorem is Quarteroni–Sacco–Saleri, Property 7.3,
p. 297, stated there without proof with a reference to Ortega–Rheinboldt;
the scalar case $|\varphi'(\alpha)|<1$ is their Property 6.3, p. 262, and
Theorem 6.1, p. 261, gives the global version on an interval with the
limit ratio $\varphi'(\alpha)$. Ortega–Rheinboldt's version assumes only
Fréchet differentiability at $x^*$; no local source states it in that form.
The order statement is Gautschi, Theorem 4.7.1, pp. 279–280, with (4.70)
and (4.71).

Item 8.3 is Gautschi, §4.3.1, pp. 261–262, with the bound (4.31). The same
method and bound are in Quarteroni–Sacco–Saleri, §6.2.1, pp. 250–251,
(6.8), where the error bound is stated as $|e^{(k)}|<(b-a)/2^{k+1}$ with
iterates numbered from $k=0$. In Gautschi's version, as here, $f(x_n)=0$
sends $x_n$ to the right endpoint, so the invariant is $f(a_n)<0\le f(b_n)$.

Item 8.4 is Gautschi, Theorem 4.5.1, pp. 270–271, and Theorem 4.5.2, p. 272,
with the bound (4.54) multiplied by $M$; written this way the bound also
covers $M=0$, where $f$ is affine on $I_\varepsilon$. The hypothesis
$f'\ne0$ on $I_\varepsilon$ is implicit in Gautschi's definition (4.49) of
$M(\varepsilon)$. Quarteroni–Sacco–Saleri, Property 6.2, p. 254, states the
order $(1+\sqrt5)/2$ without proof, citing Isaacson–Keller.

Item 8.5: the first part is Quarteroni–Sacco–Saleri, Theorem 7.1,
pp. 287–288, where the radius $r=\min(R,1/(2CL))$ is fixed in the proof;
compare Stoer–Bulirsch, Theorem (5.3.2), pp. 299–300, which assumes bounds on
$F'(x)^{-1}$ over a whole ball around $x^0$. The second part is
Nocedal–Wright, Theorem 11.2, p. 276. The affine-covariant part is
Deuflhard–Hohmann, Theorem 4.10, pp. 88–89, and Deuflhard, Theorem 2.3,
p. 50 (the refined Newton–Mysovskikh theorem of Deuflhard–Potra); the
uniqueness statement is restricted here to $D$, where the Lipschitz
condition is available.

Item 8.6 is Ciarlet, Theorem 7.7-3, pp. 485–486. Stoer–Bulirsch, Theorem
(5.3.6), p. 302, states the finite-dimensional case on a convex set $C_0$
with $h=\alpha\beta\gamma\le\frac12$, iterates in $S_{r_1}(x_0)$ and
uniqueness in $C_0\cap S_{r_2}(x_0)$, without proof.

Item 8.7: the first part is Deuflhard, Theorem 2.1, p. 46, and Remark 2.1,
p. 47, for uniqueness (proof omitted there). Deuflhard assumes only the
open ball $S(x^0,\rho_-)\subset D$ and states that the iterates remain in
it; the closed ball is assumed here so that the limit lies in $D$, and the
uniqueness statement is restricted to $h_0<\frac12$. It is also the
special case of item 8.6 applied to $F'(x^0)^{-1}F$, which has the same
Newton iterates. The second part is the affine-covariant Newton–Mysovskikh
theorem, Deuflhard, Theorem 2.2, pp. 49–50, with (2.6)–(2.8); Deuflhard
places the limit in the open ball, which the proof does not quite give, so
the closed ball is used here.

Item 8.8 is Stoer–Bulirsch, the method (5.4.2.4) and Theorem (5.4.2.5),
pp. 309–310. Nocedal–Wright, Theorem 11.6, p. 287, gives the companion
result for line searches satisfying the Wolfe conditions: the Zoutendijk
condition holds for the merit function $\frac12\|r\|^2$, so
$J_k^\top r_k\to0$ when the angles are bounded away from $\pi/2$.

Item 8.9 is Nocedal–Wright, condition (11.17), p. 277, and Theorem 11.3,
p. 278; parts (i) and (ii) are proved there with
$\bar\eta=1/(8\|J(x^*)\|\beta^*)$, $\beta^*$ bounding $\|J(x)^{-1}\|$ near
$x^*$, and part (iii) is left as an exercise. The sharper theorem of
Dembo–Eisenstat–Steihaug, linear convergence for every $\eta<1$ in the norm
$\|J(x^*)\,\cdot\,\|$, is not stated in a local source.

Item 8.10 is Nocedal–Wright, (11.24), (11.28) and Theorem 11.5,
pp. 282–283, stated without proof; Nocedal–Wright refer to the assumptions
of Theorem 11.2, and the Lipschitz condition is made explicit here as in
Quarteroni–Sacco–Saleri, Property 7.2, p. 294, which assumes the
hypotheses of their Theorem 7.1, and in the result of Broyden, Dennis and
Moré reported in Stoer–Bulirsch, pp. 315–316. The Dennis–Moré
characterization of superlinear convergence is stated in section 9.

Item 8.11 is Deuflhard–Hohmann, Theorem 4.14, p. 94. Its hypotheses do not
state that $B(x^*,\rho)\subset D$, which the proof uses; the assumption is
added here. Deuflhard, Theorems 4.7 and 4.8, pp. 194–196, gives the general
form with outer inverses and possibly deficient rank, a point-dependent
factor $\kappa(x)$, and the a posteriori estimate (4.42). Nocedal–Wright,
Theorem 10.1, p. 256, gives $J_k^\top r_k\to0$ for the Gauss–Newton method
with Wolfe line searches on a bounded level set under a uniform full-rank
condition.

Item 8.12 is Ciarlet, Theorem 7.13-1, pp. 548–549 (the implicit function
theorem in Banach spaces, with the $C^m$ statement in part (c)), applied as
in Deuflhard–Hohmann, §4.4.1, pp. 101–102, where both parts are stated as
consequences of the implicit function theorem. The differential equation
for $x'(s)$ is Deuflhard, §5.1.1, p. 238, and Deuflhard–Hohmann, p. 103.

Item 8.13: the orders of the classical and tangent predictors are
Deuflhard–Hohmann, Definition 4.21 and Lemmas 4.22–4.23, pp. 104–105, and
Deuflhard, (5.6)–(5.7), pp. 238–239. The step-size bound is
Deuflhard–Hohmann, Theorem 4.24, p. 105, whose display (4.24) defines
$s_{\max}$ with a maximum where a minimum of $\varepsilon$ and
$(2/(\omega\eta))^{1/p}$ is meant; the ball condition comes from the
hypotheses of their Theorem 4.10. Deuflhard, Theorem 5.2, p. 242, states
the same bound with "$\le$" under a "sufficiently large local domain",
although its proof needs the strict inequality of Theorem 2.3; Theorem
5.3, p. 243, gives the bound $\Delta\lambda\le((\sqrt2-1)/(\omega_0
\eta_p))^{1/p}$ under the Kantorovich-type condition of item 8.7.

Item 8.14 is Griewank–Walther, Table 2.2, p. 19, the conventions
(2.7)–(2.8), p. 21, and Proposition 2.1, p. 23, for the evaluation
procedure; Tables 3.2 and 3.4, pp. 34–35, for the tangent mode; and §3.2,
(3.3) and Table 3.5, pp. 37–41, for the incremental adjoint recursion.

Item 8.15 is Griewank–Walther, §4.4, (4.6)–(4.11), pp. 74–76, Proposition
4.3, p. 78, and the bounds (4.17), p. 82, (4.18), p. 82, (4.21), p. 85, and
(4.23), p. 85; the cheap gradient principle is (3.14), p. 44, and Rule 8,
p. 88. The bound $\omega_{\mathrm{grad}}\le4$ requires the constraints on
$w$; with $\mu$ unrestricted it rises to $5$, and counting
multiplications only gives $3$ (p. 85). The cost of taping, needed when
intermediate values are overwritten, is excluded (pp. 84 and 86).

Item 8.16 is Griewank–Walther, §8.1, (8.6)–(8.8), pp. 164–165, and p. 167
for the complete graph when a row is dense; the remark on full Jacobians
is p. 77 and Rule 17, p. 247. The Newsam–Ramsdell principle, Proposition
8.1, p. 163, is the corresponding statement for general (non-$0$–$1$)
seeds.

### 9. Numerical optimization

The local copies used here are Nocedal–Wright, 2nd ed. (2006); Nesterov,
*Lectures on Convex Optimization*, 2nd ed. (2018); Beck, *First-Order Methods
in Optimization* (SIAM, 2017); Bauschke–Combettes, 2nd ed. (2017); Boumal
(2023); Chambolle–Pock, Acta Numerica 25 (2016); Peyré–Cuturi, Foundations
and Trends in Machine Learning 11 (2019); and Hinze–Pinnau–Ulbrich–Ulbrich,
*Optimization with PDE Constraints* (Springer, 2009; the local file name
gives 2003, but the copy is the 2009 book). The pages of Beck, Bauschke–Combettes
and Nesterov were taken from the running heads, since the offset between the
PDF page index and the printed page varies within these files.

Item 9.1 is Nocedal–Wright, Theorems 2.2, 2.3 and 2.4, pp. 14–16, and
Nesterov, Theorems 1.2.1, 1.2.2 and 1.2.3, pp. 20–23; the convex case is
Nesterov, Theorem 2.1.1, p. 61. Nesterov's sufficient condition (Theorem
1.2.3) assumes only that $f$ is twice differentiable, where Nocedal–Wright
assume a continuous Hessian near $x^*$; the item states the Nocedal–Wright form.

Item 9.2 is Nocedal–Wright, problem (12.1), p. 304, Definition 12.1, p. 308,
Definition 12.4 (LICQ), p. 320, Theorem 12.1 with the KKT conditions (12.34),
p. 321, the critical cone (12.53), p. 330, Theorem 12.5, p. 332, and Theorem
12.6, p. 333. Nocedal–Wright define the critical cone as a subset of the
linearized feasible directions; (12.53) is the equivalent description used
in the item.

Item 9.3 is Nocedal–Wright, the Wolfe conditions (3.6) and strong Wolfe
conditions (3.7), p. 34, Lemma 3.1, p. 35, and Theorem 3.2 (Zoutendijk),
p. 38, with the consequence $\nabla f_k\to0$ drawn on the same page. The
lemma says "there exist intervals of step lengths"; the proof produces an
interval of positive length.

Item 9.4 is Nocedal–Wright, Theorem 3.5, p. 44, for the qualitative
statement, and Nesterov, Theorem 1.2.5, p. 39, for the radius $2\mu/(3M)$ and
the error recursion; Nesterov assumes the Hessian is $M$-Lipschitz on all of
$\mathbb R^n$ (the class $C^{2,2}_M$, assumptions stated on p. 38).

Item 9.5 is Nocedal–Wright, Theorem 3.6, p. 46, and Theorem 3.7, p. 47 (the
Dennis–Moré characterization for minimization), the BFGS update (6.19) and
Algorithm 6.1, p. 140, Assumption 6.1 and Theorem 6.5, pp. 153–154, and
Assumption 6.2 and Theorem 6.6, pp. 156–158. Nocedal–Wright's Theorem 3.7
assumes $B_k$ as in (3.34) and only twice continuous differentiability; its
proof invokes the quadratic estimate (3.33), which was derived under a
Lipschitz Hessian, but under $C^2$ the Newton step still gives an
$o(\|x_k-x^*\|)$ error, which suffices. Theorem 6.6 assumes the summability
(6.52), $\sum_k\|x_k-x^*\|<\infty$; Nocedal–Wright state on p. 156 that
(6.52) holds under Assumption 6.1 but do not prove it, so the item keeps it
as a hypothesis. Its proof establishes the Dennis–Moré condition (3.36)
and concludes via Theorem 3.6; the item states the conclusion in that form,
since superlinear convergence needs the unit step to be taken. The
positive definiteness of $\nabla^2f(x^*)$ is implicit in Theorem 6.6 (its
proof uses $\nabla^2f(x^*)^{-1/2}$). The Dennis–Moré theorem for nonlinear
equations is not stated in a local source and is not included; section 8
states the local superlinear convergence of Broyden's method.

Item 9.6 is Nocedal–Wright, Algorithm 4.1, p. 69, the Cauchy point
(Algorithm 4.2), p. 71, Lemma 4.3, p. 78, Theorem 4.4, p. 79, and Theorems
4.5 and 4.6, pp. 80 and 82; the decrease condition is (4.20) and the step
bound is (4.25).

Item 9.7 is Nesterov, Theorem 2.1.14, p. 80, Corollary 2.1.2 and Theorem
2.1.15, pp. 81–82; the bound $L\|x_0-x^*\|^2/(2k)$ is Beck, Theorem 10.21,
p. 284 (proximal gradient with $g=0$), and Chambolle–Pock, Theorem 4.1, Acta
Numerica 25, p. 184, which also gives the linear rate
$(1-\tau\mu_f)^k$ for step $\tau\le1/L$ in the strongly convex case.

Item 9.8 is Nesterov, Assumption 2.1.4, p. 69, Theorem 2.1.7, p. 71, Theorem
2.1.13, p. 79, and the constant step scheme (2.2.22) with its rate (2.2.23),
p. 94; Nesterov's general optimal scheme (2.2.7) has the rate (2.2.13) of
Theorem 2.2.2, p. 90. Chambolle–Pock, Theorems 4.3 and 4.4, p. 187, state
the lower bounds with the restriction $k<n$ and the constant
$L\|x_0-x^*\|^2/(8(k+1)^2)$ in place of Nesterov's
$3L\|x_0-x^*\|^2/(32(k+1)^2)$ for $1\le k\le\frac12(n-1)$; the item follows
Nesterov, where the construction is carried out in full.

Item 9.9 is Beck, Assumption 10.1, p. 269, Theorem 10.21, p. 284, FISTA and
Assumption 10.31, p. 291, and Theorem 10.34, p. 292, with the constant step
size $L_k\equiv L_f$; single-valuedness of the proximal map is Beck, Theorem
6.3, p. 131. Beck allows $f$ to be extended-valued with
$\mathop{\mathrm{dom}}g\subseteq\mathop{\mathrm{int}}\mathop{\mathrm{dom}}f$ for the proximal
gradient method, and also proves the same rates for a backtracking step size.
Chambolle–Pock, Theorems 4.9 and 4.10, p. 196, give the same rates in Hilbert
space for step $\tau\le1/L$, with a variant of the FISTA parameters ($t_0=0$).

Item 9.10 is Nesterov, the subgradient method (3.2.14) and Theorem 3.2.2,
p. 202, the step choice (3.2.16) and rate (3.2.17), p. 203, and the lower
bound Theorem 3.2.1, p. 197, for the class $\mathcal P(x_0,R,M)$ defined
there. Beck, Theorem 8.30, p. 217, gives an $O(1/\sqrt k)$ rate for the
unnormalized projected subgradient method on a compact set with different
constants.

Item 9.11 is Beck, the generalized conditional gradient method, p. 380, the
step-size rules, p. 383, and Theorem 13.14(a), p. 390, specialized to $g$
the indicator function of $C$ (Assumption 13.1, p. 380). Beck also covers an
adaptive step size, with the same bound.

Item 9.12 is Bauschke–Combettes, Definition 4.1, p. 69, Proposition 4.4,
p. 70, Proposition 12.28, p. 212, Example 23.3, p. 394, Corollary 23.9,
p. 396, Definition 5.1 (Fejér monotonicity), p. 91, Theorem 5.15
(Krasnosel'skiĭ–Mann, attributed to Groetsch), p. 96, Theorem 23.41
(proximal point), p. 406, Theorem 26.14 (forward–backward), p. 478, and
Theorem 26.11 (Douglas–Rachford), p. 473. These theorems also give strong
convergence under uniform monotonicity and the convergence of dual
sequences, which the item omits. The proximal point method is also Beck,
Theorem 10.28, in Euclidean spaces.

Item 9.13 is Chambolle–Pock, Algorithm 6 (PDHG), p. 212, the Lagrangian
(3.12), p. 178, and Theorem 5.1, pp. 213–214, with $h=0$; with a smooth
term $h$ having $L_h$-Lipschitz gradient the step condition becomes
$(1/\tau-L_h)/\sigma\ge L^2$. The survey cites Chambolle and Pock (2015) for
the proof, and its statement of weak convergence for strict inequality
presupposes the existence of a saddle point, which the item states
explicitly.

Item 9.14 is Nesterov, Definition 5.1.1, p. 330, the Newton decrement,
p. 346, Theorem 5.1.13, p. 347, the damped Newton method (5.1.28) and
Theorem 5.1.15, p. 348, Theorem 5.2.2(1), p. 356, Definition 5.3.2, p. 369,
Theorem 5.3.10, p. 379, and the main path-following scheme (5.3.29) with the
parameters (5.3.28) and Theorem 5.3.11, pp. 380–381. Nesterov states that
the leading term of the bound is $6.11\sqrt\nu\log(\nu\|c\|^*_{x_F^*}/\varepsilon)$.
The threshold $(3-\sqrt5)/2$ for $\lambda_f(x_+)<\lambda_f(x)$ is the
elementary solution of $\lambda<(1-\lambda)^2$ and is not stated in that
form by Nesterov, who instead uses the region $\lambda_f<1/(2M_f)$ for the
intermediate Newton method (5.2.9), p. 358.

Item 9.15 is Boumal, assumptions A4.1–A4.3, pp. 55–57, Proposition 4.7,
p. 56, Proposition 4.8, p. 57, and Corollary 4.9, p. 58.

Item 9.16 is Peyré–Cuturi, the couplings (2.10) and Kantorovich problem
(2.11), pp. 370–371, Proposition 2.4, p. 382, the entropy (4.1) and the
regularized problem (4.2), p. 425, Proposition 4.3 and Sinkhorn's iteration
(4.15), p. 432, the Hilbert metric (Remark 4.12), p. 439, and Theorems 4.1
and 4.2, pp. 440–441. Peyré–Cuturi prove Proposition 2.4 by reference to
linear programming duality, and Theorem 4.2 by reference to Franklin and
Lorenz (1989); the scaling vectors are determined only up to the rescaling
$(ru,v/r)$, which the Hilbert metric ignores.

Item 9.17 is Hinze–Pinnau–Ulbrich–Ulbrich, problem (1.77), Assumption 1.42
and Theorem 1.43, p. 53, Assumption 1.47, p. 70, Theorem 1.48 and Lemma
1.12, pp. 71–72, Corollary 1.3, p. 73, and the linear-quadratic optimality
system (1.114)–(1.116), p. 74. Sufficiency follows from Theorem 1.46, p. 66,
since the reduced objective is convex; the projection formula is Lemma
1.12(iv) with $\gamma=1/\alpha$ and $\nabla\hat J(\bar u)=\alpha\bar u+B^*\bar p$
from (1.113).

### 10. Polynomial and rational approximation

Trefethen's *Approximation Theory and Approximation Practice* is cited by
the printed pagination of the local author manuscript. Gautschi's *Numerical
Analysis* is the 2nd edition (2012), Stoer–Bulirsch the 3rd edition (2002),
Quarteroni–Sacco–Saleri the 2nd edition (2007), Deuflhard–Hohmann the 2nd
edition (2003), Han–Atkinson the 3rd edition (2009), Canuto–Hussaini–
Quarteroni–Zang the 2006 volume *Fundamentals in Single Domains*, Ciarlet's
*Linear and Nonlinear Functional Analysis with Applications* the SIAM 2013
edition, and Baker–Graves-Morris the 2nd edition (1996).

Item 10.1 is Han–Atkinson, Theorem 3.1.1 and Corollary 3.1.4, p. 116, and
Theorem 3.3.16, p. 138, together with Trefethen, Theorem 6.1, p. 51, and the
compactness argument in the proof of Theorem 10.1, p. 93.

Item 10.2: the definition of a Haar space, the three equivalent conditions
and the Mairhuber–Curtis theorem are Wendland, Definition 2.1 and Theorem
2.2, p. 18, and Theorem 2.3, p. 19. The alternation theorem for a Haar
subspace of $C[a,b]$ is stated without proof in the hints to Ciarlet,
Problem 5.4-6, p. 251, which refers to Cheney's book; there the sign
condition is misprinted as $\mathrm{sgn}(f(x_i)-p_n(x_i))=-\mathrm{sgn}(f(x_{i+1})-f(x_i))$,
where $f(x_{i+1})-p_n(x_{i+1})$ is meant. The uniqueness of the best
approximation from a Haar subspace and Haar's converse theorem rest on my
own knowledge; no local source was checked for them.

Item 10.3 is Trefethen, Theorem 10.1, p. 93, which also gives uniqueness
for complex $f$ on $[-1,1]$; Han–Atkinson, Theorems 3.3.19 and 3.3.20, p.
139, on a general interval $[a,b]$ and for trigonometric polynomials; and
Quarteroni–Sacco–Saleri, Property 10.1, p. 444. The de la Vallée Poussin
bound is Quarteroni–Sacco–Saleri, Property 10.2, pp. 444–445, and
Trefethen, Exercise 10.3, p. 98; the right-hand inequality
$E_n(f)\le\|f-q\|$ is immediate.

Item 10.4 is Gautschi, (2.81)–(2.88), pp. 86–88, Theorem 2.2.1, p. 88, the
uniqueness remark following its proof and (2.95), p. 89; and
Deuflhard–Hohmann, Theorem 7.19, p. 195, which gives the bound
$|a_n|/2^{n-1}$, and Example 7.20, p. 196, for the optimal nodes.

Item 10.5: existence and uniqueness of the interpolant is Stoer–Bulirsch,
Theorem 2.1.1.1, p. 38. The error formula is Stoer–Bulirsch, Theorem
2.1.4.1, p. 49, which assumes only that $f^{(n+1)}$ exists and places $\xi$
in the smallest interval containing $x$ and the nodes; Gautschi, (2.60)–
(2.61), p. 78, and Quarteroni–Sacco–Saleri, Theorem 8.2, p. 335, assume
$f\in C^{n+1}$; Deuflhard–Hohmann, Theorem 7.16, p. 192, gives the same
formula for Hermite interpolation with repeated nodes. The bound at the
zeros of $T_{n+1}$ is Gautschi, (2.96), p. 90.

Item 10.6 is Gautschi, (2.55)–(2.59), pp. 76–77; Deuflhard–Hohmann, Theorem
7.3 and the remark on affine invariance, p. 183; Trefethen, (15.3)–(15.4)
and Theorem 15.1, pp. 136–137, for general linear projections; and
Quarteroni–Sacco–Saleri, Property 8.1, p. 336.

Item 10.7: the three growth statements are Trefethen, Theorem 15.2, p. 137,
with the Chebyshev points of the second kind, $\cos(j\pi/n)$. The bound for
the zeros of $T_{n+1}$ is Quarteroni–Sacco–Saleri, (10.20), p. 433, and
(10.25), p. 434. The equispaced asymptotics are also in
Quarteroni–Sacco–Saleri, p. 338, and in the notes of Gautschi, p. 115. The
near-best bounds are Trefethen, Theorem 16.1, p. 154. Faber's theorem is
Gautschi, notes to Section 2.2.1, p. 116 (citing Natanson), Trefethen, p. 54
and (15.6), p. 137, and Deuflhard–Hohmann, p. 193; the divergence of the
Lebesgue constants is also in Ciarlet, Problem 5.4-4, p. 251. Gautschi's
note on p. 115 states $\Lambda_n>\frac2\pi\log n+c$ with
$c=\frac2\pi(\log\frac8\pi+\gamma)=0.9625\ldots$ for every triangular array.
That constant belongs to the Chebyshev zeros. For arbitrary nodes the sharp
constant is the smaller $0.52125\ldots$ of Trefethen, so the synopsis
follows Trefethen.

Item 10.8: the two Jackson theorems with explicit constants are Han–Atkinson,
Theorems 3.7.1 and 3.7.2, p. 159, stated there without proof with a
reference to Meinardus. The Favard-type estimate is Canuto–Hussaini–
Quarteroni–Zang, (5.1.11), p. 271, with $S_N$ defined in (5.1.1), p. 268.
Trefethen discusses the Jackson theorems informally on pp. 61 and 65.

Item 10.9: the Bernstein inequality is Canuto–Hussaini–Quarteroni–Zang,
(5.1.5), p. 268. The converse for analytic functions is Trefethen, Theorem
8.3, p. 73, which uses the inequality $\|p\|_{E_\rho}\le\rho^d\|p\|$ for
$p$ of degree $d$ (Exercise 8.6, pp. 75–76). The Bernstein inverse theorem
for Hölder classes rests on my own knowledge; no local source states it.
DeVore, Acta Numerica 7, pp. 86–87, gives the abstract Jackson and Bernstein
inequalities that underlie such characterizations.

Item 10.10 is Trefethen, Theorem 3.1, pp. 19–20, the Chebyshev points
(2.2), p. 8, the error expansions (4.8)–(4.9), p. 32, Theorem 7.1, pp.
62–63, and Theorem 7.2, p. 64. Trefethen takes $V$ to be the total
variation of $f^{(\nu)}$; when $\nu=0$, 10.10 claims only the coefficient
bound.

Item 10.11 is Trefethen, the definition of $E_\rho$, pp. 68–69, Theorem 8.1,
p. 69, Theorem 8.2, p. 70, (8.4)–(8.5), p. 71, and the remark on
Bernstein's theorem after Theorem 8.3, p. 73.

Item 10.12 is Trefethen, Theorems 5.1 and 5.2, pp. 42–43, and Gautschi,
(2.103)–(2.105), pp. 91–92. Trefethen, pp. 46–47, reports the numerical
stability of the barycentric formulas (Rack–Reimer and Higham, not local)
only qualitatively. The synopsis therefore makes no stability statement.

Item 10.13 is Trefethen: $R_{mn}$ on pp. 245–246, the defect (24.1) on p.
260, and Theorem 24.1, pp. 260–261, with equioscillation as defined
there. No second local source was found.

Item 10.14: the definition (27.3) and the generic matching (27.4) are
Trefethen, p. 305; the characterization is Theorem 27.1, p. 307; the block
structure is Theorem 27.2, p. 308; and the description of all solution
pairs is Theorem 27.4, p. 312. Baker's definition is Baker–Graves-Morris,
(4.6)–(4.7), p. 21, and the determinant $C(L/M)$ is (4.8), p. 22. The
existence of the Baker approximant when $C(L/M)\ne0$, the square blocks of
size $(r+1)\times(r+1)$ and the existence criterion $L+M\le\lambda+\mu+r$
inside a block are Theorem 1.4.3, p. 28, with the zero blocks of the
$C$-table in Theorem 1.4.2, p. 25. The two sources differ in convention.
Trefethen's $r_{mn}$ always exists, while Baker's $[L/M]$ may fail to exist.
The synopsis states the link between them, which follows directly from the
definitions and Trefethen's Theorem 27.1. The block statement is written in
terms of the order of contact $k$ and is derived from Trefethen's Theorem
27.1. Trefethen excludes the entry $r=0$, which fills whole columns.

Item 10.15 is Baker–Graves-Morris, Theorem 6.2.1, p. 282 (simple poles),
and Theorem 6.2.2, pp. 286–287 (multiple poles). The existence of $[L/M]$
for large $L$ comes from the proof, where $\det C\ne0$ for large $L$ by
(2.23), p. 285. The theorem is also mentioned in Trefethen, p. 321.

Item 10.16 is Baker–Graves-Morris: the definition, p. 193, and the series
(1.3), p. 194; existence, Corollary 1 to Theorem 5.1.2, p. 199; poles,
Theorem 5.2.1, p. 201; convergence, Theorem 5.2.6, p. 211, on the domains
$\mathcal D(\Delta)$ of Theorem 5.2.3, p. 206; the case of positive radius
of convergence, Theorems 5.4.1, p. 220, and 5.4.2, p. 221; and Carleman's
criterion, p. 239, with Theorem 5.5.1, p. 240.

Item 10.17 is Trefethen, (25.3), p. 273, and Theorem 25.1, p. 274, with the
historical remark on p. 249; and DeVore, Acta Numerica 7, p. 107, which
states Newman's $O(e^{-c\sqrt n})$ result. Trefethen quotes Newman's bounds
without a range of $n$, and Newman's paper is not local. The synopsis
therefore claims them only for sufficiently large $n$, which also follows
from the Stahl asymptotics in Theorem 25.1.

### 11. Splines, kernels and wavelets

Schumaker is the third edition (Cambridge Mathematical Library, 2007),
whose pagination is that of the original text. Wendland is the 2005
Cambridge printing of the 2004 monograph. Cohen is the 2003 North-Holland
edition. Stoer–Bulirsch is the third edition (2002), and Gautschi's
*Numerical Analysis* is the second edition (2012). DeVore's survey
"Nonlinear approximation" is cited by its pages in *Acta Numerica* 7
(1998), pp. 51–150.

Item 11.1 is Schumaker, Definition 4.1, p. 108, and Theorem 4.4, p. 110;
the simple-knot case is also Stoer–Bulirsch, §2.4.4, p. 111. Item 11.2 is
Schumaker, Definition 4.12, p. 118, Theorem 4.15 (recurrence), p. 120,
Theorem 4.17 (support and positivity), p. 121, Definition 4.19 and (4.30),
p. 124, and Theorem 4.20 (partition of unity), p. 125, with the smoothness
statement from Theorem 4.14, pp. 119–120; and Stoer–Bulirsch, (2.4.4.3),
p. 112, Theorem 2.4.4.5, p. 113, and (2.4.5.2)–(2.4.5.3), pp. 118–119.
Schumaker states the recurrence for the B-spline
$Q_i^m=N_i^m/(y_{i+m}-y_i)$, which has integral $1/m$ in his
normalization; the form in 11.2 follows by substituting his (4.29) and is
the form (2.4.5.3) of Stoer–Bulirsch, whose $B_{i,r}$ is Schumaker's
$N_i^r$ and whose $N_{i,r}$ is Schumaker's $Q_i^r$. Item 11.3 is Schumaker,
Definition 4.8 and Theorem 4.9, p. 116, and Corollary 4.10, p. 117; the
simple-knot case is Stoer–Bulirsch, Theorem 2.4.4.6, p. 115. Item 11.4 is
Schumaker, Theorem 4.61, p. 165, and Corollary 4.62, p. 166, whose condition
(4.132) reads $t_i\in\{x:N_i^m(x)\ne0\}$; Stoer–Bulirsch quote the theorem
without proof as Theorem 2.4.5.7, p. 121. Item 11.5 is Schumaker, Theorem
4.76, p. 178, with Examples 4.74–4.75, pp. 177–178; the sign-change counts
are those of Schumaker §2.4.

Item 11.6 is Stoer–Bulirsch, Definition 2.4.1.1, p. 98, the Holladay
identity Theorem 2.4.1.4, p. 99, Theorem 2.4.1.5, p. 100, and the existence
statement Theorem 2.4.2.13, p. 105; Gautschi, Theorems 2.3.1 and 2.3.2,
pp. 111–112, proves the minimality of the complete and natural spline among
$C^2$ interpolants. Item 11.7 is Stoer–Bulirsch, Theorem 2.4.3.3, p. 109,
which proves the bounds with $c_k\le2$; the sharper constants are those of
Hall and Meyer (1976), quoted without proof in the footnote on p. 109 of
Stoer–Bulirsch and in Gautschi, (2.147), p. 110, where $c_3$ is said to
depend on the mesh ratio.

Item 11.8 is Schumaker, §6.4: Lemma 6.17, p. 223, constructs a
quasi-uniform subpartition $\Delta^*\subseteq\Delta$ with
$\bar\Delta/2\le\underline\Delta^*\le\bar\Delta^*\le3\bar\Delta/2$; the
operator $Q$ of (6.37)–(6.40) and Theorem 6.18, p. 224, maps into
$\mathcal S_m(\Delta^*)\subseteq\mathcal S_m(\Delta)$ and reproduces
polynomials; the bound $(2m)^m$ is Theorem 6.22, p. 228; the estimate with
$\|f^{(\sigma)}\|_{L^p}$ is (6.50) in the proof of Theorem 6.25, p. 231,
and the modulus form is Theorem 6.25, p. 230. The modulus of smoothness is
Schumaker, Definition 2.58, p. 55, where it is defined for
$0<t\le(b-a)/\ell$; when $\bar\Delta$ exceeds that range, the modulus form
needs the evident extension, while the form with
$\|f^{(\sigma)}\|_{L^p}$ needs none. Schumaker does not track the constant
beyond "depends only on $m$ and $p$"; the local version is Theorem 6.24,
p. 229.

Item 11.9 is Wendland, Definition 6.1, p. 65, Bochner's theorem Theorem
6.6, p. 70, Theorem 6.8 (open set in the support), p. 73, Theorem 6.11, p. 74,
the Gaussian Theorem 6.10, p. 74, the inverse multiquadrics Theorem 7.15,
p. 95 (for $\beta>d/2$ already Theorem 6.13, p. 76), and the truncated
power Theorem 6.20, p. 80, with Definition 6.16, p. 78, for radial positive
definiteness. Wendland calls positive definite what some authors call
strictly positive definite. Item 11.10 is Wendland, Definition 9.4, p. 121,
Definition 9.11 and Theorems 9.12–9.13, p. 128, and Corollary 9.14 and
Table 9.1, p. 129. Item 11.11 is Wendland, Definition 8.1, p. 97, Definition
7.1 (complete monotonicity), p. 86, Micchelli's Theorem 8.19 and Corollary 8.18,
p. 113, and Corollary 8.20, p. 115.

Item 11.12 is Wendland, §10.2: Theorem 10.7, p. 137, Definition 10.9 and
Theorems 10.10–10.11, p. 138, Theorem 10.12, p. 139, and Corollary 10.13,
p. 141; the Sobolev native space of the compactly supported functions is
Theorem 10.35, p. 160, which excludes $k=0$ with $d\le2$. Item 11.13 is
Wendland, Theorem 11.1, p. 173, Definition 11.2, p. 174, Theorem 11.4,
p. 176, and Theorem 11.5, p. 177, specialized to a positive definite kernel
(trivial polynomial space and $\alpha=0$, as in the remark on p. 176); the
fill distance is Definition 1.4, p. 14, the cone condition Definition 3.6, p. 28,
and the error bound Theorem 11.17, p. 184. Wendland does not state how $C$
and $h_0$ depend on $\Omega$; by Remark 11.12, p. 181, for the generic
estimate $\Omega$ enters only through its cone condition.

Item 11.14 is Wendland, Definition 4.6, p. 41, Theorem 12.3, p. 210, and
Corollaries 12.4, p. 213, and 12.8, p. 214. Theorem 12.3 is stated for
even conditionally positive definite functions with a positive generalized
Fourier transform; 11.14 states the positive definite case. The explicit
Gaussian constant is obtained from Theorem 12.3 with $M=M_d/q_X$ and
$\varphi_0(M)=(2\alpha)^{-d/2}e^{-M^2/\alpha}$, as in Corollary 12.4.
Corollary 12.8 states $\lambda_{\min}\ge Cq_X^{2k+1}$ with $C$ depending only
on $d$ and $k$; that cannot hold for large $q_X$, since for
$q_X>1/2$ the matrix is $\varphi_{d,k}(0)I$. The bound in 11.14 follows
from Theorem 12.3 and the lower bound in Theorem 10.35 and therefore carries
the upper bound $Q$ on $q_X$, which is automatic for points in a bounded
set.

Item 11.15 is Cohen, Definition 2.2.1, p. 46, Lemma 2.6.1 and (2.6.5)–(2.6.7),
pp. 75–76, Theorem 2.6.1, p. 77, and the discussion on pp. 78–79, where the
orthonormal case $\tilde\varphi=\varphi$ gives the global orthonormal basis;
DeVore, §7.2, pp. 109–111, gives the same construction with the formula
(7.10) and the orthonormal case (7.17). Cohen works throughout with compactly
supported real refinable functions; the general case (Mallat, Meyer,
Daubechies' *Ten Lectures*) was not checked in a local source. Item 11.16
is Cohen, §2.10, pp. 105–106, with Lemma 2.10.3 (Riesz), the regularity
estimate (2.10.27), p. 106, the Fourier exponent of Definition 2.7.1 and the
relation (2.7.8), p. 84, the support statement for finite masks on p. 84,
and Remark 2.8.5, p. 93, which turns the factor
$\bigl((1+e^{-i\omega})/2\bigr)^N$ into $N$ vanishing moments of the dual
wavelet (here equal to $\psi_N$). The support $[1-N,N]$ of $\psi_N$ is
computed from the wavelet formula of 11.15 and the support of $\varphi_N$;
it is not displayed in Cohen. Daubechies' own book is not in the local
collection.

Item 11.17 is Cohen, Besov spaces (3.2.10)–(3.2.13), p. 161, and Remark
3.2.2, p. 162; Theorem 3.3.1, p. 166 ($L^p$-stability); Theorem 3.3.2,
p. 167, and Theorem 3.3.3, p. 168 (Jackson and Whitney estimates); Theorem
3.4.1, p. 171, and Theorem 3.4.3, p. 172 (Bernstein estimates); Theorem
3.6.1, pp. 182–183, and Corollary 3.6.2, p. 186 (norm equivalences). The
standing assumptions (compactly supported tensor-product dual pair) are
stated on p. 165. DeVore, (7.28), p. 113, with Remark 7.2, states the same
characterization in the $L^p$-normalization, with the hypotheses that
$\psi\in B^\beta_q(L_p)$ for some $\beta>s$ and that $\psi$ has more than
$s$ vanishing moments.

Item 11.18, first part, is DeVore, assumptions (i)–(vi), p. 82, the
approximation spaces (4.3), p. 83, and Theorem 1, p. 87, whose proof is
referred to DeVore–Lorentz; Cohen, Theorem 4.2.1, pp. 250–251, proves the
dyadic version for quasi-normed spaces. The second part is Cohen, Theorems
4.3.2 and 4.3.3, pp. 258–260, with $\Sigma_j=\mathcal S_{2^{dj}}$ as in
(4.2.15), p. 250, and DeVore, Theorem 5, p. 116, Corollary 1 and Theorem 6,
p. 117, and (7.41), p. 118. Cohen's hypothesis is the coefficient
equivalence (4.3.23), assumed for the whole range $0<s<t$ in Theorem
4.3.3; DeVore states the hypotheses only as "sufficient vanishing moments
and smoothness" of $\psi$. For $\tau<1$ the Besov space is a quasi-normed
space, treated in Cohen §3.7. Plonka–Potts–Steidl–Tasche was not used for
this section.

### 12. Orthogonal polynomials and numerical quadrature

Locators refer to Gautschi, *Orthogonal Polynomials: Computation and
Approximation* (Oxford, 2004), cited as Gautschi OP; Gautschi, *Numerical
Analysis*, 2nd ed. (Birkhäuser, 2012), cited as Gautschi NA; Stoer–Bulirsch,
3rd ed. (2002); Quarteroni–Sacco–Saleri, 2nd ed. (2007);
Deuflhard–Hohmann, 2nd ed. (2003); Kress, *Linear Integral Equations*, 3rd
ed. (2014); the author manuscript of Trefethen, *Approximation Theory and
Approximation Practice* (2013), cited as ATAP, by its own pagination; and
Trefethen–Weideman, SIAM Review 56 (2014), 385–458. Gautschi OP writes the
measure as $d\lambda$ and the Gauss weights as $\lambda_\nu$; the section
writes $\mu$ and $w_k$.

Item 12.1 is Gautschi OP, Theorem 1.2, p. 2, Theorem 1.6 and the following
paragraph (which defines the support and the support interval), p. 3, and
Lemma 1.5, p. 2; Deuflhard–Hohmann, Theorem 6.2, p. 154, gives existence and
uniqueness for a weight function. The converse direction "positive definite
implies infinite support" is immediate (a polynomial vanishing on a finite
support has norm zero) and is not stated separately in the sources.

Item 12.2 is Gautschi OP, Theorem 1.27, p. 10, with (1.3.6)–(1.3.7), p. 11,
Theorem 1.28 and Theorem 1.29, p. 12; Gautschi NA, (2.38)–(2.41), pp. 69–70;
and Stoer–Bulirsch, Theorem (3.6.3), p. 172. Favard's theorem is stated
without proof in Gautschi OP, pp. 11–12, and in Gautschi NA, Notes to
Chapter 2, p. 115, both referring to Natanson; Gautschi OP adds that the
measure has infinite support. The finiteness of all moments of the measure
in Favard's theorem is part of the standard statement (the polynomials are
in $L^2$ of the measure) and was not separately checked in a local source.

Item 12.3 is Gautschi OP, Theorems 1.19, 1.20 and 1.21, p. 7;
Stoer–Bulirsch, Theorem (3.6.10), p. 174, and Deuflhard–Hohmann, Theorem
6.5, p. 156, for a weight function on $[a,b]$. The interlacing of Gauss nodes
is also Gautschi NA, §3.2.3(d), p. 176.

Item 12.4 is Gautschi OP, Definition 1.30 and Theorem 1.31, p. 13, and
Theorem 1.32, p. 14; Stoer–Bulirsch, Theorem (3.6.20), p. 179, which also
identifies $\pi_n$ as the characteristic polynomial of $J_n$.

Item 12.5 is Gautschi OP, Definition 1.44, p. 20, Theorem 1.45, p. 21, and
the discussion of optimality, p. 22; Gautschi NA, Theorem 3.2.1, p. 170;
Stoer–Bulirsch, Theorem (3.6.12)(b),(c), p. 175, for uniqueness and for the
impossibility of degree $2n$; and Quarteroni–Sacco–Saleri, Theorem 10.1 and
Corollary 10.2, p. 430, with $n+1$ nodes.

Item 12.6 is Gautschi OP, Theorems 1.46 and 1.48, p. 23; Gautschi NA,
§3.2.3(a),(b),(f), pp. 175–177; and Deuflhard–Hohmann, Theorem 9.11, p. 282.
The formula for the Christoffel numbers is Gautschi OP, Corollary to Theorem
1.31, p. 14, combined with (3.1.6) in the proof of Theorem 3.1, p. 153.

Item 12.7 is Gautschi OP, Theorem 3.1, p. 153; Stoer–Bulirsch, Theorem
(3.6.21), p. 179, where the eigenvector is scaled to have squared length
$\beta_0$ and the weight is the square of its first component, which is
equivalent; and
Gautschi NA, §3.2.3(e), (3.47), pp. 176–177.

Item 12.8: the Gauss error formula is Gautschi OP, Corollary to Theorem
1.48, p. 24, with $\|\pi_n\|^2=\beta_0\cdots\beta_n$ from (1.3.7), p. 11;
Stoer–Bulirsch, Theorem (3.6.24), p. 180; Gautschi NA, (3.48), p. 177; and
Deuflhard–Hohmann, Theorem 9.12, p. 283, with $n+1$ nodes. The Radau and
Lobatto rules and their remainders are Gautschi OP, (1.4.21)–(1.4.24),
pp. 25–26, and their degrees are also in Gautschi NA, p. 172 (with $n$ nodes
in total, degrees $2n-2$ and $2n-3$). Gautschi OP states the Radau and
Lobatto remainders without a smoothness hypothesis and allows $b=\infty$ for
Radau; the section assumes compact support and the derivative of the order
that appears.

Item 12.9: the first two parts are Kress, Theorem 12.4 (attributed there to
Szegő) and Corollary 12.5 (Steklov), p. 222, proved by the uniform
boundedness principle; the necessity-and-sufficiency theorem is commonly
attributed to Pólya. Kress uses $n$ nodes in the $n$th rule; the proof does
not use the number of nodes, and the section allows $m_n$ nodes. The third
part is Gautschi NA, §3.2.3(c), pp. 175–176, stated there for a weight
function on a finite interval. Convergence of Gauss and Clenshaw–Curtis
rules on $[-1,1]$ for continuous integrands is also ATAP, Theorem 19.4,
p. 190.

Item 12.10 is Stoer–Bulirsch, Theorem (3.2.3), p. 152, with (3.2.9), p. 154,
for the definite case; and Gautschi NA, §3.2.6, (3.78)–(3.80), pp. 187–188.
Stoer–Bulirsch define the error as rule minus integral, as in the section;
Gautschi NA uses the opposite sign.

Item 12.11 is Quarteroni–Sacco–Saleri, Theorem 9.2, pp. 388–389, with the
error defined as integral minus rule; the full proof is referred there to
Isaacson–Keller. Stoer–Bulirsch, (3.1.4) and the table on pp. 147–148, list
the same error terms for $n\le6$ with reference to Steffensen. The composite
versions are Quarteroni–Sacco–Saleri, Theorem 9.3, pp. 392–393.

Item 12.12 is Stoer–Bulirsch, (3.3.1)–(3.3.4), pp. 156–157, with proof on
pp. 157–160; and Quarteroni–Sacco–Saleri, Property 9.3, p. 398. Gautschi NA,
Theorem 3.2.3, p. 194, and (3.97), p. 195, states the expansion without proof
for $f\in C^{2K+1}[a,b]$ with remainder $O(h^{2K+1})$, and Deuflhard–Hohmann,
Theorem 9.16, p. 288, states it with a remainder bounded uniformly in $h$.
The periodic bound is an immediate consequence of the formula, since the
boundary terms then cancel; Gautschi NA, p. 195, and Deuflhard–Hohmann,
Remark 9.17, p. 288, note the vanishing of the coefficients.

Item 12.13: the first part is Gautschi NA, Theorem 3.2.2, p. 191, with
conclusion (3.88), p. 192; Deuflhard–Hohmann, Theorem 9.22, p. 293, gives the
corresponding error estimate for the extrapolation tableau with general step
sizes. The Romberg error formula is Stoer–Bulirsch, (3.4.7), p. 165, for the
step sequence (3.4.5a), p. 163; it is quoted there without proof from Bauer,
Rutishauser and Stiefel and from Bulirsch. For $k=0$ and $k=1$ it reduces to
the trapezoidal and composite Simpson error terms.

Item 12.14 is Trefethen–Weideman, Theorem 3.2, p. 396, and Theorem 3.1,
p. 394, for the periodic case, and Theorem 5.1, p. 400, for the real line.

Item 12.15 is ATAP, Theorem 19.3, p. 189, Theorem 19.4, p. 190, and Theorem
19.5, p. 195; the Chebyshev points are (2.2), and the Bernstein ellipse is
defined in Chapter 8, p. 69. ATAP states the positivity of the
Clenshaw–Curtis weights without proof (p. 187), and also states that the
constant $64/15$ can be improved to $144/35$ for $n\ge4$ (Clenshaw–Curtis)
or $n\ge2$ (Gauss), and that the factor $\rho^{1-n}$ can be improved to
$\rho^{-n}$ for even $n$. Theorem 19.5 is quoted from Trefethen (2008)
without proof, and ATAP notes that its definition of $V$ differs slightly
from that paper. In ATAP, $V$ is the total variation of $f^{(\nu)}$ (Chapter
7, pp. 61–62).

Item 12.16 is Gautschi OP, Theorem 2.11, p. 60, and Example 2.12,
pp. 61–62, with the map defined in §2.1.3, pp. 57–58, and the infinity norm.
Gautschi OP, p. 59, factors the map from moments to recurrence coefficients
as $H_n\circ G_n$ and remarks that $H_n$ is generally well conditioned, so
that the two maps have comparable condition; that remark is heuristic, and
the section states the theorem only for $G_n$.

### 13. Discrete Fourier analysis and sparse recovery

The Fourier part follows Plonka–Potts–Steidl–Tasche, *Numerical Fourier
Analysis*, Birkhäuser 2018, whose conventions for $w_N$, $F_N$, $c_k(f)$ and
$\hat f$ the section adopts. The sparse recovery part follows
Foucart–Rauhut, *A Mathematical Introduction to Compressive Sensing*,
Birkhäuser 2013. Canuto–Hussaini–Quarteroni–Zang is volume 1 (2006),
Shen–Tang–Wang is the 2011 Springer edition, and Golub–Van Loan is the
local third edition (1996).

Item 13.1 is Plonka et al., Lemma 3.2, p. 110, Lemma 3.10, p. 119, the
identity (3.28) and the unitarity remark on pp. 119–120, Theorem 3.16,
p. 124, and the Parseval equality in Theorem 3.26(6), p. 134. Canuto et al.,
(2.1.25)–(2.1.27), p. 48, state the same orthogonality relation and inversion
formula with the factor $1/N$ on the forward transform and frequencies
$k=-N/2,\dots,N/2-1$; the statement keeps Plonka's unnormalized forward
transform. Item 13.2 is Plonka et al., the definition of cyclic convolution on
p. 130, the shift relation (3.43), p. 133, and Theorem 3.26(4)–(5),
pp. 133–134.

Item 13.3 is Plonka et al., (3.46), p. 137, Remark 3.30 and Theorem 3.31,
p. 138, Corollary 3.33, pp. 138–139, and the representation (3.50) with the
following remark on the commutative algebra, p. 139. Golub–Van Loan,
§4.7.7, (4.7.10), p. 202, states the same diagonalization without proof.
Horn–Johnson, §0.9.6, pp. 26–27, defines a circulant by its first row, the
transpose of Plonka's convention (Plonka et al., Remark 3.30, notes the
discrepancy in the literature), and records that circulants commute.

Item 13.4 is Plonka et al., (5.9), p. 243, and (5.10) with the following
description of the bit reversal, p. 244, for the factorization, and
Remark 5.10, the recursions (5.12)–(5.13), pp. 250–251, (5.17)–(5.18) and
Theorem 5.12, p. 253, for the count. The matrix $P_N$ of Plonka et al. is
the perfect shuffle of Example 5.4, p. 243, so $\Pi_N=P_N^\top$ and (5.9)
reads as in the statement; the factorization was also checked numerically
for $N=2,4,8,16$. Theorem 5.12 is stated there for $t\in\mathbb N$, but the
recursions are stated for $t\ge2$ with the initial values $\mu(2)=0$,
$\alpha(2)=16$ (p. 251). For $t=1$ the actual counts $\mu(1)=0$, $\alpha(1)=4$
differ from the closed forms, which give $1$ and $5$; the statement therefore
requires $t\ge2$.

Item 13.5 is Plonka et al., (3.3), p. 109, Theorem 3.3 and Corollary 3.4,
p. 111. Canuto et al., (2.1.36), p. 50, give the same relation under the
hypothesis that the Fourier series converges to $u$ at every node, and
Shen–Tang–Wang, (2.53), p. 36, under $u\in H^m_p$, $m>1/2$; absolute
summability of the coefficients, as in Plonka et al., is the hypothesis kept.

Item 13.6 is Canuto et al., §5.1.3, (5.1.16) and (5.1.19), p. 272, for the
interpolation error, and (5.1.10), p. 270, for the truncation error, with the
interpolant (2.1.28), p. 48, in which $N/2$ is replaced by $N$, as stated at
the start of §5.1.3. Shen–Tang–Wang, Theorem 2.1, p. 34, and Theorem 2.3,
p. 36, give the same rates for real $m>1/2$, bounded by the seminorm
$|u|_m=(\sum_k|k|^{2m}|c_k(u)|^2)^{1/2}$, which agrees with
$(2\pi)^{-1/2}\|u^{(m)}\|_{L^2(0,2\pi)}$ for integer $m$; their interpolant uses
the frequencies $|k|\le N$ with $\tilde u_N=\tilde u_{-N}$ and is a slightly
different operator from Canuto's. Neither source makes the constant explicit;
the statement asserts only that it depends on $m$ (and on $l\le m$). Plonka
et al., Lemma 3.6, p. 114, give existence and uniqueness of the interpolant
for an odd number $2n+1$ of nodes with frequencies $|k|\le n$.

Item 13.7 is Plonka et al., (2.21) and Theorem 2.26, p. 84; Remark 2.27,
p. 85, gives the decay conditions
$|f(x)|,|\hat f(x)|\le C(1+|x|)^{-1-\varepsilon}$ as a sufficient alternative.
Item 13.8 is Plonka et al., Theorem 2.29, p. 86, with the sinc function as
defined on p. 389 and $C_0(\mathbb R)$ as on p. 61.

Item 13.9 is Plonka et al., §7.1, (7.1)–(7.14) and Algorithm 7.1,
pp. 378–381, specialized to $d=1$, with (7.6), p. 379, for
$c_k(\tilde\varphi)=\hat\varphi(k)/(2\pi)$, and the B-spline window (7.29)
with (7.30)–(7.31) and Lemma 7.6, pp. 388–389. For the B-spline window
$\psi=\varphi$, so the approximation $s$ equals $s_1$ and the error is pure
aliasing. Plonka et al. assume $2m\ll\sigma N$ without making it precise; the
statement assumes $2m\le\sigma N$, which puts the support of $\varphi$ inside
$[-\pi,\pi]$, and the proof of Lemma 7.6 uses only (7.30)–(7.31) and
$|k|/(\sigma N)\le1/(2\sigma)$. The series bound (7.34) was checked
numerically for $\sigma\in\{1.25,2\}$ and $m\in\{1,2,4\}$. Lemma 7.7,
p. 390, gives $4e^{-m\pi(1-1/(2\sigma-1))}\|\hat f\|_1$ for the truncated
Gaussian window, and Theorem 7.8, p. 393, collects the bounds for four
windows, two of them only with a reference to the literature; these are not
included because the truncation hypotheses are not stated precisely there.
The operation count is the one stated after (7.14), p. 380, and in
Algorithm 7.1, p. 381.

Item 13.10 is Plonka et al., §10.1, (10.1)–(10.9) and Algorithm 10.1,
pp. 523–526. The factorization of the Hankel matrix is stated on p. 525 with
$V_M(z)^\top$; the identification of the zeros of $p$ with the $z_j$ is the
definition (10.3) together with the uniqueness of the solution of (10.7).

Item 13.11 is Foucart–Rauhut, Definitions 2.1 and 2.2, pp. 41–42,
Proposition 2.3, p. 42, Theorem 2.13, p. 49, and Theorem 2.14, p. 50.
Item 13.12 is Foucart–Rauhut, Definition 4.1, p. 78, and Theorems 4.4 and
4.5, p. 79, valid over $\mathbb K=\mathbb R$ and $\mathbb C$ alike.

Item 13.13 is Foucart–Rauhut, Definition 4.21, p. 87, Theorem 4.22, p. 88,
and Theorem 4.25 with $q=2$, p. 89, where the constants
$C=(1+\rho)^2/(1-\rho)$ and $D=(3+\rho)\tau/(1-\rho)$ are given. Theorem 4.22
states the final error bound only with unspecified constants depending on
$\rho,\tau$; the factors $2C$ and $2D$ in the statement follow from
Theorem 4.25 with $z=x^\sharp$, using $\|x^\sharp\|_1\le\|x\|_1$ and
$\|A(x^\sharp-x)\|_2\le2\eta$.

Item 13.14 is Foucart–Rauhut, Definition 6.1 with (6.2), p. 133, Theorems
6.12 and 6.13, p. 144, with the explicit $\rho$ and $\tau$ read from the proof
of Theorem 6.13, pp. 145–147. The equivalence $\rho<1\iff\delta_{2s}<4/\sqrt{41}$
follows from $(5\delta/4)^2<1-\delta^2$. Plonka et al., Remark 7.5, p. 384,
quote the same threshold.

Item 13.15 is Foucart–Rauhut, Theorem 9.27 and Remark 9.28, pp. 292–293,
for Gaussian matrices with explicit constants; Definition 9.1, p. 272, and
Theorem 9.2 and Corollary 9.3, p. 273, give the subgaussian and Bernoulli
versions with a non-explicit constant. The value $\tilde C=2C^2$ with
$C=2(1+2^{-1/2})+(1+2^{-1/2})^2\approx6.3284$ is that of Remark 9.28, valid
because $\log(eN/s)\ge1$ and $\eta^2\le\eta$.

Item 13.16 is Foucart–Rauhut, Definitions 5.1 and 5.2, p. 111, the bounds
(5.2), p. 112, the description of orthogonal matching pursuit, p. 65, and
Theorems 5.14 and 5.15, pp. 123–124. Foucart–Rauhut define $\mu_1(s)$ only for
$1\le s\le N-1$; the convention $\mu_1(0)=0$, needed for $s=1$, is implicit in
their proofs, where $\mu_1(s-1)$ bounds a sum over an empty set. The
recovery holds for any choice of the maximizing index in each step.

Item 13.17 is Foucart–Rauhut, Definition 10.1, p. 311, Theorem 10.5, p. 315,
and Theorem 10.11, p. 319. Chapter 10 of Foucart–Rauhut works over
$\mathbb R$. Trefethen's *Approximation Theory and Approximation Practice* is not
used in this section.

### 14. Initial value problems: one-step and multistep methods

The section follows Hairer–Nørsett–Wanner, *Solving Ordinary Differential
Equations I*, 2nd ed., Springer 1993 (cited as HNW), which writes $x$ for
the independent variable. Butcher, *Numerical Methods for Ordinary
Differential Equations*, is the local 2003 Wiley edition. Iserles is
*A First Course in the Numerical Analysis of Differential Equations*, 2nd
ed., Cambridge 2008; Quarteroni–Sacco–Saleri is *Numerical Mathematics*, 2nd
ed., Springer 2007; Stoer–Bulirsch is the 3rd ed., Springer 2002.

Item 14.1 is HNW, Theorem I.7.3, p. 37 (local form, with convergence of
the Euler polygons, stated for a scalar equation and carried over to
systems in Section I.9, p. 51), and Butcher, Definition 110A and Theorem
110C, p. 23 (global form on $[a,b]\times\mathbb R^N$). HNW, Theorem I.7.4,
p. 39, gives continuation up to the boundary of an open set when $f$ and
$\partial f/\partial y$ are continuous.

Item 14.2 is Quarteroni–Sacco–Saleri, Lemma 11.1, p. 481 (continuous
Gronwall lemma), and Lemma 11.2, p. 486 (discrete Gronwall lemma).

Item 14.3 is HNW, Theorem I.10.2 ("fundamental lemma"), p. 58. The
one-sided Lipschitz bound is Butcher, Definition 112A and Theorem 112B, p. 27.

Item 14.4 is HNW, Lemma II.3.5 and Theorem II.3.6, p. 162, which assume
the Lipschitz condition on $\Phi$ only in a neighbourhood of the solution;
the global Lipschitz condition stated here avoids a smallness condition on
$h$. The order is HNW, Definition II.1.2, p. 134. Quarteroni–Sacco–Saleri,
Theorem 11.2, p. 487, give the variant
$|y_n-u_n|\le(|y_0-u_0|+nh\tau(h))e^{nh\Lambda}$ with $\tau(h)$ the maximal
local truncation error. The Euler bound is HNW, Theorem I.7.5, p. 40.

Item 14.5 is HNW, Definition II.1.1 (explicit) and condition (1.9), p. 134,
Definition II.7.1, p. 205 (implicit), and Theorem II.7.2, p. 206 (unique
solvability of the stage equations).

Item 14.6 is HNW, Definitions II.2.9–2.10 and Theorem II.2.11, p. 151, the
recursions (2.17), (2.19) and Definition 2.12, p. 152, and Theorem II.2.13,
p. 153, with the tree counts in Table 2.1, p. 147, and the condition counts
in Table 2.3, p. 154. HNW states Theorem 2.13 for explicit methods; the
remark at the start of Section II.7, p. 207, extends the order conditions to
implicit methods. Butcher, Theorem 315A, pp. 147–148, treats general
tableaux, and Theorem 302B, p. 128, with Table 302(I), p. 129, gives the
generating function and the counts.

Item 14.7 is HNW, Theorem II.5.1, p. 173 ($p\ge5$), and Theorems II.5.3
(Butcher 1965) and II.5.4 (Butcher 1985), p. 179, with the existence of
the 9-stage order-7 and 11-stage order-8 methods on the same page; and
Butcher, Theorems 370A, p. 258, and 370B, p. 259, with the two further
barriers recalled on p. 260.

Item 14.8 is HNW, Theorem II.7.4 (Butcher 1964), p. 208, also restated as
Hairer–Wanner II, Theorem IV.5.1, p. 72 (Hairer–Wanner, *Solving Ordinary
Differential Equations II*, 2nd ed., Springer 1996).

Item 14.9 is HNW, Definition II.7.6, p. 211, Theorems II.7.7 and II.7.8,
p. 212, and Theorem II.7.9, p. 212. The orders of Gauss and Lobatto are
also HNW, pp. 209–210. The node polynomials and the orders of Radau IIA and
Lobatto IIIA are Hairer–Wanner II, (5.2)–(5.3), p. 72, and Theorems IV.5.3,
p. 73, and IV.5.5, p. 75. The characterization of order $2s$ is Butcher,
Corollary 342D, p. 201; the bound $p\le2s$ follows because order $p$
implies $B(p)$, and an $s$-point quadrature rule has degree of exactness at
most $2s-1$.

Item 14.10 is HNW, (2.1)–(2.2), p. 368, Definition III.2.3 and Theorem
III.2.4, p. 370, and the error constant (2.7)–(2.8), p. 372, and (2.13),
p. 373; Iserles, Theorem 2.1, p. 22, which writes the condition as
$\rho(w)-\sigma(w)\log w=c(w-1)^{p+1}+O(|w-1|^{p+2})$. Butcher,
Theorem 410C, p. 313, gives the condition with $\exp(z)$.

Item 14.11 is HNW, Definition III.3.2, p. 380 (where the root condition is
called stability), Definition III.4.1, pp. 391–392, with the assumptions
(4.2), p. 391, Theorem III.4.2, p. 392 (convergent implies stable and
consistent), and Theorem III.4.5, p. 395 (stable and consistent of order $p$
implies convergent of order $p$); Iserles, the root condition on p. 24 and
Theorem 2.2 (Dahlquist equivalence theorem), p. 25; and Butcher, Theorem
243A, p. 102, and Theorems 405A, p. 306, 405C, p. 307, and 406D, p. 310.

Item 14.12 is HNW, Theorem III.3.5, p. 384, and Butcher, Theorem 441C,
p. 339.

Item 14.13 is HNW, (3.10), p. 380, and Theorem III.3.4, p. 381, and
Iserles, Lemma 2.3, p. 27, and Theorem 2.4, p. 28. Iserles normalizes $\rho$
by the factor $(\sum_{m=1}^k1/m)^{-1}$ so that $\sigma(\zeta)=\beta\zeta^k$
with $\beta$ that factor; the two forms define the same method.

Item 14.14 is HNW, Theorem II.8.1 (Gragg 1964), p. 217, with the local
error expansion (8.2), p. 216, Theorem II.8.10, p. 222 (symmetric methods),
and, for extrapolation, (9.1)–(9.4), p. 224, and Theorem II.9.1, p. 225.

Item 14.15 is Stoer–Bulirsch, Theorem (7.2.12.7), p. 516, which also holds
for systems, and HNW, the method (9.13), p. 228, the expansion (9.18),
p. 229, and Theorem II.9.2, p. 230, for the smoothed value.

Item 14.16 is HNW, Definition II.12.1, p. 266, and Definition II.12.4 and
Theorem II.12.6 (Hairer & Wanner 1974), p. 267, with $\alpha(t)$ from
Section II.2, p. 147, and the group property as Exercise 4 of Section
II.12, p. 272. HNW sums over labelled trees; the sum over unlabelled trees
with the factor $\alpha(t)$ is its (12.7). Butcher, Subsections 384–388,
pp. 273–285, treats the group of elementary weight functions.

### 15. Stiff problems, differential-algebraic equations, and geometric integration

The section follows Hairer–Wanner, *Solving Ordinary Differential Equations
II*, 2nd ed., Springer 1996 (cited as HW), for stiff problems and
differential-algebraic equations, and Hairer–Lubich–Wanner, *Geometric
Numerical Integration*, 2nd ed., Springer 2006 (cited as HLW), for geometric
integration. Iserles is the 2nd ed. (2008) and Butcher the 2003 edition.

Item 15.1 is HW, Propositions IV.3.1, p. 40, and IV.3.2, p. 41, and, for
explicit methods, the polynomial form, Definition IV.2.1 and Theorem
IV.2.2, p. 16. Theorem IV.2.2 is stated for explicit methods; for implicit
methods the relation $R(z)=e^z+O(z^{p+1})$ follows by applying the method
to the test equation.

Item 15.2 is HW, (3.5) and Definition IV.3.3, p. 42, the criterion on
p. 43, and Definition IV.3.7, p. 44; the explicit case is HW, p. 16, and
Iserles, Lemma 4.1 and its Corollary, p. 60. Iserles defines the linear
stability domain with the strict inequality $|R(z)|<1$ and calls a method
A-stable if it contains the open left half-plane; HW uses the closed set
$|R(z)|\le1$ and the closed half-plane. For nonconstant rational $R$ the
two notions agree.

Item 15.3 is HW, Theorem IV.3.11, p. 48 (the Padé approximations), and
Theorem IV.4.12, p. 58 (A-stability if and only if $k\le j\le k+2$, proved
by order stars); and Iserles, Theorem 4.5, pp. 62–63, and Theorem 4.6
(Wanner–Hairer–Nørsett), p. 63. Butcher, Theorem 355G, p. 228, proves the
necessity of $d\le n+2$ for an $(n,d)$ Padé stability function. All three
sources write the numerator degree first.

Item 15.4 is HW, Theorems IV.5.2, p. 72, IV.5.3, p. 73, and IV.5.5, p. 75,
and, for the Gauss methods, Iserles, the Corollary to Theorem 4.6, p. 63.
L-stability of Radau IA, Radau IIA and Lobatto IIIC follows from Definition
IV.3.7 because the numerator degree of their stability functions is less
than the denominator degree.

Item 15.5 is HW, Definition V.1.1, p. 241, and Theorem V.1.4 (Dahlquist
1963), p. 247, with the A-stability of BDF2 on the same page; Iserles,
Theorems 4.10 and 4.11, p. 67; and Butcher, Theorems 443A and 443B, p. 342.
The error constant is the normalized constant $C=C_{p+1}/\sigma(1)$ of
HNW, (2.13), p. 373.

Item 15.6 is HW, Definition V.2.1 (Widlund 1967), p. 250, and the table of
angles (2.7), p. 251, which are computed values.

Item 15.7 is HW, Definition IV.12.2, p. 181, Theorem IV.12.4 and Definition
IV.12.5, p. 182, Theorem IV.12.9, p. 184, Definition IV.12.10 and Theorems
IV.12.11 and IV.12.12 (Scherer 1979), p. 185, and Theorem IV.12.13 (Burrage
& Butcher 1979) and Corollary IV.12.14, p. 186. Butcher, Definition 356A
and Theorem 356C, p. 230, Definitions 357A and 357B, p. 233, Theorem 357C,
p. 234, and Theorem 357D, p. 235, gives the same chain under the name
BN-stability, and states the converse for irreducible non-confluent methods;
HW, Corollary 12.14, needs only non-confluence. Iserles, Theorem 5.2, p. 79,
proves the sufficiency of $b_i\ge0$ and $M\succeq0$ but uses "algebraically
stable" for the nonexpansion property itself.

Item 15.8 is HW, (15.11) and Theorem IV.15.3, p. 230, and Definition IV.15.4
(Frank, Schneid & Ueberhuber 1981) and Theorem IV.15.5, p. 231.

Item 15.9 is HW, Theorem VII.1.1 (Weierstrass 1868, Kronecker 1890),
pp. 452–453, the decoupled form (1.6)–(1.7), p. 453, the index of
nilpotency, p. 454, and Definition VII.1.2 with the remark on constant
coefficients, p. 455. HW writes the system as $Bu'+Au=d(x)$.

Item 15.10 is HW, the index-1 problem (1.6)–(1.7), p. 374, the method
(1.11), pp. 374–375, stiff accuracy (1.13), p. 376, and the estimate (1.24)
with Theorem VI.1.1, p. 380; and the multistep method (2.2) with Theorem
VI.2.1, p. 382.

Item 15.11 is Hochbruck–Ostermann, "Exponential integrators", Acta Numerica
19 (2010), pp. 209–286: $\varphi_1$ in (2.10), p. 217, Assumptions 2.9 and
2.10, p. 222, the method (2.29), p. 223, and Theorem 2.14, p. 224.

Item 15.12 is HLW, Definition VI.2.2, p. 183, Theorem VI.2.4 (Poincaré
1899), p. 184, and Definition VI.3.1, p. 187; and Iserles, Theorem 5.6,
p. 89.

Item 15.13 is HLW, Theorems IV.2.1 and IV.2.2 (Cooper 1987), p. 101,
Theorems VI.4.2 and VI.4.3, p. 192, Theorem VI.7.10, p. 222, and Lemma
IV.3.2 and Theorem IV.3.3, p. 106; and Iserles, Theorem 5.7, p. 91 ($M=O$
implies symplectic).

Item 15.14 is HLW, Theorem VI.3.3, p. 189, and Theorem VI.3.4 with (3.4),
pp. 189–190.

Item 15.15 is HLW, the modified equation (1.1)–(1.4), p. 338, Theorem
IX.1.2, p. 340, the assumptions (7.2)–(7.3), p. 360, Theorem IX.7.2 with
(7.4)–(7.5), p. 361, the constant $\eta$ from the proof of Theorem IX.7.5,
p. 364, and Theorem IX.7.6, p. 365.

Item 15.16 is HLW, (8.1), p. 366, and Theorem IX.8.1 (Benettin & Giorgilli
1994), p. 367.

Item 15.17 is HLW, Section II.5, pp. 47–48 (Lie–Trotter and Strang
splitting), and the symmetric Baker–Campbell–Hausdorff formula
(4.14)–(4.15), pp. 86–87.

### 16. Finite difference methods for differential equations

Stoer–Bulirsch is the 3rd ed. (2002), Varga's *Matrix Iterative Analysis*
the 2nd ed. (2000), Iserles the 2nd ed. (2008), Quarteroni–Sacco–Saleri the
2nd ed. (2007), Hackbusch's *Iterative Solution of Large Sparse Systems of
Equations* the 2nd ed. (2016), Han–Atkinson's *Theoretical Numerical
Analysis* the 3rd ed. (2009), Trefethen–Embree's *Spectra and
Pseudospectra* the 2005 edition, Hundsdorfer–Verwer's *Numerical Solution of
Time-Dependent Advection-Diffusion-Reaction Equations* the 2003 edition (cited
as HV), LeVeque's *Finite Volume Methods for Hyperbolic Problems* the 2002
edition, and Hairer–Wanner II the 2nd ed. (1996). The finite difference
books of LeVeque (2007) and Gustafsson–Kreiss–Oliger, which treat several of
these topics, were not checked because no local copy exists.

Item 16.1 is Stoer–Bulirsch, the truncation error (7.4.2), p. 582, Theorem
(7.4.7), p. 583, and Theorem (7.4.10), p. 585; and Varga, Theorems 6.1,
p. 186, and 6.2, p. 187, with the maximum bound (6.10). The monotonicity of
the one-dimensional scheme (the discrete maximum principle) is also in
Quarteroni–Sacco–Saleri, (12.5)–(12.10), pp. 540–542.

Item 16.2 is Iserles, Lemma 12.5, p. 264 (tridiagonal Toeplitz matrices),
and Lemma 8.1, p. 151, for the five-point matrix on the unit square with
$\Delta x=1/(m+1)$ and without the factor $h^{-2}$; and Hackbusch, Theorem
3.1, pp. 35–36, and Lemma 3.2, p. 36, which give the eigenvalues, the
extreme eigenvalues and the orthonormal eigenvectors for $h=1/N$. The
condition number is the quotient of the extreme eigenvalues.

Item 16.3: the five-point formula and its order are Iserles, (8.16), p. 149;
the explicit bound on the truncation error is the one-dimensional bound of
16.1 applied in each direction. The matrix properties are Varga, Theorem 6.5,
p. 211, proved there for a five-point (box-integration) discretization of
$-(Pu_x)_x-(Pu_y)_y+\sigma u=f$ on a bounded connected region with $P>0$,
$\sigma>0$ and mixed boundary conditions, (6.37)–(6.40), p. 205; the
remark after the theorem, p. 211, notes that $\sigma>0$ may be replaced by
the presence of a Dirichlet boundary point adjacent to an unknown, which
covers the model problem. No local source states the two-dimensional discrete
maximum principle in the form given; it follows from the sign pattern of
$L_h$ by the standard argument at an interior maximum, and the
one-dimensional version is in Quarteroni–Sacco–Saleri, p. 542.

Item 16.4 rests on the discrete maximum principle of 16.3 and the comparison
function $\phi$; no local source states the explicit two-dimensional constant
$1/96$, which is the analogue of Stoer–Bulirsch, Theorem (7.4.10), and
Varga, (6.10). Iserles, Theorem 8.2, p. 154, states an $O(h^2)$ bound in the
unscaled Euclidean norm on $\mathbb R^{m^2}$. That statement is not correct as
written: the truncation vector has $m^2$ entries of size $O(h^2)$, so its
unscaled Euclidean norm is $O(h)$, not $O(h^2)$ as the proof asserts; the
bound holds for the scaled norm $\|\cdot\|_h$ of 16.4 and in the maximum
norm.

Item 16.5 is Han–Atkinson, Definitions 6.2.1–6.2.3, pp. 260–261,
Definition 6.2.7, p. 263, and Definitions 6.2.9 and 6.2.10 and Theorem
6.2.11 (Lax equivalence theorem), p. 266. The uniform bound on the
one-step family is stated before Definition 6.2.7. Iserles, Theorem 16.3, p. 360,
and LeVeque, Section 8.3.2, p. 145, state the theorem informally.

Item 16.6 is Iserles, Theorem 16.11, p. 375 (with the semi-discrete
analogue, Theorem 16.10, on the same page), Theorem 16.7, p. 368, and
Theorem 16.8, p. 370; Quarteroni–Sacco–Saleri, Theorem 13.1, p. 616
(sufficiency of $|\gamma_k|\le1$ in the periodic case); and HV, (6.30)–(6.31)
and the remark on normal matrices, p. 113.

Item 16.7 is LeVeque, Section 4.4, p. 69, which states the CFL condition as a
necessary condition for convergence and stresses that it is not sufficient,
and Quarteroni–Sacco–Saleri, Section 13.8.3, pp. 613–614. The latter
describes (13.48) as necessary and sufficient for stability of every explicit
scheme of the form (13.36); this is contradicted by its own Section 13.8.4,
pp. 615–616, where the forward Euler centered scheme is shown to be unstable
for every Courant number.

Item 16.8 is LeVeque, Example 8.2, p. 147 (upwind, 2-norm), and Section
8.3.4, pp. 147–148 (upwind, 1-norm); Quarteroni–Sacco–Saleri, the schemes
(13.37)–(13.41), p. 610, the truncation errors in Table 13.1, p. 611, the
1-norm stability of upwind and Lax–Friedrichs, pp. 614–615, where the
stability of Lax–Wendroff is only cited, and the forward Euler centered
scheme, pp. 615–616; HV, Example 6.9, p. 113, and Iserles, p. 399, for the
Lax–Wendroff amplification factor. The maximum-norm bound for upwind follows
because the scheme is a convex combination when $0\le\nu\le1$.

Item 16.9 is HV, the stability domain (6.20) and Table 6.1, p. 105, based on
the eigenvalue criterion (6.19) for normal matrices, p. 104, and the
explicit case and the exercise in footnote 43, p. 112. Quarteroni–Sacco–Saleri,
pp. 597–598, obtain the analogous restriction
$\Delta t\le2/((1-2\theta)\lambda_{\max})$ for the finite element
semi-discretization.

Item 16.10 is Trefethen–Embree, the Kreiss constant (18.1), p. 176, and
Theorem 18.1, p. 177, for an arbitrary vector norm and its induced matrix
norm; p. 177 also recounts the history of the constant $eN$.

Item 16.11 is HV, the definition (2.25) and Theorem I.2.4, p. 32, the
formulas (2.30), p. 33, and Theorem I.2.13, p. 41.

Item 16.12 is Hairer–Wanner II, Theorem IV.11.2 (von Neumann), p. 168; and
HV, Theorem I.2.8 and Corollary I.2.9, p. 39, Theorem I.2.11, p. 40, and
Corollary I.2.12, p. 41.

Item 16.13 is HV, Theorem I.7.1, p. 116, and Theorem I.7.2, p. 117.

Item 16.14 is HV, the conditions (4.9)–(4.10), p. 189, and the form (4.11)
with Theorem II.4.6, p. 190; and LeVeque, Section 10.4.2, (10.17)–(10.18),
pp. 194–195, for the total variation diminishing two-stage method. The
corresponding result for a general convex functional and general explicit
Shu–Osher forms (Shu–Osher; Gottlieb–Shu–Tadmor) has no local source and is
not stated.

Item 16.15 is the continuous-operator case of Barles–Souganidis,
[Convergence of Approximation Schemes for Fully Nonlinear Second Order
Equations](https://doi.org/10.3233/ASY-1991-4305), Theorem 2.1 and
(2.1)–(2.5), p. 275. The general form there uses the upper and lower
semicontinuous envelopes in (2.4).

### 17. Hyperbolic conservation laws and finite volume methods

Locators in this section refer to Godlewski–Raviart, *Numerical
Approximation of Hyperbolic Systems of Conservation Laws*, 2nd ed. (2021),
cited as GR; LeVeque, *Finite Volume Methods for Hyperbolic Problems* (2002);
Holden–Risebro, *Front Tracking for Hyperbolic Conservation Laws*, 2nd ed.
(2015), cited as HR; Ern–Guermond, *Finite Elements III* (2021), cited as
EG III; Hundsdorfer–Verwer, *Numerical Solution of Time-Dependent
Advection-Diffusion-Reaction Equations* (2003); and Tadmor, Acta Numerica
Vol. 12 (2003), pp. 451–512. The 2nd edition of GR treats systems and refers
the proofs of the scalar theory of schemes to its 1996 scalar volume, which
was not checked; its scalar scheme statements in Chapter IV are given with
little proof. HR works in one space dimension throughout and proves the
scalar theory by front tracking.

Item 17.1 is EG III, Definition 79.8, p. 327, with the Burgers example of two
weak solutions (79.8) on p. 328, and LeVeque, (11.39), p. 217, where the
same jump is called an entropy-violating shock. The jump characterization is
EG III, Lemma 80.15, p. 346, stated for systems, with Remark 79.14, p. 332,
for the scalar case.

Item 17.2: the definition of an entropy pair is GR, Definition 5.1, p. 38;
the vanishing viscosity limit is GR, Theorem 5.3, pp. 44–45; the entropy
solution is GR, Definition 5.2, p. 46, with the jump inequality (5.14)–(5.15)
on pp. 46–47. EG III, Theorem 79.10, p. 329, uses all convex Lipschitz
entropy pairs, and its Remark 79.12, pp. 329–330, and GR, Remark 5.5, p. 51,
state that the Kružkov pairs suffice. The Lax and Oleinik conditions are
LeVeque, Entropy Conditions 11.1 and 11.2, p. 218, with entropy functions in
(11.42)–(11.45), p. 219. The cubic identity for Burgers' equation is a direct
computation. The equivalence of the entropy inequality with the Lax and
Oleinik conditions for a general strictly convex flux is stated in LeVeque
as motivation rather than proved; for weak shocks it is the case $m=1$ of
GR, Theorems 5.2 and 5.3, pp. 109–110. No local source was checked for the
global scalar equivalence.

Item 17.3 is GR, Theorem 5.4, pp. 50–51, and EG III, Theorems 79.10 and
79.11, p. 329, for existence, uniqueness and the maximum principle. GR states
order preservation and, for BV data, the TV bound, but does not state the
$L^1$ contraction separately. The $L^1$ contraction for $f$ Lipschitz is HR,
Proposition 2.10, p. 79. The flux-stability estimate is HR, Theorem 2.14,
p. 86, whose hypotheses include piecewise $C^2$ fluxes. The full list of
properties in one space dimension, including the time continuity, is HR,
Theorem 2.15, pp. 86–87.

Item 17.4 is HR, Theorem 2.2, p. 64, and EG III, (79.14)–(79.15), p. 331, and
Theorem 79.15, p. 332, with the convex case also in GR, (5.28), pp. 51–52.
EG III assumes that $f$ has finitely many convex and concave pieces; HR
proves the envelope construction for piecewise $C^2$ fluxes by front
tracking.

Item 17.5 is GR, Chapter IV, Theorem 1.1, p. 219, with the scheme (1.2) and
the cell entropy inequality on p. 217; LeVeque, Theorem 12.1, p. 240, with
the entropy version (12.37)–(12.38), p. 243; and HR, Theorem 3.4, p. 105.
The hypotheses differ. GR assumes a uniform $L^\infty$ bound with
convergence in $L^1_{\mathrm{loc}}$ and a.e., as stated here. LeVeque assumes
$L^1$ convergence on bounded sets with a uniform TV bound and remarks that
Lax and Wendroff assumed bounded a.e. convergence. HR assumes a uniform TV
bound.

Item 17.6: the definitions are HR, Definition 3.5, p. 107, and LeVeque,
Definitions 6.1 and 6.2, pp. 109–110, with monotone methods at (12.42),
p. 245. The chain of implications is HR, Theorem 3.6, pp. 107–108; GR,
p. 220, states that a TVD scheme is monotonicity preserving, and LeVeque,
p. 110, leaves it as Exercise 6.3. The Lax–Friedrichs condition is HR,
Example 3.7, p. 109, and GR, p. 222.

Item 17.7 is HR, Theorem 3.9, p. 111, which proves convergence for every
sequence $\Delta t\to0$ using the discrete Kružkov inequality (3.33). HR
does not name the result; Tadmor, p. 462, attributes the convergence of
monotone schemes to Crandall and Majda. LeVeque, Theorem 12.3, p. 251, gives
the weaker statement that a TV-stable conservative scheme approaches the set
of weak solutions.

Item 17.8: the Harten–Hyman–Lax barrier is HR, Theorem 3.10, p. 115, with
the truncation error computed before it on pp. 114–115; GR, p. 220, and
Tadmor, p. 462, cite it. The linear barrier is Hundsdorfer–Verwer, Section
I.7, p. 119, for the scheme (3.25) with the order conditions (3.26) on p. 59
and the positivity condition (7.6) on p. 118. It is stated there for the
semi-discretization only and attributed to Godunov (1959). No fully
discrete form of Godunov's theorem was found in a local source.

Item 17.9 is HR, Lemma 3.12, p. 118; LeVeque, Theorem 6.1, p. 116; and GR,
Proposition 1.3, p. 221. LeVeque writes the coefficients as $C_{i-1}$ and
$D_i$, with the condition $C_i+D_i\le1$; HR and GR index them by half
integers as here. The maximum principle part is in HR only. GR adds that the
conditions are necessary for three-point schemes. The step from
monotonicity preserving to monotone for linear schemes is Godunov's theorem,
for which no local source was checked.

Item 17.10 is HR, (3.54)–(3.55), p. 127, and Theorem 3.14, p. 128. The
viscous bound is HR, Example 3.16, p. 134. The $\sqrt{\Delta x}$ rate is HR,
Example 3.17, pp. 134–139, with the result (3.72) on p. 139. The front
tracking statements are HR, Lemma 2.6, p. 71, Corollary 2.8, p. 73, and the
estimate (2.79) in the proof of Theorem 2.14, p. 86. HR writes the rate in
terms of $\sqrt{\Delta t}$; with $\Delta t=\lambda\Delta x$ this is the same.

Item 17.11 is Tadmor: the entropy variables (2.4) and the potential
(2.8)–(2.9), p. 457; the semi-discrete scheme (3.1)–(3.4), p. 463; Theorem
3.1, p. 464, with the necessity for three-point schemes; the scalar flux
(4.4) and the viscosity form (4.3), (4.6), p. 465; Corollary 4.1,
pp. 465–466; and Example 4.2, p. 466, for $\eta=-\log u$. Tadmor writes the
viscosity form as $g=\frac12(f_j+f_{j+1})-\frac12Q\,\Delta w$ and states
entropy stability as $Q\ge Q^*$; the coefficient $Q$ of the text is Tadmor's
$Q-Q^*$. The flux for $\eta=u^2/2$ is computed from (4.4).

Item 17.12: hyperbolicity is EG III, Definition 80.1, p. 338; genuine
nonlinearity and linear degeneracy are EG III, Definition 80.11, p. 344; the
entropy pair for systems is EG III, Definition 80.5, p. 340, and GR,
Definition 5.1, p. 38. Riemann invariants are GR, Definition 3.2, Remark 3.1
and Lemma 3.1, pp. 84–85, and Theorem 3.2, p. 88. The symmetrization is GR,
Theorem 5.1, p. 40.

Item 17.13 is HR, Definition 5.13 and Theorem 5.14, p. 248, and GR, Theorems
5.2 and 5.3, pp. 109–110; contacts and shocks are also EG III, Lemmas 80.16
and 80.17, pp. 346–347.

Item 17.14 is HR, Theorem 5.17, p. 254; EG III, Theorem 80.18, pp. 347–348;
and GR, Theorem 6.1, p. 117. EG III phrases smallness as
$\|u_L-u_R\|\le\delta$ and refers the vanishing viscosity justification to
Bianchini and Bressan.

Item 17.15 is HR, Theorem 6.4, p. 297 (front tracking is well defined with
uniformly bounded variation), Theorem 6.7, p. 307 (existence and the Lax
conditions at isolated jumps), Theorem 7.8, p. 344 (uniqueness of the limit,
$L^1$ stability and the $O(\delta)$ rate), and Theorem 7.10, p. 345
(uniqueness). Glimm's scheme and the Bianchini–Bressan vanishing viscosity
theory are cited, not proved, in EG III, Remark 80.6, pp. 340–341; the
Glimm existence result rests on that citation.

### 18. Galerkin and finite element methods for elliptic problems

Locators in this section refer to Brenner–Scott, *The Mathematical Theory of
Finite Element Methods*, 3rd ed. (2008), cited as BS, whose results are
numbered by paragraph; and Ern–Guermond, *Finite Elements I* and *Finite
Elements II* (both 2021), cited as EG I and EG II. EG works over $\mathbb C$
with sesquilinear forms; the statements here are the real case. EG uses
$\ell_D$ for the length scale and calls both inequalities of 18.5
Poincaré–Steklov inequalities. BS writes $n$ for the dimension. BS states a
non-degeneracy condition $\mathop{\mathrm{diam}}B_T\ge\rho\,\mathop{\mathrm{diam}}T$,
(4.4.16), p. 108, which is equivalent to shape regularity in the sense of EG I,
Definition 11.2, p. 124.

Item 18.1 is BS, (2.7.7), p. 62, and EG II, Lemma 25.2, p. 15 (Lax–Milgram),
and Theorem 25.9, p. 17 (BNB).

Item 18.2 is EG II, Lemma 26.3 and Theorem 26.6, p. 29, and Lemma 26.9, p. 31
(Fortin). EG proves the converse in the Hilbert setting; its constant was
not recorded here.

Item 18.3 is EG II, Lemmas 26.12 and 26.13, p. 33 (Galerkin orthogonality
and Céa, with the symmetric case), Lemma 26.14, p. 34 (Babuška), and Lemma
26.18, p. 36 (Xu–Zikatanov); and BS, (2.8.1), p. 64 (Céa). The comparison
for the inner product is a direct check.

Item 18.4 is EG II, Lemma 27.12, p. 50 (Strang 1), and Lemma 27.15, p. 51
(Strang 2). In EG a factor $c$ with $\|v_h\|\le c\|v_h\|_{V_h}$, (27.5),
p. 44, multiplies the second terms; the statement here takes the norms equal,
so $c=1$. The energy-norm version is BS, (10.1.9), p. 274; BS, (10.1.1),
p. 272, is a second-Strang-type bound for a form continuous on a larger space
and coercive on $V_h$.

Item 18.5 is EG I, Lemma 3.27, p. 34 (homogeneous Dirichlet), Lemma 3.24,
p. 34, with the convex constants (3.9), and Remark 3.28, p. 34; and BS,
(5.3.3)–(5.3.5), p. 135. BS assumes that $\Omega$ is a finite union of
domains star-shaped with respect to balls, (5.3.1), p. 134. The sharpness
example is a direct check.

Item 18.6 is EG I, Theorem 3.10, p. 31 (traces), and Theorem 2.31, p. 24
(embeddings, for open bounded Lipschitz sets with $d\ge2$); and BS, (1.6.6),
p. 39 (multiplicative trace bound), and (1.4.6), p. 34 (embedding into
continuous functions).

Item 18.7 is EG II, Theorem 31.30, pp. 110–111 (convex domains), and Theorem
31.31, p. 111 (polygons). EG quotes these from Grisvard without proof and
assumes no interior angle equal to $\pi$, Dirichlet data in
$H^{3/2}$ of each side with matching values at the vertices, and Neumann data
in $H^{1/2}$ of each side. The bound by the closed graph theorem and the
L-shaped example rest on no local source.

Item 18.8 is BS, (3.1.1), p. 69, (3.1.4), p. 70, (3.4.1), p. 82, and the
examples (3.4.4), p. 82; and EG I, Definition 5.2, Remark 5.3 and
Proposition 5.5, p. 51. BS requires a piecewise smooth boundary for $K$; EG
allows the closure of a Lipschitz domain.

Item 18.9 is EG I, Lemma 11.9, p. 127, and BS, (4.3.8), p. 102. BS's
$Q^mu$ has degree less than $m$. EG I, Remark 11.12, p. 129, notes that the
names Bramble–Hilbert and Deny–Lions are used inconsistently in the
literature.

Item 18.10 is EG I, Theorem 11.13, pp. 129–130 (local, with $C$ independent
of $v$, $K$ and $h$ for shape-regular affine meshes), and BS, (4.4.4), p. 105
(local, with explicit dependence on the chunkiness and on the interpolation
norm of the scaled element), and (4.4.20), p. 108 (global, with $C$ depending
on the reference element, $n$, $m$, $p$ and $\rho$). BS's condition for the
nodal variables of order $l$ is $m-l-n/p>0$ for $p>1$ and $m-l-n\ge0$ for
$p=1$, where $m$ is the Sobolev order; EG states it as the boundedness of
the degrees of freedom on $W^{l,p}(\hat K)$.

Item 18.11 is BS, (4.8.12), p. 123, with the operator defined in (4.8.6) and
the stability bound (4.8.15)–(4.8.16), p. 123; the averaging estimates are
EG I, Theorem 22.6, p. 278. BS states the range $0\le k\le m$; the statement
here keeps $k\ge1$, where the Scott–Zhang operator is defined for all
$p\in[1,\infty]$. The Clément operator is named only; no local locator was
checked for it.

Item 18.12 is EG I, Lemma 12.1, p. 137, and Lemma 12.8, p. 140 (discrete
trace inequality), and BS, (4.5.11), p. 112 (global, quasi-uniform). EG
reports the one-dimensional constant $\sqrt3$ for $\mathbb P_1$ on
$(-1,1)$, (12.7), p. 140, which agrees with the example.

Item 18.13 is EG II, Theorem 32.2, p. 117, and BS, (5.4.4), p. 136, which
gives $\|u-u_h\|_{H^1}\le Ch^{m-1}|u|_{H^m}$.

Item 18.14 is EG II, Lemma 32.11, p. 122, with the smoothing property
(32.18), p. 122, and Remark 32.13, p. 122 (no $L^2$ quasi-optimality in
general); and BS, (5.4.8), p. 137, under the $H^2$ regularity assumption
(5.4.7). EG states the smoothing constant as $c_{\mathrm{smo}}\alpha^{-1}$
and assumes a symmetric diffusion tensor in the duality argument.

Item 18.15 is EG II, Definition 33.8, p. 132, Lemma 33.9 and Definition 33.11,
p. 133, Remark 33.10, p. 133 (the M-matrix property), and Corollary 33.13,
p. 135 (the cotangent criterion and the case $d=2$). The continuous maximum
principle it imitates is EG II, Theorem 33.6, p. 131. EG II, Remark 33.14,
p. 135, citing Brandts et al., says the weakly acute condition cannot hold in
dimension $d\ge4$; this was not checked and is left out of the statement.
Only one local source was found for this item.

Item 18.16 is EG II, Theorem 36.11, p. 185, with the regularity assumption
(36.17), and Theorem 36.13, p. 186; and BS, (10.3.11), p. 283, and
(10.3.21), p. 285, on convex polygons, with constants depending only on
$\rho$ of (4.4.16). EG measures the error in a norm on
$H^{1+r}(\Omega)+V_h^{\mathrm{cr}}$ that contains the broken gradient. The
$L^2$ bound in the statement combines EG's (36.22) and (36.24).

Item 18.17 is EG II, the norm (38.7) and the discrete trace inequality
(38.10), pp. 201–203, Lemma 38.6, p. 203 (coercivity with the constant
shown), Theorem 38.10, p. 206, with the assumption (38.14), and Theorem 38.12,
p. 207; and BS, (10.5.19), p. 293 (coercivity with constant $\frac12$ for a
penalty above a threshold $\eta^*$), and (10.5.26), p. 295 (an
$O(h)|u|_{H^2}$ energy error with an explicit dependence on the penalty). The
augmented norm is read from the proof of Theorem 38.10.

Item 18.18 is EG II, Theorem 49.13, p. 358, with the a priori estimates
(49.38).

Item 18.19 is EG II, Proposition 50.1, p. 364, and Lemma 50.2, p. 365; and
BS, (12.3.7), p. 337, and (12.5.17), p. 345. In the extracted text of Lemma
50.2 the case distinction for $c_{2h}$ reads as if $c_{2h}=\|b\|/\alpha_h$
when $\ker B_h\subset\ker B$; this is taken to be a lost "not", since the
pressure term must vanish when the discrete kernel is conforming, as in BS,
(12.3.7). The set $Z_h$ equals EG's $\Pi_h(u)+\ker B_h$ for any Fortin
operator $\Pi_h$.

Item 18.20: the Raviart–Thomas element is EG I, Proposition 14.15, p. 166,
with $\nabla\cdot\mathrm{RT}_k\subset\mathbb P_k$ in Lemma 14.9, p. 164, and
the commuting property in Lemma 16.2, p. 189; the mixed Darcy problem is EG
II, Lemma 51.10, p. 387, and Theorem 51.16, pp. 388–389. Only one local
source was used.

Item 18.21 is EG II, Lemma 54.5, p. 425 (MINI), and Lemmas 54.8 and 54.9,
pp. 427–429 (Taylor–Hood), with the convergence rate in Remark 54.10, p. 429;
and BS, (12.6.7), p. 350, for the Taylor–Hood estimate on polygons. EG
proves the inf-sup conditions in $W^{1,p}$ for all $p\in(1,\infty)$.

Item 18.22 is EG I, Proposition 16.14 and Proposition 16.15, p. 196 (the
continuous and the local discrete complexes), Lemma 16.16, p. 197 (commuting
canonical interpolants, whose domains require extra smoothness), and Theorem
23.12, p. 296 (the commuting quasi-interpolation operators). EG works in
$\mathbb R^3$ with the two-dimensional variants in Remark 16.17, p. 197.
Isogeometric analysis (Beirão da Veiga–Buffa–Sangalli–Vázquez, Acta
Numerica Vol. 23) is not covered in this section.

### 19. Time-dependent, spectral and adaptive Galerkin methods, and eigenvalue approximation

The local copies used here are Thomée, *Galerkin Finite Element Methods for
Parabolic Problems*, 2nd ed. (2006); Ern–Guermond, *Finite Elements II* and
*III* (2021); Shen–Tang–Wang, *Spectral Methods* (2011); Canuto–Hussaini–
Quarteroni–Zang, *Spectral Methods: Fundamentals in Single Domains* (2006);
Boffi, "Finite element approximation of eigenvalue problems", Acta Numerica
19 (2010), pp. 1–120; Brenner–Scott, 3rd ed. (2008); and Bartels, *Numerical
Methods for Nonlinear Partial Differential Equations* (2015). The printed
page offset of the Thomée copy changes between chapters, so its page numbers
were read from the page images.

Item 19.1 is Ern–Guermond III: the Gelfand triple and the space $X$ are
(64.5)–(64.6), p. 121; the embedding, trace surjectivity and integration by
parts are Lemma 64.40, p. 121; the hypotheses (65.5a)–(65.5c) are on p. 124,
the problem (65.7) and its weak form (65.10) on pp. 125–126 (Lemma 65.4
shows the equivalence); Lions' theorem is Theorem 65.9, p. 129, and the a
priori estimate is (65.16) of Lemma 65.10, p. 129. The heat-equation example
is §65.1.4, pp. 127–128. Ern–Guermond prove existence constructively and
again in Chapter 71 via an inf–sup condition; the original source is Lions
(1961), not checked.

Items 19.2–19.4 follow Thomée, Chapters 1 and 3, where $\Omega$ has smooth
boundary so that the elliptic regularity estimate (1.7) holds. The
approximation hypothesis is (1.10), p. 4. In item 19.2, the Ritz projection
is (1.22) and its stability (1.24), and the error bound is Lemma 1.1, all
p. 8; the semidiscrete estimate is Theorem 1.2, p. 8, with the remark on the
choice of $v_h$ on the same page. The constant in Theorem 1.2 does not grow
with $t$: the proof (pp. 8–9) bounds $\theta=u_h-R_hu$ by
$\|\theta(0)\|+\int_0^t\|\rho_t\|$. A variant for a general coercive
time-independent form, with an exponentially decaying effect of the initial
error, is Ern–Guermond III, Theorem 66.9, p. 141, and Corollary 66.13,
p. 142. In item 19.3, the backward Euler scheme is (1.47), p. 14, and its
estimate is Theorem 1.5, p. 15; the Crank–Nicolson scheme is (1.54) and its
estimate Theorem 1.6, both p. 16. Ern–Guermond III, Theorem 67.9, p. 153,
gives an implicit Euler estimate in the same spirit, and Bartels, Theorem
3.10, p. 72, gives $\max_k\|u(t_k)-u_h^k\|^2\le c(\tau^2+h^4)$ for
piecewise linear elements. Item 19.4 is Thomée, Theorem 3.2, p. 43, with the
remark on replacing $t$ by $t+h^2$ on p. 44; the smooth-data counterpart for
$v\in\dot H^r$ is Theorem 3.1, p. 41.

Item 19.5 is Thomée, Chapter 12: the abstract setting and the scheme (12.3)–
(12.4) are on pp. 203–204, unique solvability and the reduction for $q=1$
to (12.6) on p. 205, the $(2,1)$ Padé reduction for $q=2$ on p. 206, the
first error estimate is Theorem 12.1, p. 207, and the superconvergence
estimate is Theorem 12.3, p. 211, with the remark that $u^{(q)}(t)$ must lie
in $\dot H^{2q-1}$, a strong compatibility condition at the boundary. In
Thomée $|w|_s=\|A^{s/2}w\|$.

Item 19.6 is Shen–Tang–Wang, §2.2: the Bernstein inequality (2.44) of Lemma
2.5, p. 33, with the one-line proof by orthogonality on p. 34 (which gives
the constant $1$ for $p=2$); the projection estimate Theorem 2.1, p. 34; the
maximum-norm estimate Theorem 2.2, p. 35; and the interpolation estimate
Theorem 2.3, p. 36, where the interpolant (2.50)–(2.51) has
$\tilde u_N=\tilde u_{-N}$, which is the description used here. The proof
of Theorem 2.2 bounds $\sum_{|j|>N}|j|^{-2m}$ by $N^{1-2m}/(2m-1)$,
forgetting that the sum runs over both signs of $j$; the correct bound is
$2N^{1-2m}/(2m-1)$, which gives the constant $\sqrt{2/(2m-1)}$ stated here
(for $m=1$, $N=1$ the sum is $\pi^2/3-2\approx1.29>1$). Canuto et al. state
the same results for the space $S_N$ spanned by $e^{ijx}$, $-N\le j<N$: the
Bernstein inequality with constant $1$ in every $L^p$, (5.1.5), p. 268, the
truncation estimates (5.1.9)–(5.1.10), p. 270, and the interpolation
estimate (5.1.19), p. 272.

Item 19.7: the Legendre bound with constant $\tfrac12(N+1)(N+2)$ is
Shen–Tang–Wang, Theorem 3.33, p. 115, its sharpness Remark 3.6, p. 116; the
weight-shifted inequality is Theorem 3.31, p. 113 (it is an identity for
$\varphi=x$, $N=1$, $\alpha=\beta=0$). The $L^p$ bounds are Canuto et al.,
(5.4.5), p. 282, for the Legendre case and (5.5.4), p. 293, for the
Chebyshev weight.

Item 19.8: the Jacobi estimate is Shen–Tang–Wang, Theorem 3.35, p. 118, in
the fixed-$m$ form (3.264) of Remark 3.7, p. 119; the theorem gives the
explicit factor $\sqrt{(N-m+1)!/(N-l+1)!}\,(N+m)^{(l-m)/2}$, which is at most
$m^{(m-l)/2}N^{l-m}$ for $N\ge m-1$. The Legendre and Chebyshev $L^2$
estimates in standard weighted Sobolev norms are Canuto et al., (5.4.11),
p. 283, and (5.5.9), p. 293, where the right-hand side is a seminorm
$|u|_{H^{m;N}}$ that equals $\|u^{(m)}\|$ when $N\ge m-1$. The suboptimal
$H^l$ estimate is Canuto et al., (5.4.18), p. 285, and the counterexample
$u=L_{N+1}-L_{N-1}$ is Shen–Tang–Wang, p. 120. The $H^1_0$ projection
estimate is Canuto et al., (5.4.29)–(5.4.30), p. 288; Shen–Tang–Wang,
Theorem 3.38, p. 124, has a Jacobi-weighted version.

Item 19.9: the Legendre estimates are Canuto et al., (5.4.33)–(5.4.35),
p. 289, and the $H^1$ stability (5.4.37), p. 290; the weighted LGL estimate
is Shen–Tang–Wang, Theorem 3.44, p. 137. The Chebyshev $L^2_\omega$ estimate
is Canuto et al., (5.5.22), p. 296, and the Chebyshev–Gauss estimate in
weighted derivative norms is Shen–Tang–Wang, Theorem 3.40, p. 130, in the
fixed-$m$ form obtained as in item 19.8.

Item 19.10 is Shen–Tang–Wang, Theorem 4.1, pp. 165–166, for problem (4.10),
p. 143, with $b_\pm=0$, and the scheme (4.18), p. 145; the bound for the
factorial factor is Remark 4.14, p. 166. The proof combines the first Strang
lemma (their Theorem 1.3) with Theorems 3.38 and 3.44.

Item 19.11: the scheme is Shen–Tang–Wang (4.93)–(4.95), pp. 171–172, for
the problem (4.50)–(4.53), p. 158, specialized to Dirichlet conditions (the
boundary terms in (4.95) then vanish). The error estimate is Theorem 4.5,
p. 172; Shen–Tang–Wang state that $c$ depends only on the $L^\infty$ norms
of $a$, $b$, $a'$, $b'$, but the coercivity constant of (4.98) also enters
the proof. In the extracted text the hypothesis for (4.98) reads "$b\ge b_0>0$
if $b_\pm=0$"; since for Dirichlet conditions coercivity follows from the
Poincaré inequality, this is presumably "$b_\pm\ne0$". The collocation
equivalence for constant $a$ follows from (4.39)–(4.41), p. 153, and is
stated in Remarks 4.5 and 4.8, pp. 153 and 155. The multidimensional remark
is Canuto et al., §6.4.3: the G-NI scheme (6.4.42), p. 361, and the Strang
bound (6.4.46), p. 362, applied in Example 5, pp. 362–366. The final estimate
of that example has $N^{1-m}|u|_{H^{s;\bar N}}$, presumably a misprint for
$|u|_{H^{m;\bar N}}$; it is not used here.

Item 19.12: the Fourier statement is Canuto et al., (5.1.15), p. 271, for
their truncation $P_N$ onto $S_N$; the Chebyshev statement is (5.5.27),
p. 297, attributed there to Tadmor (1986). The interpolant is at any of the
three Chebyshev Gauss-type node families of §5.5.3, p. 296. Canuto et al.
also give $\|u'-D_Nu\|\le4(\sinh\eta)^{-1}Ne^{-\eta N}\max_{|\mathrm{Im}\,z|
\le\eta}|u(z)|$ for the Fourier interpolation derivative, (5.1.22), p. 273.

Items 19.13–19.16 are from Boffi's survey, which presents the
Babuška–Osborn theory (Babuška and Osborn 1991, not checked). Item 19.13 is
the setting of §7, p. 46, with (7.1); the Rayleigh quotients (7.3), p. 47;
the min–max principle Proposition 7.2 and its discrete form (7.6), p. 48;
and the upper bound $\lambda^{(k)}\le\lambda_h^{(k)}$, p. 49. Item 19.14:
the definition of convergence (7.7) and the gap are on p. 49; the
equivalence with norm convergence is Proposition 7.4, p. 50, where
sufficiency is credited to Kato and necessity to Boffi, Brezzi and Gastaldi
(2000a), Theorem 5.1; the sufficient condition is Proposition 7.6, p. 50;
the general statement on compact operators is Theorem 9.1, pp. 59–60, under
(9.1). Item 19.15: the abstract bounds are Theorems 9.12 and 9.13, p. 64,
stated under the assumptions of §9 (norm convergence (9.1)); the Laplacian
case uses the approximation hypothesis on p. 66 and is Theorems 10.3 and
10.4, p. 67 (eigenfunctions in $H^1$ and eigenvalues), and Theorem 10.5,
p. 68 (eigenfunctions in $L^2$). Boffi writes $\tau$ for $t=\min\{k,r-1\}$.
A direct proof for piecewise linear elements, with constants depending on
$k$, is Theorem 8.1, p. 58. Item 19.16 is §15, pp. 89–91, with the
computed eigenvalues in Table 15.1, p. 91; the same phenomenon appears for
Maxwell's eigenvalue problem in Table 5.3. The failure of convergence is
shown in the survey by computation, and its proof is in Boffi, Brezzi and
Gastaldi (2000a), which was not checked. The exact eigenvalues $j^2+l^2$
are those listed as "Exact" in Table 15.1.

Item 19.17 is Ern–Guermond II, Chapter 34: the residual is Definition 34.1,
p. 142, and its equivalence with the error is Lemma 34.3, pp. 142–143; the
vertex-based upper bound is Theorem 34.12, p. 146, and the cell-based form
used here Corollary 34.14, p. 147, with $C_{\rm GUB}$ uniformly bounded on
shape-regular families by Remark 34.15, p. 148; the oscillation is
Definition 34.17, p. 149, and the local lower bound Theorem 34.19, p. 151,
with the discussion of the polynomial degrees in Remark 34.20, pp. 151–152.
Ern–Guermond leave implicit that $\mathbf d$ is smooth enough on each cell
for $r_v$ to lie in $L^2$; the representation (34.10) needs it. A second
source is Brenner–Scott, §9.2–9.3: the face-based indicator (9.2.11), p. 246,
the upper bound Theorem 9.2.15, p. 247, and the local and global lower
bounds Theorems 9.3.6 and 9.3.7, p. 249, for piecewise polynomial
coefficient and data. Bartels, Theorem 3.6, p. 59, gives the reliability
estimate for piecewise linear elements with mixed boundary conditions.

Item 19.18 is Ern–Guermond II, Chapter 52: the Prager–Synge identity is
Exercise 52.6, p. 404 (it is a one-line consequence of
$(\nabla(u-u_h),\nabla u+\sigma^*)=0$, which holds since $u-u_h\in H^1_0$
and $\nabla\cdot(\nabla u+\sigma^*)=0$); the two-sided bound is Lemma
52.12, p. 402, and the bound under cellwise equilibration Lemma 52.13,
pp. 402–403, with the constant $h_K/\pi$ from the Poincaré inequality on
convex cells. The local construction is Theorem 52.6, p. 400, and the local
efficiency Lemma 52.9, p. 401, stated for piecewise constant $\mathbf d$.
Ern–Guermond credit the identity to Prager and Synge (1947).

Item 19.19: the contraction is Brenner–Scott, Theorem 9.5.18, p. 259, for
the algorithm on pp. 258–259, with the oscillation (9.5.2), p. 254; it is
due to Mekchay and Nochetto (2005). The theorem's text says "the numbers
$\theta$ and $\gamma$"; $\eta$ is meant. Brenner–Scott show by Example
9.5.13, p. 257, that the interior-node conditions in REFINE cannot be
dropped. The optimality statement is reported, without proof, in
Ern–Guermond II, §34.4, pp. 152–155: Dörfler marking (34.23), p. 153, the
contraction (34.25) of $\|\nabla(u-u_n)\|+\gamma\eta(u_n,\mathcal T_n)$ for
symmetric coercive problems, the approximation class (34.26)–(34.27),
p. 154, and the rate (34.28), p. 155, credited to Cascón, Kreuzer, Nochetto
and Siebert (2008), Binev, Dahmen and DeVore (2004) and Stevenson (2007),
none checked. In (34.28) the exponent is printed as $-1/s$; with the
definition (34.26) it must be $-s$, as stated here. The axioms of
adaptivity of Carstensen, Feischl, Page and Praetorius (2014) are cited by
Ern–Guermond but not used here.

Item 19.20: the abstract estimate is Bartels, Theorem 5.7, p. 138, in the
setting of §5.2.1, pp. 137–138 (Remark 5.4: the terms with $u_h-v$ vanish
when $K_h\subset K$); the finite element setting is §5.2.2, p. 139, and the
error estimate Theorem 5.8, p. 139. The general assumptions on $\Omega$ and
the triangulations are those of Bartels, Chapter 3. The
$\Gamma$-convergence statement is Bartels, Definition 4.1 and Theorem 4.1,
p. 87, and Proposition 4.1(ii), p. 88; Examples 4.1 and 4.2, p. 86, show
that density alone does not give convergence of discrete minima when $I$ is
not continuous on $X$ (Lavrentiev phenomenon) or not weakly lower
semicontinuous.

### 20. Multilevel and domain decomposition methods

Hackbusch is *Iterative Solution of Large Sparse Systems of Equations*, 2nd ed.
(2016). Brenner–Scott is the 3rd edition (2008). Toselli–Widlund is the 2005
monograph, and Xu–Zikatanov is "Algebraic multigrid methods", Acta Numerica
26 (2017), pp. 591–721.

Item 20.1 is Hackbusch, (11.22)–(11.23) and Lemma 11.11, p. 274, Lemma 11.23,
Remark 11.24 and Definition 11.25 (smoothing property), p. 294, the
approximation property (11.63), p. 298, and Theorem 11.35, p. 301. Hackbusch
allows the smoothing property to hold only for $\nu<\bar\nu(h_\ell)$ with
$\bar\nu(h)\to\infty$ (Theorem 11.36, p. 301); the item states the case
$\bar\nu=\infty$. Hackbusch also notes (§11.6.4, p. 301) that the spectral
radius depends only on the total number $\nu_1+\nu_2$ of smoothing steps.
Item 20.2 is Hackbusch, the recursion (11.42a,b) of Theorem 11.19, p. 286,
conditions (11.67a,b), pp. 301–302, Lemma 11.40, p. 302, and Theorem 11.42,
p. 303; Lemma 11.40 gives the explicit bound $\|M_\ell\|_2\le\gamma\zeta/
(\gamma-1)$ when the two-grid contraction number $\zeta$ is small enough
relative to $C^*=C_p\bar C_p(C_S+1)$. Item 20.3 is Hackbusch, the symmetry
conditions (11.75a,b), p. 304, assumptions (11.81)–(11.82), p. 308, Theorem
11.55 (two-grid), p. 309, and Theorem 11.59 (V-cycle), p. 310. Remark 11.57,
p. 309, derives the weighted approximation property from (11.63) when
$\|W_\ell\|_2\le C_W\|A_\ell\|_2$.

Item 20.4 is Brenner–Scott, Chapter 6: the model problem, pp. 155–156, the
$k$-th level iteration, p. 160, Theorem 6.5.8 (two-grid), p. 164, Theorem
6.5.9 (W-cycle), p. 165, Theorem 6.6.12 (V-cycle), p. 169, and Theorem 6.7.1
(full multigrid), p. 170, whose proof uses $2\gamma^r<1$. Brenner–Scott work
in the energy norm and treat only piecewise linear elements in two dimensions
with full elliptic regularity; Remark 6.1.8, p. 156, points to the literature
without that regularity.

Item 20.5 is Brenner–Scott, the framework (7.1.7)–(7.1.9), p. 176, Lemma
7.1.14, p. 177, and Theorem 7.1.20, p. 178, and Xu–Zikatanov, Theorem 4.4,
p. 613, which gives the minimization identity with its unique minimizer. The
identity for $(B^{-1}v,v)$ is often called the lemma of Lions or the
fictitious space lemma (Xu–Zikatanov, Theorem 6.3, p. 634, in a more general
form). Item 20.6 is Xu–Zikatanov, Theorem 4.5, p. 613, with the exact-solver
form (4.26), p. 614; for inexact subspace solvers the same theorem gives an
identity in terms of the symmetrized subspace smoothers, and that form is not
reproduced here. Item 20.7 is Xu–Zikatanov, Lemma 5.2, p. 619, Theorem 5.3,
p. 620, and Theorem 5.6, pp. 622–623; the equivalence of $\bar R$ being
positive definite with $\|I-RA\|_A<1$ is their Theorem 4.1, p. 610, via
$I-\bar RA=(I-RA)^*(I-RA)$. The survey also treats semidefinite $A$ with a
kernel contained in $V_c$; the item states the definite case. The ordering
$\mu_1\le\cdots\le\mu_n$ is implicit in their use of the min–max principle.

Item 20.8 is Toselli–Widlund, the setting of §2.2, pp. 35–37, Assumptions
2.2, 2.3 and 2.4, p. 40, Lemma 2.5, p. 41, Lemma 2.6, p. 42, Theorem 2.7,
p. 43, and Theorem 2.9, p. 44. Item 20.9 is Toselli–Widlund, §3.1–3.3,
pp. 55–59, Assumptions 3.1, 3.2 and 3.5, pp. 56–59, and Theorem 3.13, p. 69;
the remark on multiplicative and hybrid variants is on p. 55. Brenner–Scott,
Theorem 7.4.28, p. 191, prove the weaker bound $C(1+H/\delta)^2$ in two
dimensions for a quasi-uniform mesh. Item 20.10 is Brenner–Scott, §7.2–7.3,
with the setting (7.2.1)–(7.2.3), p. 179, Theorem 7.2.21 (hierarchical
basis), p. 183, the definition (7.3.1)–(7.3.2) and Theorem 7.3.10 (BPX),
pp. 183–185; convexity is assumed for simplicity, and Remark 7.3.9, p. 185,
states that the estimate also holds for nonconvex polygons.

Item 20.11 is Brenner–Scott, §7.5, pp. 191–192, Theorem 7.6.20 and Remark
7.6.21 (BPS), p. 201, Theorem 7.7.16 and Remark 7.7.17 (Neumann–Neumann),
p. 205, Theorem 7.8.19 and Remark 7.8.20 (BDDC and its duality with FETI-DP),
p. 210; and Toselli–Widlund, Assumption 6.1, p. 136, Theorem 6.4 (balancing
Neumann–Neumann as a hybrid Schwarz method), p. 143, the account of the
two-dimensional FETI-DP bound of Mandel and Tezaur, p. 166, Algorithm 6.24,
p. 170, and Theorem 6.35 (FETI-DP, Algorithm B), p. 180. Toselli–Widlund also
prove the same bound for one-level FETI methods with a Dirichlet
preconditioner (Theorems 6.15 and 6.21, pp. 154–159), which the item omits.
The spectral equivalence of BDDC and FETI-DP is stated in Brenner–Scott
without proof, with references to Mandel–Dohrmann–Tezaur and Li–Widlund. The
phrase "only one or a few points" paraphrases Toselli–Widlund's Assumption 6.1,
which is itself informal.

### 21. Integral equations and boundary element methods

Kress is *Linear Integral Equations*, 3rd ed. (Applied Mathematical Sciences
82, 2014). Atkinson is *The Numerical Solution of Integral Equations of the
Second Kind* (Cambridge, 1997). Han–Atkinson is *Theoretical Numerical
Analysis*, 3rd ed. (2009). Brunner is *Collocation Methods for Volterra
Integral and Related Functional Equations* (Cambridge, 2004). Sauter–Schwab is
*Boundary Element Methods* (Springer Series in Computational Mathematics 39,
2011). Atkinson and Han–Atkinson write the second-kind equation as
$(\lambda-K)x=y$, Kress as $\varphi-A\varphi=f$; the items use both forms.

Item 21.1 is Kress, Theorems 2.27 and 2.28, p. 28, Theorem 2.29 (weakly
singular kernels on $C(G)$), p. 29, Theorem 2.30, p. 31, Theorem 2.26 (no
bounded inverse), p. 28, the Riesz theorems 3.1–3.3, from p. 34, Theorem 3.4,
p. 38, and Theorem 3.9 (spectrum of a compact operator), p. 40. Item 21.2 is
Kress, Definitions 4.1 and 4.2, p. 45, Definition 4.5, p. 46, and Theorem 4.17,
p. 55; the Banach-space form for $(\lambda-K)u=f$ is Han–Atkinson, Theorem
2.8.10, p. 101, and Atkinson, Theorem 1.3.1, p. 13. Item 21.3 is Kress, Theorem
2.14, pp. 23–24, and Theorem 10.1 with its converse part, pp. 183–184, with
Han–Atkinson, Theorem 2.3.1 (geometric series theorem), p. 61.

Item 21.4 is Kress, Definition 13.5, p. 242, Theorem 13.6, p. 243, and Theorem
13.7(b), p. 244. The item adds density of the trial spaces so that the
best-approximation error in the Céa estimate tends to zero. Item 21.5 is Atkinson, Theorem 3.1.1,
p. 55, and Han–Atkinson, Theorem 12.1.2 (with the two-sided estimate
(12.1.24)), p. 479, and Lemma 12.1.4 (compact $K$ and pointwise convergent
projections give $\|K-P_nK\|\to0$), p. 481; Kress, Theorem 13.10, p. 246,
gives the corresponding statement for $\varphi-A\varphi=f$, and Theorem 13.14,
p. 251, the convergence of collocation with linear splines. Item 21.6 is
Atkinson, §3.4, (3.4.80)–(3.4.88), pp. 72–73, Lemma 3.4.1, p. 73, and
(3.4.93), p. 74, and Han–Atkinson, §12.3.1, (12.3.12)–(12.3.16), p. 497; Kress
leaves the result as Problem 13.3, p. 278. The superconvergence is due to
Sloan.

Item 21.7 is Kress, Definition 10.9, p. 190, and Theorem 10.12, p. 191, with
the convergence $\|(A_n-A)A_n\|\to0$ from §10.3; Han–Atkinson, Theorem 12.4.3,
p. 510, give the analogous perturbation result for $\lambda-T$ under a
smallness condition (12.4.22) on $\|(T-S)S\|$. The theory of collectively
compact operators is due to Anselone. Item 21.8 is Kress, Theorems 12.7 and
12.8, from p. 225, Atkinson, Theorems 4.1.1, p. 106, and 4.1.2, p. 107, and
Han–Atkinson, Theorem 12.4.4, p. 511, whose estimate $\|u-u_n\|_\infty\le
c\,\|(K-K_n)u\|_\infty$ is the one stated.

Item 21.9 is Brunner, the resolvent equation (2.1.9), p. 55, Definition 2.1.1
and Theorem 2.1.2, p. 56, and Theorem 6.1.2, p. 343, for the weakly singular
case; Kress, Theorem 3.10, p. 41, proves unique solvability for continuous
kernels by the Neumann series. Item 21.10 is Brunner, Definition 2.2.1, p. 84,
Theorem 2.2.1 (solvability), p. 87, Theorem 2.2.3 (global order $m$), p. 92,
and Theorem 2.2.6 with Corollaries 2.2.7 (Gauss points) and 2.2.8 (Radau II
points), p. 98. Brunner notes that for Gauss points the collocation solution
itself is only $O(h^m)$ at the mesh points, so that the order $2m$ belongs to
the iterated solution; the Radau II order $2m-1$ holds for $u_h$ itself
because $c_m=1$. Item 21.11 is Brunner, the graded mesh (6.2.31), p. 370, and
Theorem 6.2.9, p. 377.

Item 21.12 is Kress, Definition 6.14 and Theorem 6.15, p. 87, Theorem 6.18,
p. 89, Theorem 6.19, p. 90, and Theorem 6.20, p. 91; the fundamental solution
is Kress, Theorem 6.2, p. 76. Item 21.13 is Sauter–Schwab, the operator
(3.1), p. 101, the definitions (3.6) of $V$, $K_\pm$, $K'_\pm$, $W$, p. 103,
Theorem 3.1.16, p. 112, and Theorem 3.3.1 (jump relations), p. 115.
Sauter–Schwab, Remark 3.1.18, p. 113, note that $|s|<\frac12$ cannot in
general be enlarged on Lipschitz boundaries, that $s=\pm\frac12$ is allowed for
the Laplacian, and that all $s>-\frac12$ are allowed on $C^\infty$ boundaries.
Their $(3.6)$ includes the sign $W=-\gamma_1D$. Item 21.14 is Sauter–Schwab,
Theorem 3.5.3, p. 151, which states the ellipticity of $b_V(\varphi,\varphi)=
(\varphi,V\varphi)_{L^2(\Gamma)}$ and of $b_W$ on the quotient
$H^{1/2}(\Gamma)/\mathbb K$; the solvability and quasi-optimality are the
Lax–Milgram and Céa consequences. Item 21.15 is Sauter–Schwab, Theorem 4.2.9,
p. 229, the special case of Theorem 4.2.7, p. 227, which requires discrete
inf–sup conditions; Remark 4.2.8, p. 229, stresses that those conditions do
not follow from density in general, whereas under the ellipticity of $a$ in
Theorem 4.2.9 they do for $\ell\ge\ell_0$. Kress, Theorem 13.30, p. 269, gives a
related Galerkin result for compact perturbations of coercive operators.

Item 21.16 is Kress, Definition 15.1, p. 298, Theorem 15.4, p. 300, and
Theorem 2.26, p. 28. The remark that $V$ is an isomorphism from
$H^{-1/2}(\Gamma)$ onto $H^{1/2}(\Gamma)$ in the setting of 21.14 follows from
Theorem 3.1.16 and Theorem 3.5.3 of Sauter–Schwab by the Lax–Milgram lemma.

### 22. Inverse problems and regularization

Kress is cited from the third edition (2014, Applied Mathematical Sciences
82), Sullivan from the 2015 Texts in Applied Mathematics 63 volume, Law,
Stuart and Zygalakis from the 2015 Texts in Applied Mathematics 62 volume,
and Han–Atkinson from the third edition (2009). Stuart's survey is "Inverse
problems: a Bayesian perspective", Acta Numerica 19 (2010), pp. 451–559, and
Benning–Burger's is "Modern regularization methods for inverse problems",
Acta Numerica 27 (2018), pp. 1–111. Kress writes $A$ for the operator,
$\varphi$ for the unknown, $f$ for the data and $\mu_n$ for the singular
values; Benning–Burger and Stuart write $u$ for the unknown.

Item 22.1 is Kress, Definition 15.1, p. 298, and Theorem 15.4, p. 300, with
Hadamard's examples on pp. 298–300; the version for a bounded injective
linear operator is Han–Atkinson, §2.4.2, p. 75. Item 22.2 is Kress,
Definition 15.15 and Theorem 15.16, p. 309, with (15.21)–(15.23) on
p. 310; the relations between ranges and null spaces are Kress, Theorem
15.8, p. 303, and $\sigma_n\to0$ follows from the spectral theorem for the
compact operator $K^*K$, Kress, Theorem 15.12, p. 305. Item 22.3 is Kress,
Theorem 15.18, p. 311; the remark that the Picard solution lies in
$N(K)^\perp$ is immediate from the formula.

For item 22.4, the definitions of best approximate and minimal norm
solutions are Benning–Burger, Definition 4.1, p. 21, which call the
regularized limits "generalized inverse" solutions without stating its
properties. The domain, the normal-equation characterization, and the
theorem that $K^\dagger$ is bounded if and only if $R(K)$ is closed are the
standard theory of Engl, Hanke and Neubauer, *Regularization of Inverse
Problems*, Chapter 2; no local source states them, and the item rests on
that standard theory. The series form for compact $K$ combines this with
Kress, Theorem 15.18. Bakushinskii's theorem, that a parameter choice
depending on $y^\delta$ alone cannot give a convergent method for an
ill-posed problem, is not stated in any local source and is not included.

Item 22.5 is Kress, Definitions 15.5 and 15.7, pp. 301–302, Theorem 15.6,
p. 301, and the error splitting (15.7), p. 302. Benning–Burger, Definitions
4.2 and 4.3, p. 21, give the equivalent notions of a linear regularization
method, its convergence to the minimum norm solution $u^\dagger$ without
assuming injectivity, and convergence rates. The spectral filters are Kress,
Theorem 15.21, p. 313, and the spectral cut-off is Theorem 15.24, p. 316.
Kress also proves, in Theorems 15.25 and 15.26, p. 317, that the
discrepancy principle is a regular stopping rule for the cut-off.

Item 22.6 is Kress, Theorem 16.4, p. 325 (minimizer and normal equation),
Theorem 16.5, p. 325 (regularization scheme and $\|R_\alpha\|\le\|K\|/\alpha$),
and Theorem 15.23, p. 315 (the compact case, with
$\|R_\alpha\|\le1/(2\sqrt\alpha)$ and the filter
$q(\alpha,\sigma)=\sigma^2/(\alpha+\sigma^2)$). Sullivan, Theorem 4.28, p. 72,
states the normal equation for the weighted functional
$\frac12\|Ax-b\|_Q^2+\frac12\|x-x_0\|_R^2$; it assumes $A$ has closed range,
which the regularized problem does not need. The a priori convergence
statement is not a numbered theorem in Kress; it follows at once from the
splitting (15.7) and the bound in Theorem 15.23, since
$\delta\|R_\alpha\|\le\delta/(2\sqrt\alpha)\to0$.

In item 22.7 the characterization at $\nu=1$ is Kress, Theorem 16.6, p. 326,
stated there as $f\in AA^*A(X)$; the case $\nu=\frac12$ with rate
$O(\sqrt\alpha)$ is the remark after Theorem 16.10, p. 329, and Benning–Burger,
p. 21, name the general source condition $u^\dagger=(K^*K)^\mu w$. The bound
$\alpha^\nu\|w\|$ for $0<\nu\le1$, the noisy-data bound with its parameter
choice and constant $\frac32$, and the saturation statement are derived here
from Kress's series (16.6), p. 326, using
$\sup_{t>0}\alpha t^\nu/(\alpha+t)=\nu^\nu(1-\nu)^{1-\nu}\alpha^\nu\le\alpha^\nu$
and monotone convergence; they are the standard results of Engl, Hanke and
Neubauer, Chapters 4 and 5, which have no local copy.

Item 22.8 is Kress, Definition 16.17, p. 334, Theorem 16.18, p. 335, the
estimate (16.20), p. 336, Theorem 16.19, p. 336, and Theorem 16.20, p. 337;
Kress states the rate as $O(\delta^{1/2})$ under $f\in AA^*(Y)$, and the
constant $2\sqrt{\|z\|\delta}$ is read off the last line of the proof.
Benning–Burger, Definition 6.1, p. 40, give the discrepancy principle with a
factor $\eta\ge1$ in the general setting of iterative methods.

Item 22.9 is Kress, Theorem 15.27, p. 319, with the iteration (15.45),
p. 319, and Theorems 15.28 and 15.29, p. 320; Kress calls it the
Landweber–Fridman iteration. The a priori rule $\delta^2m(\delta)\to0$ is
derived from the bound $\|R_m\|\le\sqrt{a(m+1)}$ and (15.7).
Benning–Burger, p. 39, write the iteration with a step size $\tau$ as
$u_k=u_{k-1}-\tau K^*(Ku_{k-1}-f^\delta)$; Kress starts from
$x_0=aK^*y$, which is the first step of this iteration from $u_{-1}=0$.

Item 22.10 is Benning–Burger, Definition 3.3, p. 18 (Bregman distance),
Definition 5.2, p. 28 (variational regularization), Definition 5.9, p. 33
(source condition), Lemma 5.13, p. 34, and Example 5.16, p. 36, where the
estimate is derived. Benning–Burger measure noise by the fidelity,
$\frac12\|f-f^\delta\|^2\le\delta$, so their $\delta/\alpha$ is
$\delta^2/(2\alpha)$ here; their choice $\alpha=\sqrt{2\delta}/\|v\|$ with
rate $O(\sqrt\delta)$ is the choice $\alpha=\delta/\|v\|$ with rate $O(\delta)$
here. In the first display of
their derivation the step $\frac12\|Ku^\dagger-f^\delta\|^2\le\frac12\|f-
f^\delta\|^2$ is an equality, since $Ku^\dagger=f$. Existence of $u_\alpha$ is
their Theorem 5.6, p. 30, under Assumption 5.4, p. 29, which is not repeated
here; the statement assumes a minimizer. The subgradient $p_\alpha$ comes from
their optimality condition (5.4), p. 28, for which the sum rule holds because
the quadratic fidelity is continuous on $U$.

Item 22.11 is Stuart, Lemma 6.10 and Theorems 6.9 and 6.11, p. 530.
Stuart defines the Cameron–Martin space as the intersection of linear
spaces of full measure and identifies it with $\mathrm{Im}(C^{1/2})$ on a
Hilbert space. The source locators for the Gaussian shift and equivalence
theorems are given under item 24.13.

Item 22.12 is Stuart, Theorem 6.31, p. 544, and Sullivan, Theorem 6.6,
p. 100, with Lemma 6.7, p. 100. Stuart requires $\mu_0(X)=1$ for a measure on
a separable Banach space, and both assume that the noise density has support
$\mathbb R^q$; the proofs use that $\rho$ is positive everywhere. The
Gaussian potential is Stuart (2.26), p. 471.

Item 22.13 is Stuart, Assumption 2.6, p. 471, Theorem 4.1 and Theorem 4.2,
p. 501, Corollary 4.4, p. 503, with Assumption 2.7 and Lemma 2.8,
pp. 471–472, for the finite-data case; and Sullivan, assumptions (A1)–(A4)
and Theorem 6.8, p. 102, and Theorem 6.9, p. 103. The Hellinger distance with
the factor $\frac12$ is Stuart, Definition 6.35, p. 546, and the bound on
expectations is Stuart, Lemma 6.37, p. 546. Sullivan defines the Hellinger
distance without the factor $\frac12$ (p. 85 and p. 103), so the constants
differ by $\sqrt2$; Sullivan's Proposition 5.12, p. 85, has the constant $2$
for that larger distance. Sullivan's Theorem 6.9 asserts one constant $C$ for
all $y,y'$, while the proof, like Stuart's Theorem 4.2, gives a constant
$C(r)$ for $\|y\|,\|y'\|<r$; the item states the local form. Stuart's
Assumption 2.6(iv) allows $C(\varepsilon,r)\in\mathbb R$, Sullivan's (A4)
requires $C>0$; this makes no difference.

Item 22.14 is Stuart, (5.1)–(5.3), p. 510, the discussion of variational
methods, p. 513, and Theorem 5.4, p. 514. Stuart motivates the minimizers of
$I$ as maximizers of small-ball probabilities in infinite dimensions but does
not prove that characterization; the item claims the mode property only in
finite dimensions.

Item 22.15 is Law–Stuart–Zygalakis, Theorem 4.1, p. 80, Corollary 4.2,
p. 81, and the variational characterization (4.10), p. 83. They assume in
the setup on p. 80 that the observation dimension is at most $n$ and that
$H$ has full row rank; the proof uses only that $\Sigma$, $\Gamma$ and $C_0$
are positive definite, and the item omits the rank assumption. Their gain is
written $K_{j+1}$; it is $L_{j+1}$ here to avoid a clash with the forward
operator. Sullivan, §7.2, pp. 117–119, describes the same filter as the
push-forward and conditioning of Gaussian measures, without a numbered
theorem.

Item 22.16 is Law–Stuart–Zygalakis, the 3DVAR filter (4.14), p. 84, and
Theorem 4.10, p. 99, with Examples 4.12 and 4.13, p. 100, showing how
the contraction hypothesis can be met. They take the data as
$y_{j+1}=Hv_{j+1}^\dagger+\epsilon_j$ and leave the constant $c$ implicit; the
proof bounds $\|K\epsilon_j\|\le c\epsilon$, which gives the value of $c$
stated here. No local source gives a comparable accuracy theorem for the
ensemble Kalman filter, so it is not included.

### 23. Monte Carlo, quasi-Monte Carlo, and stochastic differential equations

Asmussen–Glynn is the 2007 Springer volume (Stochastic Modelling and
Applied Probability 57) and is cited by chapter, section and printed page.
Kloeden–Platen is the 1992 Springer volume (Applications of Mathematics 23)
in its corrected third printing of 1999. Lord–Powell–Shardlow is the 2014
Cambridge Texts in Applied Mathematics 50. Del Moral is the 2004 Springer
volume in Probability and its Applications. The Acta Numerica surveys are
Caflisch, Acta Numerica 7 (1998), pp. 1–49; Dick–Kuo–Sloan, Acta Numerica
22 (2013), pp. 133–288; Giles, Acta Numerica 24 (2015), pp. 259–328 (the
separate file); and Lelièvre–Stoltz, Acta Numerica 25 (2016), pp. 681–880.

Item 23.1 is Asmussen–Glynn, Section III.1, formulas (1.1)–(1.4), pp.
68–70, and Caflisch, formulas (2.4)–(2.6) and Theorem 2.1, pp. 4–5; the
exact root-mean-square error for integration over the cube is
Dick–Kuo–Sloan, Theorem 2.1, p. 138. Asmussen–Glynn writes the confidence
interval as an open interval and does not state the hypothesis $\sigma>0$;
it is needed, since for $\sigma=0$ the coverage probability is $0$ or $1$.
The almost sure convergence is the strong law of large numbers, quoted by
Caflisch.

Item 23.2 is Asmussen–Glynn, Section V.2, formulas (2.1)–(2.2), pp.
138–139; the asymptotic normality of the estimator with estimated
coefficient is asserted there without a numbered theorem and follows from
the central limit theorem and Slutsky's lemma. Caflisch, Section 4.2, pp.
14–15, gives the optimal multiplier in integral form, formula (4.14), for a
control function $g$; that formula, $\lambda=\mathbb E[fg]/\mathbb E[g^2]$, is
the optimal coefficient when $g$ has mean zero.

Item 23.3 is Asmussen–Glynn, Section V.1a, formula (1.1), Example 1.1 and
Theorem 1.2, pp. 127–128. The source does not state $\mathbb E|Z|>0$; it is
needed for $P^*$ to be defined. Caflisch, Section 4.5, p. 19, treats the
same method for densities.

Item 23.4 is Asmussen–Glynn, Section XIII.3: the chain is (3.1)–(3.3) and
Theorem 3.1, pp. 361–362, whose proof is the detailed balance relation
(3.4); the ergodic statement is Corollary 3.3, p. 362, and the remark on
irreducibility is Remark 3.4, pp. 362–363. Corollary 3.3 says only that
the averages converge; the almost sure form for $\pi^*$-integrable $f$ is the
ergodic theorem for irreducible chains with a stationary distribution
(such chains are positive recurrent), which the corollary invokes. The
source allows an unnormalized $\pi\ge0$; the statement takes $\pi>0$ so
that the ratio in $\alpha$ is always defined. For a general state space,
Theorem 3.5, p. 363 (due to Tierney), gives Harris recurrence and the same
convergence under $\pi^*$-irreducibility.

Item 23.5 is Dick–Kuo–Sloan, Section 3.5, pp. 174–176: the local
discrepancy, the Hlawka–Zaremba identity, Theorem 3.9 (in the case
$p=p'=\infty$, $q=q'=1$, with the seminorm in place of the norm as remarked
after the theorem) and the classical form (3.15)–(3.16), p. 176. The
classical inequality with the Hardy–Krause variation is also Caflisch,
Theorem 5.1, p. 26, with the star discrepancy (5.3), p. 25.

Item 23.6 is Dick–Kuo–Sloan, Examples 2.3–2.5, pp. 141–142 (radical
inverse, Halton and Hammersley bounds, with $C_s$ depending only on $s$),
and Definitions 2.11 and 2.12, pp. 145–146 ($(t,m,s)$-nets and
$(t,s)$-sequences). Caflisch, formula (5.23), p. 30, gives the Halton
discrepancy bound $c_d(\log N)^dN^{-1}$ and states that Faure, Sobol' and
Niederreiter sequences satisfy bounds of the same form, with the error
bound (5.25). The discrepancy bound for general $(t,s)$-sequences with a
constant depending only on $t,s,b$ is Niederreiter's theorem; the local
sources state it only in this qualitative form.

Item 23.7 is Dick–Kuo–Sloan: the unanchored weighted space, Section 4.3,
pp. 182–183; the shift-averaged worst-case error and the mean-square bound,
Section 5.2, formula (5.8), p. 195; the formula for the shift-averaged
error, Lemma 5.5, formula (5.12) with $\beta=0$, p. 198; the CBC
construction, Algorithm 5.6, p. 199; and the bound, Theorem 5.8, formula
(5.18), p. 202. The product-weight consequence follows from
$\sum_{\emptyset\ne u}\gamma_u^\lambda c^{|u|}=\prod_{j=1}^s(1+c\gamma_j^\lambda)-1
\le\exp(c\sum_j\gamma_j^\lambda)$ and $\varphi(n)=n-1$ for prime $n$; this
step is elementary and not displayed as such in the source. The anchored
analogue is Theorem 5.9, p. 204.

Item 23.8 is Giles, Theorem 2.1, pp. 264–265, with the estimator (2.2)–(2.3),
p. 264. The SDE example follows Giles, Section 5.1, p. 287, and
Lord–Powell–Shardlow, Lemma 8.46, p. 355. On p. 287 Giles reports
$\alpha=1$, $\beta=2$, $\gamma=1$ for step $2^{-\ell}h_0$ and
$\alpha=2$, $\beta=4$, $\gamma=2$ for step $4^{-\ell}h_0$, and concludes
complexity $O(\varepsilon^{-2}(\log\varepsilon)^2)$. With the normalization of
Theorem 2.1 ($V_\ell\le c_22^{-\beta\ell}$) and $V_\ell=O(h_\ell)$, the
values are $\beta=\gamma=1$, respectively $\beta=\gamma=2$; that is the case
$\beta=\gamma$ which yields the stated complexity, so the printed values of
$\beta$ appear to be a misprint. The statement uses $\alpha=\frac12$, which
follows from the mean-square strong error alone.

Item 23.9 is Kloeden–Platen, Theorem 4.5.3, p. 131, under assumptions
A1–A4, pp. 128–129, stated there for $d=m=1$ and extended verbatim to the
vector case in Section 4.8, p. 149; and Lord–Powell–Shardlow, Theorem 8.18
under Assumption 8.17, p. 325, for autonomous coefficients with
deterministic initial value, where the solution is unique in the space
$\mathcal H_{2,T}$ of adapted processes with $\sup_t\mathbb E|u(t)|^2<\infty$.

Item 23.10 is Kloeden–Platen: multi-indices, Section 5.2, (2.1)–(2.6),
pp. 167–168; multiple Itô integrals (2.12), p. 169; the operators and
coefficient functions (3.1)–(3.3), p. 177; hierarchical and remainder sets
(4.1)–(4.4), pp. 180–181; and Theorem 5.5.1, pp. 181–182. The formula for
$I_{(j,j)}$ is (3.6), p. 347. The theorem is stated with the proviso that
all derivatives and integrals exist; no further hypotheses are given there.

Item 23.11, strong part, is Kloeden–Platen, Theorem 10.2.2, (2.8)–(2.13),
pp. 342–343, for the scheme (2.5), p. 341. The source states the error in
the absolute (first-moment) form at $T$; the mean-square form
$\sup_n(\mathbb E|X_{\tau_n}-Y_n|^2)^{1/2}=O(\delta^{1/2})$ is
Lord–Powell–Shardlow, (8.54), p. 338, left there as Exercise 8.11. The weak part is
Kloeden–Platen, Theorem 14.5.1 with $\beta=1$, pp. 472–473, where the weak
Taylor scheme (5.4) with $\Gamma_1=\{v,(0),(1),\dots,(m)\}$ is the
Euler–Maruyama scheme; the linear growth condition (5.5) on $f_\alpha$,
$\alpha\in\Gamma_1$, follows from the Lipschitz condition. A second source is
Lord–Powell–Shardlow, Theorem 8.45, p. 351, under Assumption 8.38, p. 349
($f,G\in C^\infty$ with bounded derivatives of order $\ge1$, test functions in
$C^\infty_{\mathrm{poly}}$, Definition 8.40), for uniform steps. The two
sources differ in smoothness: Kloeden–Platen needs four derivatives of
polynomial growth, Lord–Powell–Shardlow infinitely many bounded ones.

Item 23.12 is Lord–Powell–Shardlow, Theorem 8.32, p. 341, under Assumption
8.29, p. 338, and condition (8.59), with the scheme of Definition 8.24,
p. 333, specialized to $m=1$. The remarks on general $m$ are Kloeden–Platen,
Section 10.3, schemes (3.2)–(3.4), pp. 346–347, Example 10.3.4 (the
Clark–Cameron example), pp. 349–350, and Theorem 10.3.5, pp. 350–351,
whose hypotheses (3.19)–(3.23) are stated in terms of
$\underline a=a-\frac12\sum_jL^jb^j$ and the operators of 23.10; the
coincidence for additive noise is Lord–Powell–Shardlow, p. 333.

Item 23.13 is Lord–Powell–Shardlow, Example 8.26, condition (8.52) and
Definition 8.27, pp. 335–337, with the $\theta$-method condition stated on
p. 337 and left as Exercise 8.13. The formula for $R$ and the equivalence
were checked directly: $R<1$ if and only if
$\Delta t\,(2r+\sigma^2+(1-2\theta)r^2\Delta t)<0$.

Item 23.14 is Lelièvre–Stoltz, Definition 3.1, Assumption 3.2 and Theorem
3.3, pp. 759–760, with the one-step operator (3.9), p. 751, and the
application to overdamped Langevin dynamics, Section 3.3.2, (3.26)–(3.28),
pp. 763–765, including the formula for $f_2$, p. 764; existence of
$\pi_{\Delta t}$ is deduced there from Theorem 2.25 via a minorization
condition, p. 765. The weighted norm is that of Section 2.4. Leimkuhler–
Matthews treats the same expansions for Langevin and overdamped Langevin
splittings by formal series in its Chapter 7; no numbered theorem there was
used.

Item 23.15 is Del Moral, Theorem 7.4.4, estimate (7.26), p. 246, under
conditions (G) and $(\mathrm M)_m$, pp. 115–116, for the $N$-particle model
(7.4), p. 219, with the McKean transition $K_{n,\eta}(x,\cdot)=\Phi_n(\eta)$
(Case 1 there); the theorem holds for any McKean interpretation. The
moment of general integer order $p$ carries the factor $d(p)^{1/p}$ with
$d(2)=1$, which gives the constant stated for $p=2$.

Item 23.16 is Lord–Powell–Shardlow, Corollary 10.38, estimate (10.58),
p. 467, a consequence of Theorem 10.34, p. 461, with the scheme (10.57),
p. 467, the equation (10.25), p. 447, Assumption 3.19, p. 101, the
condition (3.41) on $f$, Assumption 10.5, p. 436, the cylindrical Wiener
process, Definition 10.14, p. 444, Assumption 10.23, p. 449, and existence
and uniqueness of the mild solution, Theorem 10.26 and Definition 10.22,
pp. 449–450. Theorem 10.34 also covers finite element Galerkin spaces with
mesh parameter $\delta=h$ and multiplicative noise; for space-time white
noise the source records the rate $O(\Delta t^{1/4-\epsilon})$ on p. 464.
The condition $\zeta<\frac12$ for the Dirichlet Laplacian on an interval
was checked directly from $\sum_j\lambda_j^{\zeta-1}<\infty$. The text of
Assumption 3.19 names the operator $-A$ where the eigenvalue condition
$\lambda_j>0$ refers to $A$, as the subsequent use of $e^{-tA}$ shows.

### 24. High-dimensional approximation, uncertainty quantification, and model reduction

The Acta Numerica surveys are cited by their own printed pages: Bungartz and
Griebel, "Sparse grids", Acta Numerica 13 (2004), 147–269; Dick, Kuo and
Sloan, "High-dimensional integration: the quasi-Monte Carlo way", Acta
Numerica 22 (2013), 133–288; Cohen and DeVore, "Approximation of
high-dimensional parametric PDEs", Acta Numerica 24 (2015), 1–159; DeVore,
Hanin and Petrova, "Neural network approximation", Acta Numerica 30 (2021),
327–444; and Stuart, "Inverse problems: a Bayesian perspective", Acta
Numerica 19 (2010), 451–559. Novak–Woźniakowski is *Tractability of
Multivariate Problems, Volume I: Linear Information* (EMS Tracts in
Mathematics 6, 2008). Quarteroni–Manzoni–Negri is *Reduced Basis Methods for
Partial Differential Equations* (Unitext 92, 2016). Benner–Gugercin–Willcox
is the survey in SIAM Review 57 (2015), 483–531. Sullivan is *Introduction
to Uncertainty Quantification* (Texts in Applied Mathematics 63, 2015), and
Lord–Powell–Shardlow is *An Introduction to Computational Stochastic PDEs*
(Cambridge Texts in Applied Mathematics 50, 2014).

Item 24.1 is Bungartz–Griebel, Section 3.1: the spaces $X^{q,r}_0$ and
seminorms are (3.2)–(3.3), p. 155; the hat functions, the increments $W_l$,
the index sets $I_l$ and the hierarchical basis are (3.7)–(3.16),
pp. 156–157; the unique splitting (3.19) and $|W_l|=2^{|l-1|_1}$ (3.20) are
on p. 158; the surplus bound is Lemma 3.3, (3.26), p. 160, and the
component bounds are Lemma 3.4, (3.27), p. 161. The source states the
splitting for $V=\bigoplus_lW_l$, whose $H^1$ closure is $H^1_0$, which is
the sense of convergence given in the item. The seminorm $|u|_{2,q}$ is the
$L^q$ norm of the mixed derivative $\partial^{2d}u/\partial x_1^2\cdots
\partial x_d^2$ (bold multi-index $\mathbf 2$ in the source). Item 24.2 is
Bungartz–Griebel, (3.61), p. 172, Lemma 3.6, p. 173, $A(d,n)$ in (3.65),
p. 174, and Theorem 3.8, p. 176, with the full-grid count (3.31), p. 163,
and the full-grid error bounds of Lemma 3.5, p. 164; the constants were
checked against the page image. The second energy-norm bound of Theorem
3.8, in terms of $|u|_{2,2}$, is omitted.

Item 24.3 is Novak–Woźniakowski, Section 4.1, (4.3)–(4.5), pp. 89–90 (the
book also allows adaptive information), the information complexity
(4.49)–(4.50), p. 148, Definition 4.44 of polynomial and strong polynomial
tractability, p. 149, weak tractability (4.55), p. 151, and Corollary 4.12,
p. 119, for the optimal algorithm of a compact operator between Hilbert
spaces; the same definitions for integration are Dick–Kuo–Sloan,
Definition 4.4, p. 186. Definition 4.44 quantifies over
$\varepsilon\in(0,1)$, Theorem 5.1 over $\varepsilon\in(0,1]$; Dick–Kuo–Sloan
write "some $p,q>0$ and $q\ge0$", an evident misprint for $p>0$, $q\ge0$.
Item 24.4 is Novak–Woźniakowski, Theorem 5.1, p. 157 (first bullet, with
the bound and the strong tractability criterion; the converse constants are
omitted), and Theorem 5.5, pp. 176–177, for linear tensor product problems
with $\lambda_2>0$ under the absolute error criterion, of which only the case
$\lambda_1=\lambda_2=1$ and the last bullet are stated. Item 24.5 is
Dick–Kuo–Sloan, Theorem 4.5 (strong polynomial tractability) and Theorem
4.6 (polynomial tractability), p. 187, for the anchored space of Section
4.2, pp. 179–180 (kernel (4.1)–(4.3)), and the unanchored space of Section
4.3; the algorithms allowed are arbitrary, possibly nonlinear, uses of $n$
function values. The source attributes these results to Sloan and
Woźniakowski and to Hickernell and Woźniakowski; the corresponding
weighted results for $\Lambda^{\mathrm{all}}$ and normalized errors are
Novak–Woźniakowski, Theorem 5.7, pp. 202–204, not stated here. The
construction of lattice rules achieving these bounds is in section 23.

Item 24.6 is Cohen–DeVore, the Kolmogorov width (1.41), p. 11, the weak
greedy algorithm (8.7)–(8.10), p. 134, and Corollary 8.4, p. 139, derived
from Theorem 8.3, p. 138 (from DeVore, Petrova and Wojtaszczyk). In (8.26)
the minimum over $1\le m<n$ is empty for $n=1$, so the first bound is
stated for $n\ge2$. The weaker comparison
$\sigma_N\le C(N+1)2^{N+1}d_N$ and its exponential corollary are
Quarteroni–Manzoni–Negri, Theorem 7.1 and Corollary 7.1, pp. 150–151.
Item 24.7 is Cohen–DeVore: the model problem (1.5)–(1.9), p. 3, the complex
extension with the bound $\|f\|_W/r$, (2.17)–(2.21), pp. 22–23, the
uniform ellipticity assumption UEA$(r)$, (2.84)–(2.85), p. 33, the polydisc
extension (2.89)–(2.93), p. 34, the Taylor coefficients (3.20)–(3.21),
p. 44, Theorem 3.9(i) and Corollary 3.10, p. 47, which apply under the
hypotheses of Theorem 2.8, p. 36, verified for the model problem by the
preceding items with the open set $\{\mathrm{ess\,inf}\,\mathrm{Re}\,a>r/2\}$.
The source states analogous Legendre results (Corollary 3.11, p. 48) with
rate $(n+1)^{-(1/p-1/2)}$ in $L^2(U,V,\mu)$ for the uniform measure.

Item 24.8 is Quarteroni–Manzoni–Negri, Proposition 6.2, p. 127, with the
Schmidt–Eckart–Young theorem, Theorem 6.1, and Proposition 6.1 in Section
6.3. The source writes the minimum over its set $\mathcal V_N$ of
Euclidean-orthonormal matrices while using the $X_h$-orthogonal projection
$WW^\top X_h$; the item states the minimum over $X_h$-orthonormal $W$, the
form in which the identity is correct. Low-rank approximation itself is in
section 6. Item 24.9 is Quarteroni–Manzoni–Negri, (3.13)–(3.14), p. 42, and
Section 3.6, (3.70)–(3.73), pp. 58–59; the use of a lower bound
$\beta^{\mathrm{LB}}_h$, computed for instance by the successive constraint
method, is (3.79), p. 63. The effectivity bound with $\beta^{\mathrm{LB}}$ in
place of $\beta_h$ follows at once from the two-sided inequality. Item
24.10 is Quarteroni–Manzoni–Negri, Section 10.1, (10.5)–(10.7), pp. 196–197,
Theorem 10.1 and (10.8), p. 198, and Section 10.2, (10.9)–(10.10) and
Proposition 10.1, p. 199. The bound $\Lambda_M\le2^M-1$ is stated on p. 199
and left as Exercise 3 of Chapter 10, p. 214, whose outline the item
follows; Proposition 10.1 is likewise left as Exercise 4. Theorem 10.2,
p. 200, an exponential convergence statement for empirical interpolation
cited from the literature, is not used.

Item 24.11 is Benner–Gugercin–Willcox, Section 3.3, (3.10)–(3.16),
pp. 500–501, with the $\mathcal H_\infty$ norm (2.21), p. 495. The source
works with a nonsingular $E$ and the generalized Lyapunov equations (3.15)
and refers to Antoulas for the proofs; the item takes $E=I$ and adds
controllability and observability so that the Gramians are positive
definite. The bound is stated with all $\eta_{r+1},\dots,\eta_n$; the
classical sharper form counts each distinct Hankel singular value once.
Item 24.12 is Benner–Gugercin–Willcox, Theorem 3.1, p. 498, with the
projection (2.6), p. 492, and the transfer functions (2.19)–(2.20), p. 495;
the source uses a real parameter domain but complex interpolation points
$\hat p\in\mathbb C^d$. Classical moment matching at a point is the
non-parametric case of this theorem.

Item 24.13 is Sullivan, Section 2.7: Theorem 2.46 (characterization and
uniqueness by mean and covariance), Theorem 2.47 (Fernique), p. 26,
Theorem 2.49 (Sazonov), p. 27, Definition 2.50 (Cameron–Martin space),
pp. 27–28, and Theorem 2.51 (Feldman–Hájek), p. 28; and Stuart, Theorem
6.6, p. 529, Lemma 6.10, p. 530, and Theorems 6.13 and 6.14, p. 531, from
which the density formula and the meaning of $\langle h,x-m\rangle_C$ are
taken. Sullivan states the equivalence of shifts only as one of several
equivalent descriptions in Definition 2.50, without proof, and prints the
density with $\langle v,x\rangle_{C^{-1}}$ undefined for general $x$; Stuart's
limiting definition is used. Item 24.14 is Lord–Powell–Shardlow, Theorem
7.52, p. 293, and Theorem 7.53, p. 294 (the random-field forms of Theorems
5.28 and 5.29, pp. 202–203, which are proved there); the source divides by
$\sqrt{\nu_j}$ without excluding $\nu_j=0$, and the item restricts the sum to
$\nu_j>0$, the remaining terms vanishing almost surely. The identity for
$\mathbb E\|u-u_J\|^2_{L^2(D)}$ follows directly from the expansion; the
source states it for stationary fields as Corollary 7.54, p. 294. Sullivan,
Theorems 11.3 (Mercer) and 11.4 (Karhunen–Loève), p. 225, states the same
expansion less precisely. Item 24.15 is Sullivan, Section 11.2, pp. 234–237,
with Definition 11.11 and Lemma 11.13, and Section 11.3, pp. 237–238, with
Theorem 8.25, p. 157, for the product basis. Sullivan justifies completeness
of the Hermite polynomials by the Weierstrass theorem, which on the
unbounded line needs a supplement; the sufficient condition of finite
exponential moments on p. 139 covers the Gaussian case, and completeness of
the product basis follows from the tensor product structure of
$L^2(\mathbb R^d,\gamma_d)$ noted on p. 237. The extension to countably many
Gaussian variables (Cameron and Martin 1947) is mentioned by Sullivan,
p. 236, and Lord–Powell–Shardlow, p. 427, but no local source proves it, and
it is not stated. Item 24.16 is Sullivan, Theorem 12.13, p. 268, with Céa's
lemma, Lemma 12.11, p. 266, applied to $\alpha$ on $\mathcal H$; the energy
best-approximation property in the symmetric case is Lord–Powell–Shardlow,
Theorem 9.46, p. 396, for the elliptic problem of Assumption 9.42 and
Theorems 9.43 and 9.45, p. 396.

Item 24.17 is DeVore–Hanin–Petrova: the networks $\Upsilon^{W,L}$ are
defined in Sections 2.1–2.2, pp. 331–333, the class error in (5.1), p. 377,
and $\mathrm{Lip}\,1$ with the norm of the item on p. 370. The
first part is Theorem 8.11, p. 414 (Yarotsky's super-convergence); the
lower bound is (8.49), p. 415, stated for the unit ball of $C^s([0,1]^d)$ as
a consequence of Section 5.9 and Theorem 3.12, and it applies here because
the unit ball of $C^1[0,1]$ lies in that of $\mathrm{Lip}\,1$. The source
states (8.45) for all $n\ge1$, but its proof treats even $n\ge4$; the item
states it for even $n$ (for $n=2$ it is trivial, since the zero function
has error at most $1$). The second part is Theorem 8.10, p. 409, whose
depth $C\,n[\log_2n]^\beta$ is written with a ceiling; the source states the
bound for $n\ge1$, where the logarithm vanishes at $n=1$. Hackbusch's
*Tensor Spaces* was not needed for this section.
