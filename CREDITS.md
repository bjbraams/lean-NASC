# Credits

The statements follow the [mathematical synopsis](SYNOPSIS.md) and
[gap catalogue](GAPS.md). The synopsis reference guide and the
[bibliography](NASC-bib.md) give the mathematical source provenance.

- Mathlib provides the finite-dimensional singular-value and matrix APIs,
  the cyclic Fourier transform with its standard additive character,
  Lagrange interpolation, Vandermonde nonsingularity for Prony reconstruction,
  and multivariate Gaussian and covariance operators. The Gaussian covariance
  statements use the uncentered
  operator applied to the centered law.
- The conditioning proofs use Mathlib's derivative norm bound for locally
  Lipschitz maps and its Hahn–Banach norming functional. The compact-operator
  proof uses the finite-dimensionality criterion from a totally bounded
  neighborhood.
- The stationary iteration proof uses Mathlib's Gelfand formula. The matrix
  function proofs use its polynomial Taylor and Hasse derivative identities.
  The least-squares proofs use its adjoint criterion for minimizers.
- The approximation and quadrature proofs use Mathlib's finite-dimensional
  evaluation criterion, nodal polynomials, Rolle's theorem, orthogonal
  projection identity, and positivity criterion for integrals.
- The interval and nonlinear equation proofs use Mathlib's mean value,
  intermediate value, and integrated derivative bounds. The Tikhonov
  existence proof uses its Lax–Milgram equivalence.
- TauCeti's supporting-plane inequality for a differentiable convex function
  gives the lower bound used in the gradient descent proof.
- TauCeti provides the weak Sobolev spaces, bounded boundary trace,
  and weak Dirichlet formulation used by the finite and boundary element
  modules. The Prager–Synge proof uses its gradient-inner-product form of
  the Poisson energy. The stochastic equation module uses TauCeti's Itô integral
  predicate and deterministic Wiener integral. The ReLU approximation
  module uses TauCeti's multilayer perceptron evaluator.

The [coverage inventory](STRUCTURE.md#source-baseline) records the pinned
library revisions.
