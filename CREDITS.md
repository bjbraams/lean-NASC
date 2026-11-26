# Credits

The statements follow the [mathematical synopsis](SYNOPSIS.md) and
[gap catalogue](GAPS.md). The synopsis reference guide and the
[bibliography](NASC-bib.md) give the mathematical source provenance.

- Mathlib provides the finite-dimensional singular-value and matrix APIs,
  the cyclic Fourier transform with its standard additive character,
  Lagrange interpolation, and multivariate Gaussian and covariance
  operators. The Gaussian covariance statements use the uncentered
  operator applied to the centered law.
- TauCeti provides the weak Sobolev spaces, bounded boundary trace,
  and weak Dirichlet formulation used by the finite and boundary element
  modules. The stochastic equation module uses TauCeti's Itô integral
  predicate and deterministic Wiener integral. The ReLU approximation
  module uses TauCeti's multilayer perceptron evaluator.

The [coverage inventory](STRUCTURE.md#source-baseline) records the pinned
library revisions.
r