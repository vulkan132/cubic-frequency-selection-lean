# F37: the actual integer-valued observation subgroup

Later update: F38 proves compatible adapted integer and real bases from
the literal rational presentation, identifies the basis size with real
dimension, and supplies the actual real quotient coordinates and exact
decomposition. Uniform height bounds and cocompactness remain open. See
OBSERVATION_QUOTIENT_BASIS_INTERFACE.md. The F37 scope below is historical.

P0 and WeightedCapture remain unproved. This checkpoint adds 19 internal
results to the F36 observation-module construction. It introduces no new
external deep-theorem input or project axiom.

## Exact objects and hypotheses

V is the original translation-invariant real space of functions on G.
Gamma is the actual subgroup of G. The integer module is exactly

    V_Z = {F in V : for every gamma in Gamma, F(gamma) is an integer}.

`observationIntegerLattice` is the integer submodule corresponding to the
existing `observationIntegerFunctions`; it does not replace its carrier.
Its topology is inherited from V and the original pointwise function space.

The main full-lattice result assumes a finite real basis b of V, polynomials
P_i with rational coefficients, and a coordinate map coord on G, such that

    b_i(g) = P_i(coord(g))  for every i and every g in G.

It separately requires both directions of the integer-grid presentation:
every gamma in Gamma has integer coordinates, and every integer coordinate
vector is attained by some actual gamma in Gamma. None of these hypotheses
is a supplied discreteness, spanning or integer-basis conclusion.
Constructing this basis and presentation from full rational Malcev data
remains necessary core work.

## Checked arguments

1. For each rational multivariate polynomial P, a positive integer k is
   chosen before all integer inputs z, and k*P(z) is an integer for every z.
   The proof clears denominators by polynomial induction.
2. A real polynomial vanishing on every integer coordinate vector is zero.
   This uses polynomial uniqueness on a product of infinite coordinate sets,
   not a finite numerical test. Polynomial representatives and actual grid
   coverage therefore make Gamma evaluations separate V.
3. In finite-dimensional V, separating Gamma evaluations contain a finite
   determining family of at most dim(V) actual points. The proof selects
   generators of their span in the dual space; it does not substitute
   arbitrary points outside Gamma.
4. Requiring the absolute values of these finitely many evaluations to be
   less than one isolates zero in V_Z. Every such evaluation is continuous,
   so this is an open singleton and V_Z is discrete.
5. Positive integer multiples of the actual rational polynomial basis
   vectors belong to V_Z. Dividing these multiples in the real ambient
   vector space proves that the real span of V_Z equals V.
6. The integer evaluations define an injective integer-linear map from
   V_Z into Z^n. Taking a basis of its actual image over the PID Z and
   pulling it back constructs a finite integer basis of the original V_Z.

The qualitative integer-basis theorem needs only finite dimension and
separating Gamma evaluations. The real-spanning theorem additionally uses
rational polynomial representatives and integrality of all Gamma coordinates.
Keeping these hypotheses distinct prevents an unwarranted full-lattice
claim from separation alone.

## Scope and remaining work

`observation_integer_full_lattice` concludes the pair: DiscreteTopology of
V_Z and real span equal to V. This is the discrete-and-spanning
characterization of a full lattice. The file does not install a normed
`IsZLattice` instance or prove a compact-quotient theorem.

The finite integer basis is qualitative. Its rank is not identified with
dim(V) by a separate theorem here; no uniform height estimate or adaptation
to W is claimed. The proof uses exact evaluations and denominator clearing;
a classification by integer-valued binomial polynomials is not asserted.

Still required are the full rational Malcev presentation, bounded bases
adapted to W and the quotient, bounded character data, group lattice
cocompactness and Lie structure, observation boundary estimates, general
rational descents and original-frequency realization. Existing external
deep inputs retain their explicit scope.

No original function, response, weight, full-label metric or circle-root
branch is modified. The historical twelve invalid three-dimensional
applications remain unused, and no closure of U0 or P2-CSE is asserted.

## Verification

Run `python verify.py` in the repository. It builds the root module and
Audit, checks every explicit theorem declaration against its transitive
axiom report, and records the result in `verification/result.json`.
Verification covers the actual theorem statements and premises above;
it does not certify a full proof of the manuscript or P0.
