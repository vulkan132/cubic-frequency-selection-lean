# Original exponential sets and lattice spans — F64

Historical checkpoint. F65 proves native bracket compatibility of actual
conjugation and conjugation invariance of these lower-central exponential
sets; see ORIGINAL_CONJUGATION_FILTRATION_INTERFACE.md. Multiplicative
closure and group-series matching remain open.

F64 adds 15 theorem declarations to F63's 1661. The complete verification
records are verification/result.json, build.log and axioms.log. P0 and
WeightedCapture remain unproved. No external theorem or project axiom is added.

## Actual exponential sets and topology

For the same original global logarithm L and a real linear subspace U,
originalExponentialImage is the subset {g : L(g) belongs to U}. Because
L is an actual equivalence, this is exactly Exp(U). It is defined as a
set, without silently adding a subgroup structure.

The previously proved rational arrays give a homeomorphism with exactly
the same logarithm and inverse, on the original group topology. Its
restriction identifies Exp(U) with U, with their inherited topologies.
Every U is finite dimensional, hence closed; consequently Exp(U) is
closed and contractible. Rationality of U is not needed for these facts.

The original native one-parameter subgroup law proves

```
Exp(-v) = Exp(v)^(-1),
Exp(n v) = Exp(v)^n,
L(g^n) = n L(g)                         (n a natural number).
```

Thus Exp(U) contains the original identity and is inverse closed.
For every g and every n>0, g^n belongs to Exp(U) if and only if g does.
The proof explicitly uses n!=0; it does not assert this for the zero power.
These statements alone do not imply multiplicative closure.

## Actual original-lattice points spanning each rational subspace

Take the proved fixed denominator inclusion

```
den * Z^sigma  subset  L(Gamma),         den > 0.
```

For any fixed finite family of rational vectors a_j, simultaneous
denominator clearing gives one k>0 and actual gamma_j in the original
Gamma satisfying L(gamma_j)=k*a_j for every j. The scale and family are
chosen before the family index; no arbitrary real observation coefficient
is bounded or changed.

For a rational U, apply this to its finite rational generator family.
All L(gamma_j) belong to U and nonzero real scaling preserves their span.
This produces an actual finite subset F of the original Gamma with

```
L(g) belongs to U for every g in F,
span_R(L(F)) = U,
span_R(L({g in Gamma : L(g) belongs to U})) = U.
```

Zero-dimensional subspaces and empty generator families are included.
No addition of logarithms is assumed to stay in L(Gamma). These are exact
real-span statements, not a proof that Gamma intersect Exp(U) is a
cocompact subgroup lattice, and not a quantitative Malcev basis bound.

## Connection to the actual native lower-central ideals

OriginalExponentialSubspaceData bundles the topology, identity, inverse,
positive-power membership equivalence, finite original-lattice span and
full original-intersection span. It contains no multiplicative-closure field.

original_weak_basis_lower_central_exponential_data applies these results to
every actual Mathlib native Lie lower-central ideal using F63 rationality.
Mathlib index zero remains the entire Lie algebra. No identification with
the manuscript's group-series indices is assumed.

original_full_exponential_lie_filtration invokes F63 once, retaining all
original integer/real bases, the full original lattice, weak-basis bound,
smooth maps, rational arrays, all coefficient/degree bounds, actual
Lie-layer rationality and finite-depth bounded bases. The new exponential
set data are added with precisely those same witnesses.

## Counterexample check and remaining obligations

The exact Heisenberg coordinate formulas give a product of the exponentials
of e1 and e2 whose logarithm has central coordinate 1/2. Both initial
vectors lie in the horizontal plane. This polynomial computation refutes
the shortcut from arbitrary linear subspaces to multiplicatively closed
exponential images. It does not refute integration of Lie ideals or P0.

The next obligation is to use the actual Lie bracket to prove the required
integrated subgroup closure and normality, then identify the original
group lower-central subgroups with the appropriate exponential images.
Original lattice-intersection cocompactness, a common adapted Malcev
presentation and quantitative external metric/test/interval matching
remain open. Exact logarithmic span is only one part of that interface.

Controlled general descent families and quantitative termination,
original full-label frequency realization with all circle branches and
quadratic freedom, and final WeightedCapture/P0 also remain open.
P2-CSE and U0 remain open. The historical twelve incorrect
three-dimensional composite applications remain deferred and unused.
