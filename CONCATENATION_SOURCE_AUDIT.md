# Family concatenation source audit, after F17

The original [Tao–Ziegler paper](https://arxiv.org/pdf/1603.07815), Definitions
1.6, 1.9, 1.10 and Theorem 1.23, was read directly on 2026-09-07. Its finite
family conclusion has a modulus depending only on rank and degree, with no
family-cardinality dependence. At rank one and degree four the paired norm
has degree seven. The progressions are parameterized multisets; shrinking
acts on parameter radii. These conventions match the intended application.
Section 8 obtains the family result via bounded sampling and a nonstandard
characteristic-factor argument. None of that proof is currently implemented
in this project. Source agreement is not machine verification.

The implementation must retain the following project-specific obligations:

- The checked object is `localCubeNorm 3` for the exact map v -> 2*h*v mod q.
  The rank-one presentation, its positive radius, and the shrunk parameter
  interval must be supplied. A statement merely about the set of image values
  loses multiplicities and does not specify what shrinking means.
- The same `modulatedCyclicField` must be used for every h and both paired
  directions at each fixed (x,j). The fixed lift F must not depend on h or j.
- First fix the family modulus, then u from beta, and then all scale thresholds.
  A function-specific u or a modulus depending on q, N, or the mesh size is
  insufficient for the final uniform conclusion.
- A theorem declaration may not assume this family result as a new axiom.
  The full required proof, or an actual checked implementation with matching
  definitions, remains open.

The separate finite Fourier and full local-to-global comparison are proved
at F19 for every s>=2, using a direct character-twist argument. This does not
prove the family concatenation theorem. P0 and WeightedCapture remain open.
