# P0 formalization

Status: in progress; the complete P0 theorem has NOT been formally verified.

Checkpoint F20: 688 checked theorem declarations. Finite Fourier inversion,
Parseval, original parameter/difference pushforwards and the exact nonnegative
Fourier expansion of local cube moments are checked. The complete multiset local-to-global comparison for every s>=2 is now proved,
with no unproved character-twist premise. Exact global seventh-moment frequency
averaging is also checked; a positive seventh-moment lower bound still requires
the family theorem and actual pair geometry.
F20 additionally checks the elementary pair-geometry prerequisites: the local
fourth-moment bound forces a <= 256, with uniform shrink thresholds, integer
range and no-wrap lemmas for paired shifts. Representation multiplicity and
the family theorem remain open.
See LOCAL_GLOBAL_INTERFACE.md for its precise remaining scope.

The earlier checked spine remains: The recursive box moment now
equals the full Boolean-vertex expansion in C, with all multiplicities intact.
The complete cyclic rerooting and t-average reindexing are checked. Sixteen
original weights remain outside the cubic t sum, whose leading coefficient is
minus the signed original frequency sum and is independent of the lag k.
The resulting weighted norm average is >=(a/4)^16 with uniform constants and
original responses retained. Every nonzero-weight cube vertex is an actual
retained original base point. Linear inverse Weyl estimates are now proved for
all affine phases and actual integer intervals with the original N denominator.
Exact differencing, explicit nonzero-shift counts above N*rho^2>=2, a checked
small-scale obstruction, and quadratic/cubic phase derivatives are established.
Dense affine recurrence amplification and the quadratic/cubic leading-coefficient
inverse estimates are now checked, at every positive scale. One common denominator
is chosen before the scale and all coefficients. Applied to the actual original
cube time sum, it retains weighted cube mass >=(a/4)^16/2 at scale N^(-3), with
the same original safe mass and complete responses. This captures a cube coefficient,
not an original point frequency. The unused k mean is now removed exactly;
simultaneous sign reflection fixes every actual vertex and gives the positive-h
mean with no loss. Pair collisions cost at most 1/(2*ell+1), and the complete
120-pair union costs at most 120/(2*ell+1). A uniform data-independent threshold
leaves distinct-vertex original weighted cube mass >=(a/4)^16/4, preserving the
same original safe mass and complete responses. The nonzero modular step and
short interval hypotheses are explicit; a checked zero-step counterexample
shows why the former cannot be omitted. One simultaneous real lift is now
checked: every point receives one of 57 choices shared across all cubes.
The same rounded values give S=l*M_lift+r, |l|<=8 and |r|<=9. Uniform restriction
to distinct vertices and weighted expectation retain real-zero four-cube mass
>=(a/4)^16/(4*57^16). Here M_lift=floor(N^3/E)>=9, |F|<=3, F lies on the grid,
and its supported circle error to d*theta is <=19*E/N^3. Constants precede N,q
and all original data, and original responses remain unchanged. Exact frequency
averaging is now checked on the complete j/1024 mesh for all dimensions <=7,
with grid integrality and the strict size bound. It detects real zero and
retains every original weight. The same F has local fourth-norm sixteenth
moment >=beta=(a/4)^16/(4*57^16), and at least beta/2 of actual (x,j) fibres
have mean_h local norm >=beta/2. All multiset multiplicities and complete
original responses remain in the uniform theorem. Local-to-global comparison,
family concatenation, structural realization, uniform freezing and deeper
external dependencies remain open.

Primary source: ../GMZ_P0_Zenodo/sections/01-introduction.tex through 05-selection.tex.
Original contract: ../GMZ_P0_Phase40_Final_Adjudication/historical_contracts/phase12_capture_contract.json.

The main target preserves the order `delta, c(delta), N, f, theta` and uses the
same original function in the conclusion. The stronger weighted target preserves
the original weight, all cubic labels, all circle roots, and uniform list size.

Lean 4.33.0 and Mathlib v4.33.0 are pinned. Official dependency source archives
use the precise revisions in Mathlib's original manifest, recorded in
dependency-provenance.json. Local path dependencies avoid an unreliable Git
transport in this environment; no upstream mathematical source has been edited.

In the configured workspace, run `python verify.py` to build and audit all
theorems. With Lean 4.33.0 and Python installed, `./setup.ps1` retrieves the
official sources and builds from source on a fresh Windows checkout.
Optional `./setup.ps1 -UseCache` retrieves official compiled artifacts first.
The setup script accepts `-Python` for an explicit Python executable path.
The regular build command is `lake build`; the axiom audit is
`lake env lean GMZP0/Audit.lean`.

See STATUS.md for the exact current checked scope and remaining obligations.
Proved declarations must have no `sorry` or added axioms.
Unproved results are recorded as propositions or in the dependency ledger;
conditional reductions must explicitly name their hypotheses.

No historical claim of proof, successful numerical test, hash, or document
compilation counts as a formal proof. U0 is outside this target. The twelve
deferred erroneous three-dimensional applications must remain unused.
