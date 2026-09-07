# Exact target and acceptance conditions

## Sources actually read at initialization

- Zenodo source sections 1, 2, 5; section 3 through the lag phase;
  section 4 through the uniform-freezing statement.
- Original phase12_capture_contract.json, copied in the Phase 40 historical contracts.
- The remaining proof sections will be read before their corresponding formalization.

## P0

For every real delta with 0 < delta <= 1 there exists a real c > 0 such that,
for every natural N >= 1, every f : Z x Z -> C bounded in norm by 1, and
every theta : B_N -> R/Z, a mean original response at least delta implies
the existence of beta : R/Z with mean response for the SAME f at least c.
B_N = {1,...,N} x {1,...,N^2}; every average uses r = 1,...,N.

The existential c precedes N, f and theta. A bound depending on N is not P0.

## Weighted finite capture (strong universal-list version asserted in the paper)

For every kappa, eta, epsilon with 0 < kappa, eta <= 1 and
0 < epsilon <= eta/2, there exist c > 0, L >= 1, N0 >= 1 such that
for every N >= N0 there exists a list beta : Fin L -> R/Z such that
for every admissible ORIGINAL f, theta, lambda, mu there exist a retained
set A and an assignment j on A satisfying the conclusion.

Admissibility: norm f <= 1, norm lambda_z = 1,
0 <= mu_z <= N^(-3), sum mu >= kappa, and
Re(lambda_z T_z^f(theta_z)) >= eta whenever mu_z != 0.

Conclusion: A is contained in the original support of mu,
sum_(z in A) mu_z >= c, and d_(3,N)(theta_z, beta_(j(z))) <= epsilon.
The distance is the square root of the average of squared chord differences
over ALL r in {1,...,N}. The list may depend on N and the parameters, but in
this stronger version it precedes all original data. An assignment outside
A may be chosen arbitrarily because L >= 1; it carries no additional claim.

## Connection with the old contract

The old Phase 12 contract requests bounded bracket circuits and an averaged
squared full-label error on positive original base weight. The paper's
pointwise constant capture is a stronger proposed target. Constants are
allowed circuit leaves, but the reduction to the old contract is still to be
proved, with the original measure supplied explicitly. Neither contract is
to be silently weakened to a selected label set, an anchored coefficient,
or a different response. No claim about U0 follows.

## Acceptance

1. State the target using actual mathematical definitions, not an abstract
   proposition supplied as a hypothesis under a proved-sounding name.
2. Check every exported proof with the pinned Lean kernel.
3. Inspect transitive axioms: only standard Mathlib foundations are allowed;
   no sorryAx and no project-specific unproved axiom may occur.
4. An explicit conditional reduction is useful but is not proof of its premises.
5. A missing Lean library, a failed proof attempt, or a finite numerical example
   is not a mathematical refutation. A genuine counterexample must satisfy
   the exact original hypotheses and negate the exact uniform conclusion.
6. Full formalization remains unfinished until P0 and every necessary dependency
   are discharged. Paper status labels and artifact hashes provide no substitute.
