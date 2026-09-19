# F40: normalized Haar and the original observation's fiber mean

Historical checkpoint. F41 constructs actual measurable sections, Borel
quotients and compactly contained strict domains, and proves measurability
of the original observation for any specified measurable section. F42
constructs full-quotient invariant probability and global zero cutoff
means under the explicit rational presentation hypotheses. See
OBSERVATION_GLOBAL_MEAN_INTERFACE.md for the current scope and remaining inputs.

P0 and WeightedCapture remain unproved. This interface concerns the
fiberwise mean-zero step immediately after `eq:observation` in Section 4
of `../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`. It introduces no new
external deep premise or project axiom. Verification is recorded in
`verification/result.json` after the complete audit.
This checkpoint adds 29 explicit theorem declarations in six modules.

## Actual objects and exact quantifiers

The fiber is the original additive quotient V/V_Z, with its quotient
topology and Borel measurable structure. For every actual gamma in Gamma,
evaluation F -> F(gamma) modulo one descends to an additive map into R/Z.
Its complex exponential is continuous and has modulus one. There is no
change of lattice and no chosen real lift or circle root.

For every original base representative g, the map

    [F] in V/V_Z  ->  [(g,F)] in H/Gamma_H

is well-defined, injective and continuous, and its range is exactly the
fiber over g*Gamma of the original base projection. Surjectivity onto that
fiber uses the actual right lattice correction and its pullback. Neither
Gamma nor Gamma_H is assumed normal. A continuous inverse on the fiber
is not asserted by these statements.

For every algebraic section c already defined in F33 and every g, the
restriction of the original quotient observation is exactly

    Psi([(g,F)]) = e(F(gamma_g)),
    gamma_g = observationCorrection(c,g) in Gamma.

At a canonical representative this is evaluation at the identity. The
more general equality retains the correction at every representative,
including those on a section boundary. Measurability or regularity of c
is not required for a single fiber, and is not proved here globally.

## Genuine zero mean, with integrability checked

Assume the constant-one function belongs to V. Then every real constant
function belongs to V, and each circle-valued fiber evaluation is
surjective. The actual class of the constant function 1/2 changes every
fiber character by a factor of -1. Translation invariance of the measure
therefore gives zero integral.

Separately, continuity and the pointwise modulus-one identity prove
integrability with respect to every finite Borel measure on the fiber.
Thus the normalized Haar zero-mean theorem is an integral of an integrable
function, not the default value assigned to a nonintegrable Bochner integral.

The original discrete lattice is closed and its additive quotient is
Hausdorff. F39 compactness permits the construction `addHaarMeasure top`,
and Mathlib proves its additive Haar invariance and total mass exactly one.
For every section c, every base representative g and every complex scalar
a, the original function a*Psi([(g,F)]) is integrable and has zero mean
with this same normalized fiber Haar measure. A cutoff depending only on
the base has such a constant value on each fixed fiber.

## Integration with the rational presentation

`observation_fiber_haar_of_presentation` takes the literal rational
polynomial basis, integer coordinates on Gamma, coverage of the entire
integer grid by actual Gamma points, and constant-one membership in V.
It internally derives the discrete lattice, compatible integer/real bases,
compact fiber and Hausdorff fiber, and constructs one probability Haar
measure before quantifying over all c, g and a above. No compact fiber or
Haar measure is added as a new unproved input to this integrated theorem.

## Global cutoff symmetry and its precise conditional scope

Left translation by the original group element (1,constant(a)) preserves
the original base coset and multiplies Psi by e(a). Consequently the
element with a=1/2 negates both Psi and chi(base)*Psi for every base cutoff.
This identity holds on the original quotient, with no regularity premise
on the algebraic section.

`quotient_observation_cutoff_integral_zero` proves a genuine global zero
mean if the original quotient is supplied with an actual invariant finite
measure, a measurable group action, an almost everywhere strongly measurable
cutoff observation, and a pointwise bounded base cutoff. Integrability is
proved from the bound and the original modulus-one identity. Invariance
and the exact sign change then force the integral to vanish. These are
explicit hypotheses: the result does not construct the global invariant
measure or prove that the chosen canonical section is measurable.

## Exact obstruction and remaining interfaces

The zero observation module is translation-invariant but has zero
evaluation. Its fiber is a singleton, the original exponential character
is identically one, and its normalized Haar integral is one. The exact
theorem `observation_zero_module_mean_obstruction` shows why the nonzero
evaluation condition cannot be omitted. This is not a counterexample to P0.

The global invariant probability measure on H/Gamma_H remains to be
constructed. The full-quotient translation proof gives a route to the
global mean-zero statement without presupposing a disintegration theorem.
Global measurability of the
chosen section, discharge of the global cutoff theorem's premises, controlled
fundamental-domain faces, boundary neighborhood majorants and Lipschitz
estimates are not supplied by the fiber calculation. In particular, small
Haar measure alone does not imply few visits by an arbitrary orbit.

The full rational Malcev/Lie presentation, uniform height bounds, general
structural descents and uniform termination, and realization for original
frequency data remain open. The conditional capture and P0 reductions
retain their exact original-response and full-label hypotheses. The
historical twelve invalid three-dimensional applications remain unused.
