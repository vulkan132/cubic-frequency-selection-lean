import GMZP0.PairSeventhMoment

/-! An external input for the core proof, not an asserted theorem or axiom.
The intended source is Tao--Ziegler, Theorem 1.23, at rank one and degree four.
See CONCATENATION_SOURCE_AUDIT.md. The exact interface includes parameter
multiplicities and fixes u before all scales, groups, radii and functions. -/

noncomputable section
namespace GMZP0

def CyclicConcatenationInput : Prop :=
  ∀ β : ℝ, 0 < β → ∃ u : ℝ, 0 < u ∧ u < 1 / 8 ∧
    ∀ (N q ℓ : ℕ) [NeZero q], 0 < N → 0 < ℓ →
      ∀ H : ZMod q → ℂ, (∀ y, ‖H y‖ ≤ 1) →
        β / 2 ≤ realUniformMean (fun h : Fin N => localCubeNorm 3 H (cyclicShiftMap q ℓ (label h))) →
        u < cyclicPairSeventhMean N q ⌊u * ℓ⌋₊ H

end GMZP0
