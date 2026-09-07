import GMZP0.CubeExpansion
import GMZP0.UniformBoxAverage

/-! Complete four-dimensional expansion of the original cyclic box moment. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev CubeShiftPairs (ℓ : ℕ) := Fin 4 → smoothingShiftLabels ℓ × smoothingShiftLabels ℓ

theorem card_cubeShiftPairs (ℓ : ℕ) : Fintype.card (CubeShiftPairs ℓ) = (2 * ℓ + 1) ^ 8 := by
  simp only [CubeShiftPairs, Fintype.card_fun, Fintype.card_prod, Fintype.card_coe,
    card_smoothingShiftLabels, Fintype.card_fin]
  ring

def cyclicCubeProduct (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) (u : CubeShiftPairs ℓ) : ℂ :=
  cubeProduct 4 (cyclicLagBoxFunction N q ℓ p σ lam x v h t k) u

def cyclicCubeAverage (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℂ :=
  complexUniformMean (fun z : CyclicBoxSamplingSpace N q =>
    complexUniformMean (fun u : CubeShiftPairs ℓ => cyclicCubeProduct N q ℓ p σ lam
      z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val u))

theorem cyclic_cube_expansion (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicCubeAverage N q ℓ p σ lam = (cyclicBoxMomentAverage N q ℓ p σ lam : ℂ) := by
  unfold cyclicCubeAverage cyclicCubeProduct cyclicBoxMomentAverage
  change complexUniformMean (fun z : CyclicBoxSamplingSpace N q =>
    cubeMean 4 (cyclicLagBoxFunction N q ℓ p σ lam
      z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val)) = _
  simp only [cubeMean_eq_boxMoment, complexUniformMean_ofReal]

theorem cyclicCubeAverage_re (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    (cyclicCubeAverage N q ℓ p σ lam).re = cyclicBoxMomentAverage N q ℓ p σ lam := by
  rw [cyclic_cube_expansion, Complex.ofReal_re]

end GMZP0
