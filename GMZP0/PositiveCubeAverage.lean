import GMZP0.CubeSignSymmetry
import GMZP0.SignedShiftMean

/-! Exact positive-step form of the original weighted cube average. -/

noncomputable section
namespace GMZP0

theorem realUniformMean_prod_four {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → ℝ) :
    realUniformMean (fun z : A × B × C × D => F z.1 z.2.1 z.2.2.1 z.2.2.2) =
      realUniformMean (fun a => realUniformMean (fun b => realUniformMean (fun c => realUniformMean (F a b c)))) := by
  rw [realUniformMean_prod (fun a (z : B × C × D) => F a z.1 z.2.1 z.2.2)]
  congr 1
  funext a
  rw [realUniformMean_prod (fun b (z : C × D) => F a b z.1 z.2)]
  congr 1
  funext b
  exact realUniformMean_prod (F a b)

abbrev PositiveCubeParameters (N q ℓ : ℕ) := Fin N × Fin N × ZMod q × CubeShiftPairs ℓ

def cyclicPositiveCubeNearMass (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) : ℝ :=
  realUniformMean (fun z : PositiveCubeParameters N q ℓ =>
    cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2)

theorem card_positiveCubeParameters (N q ℓ : ℕ) [NeZero q] :
    Fintype.card (PositiveCubeParameters N q ℓ) = q * N ^ 2 * (2 * ℓ + 1) ^ 8 := by
  simp only [PositiveCubeParameters, CubeShiftPairs, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, ZMod.card, Fintype.card_fun, card_smoothingShiftLabels]
  ring

/-- Both signs give exactly the same weighted mean, with no loss in the lower bound. -/
theorem cyclicSpatialCubeNearMass_positive (N q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (σ : Base N → ℝ) (d : ℕ) (E : ℝ) :
    cyclicSpatialCubeNearMass N q ℓ p σ d E = cyclicPositiveCubeNearMass N q ℓ p σ d E := by
  rw [cyclicSpatialCubeNearMass, cyclicPositiveCubeNearMass]
  rw [realUniformMean_prod_four (fun (x : Fin N) (h : horizontalShiftLabels N) Y u =>
    cyclicCubeNearWeight N q ℓ p σ d E x Y h.val u)]
  rw [realUniformMean_prod_four (fun (x : Fin N) (h : Fin N) Y u =>
    cyclicCubeNearWeight N q ℓ p σ d E x Y (label h) u)]
  congr 1
  funext x
  apply real_signed_mean_eq_positive N
    (fun h => realUniformMean (fun Y : ZMod q => realUniformMean (fun u : CubeShiftPairs ℓ =>
      cyclicCubeNearWeight N q ℓ p σ d E x Y h u)))
  intro h
  congr 1
  funext Y
  exact cubeNearWeight_mean_neg N q ℓ p σ d E x Y h

theorem cyclicCubeNearMass_positive (N q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (σ : Base N → ℝ) (d : ℕ) (E : ℝ) :
    cyclicCubeNearMass N q ℓ p σ d E = cyclicPositiveCubeNearMass N q ℓ p σ d E := by
  rw [cyclicCubeNearMass_remove_lag, cyclicSpatialCubeNearMass_positive]

end GMZP0
