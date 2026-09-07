import GMZP0.UniformOriginalCubeCapture

/-! Exact removal of the redundant lag average from the original weighted cube capture. -/

noncomputable section
namespace GMZP0

theorem realUniformMean_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (F : J → ℝ) : realUniformMean (fun i => F (e i)) = realUniformMean F := by
  unfold realUniformMean
  rw [Equiv.sum_comp e F, Fintype.card_congr e]

abbrev CubeSpatialParameters (N q ℓ : ℕ) :=
  Fin N × horizontalShiftLabels N × ZMod q × CubeShiftPairs ℓ

def cubeRemoveLag (N q ℓ : ℕ) :
    (CubeSpatialParameters N q ℓ × fullLagLabels N) ≃ CubeWeylParameters N q ℓ where
  toFun z := (z.1.1, z.1.2.1, z.1.2.2.1, z.2, z.1.2.2.2)
  invFun z := ((z.1, z.2.1, z.2.2.1, z.2.2.2.2), z.2.2.2.1)
  left_inv z := by rcases z with ⟨⟨x, h, Y, u⟩, k⟩; rfl
  right_inv z := by rcases z with ⟨x, h, Y, k, u⟩; rfl

def cyclicCubeNearWeight (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) : ℝ :=
  if ‖d • cyclicCubeCubicCoeff N q ℓ p x Y h u‖ ≤ E / (N : ℝ) ^ 3
  then cyclicCubeWeight N q ℓ σ x Y h u else 0

def cyclicSpatialCubeNearMass (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) : ℝ :=
  realUniformMean (fun z : CubeSpatialParameters N q ℓ =>
    cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 z.2.1.val z.2.2.2)

theorem card_cubeSpatialParameters (N q ℓ : ℕ) [NeZero q] :
    Fintype.card (CubeSpatialParameters N q ℓ) = 2 * q * N ^ 2 * (2 * ℓ + 1) ^ 8 := by
  simp only [CubeSpatialParameters, CubeShiftPairs, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, horizontalShiftLabels_card, ZMod.card, Fintype.card_fun,
    card_smoothingShiftLabels]
  ring

/-- No loss or cardinality factor occurs: the mean over the unused k coordinate is one. -/
theorem cyclicCubeNearMass_remove_lag (N q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (σ : Base N → ℝ) (d : ℕ) (E : ℝ) :
    cyclicCubeNearMass N q ℓ p σ d E = cyclicSpatialCubeNearMass N q ℓ p σ d E := by
  have he := realUniformMean_equiv (cubeRemoveLag N q ℓ)
    (fun z : CubeWeylParameters N q ℓ =>
      cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 z.2.1.val z.2.2.2.2)
  change realUniformMean (fun z : CubeSpatialParameters N q ℓ × fullLagLabels N =>
    cyclicCubeNearWeight N q ℓ p σ d E z.1.1 z.1.2.2.1 z.1.2.1.val z.1.2.2.2) =
      cyclicCubeNearMass N q ℓ p σ d E at he
  rw [realUniformMean_prod (fun (z : CubeSpatialParameters N q ℓ) (_ : fullLagLabels N) =>
    cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 z.2.1.val z.2.2.2)] at he
  simp only [realUniformMean_const] at he
  exact he.symm

theorem cyclicCubeNearWeight_bounds (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ)
    (u : CubeShiftPairs ℓ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) :
    0 ≤ cyclicCubeNearWeight N q ℓ p σ d E x Y h u ∧
      cyclicCubeNearWeight N q ℓ p σ d E x Y h u ≤ cyclicCubeWeight N q ℓ σ x Y h u := by
  have hw := cyclicCubeWeight_bounds N q ℓ σ x Y h u hσ
  unfold cyclicCubeNearWeight
  split_ifs <;> constructor <;> linarith

end GMZP0
