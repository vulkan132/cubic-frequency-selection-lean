import GMZP0.CubeLagRemoval

/-! Simultaneous sign reflection fixes every actual cube vertex, including multiplicities. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def smoothingShiftNeg (ℓ : ℕ) : smoothingShiftLabels ℓ ≃ smoothingShiftLabels ℓ where
  toFun r := ⟨-r.val, by
    have hr := r.property
    simp only [smoothingShiftLabels, Finset.mem_Icc] at hr ⊢
    omega⟩
  invFun r := ⟨-r.val, by
    have hr := r.property
    simp only [smoothingShiftLabels, Finset.mem_Icc] at hr ⊢
    omega⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv r := by apply Subtype.ext; simp

def cubeShiftPairsNeg (ℓ : ℕ) : CubeShiftPairs ℓ ≃ CubeShiftPairs ℓ where
  toFun u := fun i => (smoothingShiftNeg ℓ (u i).1, smoothingShiftNeg ℓ (u i).2)
  invFun u := fun i => ((smoothingShiftNeg ℓ).symm (u i).1, (smoothingShiftNeg ℓ).symm (u i).2)
  left_inv u := by funext i; apply Prod.ext <;> simp
  right_inv u := by funext i; apply Prod.ext <;> simp

theorem cubeShiftSum_neg (ℓ : ℕ) (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) :
    cubeShiftSum ℓ (cubeShiftPairsNeg ℓ u) ω = -cubeShiftSum ℓ u ω := by
  have hi (i : Fin 4) : (cubeVertex (cubeShiftPairsNeg ℓ u) ω i).val =
      -(cubeVertex u ω i).val := by
    unfold cubeVertex
    split_ifs <;> rfl
  unfold cubeShiftSum fourShiftSum
  simp only [hi, Finset.sum_neg_distrib]

theorem cyclicCubeVertex_neg_reflect (q ℓ : ℕ) (h : ℤ) (Y : ZMod q)
    (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) :
    cyclicCubeVertex q ℓ (-h) Y (cubeShiftPairsNeg ℓ u) ω = cyclicCubeVertex q ℓ h Y u ω := by
  simp only [cyclicCubeVertex, cubeShiftSum_neg]
  have he : 2 * (-h) * (-cubeShiftSum ℓ u ω) = 2 * h * cubeShiftSum ℓ u ω := by ring
  rw [he]

theorem cyclicCubeCubicCoeff_neg_reflect (N q ℓ : ℕ) (p : Base N → Frequency)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeCubicCoeff N q ℓ p x Y (-h) (cubeShiftPairsNeg ℓ u) =
      cyclicCubeCubicCoeff N q ℓ p x Y h u := by
  simp only [cyclicCubeCubicCoeff, cyclicCubeVertex_neg_reflect]

theorem cyclicCubeWeight_neg_reflect (N q ℓ : ℕ) (σ : Base N → ℝ)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeWeight N q ℓ σ x Y (-h) (cubeShiftPairsNeg ℓ u) =
      cyclicCubeWeight N q ℓ σ x Y h u := by
  simp only [cyclicCubeWeight, cyclicCubeVertex_neg_reflect]

theorem cyclicCubeNearWeight_neg_reflect (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeNearWeight N q ℓ p σ d E x Y (-h) (cubeShiftPairsNeg ℓ u) =
      cyclicCubeNearWeight N q ℓ p σ d E x Y h u := by
  simp only [cyclicCubeNearWeight, cyclicCubeCubicCoeff_neg_reflect, cyclicCubeWeight_neg_reflect]

theorem cubeNearWeight_mean_neg (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ) :
    realUniformMean (fun u : CubeShiftPairs ℓ => cyclicCubeNearWeight N q ℓ p σ d E x Y (-h) u) =
      realUniformMean (fun u : CubeShiftPairs ℓ => cyclicCubeNearWeight N q ℓ p σ d E x Y h u) := by
  have he := realUniformMean_equiv (cubeShiftPairsNeg ℓ)
    (fun u => cyclicCubeNearWeight N q ℓ p σ d E x Y (-h) u)
  simpa only [cyclicCubeNearWeight_neg_reflect] using he.symm

end GMZP0
