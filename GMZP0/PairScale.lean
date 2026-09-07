import GMZP0.PairGeometry
import GMZP0.CyclicFrequencyAverage
import GMZP0.OriginalWeights

/-! The original local-moment lower bound supplies the scale bound actually used by pair geometry. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cyclicLocalFourthNormAverage_le_one {N q M ℓ : ℕ} [NeZero q]
    (hN : 0 < N) (hM : 0 < M) (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) : cyclicLocalFourthNormAverage N q ℓ M σ F ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (1024 * M)) := ⟨⟨0, by omega⟩⟩
  unfold cyclicLocalFourthNormAverage
  calc
    _ ≤ realUniformMean (fun _ : Fin N => realUniformMean (fun _ : Fin (1024 * M) =>
        realUniformMean (fun _ : Fin N => (1 : ℝ)))) := by
      apply realUniformMean_mono
      intro x
      apply realUniformMean_mono
      intro j
      apply realUniformMean_mono
      intro h
      exact pow_le_one₀ (localCubeNorm_nonneg 3 _ _)
        (localCubeNorm_le_one 3 _ _ (modulatedCyclicField_norm_le N q M σ F hσ x j))
    _ = 1 := by simp only [realUniformMean_const]

theorem original_scale_bound_of_local_four {N q M : ℕ} [NeZero q]
    (hN : 0 < N) (hM : 0 < M) (μ : Base N → ℝ) (D : Finset (Base N))
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) (F : Fin N → ZMod q → ℝ) (a : ℝ)
    (hlarge : (a / 4) ^ 16 / (4 * 57 ^ 16) ≤
      cyclicLocalFourthNormAverage N q (smoothingRadius N a) M (originalScaledWeight N μ D) F) :
    a ≤ 256 := by
  exact original_scale_parameter_bound a (hlarge.trans
    (cyclicLocalFourthNormAverage_le_one hN hM _ F (originalScaledWeight_bounds hN μ D hμ)))

end GMZP0
