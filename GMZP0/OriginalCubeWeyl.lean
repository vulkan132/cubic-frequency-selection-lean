import GMZP0.CubicCommonDenominator
import GMZP0.CyclicCubeTime

/-! The checked cubic inverse estimate applied to the exact original cube time sum. -/

noncomputable section
namespace GMZP0

theorem cyclicCubeTimeAverage_as_polynomial (N q ℓ : ℕ) (p : Base N → Frequency)
    (x : Fin N) (Y : ZMod q) (h k : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeTimeAverage N q ℓ p x Y h k u =
      integerIntervalMean N (fun t => circleCharacter (cubicCirclePolynomial
        (cyclicCubeCubicCoeff N q ℓ p x Y h u)
        (cyclicCubeCoefficients N q ℓ p x Y h k u 2)
        (cyclicCubeCoefficients N q ℓ p x Y h k u 1)
        (cyclicCubeCoefficients N q ℓ p x Y h k u 0) t)) := by
  rw [integerIntervalMean_eq_fin]
  simp only [cyclicCubeTimeAverage, cyclicCubePhase_polynomial,
    cubicCirclePolynomial, cyclicCubeCoefficients_top]

/-- D and E precede N, the cyclic modulus, all original fields and every cube parameter.
The conclusion concerns the alternating cube coefficient, not an original point frequency. -/
theorem uniform_original_cube_weyl (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ D : ℕ, ∃ E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ q ℓ : ℕ, ∀ p : Base N → Frequency,
      ∀ x : Fin N, ∀ Y : ZMod q, ∀ h k : ℤ, ∀ u : CubeShiftPairs ℓ,
        ρ ≤ ‖cyclicCubeTimeAverage N q ℓ p x Y h k u‖ →
          ‖D • cyclicCubeCubicCoeff N q ℓ p x Y h u‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨D, E, hD, hE, hw⟩ := uniform_cubic_common_denominator ρ hρ
  refine ⟨D, E, hD, hE, ?_⟩
  intro N hN q ℓ p x Y h k u hlarge
  rw [cyclicCubeTimeAverage_as_polynomial] at hlarge
  exact hw N hN _ _ _ _ hlarge

end GMZP0
