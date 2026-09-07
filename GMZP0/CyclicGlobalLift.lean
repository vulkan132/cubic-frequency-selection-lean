import GMZP0.CyclicLiftProbability
import GMZP0.GlobalFiniteChoice

/-! One global real lift realizes the full original weighted cube expectation. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem exists_cyclic_lift_choice {N q ℓ M : ℕ} [NeZero q] (hM : 0 < M)
    (p : Base N → Frequency) (σ : Base N → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (d : ℕ) (E : ℝ) (hscale : (M : ℝ) * (E / (N : ℝ) ^ 3) ≤ 1) :
    ∃ c : CyclicLiftAssignments N q,
      (1 / (57 : ℝ) ^ 16) * cyclicDistinctPositiveCubeNearMass N q ℓ p σ d E ≤
        cyclicRealCubeMass N q ℓ σ (cyclicLiftValue N q M p σ d c) := by
  classical
  let W (z : PositiveCubeParameters N q ℓ) :=
    cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 (label z.2.1) z.2.2.2
  let P (z : PositiveCubeParameters N q ℓ) :=
    0 < cyclicDistinctCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2
  let Q (z : PositiveCubeParameters N q ℓ) (c : CyclicLiftAssignments N q) :=
    cyclicRealCubeDifference q ℓ (cyclicLiftValue N q M p σ d c) z.1 z.2.2.1 (label z.2.1) z.2.2.2 = 0
  have hW (z : PositiveCubeParameters N q ℓ) : 0 ≤ W z :=
    (cyclicCubeWeight_bounds N q ℓ σ z.1 z.2.2.1 (label z.2.1) z.2.2.2 hσ).1
  have hp (z : PositiveCubeParameters N q ℓ) (hz : P z) :
      1 / (57 : ℝ) ^ 16 ≤ realUniformMean (fun c => if Q z c then 1 else 0) :=
    cyclic_lift_cube_probability hM p σ hσ d E hscale z.1 z.2.2.1 (label z.2.1) z.2.2.2 hz
  obtain ⟨c, hc⟩ := exists_global_weighted_success W hW P Q (1 / (57 : ℝ) ^ 16) hp
  refine ⟨c, ?_⟩
  simpa only [W, P, Q, cyclicDistinctCubeNearWeight_eq_ite_pos N q ℓ p σ hσ,
    cyclicDistinctPositiveCubeNearMass, cyclicRealCubeMass] using hc

theorem exists_cyclic_real_lift {N q ℓ M : ℕ} [NeZero q] (hM : 9 ≤ M)
    (p : Base N → Frequency) (σ : Base N → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (d : ℕ) (E : ℝ) (hscale : (M : ℝ) * (E / (N : ℝ) ^ 3) ≤ 1)
    (herror : 19 / (2 * (M : ℝ)) ≤ 19 * E / (N : ℝ) ^ 3) :
    ∃ F : Fin N → ZMod q → ℝ,
      (∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) ∧
      (∀ x Y, |F x Y| ≤ 3) ∧
      (∀ x Y, cyclicField N q σ 0 x Y = 0 → F x Y = 0) ∧
      (∀ x Y, 0 < cyclicField N q σ 0 x Y →
        ‖((F x Y : ℝ) : Frequency) - d • cyclicField N q p 0 x Y‖ ≤ 19 * E / (N : ℝ) ^ 3) ∧
      (1 / (57 : ℝ) ^ 16) * cyclicDistinctPositiveCubeNearMass N q ℓ p σ d E ≤
        cyclicRealCubeMass N q ℓ σ F := by
  have hm : 0 < M := by omega
  obtain ⟨c, hc⟩ := exists_cyclic_lift_choice (q := q) (ℓ := ℓ) hm p σ hσ d E hscale
  refine ⟨cyclicLiftValue N q M p σ d c,
    cyclicLiftValue_grid hm p σ d c, cyclicLiftValue_abs_le hM p σ d c,
    cyclicLiftValue_zero p σ d c, ?_, hc⟩
  intro x Y hs
  exact (cyclicLiftValue_circle_error hm p σ d c x Y hs).trans herror

end GMZP0
