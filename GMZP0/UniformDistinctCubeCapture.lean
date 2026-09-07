import GMZP0.UniformCollisionScale
import GMZP0.UniformPositiveCubeCapture

/-! Positive original-weight mass of successful cubes with sixteen distinct actual vertices. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cyclicDistinctCubeNearWeight_pos_iff (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ)
    (u : CubeShiftPairs ℓ) :
    0 < cyclicDistinctCubeNearWeight N q ℓ p σ d E x Y h u ↔
      Function.Injective (cyclicCubeVertex q ℓ h Y u) ∧
      ‖d • cyclicCubeCubicCoeff N q ℓ p x Y h u‖ ≤ E / (N : ℝ) ^ 3 ∧
      0 < cyclicCubeWeight N q ℓ σ x Y h u := by
  classical
  unfold cyclicDistinctCubeNearWeight cyclicCubeNearWeight
  split_ifs <;> simp_all

theorem uniform_distinct_original_cube_capture (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c a : ℝ, ∃ d : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < a ∧ 0 < d ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [Fact q.Prime], N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ b : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ b ≤ x.val ∧ x.val ≤ b + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          (a / 4) ^ 16 / 4 ≤ cyclicDistinctPositiveCubeNearMass N q (smoothingRadius N a)
            θ (originalScaledWeight N μ D) d E ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, a, d, E, N₁, hM, hc, ha, hd, hE, hN₁, hcubes⟩ :=
    uniform_positive_original_cube_capture κ η hκ hη hη1
  obtain ⟨N₂, hN₂, hscales⟩ := uniform_collision_scale a ((a / 4) ^ 16 / 4) ha (by positivity)
  refine ⟨M, c, a, d, E, max N₁ N₂, hM, hc, ha, hd, hE,
    hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hNN
  have hNN₂ : N₂ ≤ N := (le_max_right _ _).trans hNN
  have hN : 0 < N := hN₁.trans_le hNN₁
  obtain ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, hnear, hresponse⟩ :=
    hcubes N hNN₁ q hq hqUpper f θ lam μ hdata
  obtain ⟨hstep, hshort, hbudget⟩ := hscales N hNN₂ q hq
  have hclean := cyclicDistinctPositiveCubeNearMass_lower hN hshort hstep θ
    (originalScaledWeight N μ D) (originalScaledWeight_bounds hN μ D hdata.2.2.1) d E
  refine ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  linarith

end GMZP0
