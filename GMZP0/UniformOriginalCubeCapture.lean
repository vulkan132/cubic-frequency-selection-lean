import GMZP0.WeightedCubeWeyl
import GMZP0.UniformWeightedTimeAverage

/-! Uniform positive original cube weight at the natural scale, with all original responses. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_cube_capture (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c a : ℝ, ∃ d : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < a ∧ 0 < d ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q], N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ b : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ b ≤ x.val ∧ x.val ≤ b + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          (a / 4) ^ 16 / 2 ≤ cyclicCubeNearMass N q (smoothingRadius N a)
            θ (originalScaledWeight N μ D) d E ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, a, N₀, hM, hc, ha, hN₀, hwindow⟩ :=
    uniform_positive_weighted_time_average κ η hκ hη hη1
  obtain ⟨d, E, hd, hE, hw⟩ := uniform_weighted_cube_weyl ((a / 4) ^ 16) (by positivity)
  refine ⟨M, c, a, d, E, N₀, hM, hc, ha, hd, hE, hN₀, ?_⟩
  intro N hNth q _ hq hqUpper f θ lam μ hdata
  have hN : 0 < N := hN₀.trans_le hNth
  obtain ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, htime, hresponse⟩ :=
    hwindow N hNth q hq hqUpper f θ lam μ hdata
  refine ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  exact hw N hN q (smoothingRadius N a) θ (originalScaledWeight N μ D)
    (originalScaledWeight_bounds hN μ D hdata.2.2.1) htime

end GMZP0
